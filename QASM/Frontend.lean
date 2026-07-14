    import Lean
    import LiterateLean
    import Std.Internal.Parsec.String

    open scoped LiterateLean

# OpenQASM 3.0 frontend

The frontend parses OpenQASM source independently of Lean's token grammar.

```lean
namespace QASM
namespace Frontend

structure SourcePos where
  offset : Nat
  line : Nat
  column : Nat
  deriving Repr, Inhabited, BEq

structure SourceSpan where
  start : SourcePos
  stop : SourcePos
  deriving Repr, Inhabited, BEq

structure ParseError where
  position : SourcePos
  message : String
  deriving Repr, Inhabited, BEq

instance : ToString ParseError where
  toString error := s!"{error.position.line}:{error.position.column}: {error.message}"

inductive TokenKind where
  | identifier (value : String)
  | number (raw : String)
  | stringLiteral (value : String)
  | hardwareQubit (index : Nat)
  | symbol (value : String)
  | newline
  deriving Repr, Inhabited, BEq

structure Token where
  kind : TokenKind
  span : SourceSpan
  deriving Repr, Inhabited, BEq


private structure LexCursor where
  rest : List Char
  position : SourcePos

private def initialCursor (source : String) : LexCursor :=
  ⟨source.toList, ⟨0, 1, 1⟩⟩

private def advancePosition (position : SourcePos) (char : Char) : SourcePos :=
  if char == '\n' then ⟨position.offset + 1, position.line + 1, 1⟩
  else ⟨position.offset + 1, position.line, position.column + 1⟩

private def LexCursor.next? (cursor : LexCursor) : Option (Char × LexCursor) :=
  match cursor.rest with
  | [] => none
  | char :: rest => some (char, ⟨rest, advancePosition cursor.position char⟩)

private partial def takeWhile
    (predicate : Char → Bool) (cursor : LexCursor)
    (accumulator : List Char := []) : String × LexCursor :=
  match cursor.rest with
  | char :: _ =>
      if predicate char then
        match cursor.next? with
        | some (_, next) => takeWhile predicate next (char :: accumulator)
        | none => (String.ofList accumulator.reverse, cursor)
      else (String.ofList accumulator.reverse, cursor)
  | [] => (String.ofList accumulator.reverse, cursor)

private def startsWithChars (chars expectedChars : List Char) : Bool :=
  match expectedChars, chars with
  | [], _ => true
  | _, [] => false
  | expected :: expectedChars, actual :: chars =>
      expected == actual && startsWithChars chars expectedChars

private partial def consumeCount (count : Nat) (cursor : LexCursor) : LexCursor :=
  match count with
  | 0 => cursor
  | count + 1 =>
      match cursor.next? with
      | none => cursor
      | some (_, next) => consumeCount count next

private def isIdentifierStart (char : Char) : Bool :=
  char == '_' || char.isAlpha || char.toNat ≥ 0x80
private def isIdentifierRest (char : Char) : Bool := isIdentifierStart char || char.isDigit
private def isNumberRest (char : Char) : Bool :=
  char.isAlphanum || char == '_' || char == '.' || char == 'µ'

private def symbols : List String := [
  "**=", "<<=", ">>=", "->", "++", "**", "||", "&&", "==", "!=",
  ">=", "<=", "+=", "-=", "*=", "/=", "&=", "|=", "^=", "%=",
  "<<", ">>", "[", "]", "{", "}", "(", ")", ":", ";", ".", ",",
  "=", "+", "-", "*", "/", "%", "|", "&", "^", "@", "~", "!"
]

private def matchingSymbol? (cursor : LexCursor) : Option String :=
  symbols.find? fun symbol => startsWithChars cursor.rest symbol.toList

private partial def skipLineComment (cursor : LexCursor) : LexCursor :=
  match cursor.rest with
  | [] | '\n' :: _ => cursor
  | _ => match cursor.next? with
    | none => cursor
    | some (_, next) => skipLineComment next

private partial def skipBlockComment (start : SourcePos) (cursor : LexCursor) :
    Except ParseError LexCursor :=
  if startsWithChars cursor.rest ['*', '/'] then pure (consumeCount 2 cursor)
  else match cursor.next? with
    | none => throw ⟨start, "unterminated block comment"⟩
    | some (_, next) => skipBlockComment start next

private partial def lexString (quote : Char) (start : SourcePos) (cursor : LexCursor)
    (accumulator : List Char := []) : Except ParseError (String × LexCursor) :=
  match cursor.next? with
  | none => throw ⟨start, "unterminated string literal"⟩
  | some (char, next) =>
      if char == quote then pure (String.ofList accumulator.reverse, next)
      else if char == '\n' || char == '\r' || char == '\t' then
        throw ⟨cursor.position, "line break or tab in string literal"⟩
      else lexString quote start next (char :: accumulator)

private partial def lexTokens (cursor : LexCursor) (tokens : Array Token := #[]) :
    Except ParseError (Array Token) := do
  match cursor.rest with
  | [] => pure tokens
  | char :: _ =>
      let start := cursor.position
      if char == ' ' || char == '\t' || char == '\r' then
        match cursor.next? with
        | none => pure tokens
        | some (_, next) => lexTokens next tokens
      else if char == '\n' then
        match cursor.next? with
        | none => pure tokens
        | some (_, next) => lexTokens next (tokens.push ⟨.newline, ⟨start, next.position⟩⟩)
      else if startsWithChars cursor.rest ['/', '/'] then
        lexTokens (skipLineComment (consumeCount 2 cursor)) tokens
      else if startsWithChars cursor.rest ['/', '*'] then
        let next ← skipBlockComment start (consumeCount 2 cursor)
        lexTokens next tokens
      else if char == '"' || char == '\'' then
        let (value, next) ← lexString char start (consumeCount 1 cursor)
        lexTokens next (tokens.push ⟨.stringLiteral value, ⟨start, next.position⟩⟩)
      else if char == '$' then
        let (digits, next) := takeWhile Char.isDigit (consumeCount 1 cursor)
        if digits.isEmpty then throw ⟨start, "hardware qubit requires a decimal index"⟩
        else lexTokens next (tokens.push ⟨.hardwareQubit digits.toNat!, ⟨start, next.position⟩⟩)
      else if isIdentifierStart char then
        let (identifier, next) := takeWhile isIdentifierRest cursor
        lexTokens next (tokens.push ⟨.identifier identifier, ⟨start, next.position⟩⟩)
      else if char.isDigit then
        let (raw, next) := takeWhile isNumberRest cursor
        lexTokens next (tokens.push ⟨.number raw, ⟨start, next.position⟩⟩)
      else match matchingSymbol? cursor with
        | some symbol =>
            let next := consumeCount symbol.length cursor
            lexTokens next (tokens.push ⟨.symbol symbol, ⟨start, next.position⟩⟩)
        | none => throw ⟨start, s!"unexpected character {repr char}"⟩

private abbrev SourceParser := Std.Internal.Parsec.String.Parser

private def tokenStreamParser : SourceParser (Array Token) := fun input =>
  match lexTokens (initialCursor input.1) with
  | .ok tokens => .success ⟨input.1, input.1.endPos⟩ tokens
  | .error error => .error input (.other (toString error))

def lex (source : String) : Except ParseError (Array Token) :=
  lexTokens (initialCursor source)

private def _parsecImplementationWitness : SourceParser (Array Token) := tokenStreamParser

structure Version where
  major : Nat
  minor : Nat
  deriving Repr, Inhabited, BEq

inductive Operand where
  | identifier (name : String) (index : Option Nat := none)
  | hardware (index : Nat)
  deriving Repr, Inhabited, BEq

inductive Statement where
  | includeFile (filename : String)
  | qubit (name : String) (size : Nat := 1)
  | bit (name : String) (size : Nat := 1)
  | qreg (name : String) (size : Nat := 1)
  | creg (name : String) (size : Nat := 1)
  | gateCall (name : String) (parameters : Array String) (operands : Array Operand)
  | measure (source : Operand) (target : Option Operand)
  | reset (operand : Operand)
  | barrier (operands : Array Operand)
  deriving Repr, Inhabited, BEq

structure Program where
  version : Option Version
  statements : Array Statement
  deriving Repr, Inhabited, BEq

private structure ParseCursor where
  tokens : Array Token
  index : Nat := 0

private abbrev GrammarParser := StateT ParseCursor (Except ParseError)

private partial def skipNewlines : GrammarParser Unit := do
  let cursor ← get
  match cursor.tokens[cursor.index]? with
  | some ⟨.newline, _⟩ =>
      set { cursor with index := cursor.index + 1 }
      skipNewlines
  | _ => pure ()

private def current? : GrammarParser (Option Token) := do
  skipNewlines
  let cursor ← get
  pure cursor.tokens[cursor.index]?

private def failAtCurrent (message : String) : GrammarParser α := do
  let cursor ← get
  match cursor.tokens[cursor.index]? with
  | some token => throw ⟨token.span.start, message⟩
  | none => throw ⟨cursor.tokens.back?.map (·.span.stop) |>.getD ⟨0, 1, 1⟩, message⟩

private def consume : GrammarParser Token := do
  skipNewlines
  let cursor ← get
  match cursor.tokens[cursor.index]? with
  | none => failAtCurrent "unexpected end of input"
  | some token =>
      set { cursor with index := cursor.index + 1 }
      pure token

private def tokenText : TokenKind → String
  | .identifier value | .number value | .symbol value => value
  | .stringLiteral value => s!"\"{value}\""
  | .hardwareQubit index => s!"${index}"
  | .newline => "\n"

private def kindMatches (expected : String) : TokenKind → Bool
  | .identifier value | .symbol value => value == expected
  | _ => false

private def accept (expected : String) : GrammarParser Bool := do
  match ← current? with
  | some token =>
      if kindMatches expected token.kind then
        let _ ← consume
        pure true
      else pure false
  | none => pure false

private def expect (expected : String) : GrammarParser Unit := do
  unless ← accept expected do failAtCurrent s!"expected '{expected}'"

private def parseIdentifier : GrammarParser String := do
  match (← consume).kind with
  | .identifier value => pure value
  | _ => failAtCurrent "expected identifier"

private def parseNat : GrammarParser Nat := do
  match (← consume).kind with
  | .number raw => match raw.toNat? with
    | some value => pure value
    | none => failAtCurrent "expected decimal integer"
  | _ => failAtCurrent "expected decimal integer"

private def parseSize? : GrammarParser (Option Nat) := do
  if ← accept "[" then
    let size ← parseNat
    expect "]"
    pure (some size)
  else pure none

private def parseOperand : GrammarParser Operand := do
  match ← current? with
  | some ⟨.hardwareQubit index, _⟩ =>
      let _ ← consume
      pure (.hardware index)
  | some ⟨.identifier _, _⟩ =>
      let name ← parseIdentifier
      pure (.identifier name (← parseSize?))
  | _ => failAtCurrent "expected gate operand"

private partial def parseOperandList (operands : Array Operand := #[]) :
    GrammarParser (Array Operand) := do
  let operands := operands.push (← parseOperand)
  if ← accept "," then parseOperandList operands else pure operands

private partial def parseParameterTokens (depth : Nat := 0) (current : String := "")
    (parameters : Array String := #[]) : GrammarParser (Array String) := do
  let token ← consume
  match token.kind with
  | .symbol "(" => parseParameterTokens (depth + 1) (current ++ "(") parameters
  | .symbol ")" =>
      if depth == 0 then
        pure (if current.trimAscii.copy.isEmpty then parameters else parameters.push current.trimAscii.copy)
      else parseParameterTokens (depth - 1) (current ++ ")") parameters
  | .symbol "," =>
      if depth == 0 then parseParameterTokens depth "" (parameters.push current.trimAscii.copy)
      else parseParameterTokens depth (current ++ ",") parameters
  | kind => parseParameterTokens depth (current ++ tokenText kind) parameters

private def parseVersion? : GrammarParser (Option Version) := do
  if ← accept "OPENQASM" then
    let raw ← match (← consume).kind with
      | .number raw => pure raw
      | _ => failAtCurrent "expected OpenQASM version"
    expect ";"
    match raw.splitOn "." with
    | [major, minor] => match major.toNat?, minor.toNat? with
      | some 3, some 0 => pure (some ⟨3, 0⟩)
      | _, _ => failAtCurrent s!"unsupported OpenQASM version {raw}"
    | _ => failAtCurrent "invalid OpenQASM version"
  else pure none

private def parseDeclaration (quantum legacy : Bool) : GrammarParser Statement := do
  if legacy then
    let name ← parseIdentifier
    let size := (← parseSize?).getD 1
    expect ";"
    pure (if quantum then .qreg name size else .creg name size)
  else
    let size := (← parseSize?).getD 1
    let name ← parseIdentifier
    expect ";"
    pure (if quantum then .qubit name size else .bit name size)

private def parseStatement : GrammarParser Statement := do
  match ← current? with
  | some ⟨.identifier "include", _⟩ =>
      let _ ← consume
      let filename ← match (← consume).kind with
        | .stringLiteral value => pure value
        | _ => failAtCurrent "expected include filename"
      expect ";"
      pure (.includeFile filename)
  | some ⟨.identifier "qubit", _⟩ => let _ ← consume; parseDeclaration true false
  | some ⟨.identifier "bit", _⟩ => let _ ← consume; parseDeclaration false false
  | some ⟨.identifier "qreg", _⟩ => let _ ← consume; parseDeclaration true true
  | some ⟨.identifier "creg", _⟩ => let _ ← consume; parseDeclaration false true
  | some ⟨.identifier "measure", _⟩ =>
      let _ ← consume
      let source ← parseOperand
      let target ← if ← accept "->" then some <$> parseOperand else pure none
      expect ";"
      pure (.measure source target)
  | some ⟨.identifier "reset", _⟩ =>
      let _ ← consume
      let operand ← parseOperand
      expect ";"
      pure (.reset operand)
  | some ⟨.identifier "barrier", _⟩ =>
      let _ ← consume
      if ← accept ";" then pure (.barrier #[])
      else
        let operands ← parseOperandList
        expect ";"
        pure (.barrier operands)
  | some ⟨.identifier name, _⟩ =>
      let _ ← consume
      let parameters ← if ← accept "(" then parseParameterTokens else pure #[]
      let operands ← parseOperandList
      expect ";"
      pure (.gateCall name parameters operands)
  | _ => failAtCurrent "unsupported OpenQASM statement in the 20% frontend"

private partial def parseStatements (statements : Array Statement := #[]) :
    GrammarParser (Array Statement) := do
  match ← current? with
  | none => pure statements
  | some _ => parseStatements (statements.push (← parseStatement))

private def programParser : GrammarParser Program := do
  pure ⟨← parseVersion?, ← parseStatements⟩

def parseTokens (tokens : Array Token) : Except ParseError Program := do
  let (program, _) ← programParser.run ⟨tokens, 0⟩
  pure program

def parse (source : String) : Except ParseError Program := lex source >>= parseTokens

private def Operand.toQasm : Operand → String
  | .identifier name none => name
  | .identifier name (some index) => s!"{name}[{index}]"
  | .hardware index => s!"${index}"

private def joinOperands (operands : Array Operand) : String :=
  String.intercalate ", " (operands.toList.map Operand.toQasm)

def Statement.toQasm : Statement → String
  | .includeFile filename => s!"include \"{filename}\";"
  | .qubit name 1 => s!"qubit {name};"
  | .qubit name size => s!"qubit[{size}] {name};"
  | .bit name 1 => s!"bit {name};"
  | .bit name size => s!"bit[{size}] {name};"
  | .qreg name 1 => s!"qreg {name};"
  | .qreg name size => s!"qreg {name}[{size}];"
  | .creg name 1 => s!"creg {name};"
  | .creg name size => s!"creg {name}[{size}];"
  | .gateCall name parameters operands =>
      let parameters := if parameters.isEmpty then ""
        else s!"({String.intercalate ", " parameters.toList})"
      s!"{name}{parameters} {joinOperands operands};"
  | .measure source none => s!"measure {source.toQasm};"
  | .measure source (some target) => s!"measure {source.toQasm} -> {target.toQasm};"
  | .reset operand => s!"reset {operand.toQasm};"
  | .barrier operands => if operands.isEmpty then "barrier;"
      else s!"barrier {joinOperands operands};"

def Program.toQasm (program : Program) : String :=
  let version := program.version.map (fun v => s!"OPENQASM {v.major}.{v.minor};")
  String.intercalate "\n" (version.toList ++ program.statements.toList.map Statement.toQasm)
end Frontend

abbrev ParseError := Frontend.ParseError
abbrev SourceProgram := Frontend.Program

def parse (source : String) : Except ParseError SourceProgram :=
  Frontend.parse source
end QASM
```
