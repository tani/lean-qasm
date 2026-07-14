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
  "=", "#", ">", "<", "+", "-", "*", "/", "%", "|", "&", "^", "@", "~", "!"
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

inductive Literal where
  | integer (raw : String)
  | float (raw : String)
  | imaginary (raw : String)
  | boolean (value : Bool)
  | bitstring (value : String)
  | timing (raw : String)
  deriving Repr, Inhabited, BEq

inductive Expression where
  | literal (value : Literal)
  | identifier (name : String)
  | hardwareQubit (index : Nat)
  | unary (operator : String) (operand : Expression)
  | binary (operator : String) (left right : Expression)
  | call (name : String) (arguments : Array Expression)
  | cast (typeName : String) (width : Option Expression) (value : Expression)
  | index (value : Expression) (indices : Array Expression)
  | range (start step stop : Option Expression)
  | set (values : Array Expression)
  | array (values : Array Expression)
  deriving Repr, Inhabited, BEq

inductive TypeSpec where
  | scalar (name : String) (width : Option Expression := none)
  | array (element : TypeSpec) (dimensions : Array Expression)
  | arrayRef (mutable : Bool) (element : TypeSpec)
      (dimensions : Array Expression) (dimensionCount : Option Expression)
  deriving Repr, Inhabited, BEq

structure ArgumentDefinition where
  type : TypeSpec
  name : String
  deriving Repr, Inhabited, BEq

inductive Statement where
  | includeFile (filename : String)
  | qubit (name : String) (size : Nat := 1)
  | bit (name : String) (size : Nat := 1)
  | qreg (name : String) (size : Nat := 1)
  | creg (name : String) (size : Nat := 1)
  | gateCall (name : String) (parameters : Array Expression) (operands : Array Operand)
  | measure (source : Operand) (target : Option Operand)
  | reset (operand : Operand)
  | barrier (operands : Array Operand)

  | classicalDeclaration (type : TypeSpec) (name : String)
      (initializer : Option Expression)
  | constDeclaration (type : TypeSpec) (name : String) (value : Expression)
  | ioDeclaration (input : Bool) (type : TypeSpec) (name : String)
  | aliasDeclaration (name : String) (value : Expression)
  | assignment (target : Expression) (operator : String) (value : Expression)
  | expression (value : Expression)
  | scope (statements : Array Statement)
  | ifStatement (condition : Expression) (thenBody : Array Statement)
      (elseBody : Option (Array Statement))
  | whileStatement (condition : Expression) (body : Array Statement)
  | forStatement (type : TypeSpec) (iterator : String)
      (iterable : Expression) (body : Array Statement)
  | breakStatement
  | continueStatement
  | endStatement
  | returnStatement (value : Option Expression)
  | defStatement (name : String) (arguments : Array ArgumentDefinition)
      (returnType : Option TypeSpec) (body : Array Statement)
  | externStatement (name : String) (arguments : Array TypeSpec)
      (returnType : Option TypeSpec)
  | gateDefinition (name : String) (parameters qubits : Array String)
      (body : Array Statement)
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
  | .hardwareQubit hardwareIndex => s!"${hardwareIndex}"
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


private def scalarTypeNames : List String :=
  ["bit", "int", "uint", "float", "angle", "bool", "duration", "stretch", "complex"]

private def isScalarTypeName (name : String) : Bool := scalarTypeNames.contains name

private def binaryPrecedence : String → Option Nat
  | "||" => some 1
  | "&&" => some 2
  | "|" => some 3
  | "^" => some 4
  | "&" => some 5
  | "==" | "!=" => some 6
  | ">" | "<" | ">=" | "<=" => some 7
  | ">>" | "<<" => some 8
  | "+" | "-" | "++" => some 9
  | "*" | "/" | "%" => some 10
  | "**" => some 11
  | _ => none

private def currentOperator? : GrammarParser (Option (String × Nat)) := do
  match ← current? with
  | some ⟨.symbol operator, _⟩ => pure ((binaryPrecedence operator).map (operator, ·))
  | _ => pure none

private def classifyNumber (raw : String) : Literal :=
  if raw.endsWith "im" then .imaginary raw
  else if ["dt", "ns", "us", "µs", "ms", "s"].any (fun unit => raw.endsWith unit) then .timing raw
  else if raw.contains '.' || raw.contains 'e' || raw.contains 'E' then .float raw
  else .integer raw

mutual
  private partial def parseExpression (minimumPrecedence : Nat := 0) :
      GrammarParser Expression := do
    let left ← parseUnary
    parseBinaryRest left minimumPrecedence

  private partial def parseBinaryRest (left : Expression) (minimumPrecedence : Nat) :
      GrammarParser Expression := do
    match ← currentOperator? with
    | some (operator, precedence) =>
        if precedence < minimumPrecedence then pure left
        else
          let _ ← consume
          let nextMinimum := if operator == "**" then precedence else precedence + 1
          let right ← parseExpression nextMinimum
          parseBinaryRest (.binary operator left right) minimumPrecedence
    | none => pure left

  private partial def parseUnary : GrammarParser Expression := do
    match ← current? with
    | some ⟨.symbol operator, _⟩ =>
        if operator == "~" || operator == "!" || operator == "-" then
          let _ ← consume
          pure (.unary operator (← parseUnary))
        else parsePostfix (← parsePrimary)
    | _ => parsePostfix (← parsePrimary)

  private partial def parsePrimary : GrammarParser Expression := do
    match (← consume).kind with
    | .number raw => pure (.literal (classifyNumber raw))
    | .stringLiteral value => pure (.literal (.bitstring value))
    | .hardwareQubit index => pure (.hardwareQubit index)
    | .identifier "true" => pure (.literal (.boolean true))
    | .identifier "false" => pure (.literal (.boolean false))
    | .identifier name =>
        let saved ← get
        let width ←
          if isScalarTypeName name && (← accept "[") then
            let width ← parseExpression
            expect "]"
            pure (some width)
          else pure none
        if isScalarTypeName name && (← accept "(") then
          let value ← parseExpression
          expect ")"
          pure (.cast name width value)
        else
          set saved
          if ← accept "(" then
            pure (.call name (← parseExpressionList ")"))
          else pure (.identifier name)
    | .symbol "(" =>
        let value ← parseExpression
        expect ")"
        pure value
    | .symbol "{" => pure (.array (← parseExpressionList "}"))
    | _ => failAtCurrent "expected expression"

  private partial def parsePostfix (value : Expression) : GrammarParser Expression := do
    if ← accept "[" then
      let indices ← parseExpressionList "]"
      parsePostfix (.index value indices)
    else pure value

  private partial def parseExpressionList (terminator : String)
      (values : Array Expression := #[]) : GrammarParser (Array Expression) := do
    if ← accept terminator then pure values
    else
      let values := values.push (← parseExpression)
      if ← accept "," then parseExpressionList terminator values
      else
        expect terminator
        pure values
end

private partial def parseType : GrammarParser TypeSpec := do
  let name ← parseIdentifier
  if name == "array" then
    expect "["
    let element ← parseType
    expect ","
    let dimensions ← parseExpressionList "]"
    pure (.array element dimensions)
  else if name == "readonly" || name == "mutable" then
    let mutable := name == "mutable"
    let arrayName ← parseIdentifier
    unless arrayName == "array" do failAtCurrent "expected array reference type"
    expect "["
    let element ← parseType
    expect ","
    if ← accept "#" then
      expect "dim"
      expect "="
      let count ← parseExpression
      expect "]"
      pure (.arrayRef mutable element #[] (some count))
    else
      pure (.arrayRef mutable element (← parseExpressionList "]") none)
  else if isScalarTypeName name then
    let width ← if ← accept "[" then
      let value ← parseExpression
      expect "]"
      pure (some value)
    else pure none
    pure (.scalar name width)
  else failAtCurrent s!"unknown OpenQASM type '{name}'"

private def assignmentOperators : List String :=
  ["=", "+=", "-=", "*=", "/=", "&=", "|=", "^=", "<<=", ">>=", "%=", "**="]

private def currentAssignmentOperator? : GrammarParser (Option String) := do
  match ← current? with
  | some ⟨.symbol operator, _⟩ =>
      pure (if assignmentOperators.contains operator then some operator else none)
  | _ => pure none
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

private partial def parseStatement : GrammarParser Statement := do
  match ← current? with
  | some ⟨.symbol "{", _⟩ =>
      let _ ← consume
      pure (.scope (← parseBlockStatements))
  | some ⟨.identifier "include", _⟩ =>
      let _ ← consume
      let filename ← match (← consume).kind with
        | .stringLiteral value => pure value
        | _ => failAtCurrent "expected include filename"
      expect ";"
      pure (.includeFile filename)
  | some ⟨.identifier "qubit", _⟩ => let _ ← consume; parseDeclaration true false
  | some ⟨.identifier "qreg", _⟩ => let _ ← consume; parseDeclaration true true
  | some ⟨.identifier "creg", _⟩ => let _ ← consume; parseDeclaration false true
  | some ⟨.identifier "const", _⟩ =>
      let _ ← consume
      let type ← parseType
      let name ← parseIdentifier
      expect "="
      let value ← parseExpression
      expect ";"
      pure (.constDeclaration type name value)
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
  | some ⟨.identifier "if", _⟩ =>
      let _ ← consume
      expect "("
      let condition ← parseExpression
      expect ")"
      let thenBody ← parseBody
      let elseBody ← if ← accept "else" then some <$> parseBody else pure none
      pure (.ifStatement condition thenBody elseBody)
  | some ⟨.identifier "while", _⟩ =>
      let _ ← consume
      expect "("
      let condition ← parseExpression
      expect ")"
      pure (.whileStatement condition (← parseBody))
  | some ⟨.identifier "for", _⟩ =>
      let _ ← consume
      let type ← parseType
      let iterator ← parseIdentifier
      expect "in"
      let iterable ← parseForIterable
      pure (.forStatement type iterator iterable (← parseBody))
  | some ⟨.identifier "break", _⟩ =>
      let _ ← consume
      expect ";"
      pure .breakStatement
  | some ⟨.identifier "continue", _⟩ =>
      let _ ← consume
      expect ";"
      pure .continueStatement
  | some ⟨.identifier "end", _⟩ =>
      let _ ← consume
      expect ";"
      pure .endStatement
  | some ⟨.identifier "return", _⟩ =>
      let _ ← consume
      if ← accept ";" then pure (.returnStatement none)
      else
        let value ← parseExpression
        expect ";"
        pure (.returnStatement (some value))
  | some ⟨.identifier "def", _⟩ =>
      let _ ← consume
      let name ← parseIdentifier
      expect "("
      let arguments ← parseArgumentList
      let returnType ← parseReturnType?
      pure (.defStatement name arguments returnType (← parseRequiredScope))
  | some ⟨.identifier "extern", _⟩ =>
      let _ ← consume
      let name ← parseIdentifier
      expect "("
      let arguments ← parseTypeList
      let returnType ← parseReturnType?
      expect ";"
      pure (.externStatement name arguments returnType)
  | some ⟨.identifier "gate", _⟩ =>
      let _ ← consume
      let name ← parseIdentifier
      let parameters ← if ← accept "(" then parseNameList ")" else pure #[]
      let qubits ← parseNameList "{"
      pure (.gateDefinition name parameters qubits (← parseBlockStatements))
  | some ⟨.identifier direction, _⟩ =>
      if direction == "input" || direction == "output" then
        let _ ← consume
        let type ← parseType
        let name ← parseIdentifier
        expect ";"
        pure (.ioDeclaration (direction == "input") type name)
      else if direction == "let" then
        let _ ← consume
        let name ← parseIdentifier
        expect "="
        let value ← parseExpression
        expect ";"
        pure (.aliasDeclaration name value)
      else if isScalarTypeName direction || direction == "array" then
        let type ← parseType
        let name ← parseIdentifier
        let initializer ← if ← accept "=" then some <$> parseExpression else pure none
        expect ";"
        pure (.classicalDeclaration type name initializer)
      else parseIdentifierLedStatement
  | _ => failAtCurrent "unsupported OpenQASM statement in the 60% frontend"

where
  parseBlockStatements (statements : Array Statement := #[]) :
      GrammarParser (Array Statement) := do
    if ← accept "}" then pure statements
    else parseBlockStatements (statements.push (← parseStatement))

  parseBody : GrammarParser (Array Statement) := do
    if ← accept "{" then parseBlockStatements
    else pure #[← parseStatement]

  parseRequiredScope : GrammarParser (Array Statement) := do
    expect "{"
    parseBlockStatements

  parseArgumentType : GrammarParser TypeSpec := do
    match ← current? with
    | some ⟨.identifier name, _⟩ =>
        if name == "qubit" || name == "qreg" || name == "creg" then
          let _ ← consume
          let width ← if ← accept "[" then
            let width ← parseExpression
            expect "]"
            pure (some width)
          else pure none
          pure (.scalar name width)
        else parseType
    | _ => failAtCurrent "expected argument type"

  parseArgumentList (arguments : Array ArgumentDefinition := #[]) :
      GrammarParser (Array ArgumentDefinition) := do
    if ← accept ")" then pure arguments
    else
      let type ← parseArgumentType
      let name ← parseIdentifier
      let arguments := arguments.push ⟨type, name⟩
      if ← accept "," then parseArgumentList arguments
      else
        expect ")"
        pure arguments

  parseTypeList (types : Array TypeSpec := #[]) : GrammarParser (Array TypeSpec) := do
    if ← accept ")" then pure types
    else
      let types := types.push (← parseArgumentType)
      if ← accept "," then parseTypeList types
      else
        expect ")"
        pure types

  parseReturnType? : GrammarParser (Option TypeSpec) := do
    if ← accept "->" then some <$> parseType else pure none

  parseNameList (terminator : String) (names : Array String := #[]) :
      GrammarParser (Array String) := do
    if ← accept terminator then pure names
    else
      let names := names.push (← parseIdentifier)
      if ← accept "," then parseNameList terminator names
      else
        expect terminator
        pure names

  parseForIterable : GrammarParser Expression := do
    if ← accept "[" then
      let start ← if ← accept ":" then pure none else
        let start ← parseExpression
        expect ":"
        pure (some start)
      let middle ← if ← accept "]" then pure none else some <$> parseExpression
      match middle with
      | none => pure (.range start none none)
      | some middle =>
          if ← accept ":" then
            let stop ← if ← accept "]" then pure none else
              let stop ← parseExpression
              expect "]"
              pure (some stop)
            pure (.range start (some middle) stop)
          else
            expect "]"
            pure (.range start none (some middle))
    else parseExpression

  parseIdentifierLedStatement : GrammarParser Statement := do
    let saved ← get
    let candidate ← parseExpression
    match ← currentAssignmentOperator? with
    | some operator =>
        let _ ← consume
        let value ← parseExpression
        expect ";"
        pure (.assignment candidate operator value)
    | none =>
        if ← accept ";" then pure (.expression candidate)
        else
          set saved
          let name ← parseIdentifier
          let parameters ← if ← accept "(" then parseExpressionList ")" else pure #[]
          let operands ← parseOperandList
          expect ";"
          pure (.gateCall name parameters operands)


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


private def Literal.toQasm : Literal → String
  | .integer raw | .float raw | .imaginary raw | .timing raw => raw
  | .boolean true => "true"
  | .boolean false => "false"
  | .bitstring value => s!"\"{value}\""

partial def Expression.toQasm : Expression → String
  | .literal value => value.toQasm
  | .identifier name => name
  | .hardwareQubit hardwareIndex => s!"${hardwareIndex}"
  | .unary operator operand => s!"{operator}{operand.toQasm}"
  | .binary operator left right => s!"({left.toQasm} {operator} {right.toQasm})"
  | .call name arguments =>
      s!"{name}({String.intercalate ", " (arguments.toList.map Expression.toQasm)})"
  | .cast name width value =>
      let width := width.map (fun width => s!"[{width.toQasm}]") |>.getD ""
      s!"{name}{width}({value.toQasm})"
  | .index value indices =>
      s!"{value.toQasm}[{String.intercalate ", " (indices.toList.map Expression.toQasm)}]"
  | .range start step stop =>
      let start := start.map Expression.toQasm |>.getD ""
      let stop := stop.map Expression.toQasm |>.getD ""
      match step with
      | none => s!"{start}:{stop}"
      | some step => s!"{start}:{step.toQasm}:{stop}"
  | .set values => "{" ++ String.intercalate ", " (values.toList.map Expression.toQasm) ++ "}"
  | .array values => "{" ++ String.intercalate ", " (values.toList.map Expression.toQasm) ++ "}"

partial def TypeSpec.toQasm : TypeSpec → String
  | .scalar name none => name
  | .scalar name (some width) => s!"{name}[{width.toQasm}]"
  | .array element dimensions =>
      s!"array[{element.toQasm}, {String.intercalate ", " (dimensions.toList.map Expression.toQasm)}]"
  | .arrayRef mutable element dimensions none =>
      let qualifier := if mutable then "mutable" else "readonly"
      s!"{qualifier} array[{element.toQasm}, {String.intercalate ", " (dimensions.toList.map Expression.toQasm)}]"
  | .arrayRef mutable element _ (some count) =>
      let qualifier := if mutable then "mutable" else "readonly"
      s!"{qualifier} array[{element.toQasm}, #dim={count.toQasm}]"
partial def Statement.toQasm : Statement → String
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
        else s!"({String.intercalate ", " (parameters.toList.map Expression.toQasm)})"
      s!"{name}{parameters} {joinOperands operands};"
  | .measure source none => s!"measure {source.toQasm};"
  | .measure source (some target) => s!"measure {source.toQasm} -> {target.toQasm};"
  | .reset operand => s!"reset {operand.toQasm};"
  | .barrier operands => if operands.isEmpty then "barrier;"
      else s!"barrier {joinOperands operands};"
  | .classicalDeclaration type name none => s!"{type.toQasm} {name};"
  | .classicalDeclaration type name (some initializer) =>
      s!"{type.toQasm} {name} = {initializer.toQasm};"
  | .constDeclaration type name value => s!"const {type.toQasm} {name} = {value.toQasm};"
  | .ioDeclaration input type name =>
      s!"{if input then "input" else "output"} {type.toQasm} {name};"
  | .aliasDeclaration name value => s!"let {name} = {value.toQasm};"
  | .assignment target operator value => s!"{target.toQasm} {operator} {value.toQasm};"
  | .expression value => s!"{value.toQasm};"
  | .scope statements => block statements
  | .ifStatement condition thenBody none =>
      s!"if ({condition.toQasm}) {block thenBody}"
  | .ifStatement condition thenBody (some elseBody) =>
      s!"if ({condition.toQasm}) {block thenBody} else {block elseBody}"
  | .whileStatement condition body => s!"while ({condition.toQasm}) {block body}"
  | .forStatement type iterator iterable body =>
      let iterable := match iterable with
        | .range _ _ _ => s!"[{iterable.toQasm}]"
        | _ => iterable.toQasm
      s!"for {type.toQasm} {iterator} in {iterable} {block body}"
  | .breakStatement => "break;"
  | .continueStatement => "continue;"
  | .endStatement => "end;"
  | .returnStatement none => "return;"
  | .returnStatement (some value) => s!"return {value.toQasm};"
  | .defStatement name arguments returnType body =>
      let arguments := arguments.toList.map fun argument =>
        s!"{argument.type.toQasm} {argument.name}"
      let returnType := returnType.map (fun type => s!" -> {type.toQasm}") |>.getD ""
      s!"def {name}({String.intercalate ", " arguments}){returnType} {block body}"
  | .externStatement name arguments returnType =>
      let arguments := arguments.toList.map TypeSpec.toQasm
      let returnType := returnType.map (fun type => s!" -> {type.toQasm}") |>.getD ""
      s!"extern {name}({String.intercalate ", " arguments}){returnType};"
  | .gateDefinition name parameters qubits body =>
      let parameters := if parameters.isEmpty then ""
        else s!"({String.intercalate ", " parameters.toList})"
      s!"gate {name}{parameters} {String.intercalate ", " qubits.toList} {block body}"
where
  indent (source : String) : String :=
    String.intercalate "\n" (source.splitOn "\n" |>.map fun line => "  " ++ line)

  block (statements : Array Statement) : String :=
    if statements.isEmpty then "{}"
    else
      let body := statements.toList.map (fun statement => indent statement.toQasm)
      "{\n" ++ String.intercalate "\n" body ++ "\n}"

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
