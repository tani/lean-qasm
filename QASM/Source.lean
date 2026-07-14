import Lean

namespace QASM

open Lean Parser

private def isHorizontalSpace (char : Char) : Bool :=
  char == ' ' || char == '\t' || char == '\r'

private partial def lineEnd (context : ParserContext) (position : String.Pos.Raw) :
    String.Pos.Raw :=
  if h : context.atEnd position then position
  else if context.get' position h == '\n' then position
  else lineEnd context (context.next' position h)

private def nextLine (context : ParserContext) (position : String.Pos.Raw) :
    String.Pos.Raw :=
  if h : context.atEnd position then position
  else context.next' position h

private partial def findEndDelimiter
    (context : ParserContext) (lineStart : String.Pos.Raw) :
    Option (String.Pos.Raw × String.Pos.Raw) :=
  if context.atEnd lineStart then none
  else
    let stop := lineEnd context lineStart
    let line := context.extract lineStart stop
    if line.trimAscii == "end_qasm" then
      some (lineStart, stop)
    else
      findEndDelimiter context (nextLine context stop)

/--
Consumes the raw bytes after `begin_qasm` through an `end_qasm` delimiter line.
The opening token's trailing whitespace has already been consumed by Lean's token parser, so the
token source range is used to recover the actual byte immediately following `begin_qasm`.
-/
private def qasmRawFn : ParserFn := fun context state => Id.run do
  let opening := state.stxStack.back
  let openingStop := opening.getTailPos?.getD state.pos
  let openingLineStop := lineEnd context openingStop
  let afterOpening := context.extract openingStop openingLineStop
  unless afterOpening.toList.all isHorizontalSpace do
    return state.mkUnexpectedErrorAt
      "`begin_qasm` must be followed only by whitespace and a newline"
      openingStop
  if context.atEnd openingLineStop then
    return state.mkUnexpectedErrorAt "unterminated `begin_qasm` block" openingStop
  let bodyStart := nextLine context openingLineStop
  let some (bodyStop, delimiterStop) := findEndDelimiter context bodyStart
    | return state.mkUnexpectedErrorAt "unterminated `begin_qasm` block" bodyStart
  let leading := context.mkEmptySubstringAt bodyStart
  let trailing := context.mkEmptySubstringAt bodyStop
  let body := context.extract bodyStart bodyStop
  let atom := mkAtom (.original leading bodyStart trailing bodyStop) body
  let state := state.setPos delimiterStop |>.pushSyntax atom
  whitespace context state

def qasmRaw : Parser where
  info := epsilonInfo
  fn := qasmRawFn

@[combinator_parenthesizer qasmRaw]
def qasmRaw.parenthesizer := Lean.PrettyPrinter.Parenthesizer.visitToken

@[combinator_formatter qasmRaw]
def qasmRaw.formatter := Lean.PrettyPrinter.Formatter.visitAtom Name.anonymous

syntax (name := qasmStringTerm) "begin_qasm" qasmRaw : term

@[macro qasmStringTerm] def expandQasmString : Macro := fun stx => do
  let some body := stx.getArgs.back?
    | Macro.throwErrorAt stx "invalid raw OpenQASM block"
  match body with
  | .atom _ value => pure (Lean.Syntax.mkStrLit value)
  | _ => Macro.throwErrorAt body "invalid raw OpenQASM block"

end QASM
