    import LiterateLean
    import Lean

    open scoped LiterateLean

# OpenQASM quotation parser for `qasm%`

`qasm% { ... }` performs balanced extraction and constructs the raw
OpenQASM source string as `qasmRaw`, implemented as a low-level parser.

```lean
namespace QASM

open Lean Parser


private inductive QasmBlockMode where
  | normal
  | string
  | lineComment
  | blockComment

private def qasmAdvance (context : ParserContext) (position : String.Pos.Raw) : String.Pos.Raw :=
  if h : context.atEnd position then position else context.next' position h

private def qasmChar? (context : ParserContext) (position : String.Pos.Raw) : Option Char :=
  if h : context.atEnd position then none else some (context.get' position h)

private partial def qasmFindClose (context : ParserContext) (position : String.Pos.Raw)
    (depth : Nat) (mode : QasmBlockMode) : Option String.Pos.Raw :=
  match qasmChar? context position with
  | none => none
  | some char =>
      let next := qasmAdvance context position
      match mode with
      | .normal =>
          if char == '"' then qasmFindClose context next depth .string
          else if char == '/' then
            match qasmChar? context next with
            | some '/' => qasmFindClose context (qasmAdvance context next) depth .lineComment
            | some '*' => qasmFindClose context (qasmAdvance context next) depth .blockComment
            | _ => qasmFindClose context next depth .normal
          else if char == '{' then qasmFindClose context next (depth + 1) .normal
          else if char == '}' then
            if depth == 0 then some position else qasmFindClose context next (depth - 1) .normal
          else qasmFindClose context next depth .normal
      | .string =>
          if char == '\\' then qasmFindClose context (qasmAdvance context next) depth .string
          else if char == '"' then qasmFindClose context next depth .normal
          else qasmFindClose context next depth .string
      | .lineComment =>
          if char == '\n' then qasmFindClose context next depth .normal
          else qasmFindClose context next depth .lineComment
      | .blockComment =>
          if char == '*' && qasmChar? context next == some '/' then
            qasmFindClose context (qasmAdvance context next) depth .normal
          else qasmFindClose context next depth .blockComment

private def qasmBlockFn : ParserFn := fun context state => Id.run do
  let opening := state.stxStack.back
  let bodyStart := opening.getTailPos?.getD state.pos
  let some bodyStop := qasmFindClose context bodyStart 0 .normal
    | return state.mkUnexpectedErrorAt "unterminated qasm% block" bodyStart
  let leading := context.mkEmptySubstringAt bodyStart
  let trailing := context.mkEmptySubstringAt bodyStop
  let body := context.extract bodyStart bodyStop
  let atom := mkAtom (.original leading bodyStart trailing bodyStop) body
  return (state.setPos (qasmAdvance context bodyStop)).pushSyntax atom

def qasmBlock : Parser where
  info := epsilonInfo
  fn := qasmBlockFn

@[combinator_parenthesizer qasmBlock]
def qasmBlock.parenthesizer := Lean.PrettyPrinter.Parenthesizer.visitToken

@[combinator_formatter qasmBlock]
def qasmBlock.formatter := Lean.PrettyPrinter.Formatter.visitAtom Name.anonymous

```

The raw quotation parser is registered before its syntax expansion.

```lean
syntax (name := qasmQuotation) "qasm%" "{" qasmBlock : term
syntax (name := qasmFileQuotation) "qasmFile%" str : term

private def normalizeQasmBlock (source : String) : String :=
  let source := if source.startsWith "\n" then source.drop 1 |>.toString else source
  match source.splitOn "\n" |>.reverse with
  | trailing :: rest =>
      if trailing.toList.all (fun char => char == ' ' || char == '\t' || char == '\r') then
        String.intercalate "\n" rest.reverse ++ "\n"
      else source
  | [] => source

@[macro qasmQuotation] def expandQasmQuotation : Macro := fun stx => do
  let some body := stx.getArgs.back?
    | Macro.throwErrorAt stx "invalid qasm% block"
  match body with
  | .atom _ value => pure (Lean.Syntax.mkStrLit (normalizeQasmBlock value))
  | _ => Macro.throwErrorAt body "invalid qasm% block"

@[macro qasmFileQuotation] def expandQasmFileQuotation : Macro := fun stx => do
  let some path := stx.getArgs.back?
    | Macro.throwErrorAt stx "invalid qasmFile% quotation"
  pure path

end QASM
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
