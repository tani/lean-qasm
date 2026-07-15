    import LiterateLean
    import Lean

    open scoped LiterateLean

# Balanced OpenQASM block parser for `qasm!`

`qasm! Name { ... } using options` uses this low-level parser to extract the inline
OpenQASM block without sending its contents through the Lean token grammar.

The scanner distinguishes strings and both comment forms, so braces inside quoted or
commented text never terminate the block early.

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

```

## Turning the balanced slice into Lean syntax

After the scanner locates the matching brace, the parser extracts exactly that source
slice and stores it as one syntax atom. Parenthesizer and formatter hooks preserve the raw
body rather than attempting to format OpenQASM as Lean.

```lean

private def qasmBlockFn : ParserFn := fun context state => Id.run do
  let opening := state.stxStack.back
  let bodyStart := opening.getTailPos?.getD state.pos
  let some bodyStop := qasmFindClose context bodyStart 0 .normal
    | return state.mkUnexpectedErrorAt "unterminated qasm! block" bodyStart
  let leading := context.mkEmptySubstringAt bodyStart
  let trailing := context.mkEmptySubstringAt bodyStop
  let body := context.extract bodyStart bodyStop
  let atom := mkAtom (.original leading bodyStart trailing bodyStop) body
  return (state.setPos bodyStop).pushSyntax atom

def qasmBlock : Parser where
  info := epsilonInfo
  fn := qasmBlockFn

@[combinator_parenthesizer qasmBlock]
def qasmBlock.parenthesizer := Lean.PrettyPrinter.Parenthesizer.visitToken

@[combinator_formatter qasmBlock]
def qasmBlock.formatter := Lean.PrettyPrinter.Formatter.visitAtom Name.anonymous

end QASM
```


<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
