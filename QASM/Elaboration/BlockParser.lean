    import LiterateLean
    import Lean

    open scoped LiterateLean

# Balanced OpenQASM block parser for `qasm!`

`qasm! Name { ... } [using options]` uses this low-level parser to extract the inline
OpenQASM block without sending its contents through the Lean token grammar.

The scanner distinguishes strings and both comment forms, so braces inside quoted or
commented text never terminate the block early.

The scanner is a small state machine whose brace counter changes only in normal mode:

```mermaid
stateDiagram-v2
    [*] --> Normal
    Normal --> String: quote
    String --> Normal: unescaped quote
    Normal --> LineComment: double slash
    LineComment --> Normal: newline
    Normal --> BlockComment: slash star
    BlockComment --> Normal: star slash
    Normal --> Normal: opening or closing brace
```

If the nested depth before a normal-mode closing brace is $d$, the transition is
$d \mapsto d-1$ for $d>0$; at $d=0$ that brace terminates the outer `qasm!` body.

```lean
namespace QASM

open Lean Parser


```

## Scanner modes

Finding a matching brace requires more context than counting `{` and `}` characters.
OpenQASM permits both braces inside strings and arbitrary source text inside comments.
`QasmBlockMode` records exactly the lexical state needed to decide whether the current
character is structural.

The type is private because it describes Lean command parsing, not the OpenQASM frontend
lexer. Keeping those layers separate lets the command parser capture source faithfully
before the full frontend assigns tokens and diagnostics.

```lean
private inductive QasmBlockMode where
  | normal
  | string
  | lineComment
  | blockComment

```

## Safe cursor movement

Lean's parser context indexes UTF-8 source with raw positions. These two helpers centralize
the end-of-input proof required by `ParserContext.next'` and `ParserContext.get'`.
Returning the same position or `none` at EOF gives the recursive scanner one explicit
termination case and avoids unchecked indexing.

```lean
private def qasmAdvance (context : ParserContext) (position : String.Pos.Raw) : String.Pos.Raw :=
  if h : context.atEnd position then position else context.next' position h

private def qasmChar? (context : ParserContext) (position : String.Pos.Raw) : Option Char :=
  if h : context.atEnd position then none else some (context.get' position h)

```

## The balanced-brace walk

`qasmFindClose` starts immediately after the opening brace with depth zero. An opening
brace in normal mode increments the nested depth. A closing brace either decrements that
depth or, when the depth is already zero, identifies the end of the outer `qasm!` block.

Mode transitions deliberately consume both characters of `//`, `/*`, and `*/`. Inside a
string, a backslash also consumes the following character so an escaped quote cannot end
the string. Reaching EOF in any mode returns `none`; the caller turns that absence into a
diagnostic anchored at the block body.

```lean
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


The raw scanner returns the position of the closing brace but does not consume it. This
matches Lean's surrounding command grammar: `qasmBlockFn` contributes only the body atom,
then leaves the closing delimiter for the parser that opened the block.

The atom retains original leading and trailing source information. That preservation is
important for source locations and for printing the command without normalizing its
OpenQASM contents.

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

```

## Exposing the parser combinator

`qasmBlockFn` is the state-transforming implementation. The public `qasmBlock` value wraps
it as a Lean `Parser` with epsilon parser metadata, allowing the `qasm!` command grammar in
the elaborator to embed it like any other combinator.

```lean
def qasmBlock : Parser where
  info := epsilonInfo
  fn := qasmBlockFn

```

## Parenthesizing and formatting raw source

The body is intentionally one atom, not a tree of Lean syntax. Its parenthesizer therefore
visits it as a token, and its formatter emits the atom unchanged. OpenQASM formatting
belongs to the standalone frontend printer; Lean's formatter must not reinterpret spaces,
comments, or punctuation inside the captured block.

```lean
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
