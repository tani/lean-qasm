# LeanQASM agent instructions

## LiterateLean is mandatory

Every project-owned Lean source module must be written as a LiterateLean document. This applies to root examples, tests, smoke modules, and every module under `QASM/`. It does not apply to `lakefile.lean`, generated files, or vendored fixtures.

For every affected `.lean` file:

1. Import `LiterateLean` directly. Do not rely on a transitive import.
2. Open `LiterateLean` explicitly with `open scoped LiterateLean`.
3. Indent the executable header by four spaces so it is valid Lean and renders as an implicit Markdown code block.
4. Give the document one level-one heading that states the module's purpose.
5. Put explanatory Markdown prose outside Lean fences. Explain contracts, invariants, data flow, failure behavior, and architectural boundaries—not a line-by-line paraphrase of the code.
6. Put executable declarations only inside explicit ```` ```lean ```` fences. Namespace and section commands, including every matching `end`, must remain inside Lean fences.
7. Split large modules into coherent sections with prose between fences. Do not hide an entire production module in one monolithic fence merely to satisfy the syntax.
8. Keep prose synchronized with implementation changes. In particular, describe the canonical `QASM.IR.Program` pipeline and shared `QASM.Codegen.run` interpreter accurately; do not revive obsolete native-control-flow or `CheckedProgramInfo` descriptions.
9. End the file, after the final closing Lean fence, with exactly this Markdown footer:

```text
<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
```

The footer is prose. Never place it inside a Lean fence, and never append a second copy.

## Required checks

After changing LiterateLean structure or prose:

- Check that every opening fence is paired, headings do not skip levels, no Lean command escaped a fence, and the canonical footer is the final non-whitespace content.
- Run `lake build QASM lean_qasm_tests`.
- Run `lake test` when executable behavior or test sources changed.
- Compile changed files that are outside Lake targets with `lake env lean <file>`. Current standalone modules are `Examples/Bell.lean` and `Tests/Lowering.lean`; any future smoke or scratch module not imported by `QASM.lean` must also be checked directly.

A successful build does not excuse malformed Markdown, stale prose, missing standalone checks, or a footer inside executable code.
