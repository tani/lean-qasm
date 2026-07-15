    import LiterateLean
    import QASM.Diagram
    import QASM.Diagram.FromIR
    open scoped LiterateLean

# HTML evaluation for canonical programs

`#html` renders immutable IR through the shared circuit-diagram model and never executes the program.

```lean
meta instance : ProofWidgets.HtmlEval QASM.IR.Program where
  eval program := pure (QASM.Diagram.ofProgram program).toHtml
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
