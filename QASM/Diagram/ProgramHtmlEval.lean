    import LiterateLean
    import QASM.Diagram
    import QASM.Diagram.FromIR
    open scoped LiterateLean

# HTML evaluation for canonical programs

`#html` renders immutable IR through the shared circuit-diagram model and never executes the program.

The `#html` route has no execution edge:

```mermaid
flowchart LR
    Program["QASM.IR.Program"] --> OfProgram["Diagram.ofProgram"]
    OfProgram --> Model["CircuitDiagram"]
    Model --> ToHtml
    ToHtml --> Infoview
```

In particular, `QuantumBackend` is absent from this path, so rendering cannot allocate or
measure a qubit.

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
