    import LiterateLean
    import QASM.Runtime
    import QASM.Backend
    import QASM.Diagram
    import QASM.Source
    import QASM.Frontend
    import QASM.Semantics
    import QASM.Typing
    import QASM.Elab

    open scoped LiterateLean

# QASM module bootstrap

`QASM.lean` is the single public entry point for LeanQASM. Importing it does not define
a second façade API; instead, it re-exports the concrete modules that own parsing,
checking, execution, visualization, and elaboration. Users can therefore start with
`import QASM` and still refer to the original declarations and namespaces.

## Why the imports are ordered

The indented header is executable Literate Lean code. Its order mirrors the dependency
graph of the implementation:

1. `Runtime` defines the portable values and the `QuantumBackend` boundary used by
   generated programs.
2. `Backend` supplies the deterministic trace implementation of that boundary.
3. `Diagram` renders already-checked program metadata without executing it.
4. `Source` teaches Lean how to capture a balanced raw OpenQASM block.
5. `Frontend` turns that raw source into positioned tokens and a source AST.
6. `Semantics` evaluates constants, validates source-wide control flow, and discovers
   backend requirements.
7. `Typing` resolves OpenQASM types and checks expressions, statements, and callables.
8. `Elab` coordinates all preceding layers and emits native Lean declarations for
   `qasm!`.

This sequence is more than presentation: later modules mention declarations from earlier
ones, while the runtime remains independent of the parser and compiler.

## Why this module declares nothing

An aggregation module should not introduce aliases or duplicate ownership of public
symbols. Keeping this file declaration-free means documentation and code navigation lead
back to the layer that implements each feature. It also ensures that importing a narrower
module remains possible for tools that need only the frontend, runtime, or diagram model.


<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
