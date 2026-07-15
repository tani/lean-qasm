    import LiterateLean
    import QASM.Runtime
    import QASM.Backend
    import QASM.Diagram
    import QASM.Source
    import QASM.IR.Program
    import QASM.IR.Equiv
    import QASM.Emit
    import QASM.Instances.ProgramHtmlEval
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
graph and the two boundaries of the implementation:

1. `Runtime` defines classical carriers and `QuantumBackend`; `Backend` provides a
   deterministic implementation, while `Diagram` defines the backend-independent
   presentation model.
2. `Source` captures balanced inline OpenQASM before Lean tokenization.
3. `IR.Program` defines the canonical compilation unit and `IR.Equiv` defines the
   equality relations used by emitters and round-trip checks.
4. `Emit` exposes canonical OpenQASM rendering, and `ProgramHtmlEval` derives an HTML
   diagram from immutable IR without executing it.
5. `Frontend`, `Semantics`, and `Typing` parse and validate source while preserving the
   distinction between source syntax and resolved IR.
6. `Elab` expands includes, lowers checked source to `QASM.IR.Program`, declares typed
   input/output structures, and emits the `execute` wrapper around `QASM.Codegen.run`.

The order is architectural rather than cosmetic: presentation and runtime types do not
depend on parsing, canonical IR remains independent of Lean elaboration, and only the
final elaborator joins the frontend, lowering, interpreter, and generated boundary API.

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
