    import LiterateLean
    import QASM.Runtime
    import QASM.Runtime.TraceBackend
    import QASM.Diagram
    import QASM.IR.Program
    import QASM.IR.Equiv
    import QASM.Execution.Interpreter
    import QASM.Diagram.ProgramHtmlEval
    import QASM.Emit
    import QASM.Frontend
    import QASM.Frontend.Semantics
    import QASM.Frontend.Typing
    import QASM.Elaboration

    open scoped LiterateLean

# QASM module bootstrap

`QASM.lean` is the single public entry point for LeanQASM. Importing it does not define
a second façade API; instead, it re-exports the concrete modules that own parsing,
checking, execution, visualization, and elaboration. Users can therefore start with
`import QASM` and still refer to the original declarations and namespaces.

## Why the imports are ordered

The indented header is executable Literate Lean code. Its order mirrors the dependency
graph and the ownership boundaries expressed by the directory structure:

1. `Runtime` defines classical carriers and `QuantumBackend`;
   `Runtime.TraceBackend` provides the deterministic implementation used by examples and
   tests.
2. `Diagram.Model` owns backend-independent presentation data, while `Diagram` renders
   that model without depending on parsing or elaboration.
3. `IR.Program` defines the canonical compilation unit and `IR.Equiv` defines the
   equality relations used by emitters and round-trip checks.
4. `Execution.Interpreter` evaluates canonical IR through the runtime backend boundary.
5. `Diagram.ProgramHtmlEval` projects immutable IR into diagrams, and `Emit` exposes
   canonical OpenQASM rendering.
6. `Frontend`, `Frontend.Semantics`, and `Frontend.Typing` parse and validate source while
   preserving the distinction between source syntax and resolved IR.
7. `Elaboration.BlockParser` captures inline OpenQASM before Lean tokenization;
   `Elaboration` expands includes, lowers checked source to `QASM.IR.Program`, declares
   typed input/output structures, and emits the `execute` wrapper around
   `QASM.Execution.run`.

The order is architectural rather than cosmetic: visualization and runtime remain
independent of parsing, canonical IR remains independent of Lean elaboration, and only the
final elaborator joins the frontend, lowering, interpreter, and generated boundary API.

The import graph exposes the same ownership boundaries:

```mermaid
flowchart TD
    QASM --> Runtime
    QASM --> Frontend
    QASM --> IR["IR.Program / IR.Equiv"]
    QASM --> Execution
    QASM --> Diagram
    QASM --> Emit
    QASM --> Elaboration
    Frontend --> Semantics
    Semantics --> Typing
    Typing --> Elaboration
    IR --> Execution
    Runtime --> Execution
    Execution --> Elaboration
    IR --> Diagram
    IR --> Emit
    Runtime --> Elaboration
```

Arrows from `QASM` mean public re-export; arrows between subsystems show the principal
compile-time dependency direction.

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
