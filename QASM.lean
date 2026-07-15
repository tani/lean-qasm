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

`QASM.lean` is the library entry point that re-exports the core components
from `QASM.Runtime` through `QASM.Elab`.

## Imported layers

The indented header is executable Literate Lean code. Import order follows the compiler
pipeline: runtime contracts and block parsing first, then parsing, semantics, typing, and
finally command elaboration. No additional declarations are needed at this aggregation
layer.


<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
