    import LiterateLean
    import QASM.Emit.OpenQASM
    open scoped LiterateLean

# Public IR emission

`ToString` is the stable public route to canonical OpenQASM; callers that need include preservation can use `OpenQASM.emitWithMode` directly.

The public conversion is a thin ownership boundary:

```mermaid
flowchart LR
    Program["QASM.IR.Program"] --> ToString
    ToString --> Emit["OpenQASM.emit"]
    Emit --> Text["canonical OpenQASM"]
```

Specialized callers bypass only the `ToString` convenience edge when selecting an
include-preservation mode.

```lean
instance : ToString QASM.IR.Program where
  toString := QASM.Emit.OpenQASM.emit
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
