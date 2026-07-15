    import LiterateLean
    import QASM.Emit.OpenQASM
    open scoped LiterateLean

# Public IR emission

`ToString` is the stable public route to canonical OpenQASM; callers that need include preservation can use `OpenQASM.emitWithMode` directly.

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
