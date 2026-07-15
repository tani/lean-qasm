    import LiterateLean
    open scoped LiterateLean

# IR source metadata

Source positions are retained as flat, backend-independent metadata on IR nodes. Empty
spans are valid for synthesized nodes; populated spans use offsets and line/column pairs
only for diagnostics and never participate in execution.

```lean
namespace QASM.IR

structure SourceSpan where
  fileName    : String := ""
  startOffset : Nat := 0
  endOffset   : Nat := 0
  startLine   : Nat := 0
  startColumn : Nat := 0
  endLine     : Nat := 0
  endColumn   : Nat := 0
  deriving Repr, BEq, Inhabited

end QASM.IR
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
