    import LiterateLean
    import QASM.IR.Source
    import QASM.IR.Interface
    open scoped LiterateLean

# Wire permutations

A permutation records how an ordered circuit interface is rewired. `mapping[i]` selects
the source lane placed at output position `i`; domain, codomain, and origin remain explicit
so lowering and emitters can validate direction rather than infer it from array length.

```lean
namespace QASM.IR

structure WirePermutation where
  domain   : Interface
  codomain : Interface
  mapping  : Array Nat
  origin   : SourceSpan := {}
  deriving Repr, BEq, Inhabited

end QASM.IR
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
