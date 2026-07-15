    import LiterateLean
    import QASM.IR.Source
    import QASM.IR.Name
    import QASM.IR.Type
    import QASM.IR.Interface
    import QASM.IR.Expr
    open scoped LiterateLean

# Primitive circuits

Primitive signatures preserve resolved parameters and exact wire interfaces. Standard
gates use a closed semantic kind while user gates carry a stable declaration ID; the
display name is retained for emission and diagnostics. `ControlSpec` keeps control
interface and polarity order together for categorical composition.

```lean
namespace QASM.IR

inductive PrimitiveKind
  | u | gphase | p
  | x | y | z | h | s | sdg | t | tdg | sx | rx | ry | rz
  | cx | cy | cz | ch | swap | cp | crx | cry | crz | ccx | cswap | cu
  | phase | cphase | id | u1 | u2 | u3
  | userDefined (id : DeclId)
  deriving Repr, BEq, DecidableEq, Hashable, Inhabited

structure Primitive where
  kind       : PrimitiveKind
  name       : Name
  parameters : Array Expr := #[]
  input      : Interface
  output     : Interface
  origin     : SourceSpan := {}
  deriving Repr, BEq, Inhabited

structure ControlSpec where
  controls    : Interface
  polarities  : Array ControlPolarity
  origin      : SourceSpan := {}
  deriving Repr, BEq, Inhabited

end QASM.IR
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
