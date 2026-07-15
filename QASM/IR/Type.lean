    import LiterateLean
    open scoped LiterateLean

# Resolved IR types

IR types contain only resolved widths, array shapes, and reference ranks; they never
depend on elaboration state or source expressions. Scalar `bit` keeps `none` distinct from
`bit[1]`, array references record mutability separately from shape knowledge, and `void`,
qubit, and stretch remain explicit so capability failures cannot masquerade as classical
values.

```lean
namespace QASM.IR

inductive ScalarTy where
  | bit (width : Option Nat)
  | sint (width : Nat)
  | uint (width : Nat)
  | float (width : Nat)
  | angle (width : Nat)
  | boolean
  | complex (width : Nat)
  | duration
  | stretch
  | qubit (count : Nat)
  | void
  deriving Repr, BEq, DecidableEq, Hashable, Inhabited

inductive «Type» where
  | scalar (value : ScalarTy)
  | array (element : ScalarTy) (shape : Array Nat)
  | arrayRef (mutable : Bool) (element : ScalarTy) (shape : Option (Array Nat)) (rank : Nat)
  deriving Repr, BEq, DecidableEq, Hashable, Inhabited

end QASM.IR
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
