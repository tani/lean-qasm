    import LiterateLean
    open scoped LiterateLean

# Resolved IR types

Concrete IR types use natural-number widths and shapes. The optional size type
parameter lets compilation use symbolic sizes with the same grammar; the default remains
`Nat`, and runtime consumers never depend on elaborator state. Scalar `bit` keeps `none` distinct from
`bit[1]`, array references record mutability separately from shape knowledge, and `void`,
qubit, and stretch remain explicit so capability failures cannot masquerade as classical
values.

The resolved type grammar can be summarized as

```math
\tau ::= \mathrm{scalar}(s)
      \mid \mathrm{array}(s, [n_1,\ldots,n_k])
      \mid \mathrm{arrayRef}(m, s, \sigma, k),
```

In concrete programs every $`n_i`$ is a natural number; rank $`k`$ stays concrete in
compilation templates as well. The optional shape $`\sigma`$ records whether
an array-reference extent is known without conflating unknown shape with scalar type.

```lean
namespace QASM.IR

inductive ScalarTy (size : Type := Nat) where
  | bit (width : Option size)
  | sint (width : size)
  | uint (width : size)
  | float (width : size)
  | angle (width : size)
  | gateAngle
  | boolean
  | complex (width : size)
  | duration
  | stretch
  | qubit (count : size)
  | void
  deriving Repr, BEq, DecidableEq, Hashable, Inhabited

inductive «Type» (size : Type := Nat) where
  | scalar (value : (ScalarTy size))
  | array (element : (ScalarTy size)) (shape : Array size)
  | arrayRef (mutable : Bool) (element : (ScalarTy size)) (shape : Option (Array size)) (rank : Nat)
  deriving Repr, BEq, DecidableEq, Hashable, Inhabited

end QASM.IR
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
