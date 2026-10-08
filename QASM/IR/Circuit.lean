    import LiterateLean
    import QASM.IR.Interface
    import QASM.IR.Permutation
    import QASM.IR.Primitive
    open scoped LiterateLean

# Categorical circuits

Circuits preserve sequential composition, parallel tensoring, permutation, and modifiers
as distinct nodes. Every constructor has an explicit domain and codomain derivable without
execution; unsupported capabilities retain both interfaces so a failed target feature
cannot break surrounding circuit composition.

The constructors retain the categorical boundary equations:

```math
\mathrm{dom}(g \circ f)=\mathrm{dom}(f),\qquad
\mathrm{cod}(g \circ f)=\mathrm{cod}(g),
```

```math
\mathrm{dom}(f \otimes g)=\mathrm{dom}(f)\mathbin{+\!\!+}\mathrm{dom}(g),
\qquad
\mathrm{cod}(f \otimes g)=\mathrm{cod}(f)\mathbin{+\!\!+}\mathrm{cod}(g).
```

Lowering must additionally ensure the composition side condition
$`\mathrm{cod}(f)=\mathrm{dom}(g)`$.

```lean
namespace QASM.IR

inductive Circuit (size : Type := Nat) (integer : Type := Int)
  | identity   (wires : Interface)
  | primitive  (prim : (Primitive size integer))
  | compose    (f g : (Circuit size integer))
  | tensor     (f g : (Circuit size integer))
  | permute    (perm : WirePermutation)
  | inverse    (circuit : (Circuit size integer))
  | power      (exponent : (Expr size integer)) (circuit : (Circuit size integer))
  | controlled (spec : ControlSpec) (circuit : (Circuit size integer))
  | unsupported (capability : Capability) (detail : String)
      (input output : Interface)
  deriving Repr, BEq, Inhabited

```

## Structural interfaces

`dom` and `cod` are total, kernel-reducible structural projections. Their defining
equations can be used in proofs without executing or specializing a circuit. Composition takes its outer interfaces,
tensor concatenates its children, modifiers preserve boundaries, and unsupported nodes
return their recorded interfaces. Lowering is responsible for constructing only
well-matched compositions and valid permutations.

```lean
namespace Circuit

mutual
def dom {size integer : Type} : (Circuit size integer) → Interface
  | identity w => w
  | primitive p => p.input
  | compose f _ => dom f
  | tensor f g => dom f ++ dom g
  | permute p => p.domain
  | inverse c => cod c
  | power _ c => dom c
  | controlled s c => s.controls ++ dom c
  | unsupported _ _ input _ => input

def cod {size integer : Type} : (Circuit size integer) → Interface
  | identity w => w
  | primitive p => p.output
  | compose _ g => cod g
  | tensor f g => cod f ++ cod g
  | permute p => p.codomain
  | inverse c => dom c
  | power _ c => cod c
  | controlled s c => s.controls ++ cod c
  | unsupported _ _ _ output => output
end

end Circuit

end QASM.IR
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
