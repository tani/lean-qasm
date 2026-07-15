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

$$
\operatorname{dom}(g \circ f)=\operatorname{dom}(f),\qquad
\operatorname{cod}(g \circ f)=\operatorname{cod}(g),
$$

$$
\operatorname{dom}(f \otimes g)=\operatorname{dom}(f)\mathbin{+\!\!+}\operatorname{dom}(g),
\qquad
\operatorname{cod}(f \otimes g)=\operatorname{cod}(f)\mathbin{+\!\!+}\operatorname{cod}(g).
$$

Lowering must additionally ensure the composition side condition
$\operatorname{cod}(f)=\operatorname{dom}(g)$.

```lean
namespace QASM.IR

inductive Circuit
  | identity   (wires : Interface)
  | primitive  (prim : Primitive)
  | compose    (f g : Circuit)
  | tensor     (f g : Circuit)
  | permute    (perm : WirePermutation)
  | inverse    (circuit : Circuit)
  | power      (exponent : Expr) (circuit : Circuit)
  | controlled (spec : ControlSpec) (circuit : Circuit)
  | unsupported (capability : Capability) (detail : String)
      (input output : Interface)
  deriving Repr, BEq, Inhabited

```

## Structural interfaces

`dom` and `cod` are total structural projections. Composition takes its outer interfaces,
tensor concatenates its children, modifiers preserve boundaries, and unsupported nodes
return their recorded interfaces. Lowering is responsible for constructing only
well-matched compositions and valid permutations.

```lean
namespace Circuit

mutual
partial def dom : Circuit → Interface
  | identity w => w
  | primitive p => p.input
  | compose f _ => dom f
  | tensor f g => dom f ++ dom g
  | permute p => p.domain
  | inverse c => cod c
  | power _ c => dom c
  | controlled s c => s.controls ++ dom c
  | unsupported _ _ input _ => input

partial def cod : Circuit → Interface
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
