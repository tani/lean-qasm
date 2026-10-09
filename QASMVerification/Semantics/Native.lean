    import LiterateLean
    import QASMVerification.Semantics.Circuit
    open scoped LiterateLean

# Native primitive equations for the QFT fragment

The primitive relation fixes actual matrices for native U, gphase, H, P, controlled
phase, identity, and physical SWAP. Arity and parameter lists are checked by premises.
Other gates must be expanded into these equations or supplied by a larger checked
profile; an unknown gate has no identity fallback. Real argument evaluation is a
separate relation, allowing symbolic and finite-angle profiles to share gate equations.

```lean
noncomputable section
namespace QASMVerification
open QASM.IR

def swapGate : Operator 2 := fun row col =>
  if row.val = 2 * (col.val % 2) + col.val / 2 then 1 else 0

inductive NativePrimitive (argument : Expr → ℝ → Prop) :
    (n : Nat) → Primitive → Operator n → Prop where
  | u (hk : p.kind = .u) (hp : p.parameters = #[theta, phi, lambda])
      (ht : argument theta t) (hf : argument phi f) (hl : argument lambda l) :
      NativePrimitive argument 1 p (nativeU t f l)
  | gphase (hk : p.kind = .gphase) (hp : p.parameters = #[gamma])
      (hg : argument gamma g) : NativePrimitive argument 0 p (fun _ _ => phase g)
  | h (hk : p.kind = .h) (hp : p.parameters = #[]) :
      NativePrimitive argument 1 p hadamard
  | p (hk : p.kind = .p) (hp : p.parameters = #[theta]) (ht : argument theta t) :
      NativePrimitive argument 1 p (phaseGate t)
  | cp (hk : p.kind = .cp) (hp : p.parameters = #[theta]) (ht : argument theta t) :
      NativePrimitive argument 2 p (controlledPhase t)
  | swap (hk : p.kind = .swap) (hp : p.parameters = #[]) :
      NativePrimitive argument 2 p swapGate
  | id (hk : p.kind = .id) (hp : p.parameters = #[]) :
      NativePrimitive argument 1 p 1

def nativeProfile (argument : Expr → ℝ → Prop) (integer : Expr → Int → Prop) :
    CircuitProfile := { primitive := NativePrimitive argument, integer }

/-- Symbolic extraction cannot erase an explicit finite-precision cast. -/
def SymbolicArgument (env : RealEnvironment) (expression : Expr) (value : ℝ) : Prop :=
  ∃ exact, ExactRealExpr.ofExpr? expression = some exact ∧ RealEval env exact value
end QASMVerification
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
