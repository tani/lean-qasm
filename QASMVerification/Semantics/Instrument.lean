    import LiterateLean
    import QASMVerification.Semantics.Quantum
    open scoped LiterateLean

# Density matrices and finite instruments

Measurement returns subnormalized branches: branch trace is the outcome probability.
This representation does not divide by a potentially zero probability. Reset is a sum
of two Kraus actions and therefore removes correlations with the reset qubit. These
single-qubit definitions extend to a register through the circuit placement relation.
An instrument stores finite Kraus lists and a completeness proof. Positivity and trace
conservation theorems from that proof remain explicit verification work.

```lean
noncomputable section
namespace QASMVerification
abbrev Density (n : Nat) := Operator n

def krausAction {n : Nat} (k : Operator n) (rho : Density n) : Density n :=
  k * rho * k.conjTranspose

def densityTrace {n : Nat} (rho : Density n) : ℂ := ∑ i, rho i i

def IsDensity {n : Nat} (rho : Density n) : Prop :=
  rho.conjTranspose = rho ∧
  (∀ v : Basis n → ℂ, 0 ≤ (∑ i, ∑ j, star (v i) * rho i j * v j).re) ∧
  0 ≤ (densityTrace rho).re ∧ (densityTrace rho).re ≤ 1

def projector (outcome : Bool) : Operator 1 := fun row col =>
  if row = col ∧ row.val = (if outcome then 1 else 0) then 1 else 0

def measureZ (outcome : Bool) (rho : Density 1) : Density 1 :=
  krausAction (projector outcome) rho

def resetKraus (outcome : Bool) : Operator 1 := fun row col =>
  if row.val = 0 ∧ col.val = (if outcome then 1 else 0) then 1 else 0

def reset (rho : Density 1) : Density 1 :=
  krausAction (resetKraus false) rho + krausAction (resetKraus true) rho

/-- Finite Kraus families with explicit completeness; no positivity axiom is assumed. -/
structure Instrument (n : Nat) (Outcome : Type) [Fintype Outcome] where
  kraus : Outcome → List (Operator n)
  complete : (∑ outcome, ((kraus outcome).map fun k => k.conjTranspose * k).sum) = 1

def Instrument.branch {n : Nat} {Outcome : Type} [Fintype Outcome]
    (instrument : Instrument n Outcome) (outcome : Outcome) (rho : Density n) : Density n :=
  ((instrument.kraus outcome).map fun k => krausAction k rho).sum

/-- Probabilities are read from the branch trace, without renormalization. -/
def Instrument.probability {n : Nat} {Outcome : Type} [Fintype Outcome]
    (instrument : Instrument n Outcome) (outcome : Outcome) (rho : Density n) : ℝ :=
  (densityTrace (instrument.branch outcome rho)).re
end QASMVerification

```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
