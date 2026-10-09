    import LiterateLean
    import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
    import Mathlib.Analysis.Real.Sqrt
    import Mathlib.LinearAlgebra.Matrix.ConjTranspose
    open scoped LiterateLean

# Quantum state spaces and exact gates

Basis indices use little-endian register order: the low bit is qubit zero. Matrices act
on column vectors. Sequential composition executes its left operand first. This module
is isolated from the executable library; no Mathlib import enters the runtime.

The native U matrix retains the global phase specified by OpenQASM 3.0. Permutations
below change coordinates; physical SWAP is a separate gate.

```lean
noncomputable section
namespace QASMVerification
abbrev Basis (n : Nat) := Fin (2 ^ n)
abbrev Operator (n : Nat) := Matrix (Basis n) (Basis n) ℂ

def sequential {n : Nat} (first second : Operator n) : Operator n := second * first

def IsUnitary {n : Nat} (u : Operator n) : Prop :=
  u.conjTranspose * u = 1 ∧ u * u.conjTranspose = 1

def phase (theta : ℝ) : ℂ := Complex.exp ((theta : ℂ) * Complex.I)

def nativeU (theta phi lambda : ℝ) : Operator 1 := fun row col =>
  if row.val = 0 then
    if col.val = 0 then (1 + phase theta) / 2
    else -Complex.I * phase lambda * (1 - phase theta) / 2
  else
    if col.val = 0 then Complex.I * phase phi * (1 - phase theta) / 2
    else phase (phi + lambda) * (1 + phase theta) / 2

def hadamard : Operator 1 := fun row col =>
  (if row.val = 1 ∧ col.val = 1 then -1 else 1) / (Real.sqrt 2 : ℂ)

def phaseGate (theta : ℝ) : Operator 1 := fun row col =>
  if row = col then if row.val = 0 then 1 else phase theta else 0

def controlledPhase (theta : ℝ) : Operator 2 := fun row col =>
  if row = col then if row.val = 3 then phase theta else 1 else 0

def coordinatePermutation {n : Nat} (p : Equiv.Perm (Basis n)) : Operator n :=
  fun row col => if row = p col then 1 else 0

def reverseBits (n x : Nat) : Nat :=
  (List.range n).foldl (fun acc j => acc * 2 + (x / 2 ^ j) % 2) 0

/-- Positive-sign Fourier transform including final bit reversal. -/
def fourier (n : Nat) : Operator n := fun y x =>
  phase (2 * Real.pi * (x.val : ℝ) * (y.val : ℝ) / (2 ^ n : ℝ)) /
    (Real.sqrt (2 ^ n : ℝ) : ℂ)

@[simp] theorem sequential_identity_left {n : Nat} (u : Operator n) :
    sequential 1 u = u := by simp [sequential]
@[simp] theorem sequential_identity_right {n : Nat} (u : Operator n) :
    sequential u 1 = u := by simp [sequential]
theorem sequential_assoc {n : Nat} (a b c : Operator n) :
    sequential (sequential a b) c = sequential a (sequential b c) := by
  simp only [sequential, Matrix.mul_assoc]
end QASMVerification
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
