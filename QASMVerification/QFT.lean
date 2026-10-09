    import LiterateLean
    import QASM.IR.QFT
    import QASMVerification.ExactReal
    open scoped LiterateLean

# Parameter-dependent QFT circuit families

The imported IR family retains descending outer and inner Proc loops. The mathematical
gate list below enumerates their iterations as a specification for every size; it is
not an execution-time rewrite of the IR. Qubit zero is least
significant; controlled phases precede the final physical swaps. The empty register
has no gate or allocation. Correctness below is a proposition, not an asserted theorem.

Fixed-width execution must satisfy both angle precision and signed-index range bounds.
This contract does not assert that a floating-point backend meets those conditions.

```lean
noncomputable section
namespace QASMVerification
inductive QFTStep where
  | hadamard (target : Nat)
  | controlledPhase (control target distance : Nat)
  | swap (first second : Nat)
  deriving Repr, BEq, DecidableEq

def qftCore (n : Nat) : List QFTStep :=
  (List.range n).reverse.flatMap fun j =>
    .hadamard j :: (List.range j).reverse.map (fun k => .controlledPhase k j (j-k))
def qftSwaps (n : Nat) : List QFTStep :=
  (List.range (n / 2)).map fun j => .swap j (n-1-j)
def qftSteps (n : Nat) : List QFTStep := qftCore n ++ qftSwaps n

def QFTStep.Valid (n : Nat) : QFTStep → Prop
  | .hadamard j => j < n
  | .controlledPhase k j d => k < j ∧ j < n ∧ d = j-k
  | .swap j k => j < n ∧ k < n

def QFTRangeSafe (n width indexWidth : Nat) : Prop :=
  width ≥ max 3 n ∧ indexWidth ≥ 2 ∧ n < 2 ^ (indexWidth-1)

def qftPhase (distance : Nat) : ℝ := Real.pi / (2 ^ distance : ℝ)

/-- Extract a computational-basis bit; qubit zero is least significant. -/
def basisBit (x j : Nat) : Nat := (x / 2^j) % 2

/-- A target outside the register is explicitly rejected by the zero operator. -/
def stepOperator (n : Nat) : QFTStep → Operator n
  | .hadamard j => fun row col =>
      if j < n ∧ row.val - basisBit row.val j * 2^j = col.val - basisBit col.val j * 2^j then
        hadamard ⟨basisBit row.val j, Nat.mod_lt _ (by decide)⟩
          ⟨basisBit col.val j, Nat.mod_lt _ (by decide)⟩
      else 0
  | .controlledPhase k j d => fun row col =>
      if k < j ∧ j < n ∧ d = j-k ∧ row = col then
        if basisBit col.val k = 1 ∧ basisBit col.val j = 1 then phase (qftPhase d) else 1
      else 0
  | .swap j k => fun row col =>
      if j = k then (if j < n ∧ row = col then 1 else 0) else
      if j < n ∧ k < n ∧ row.val =
          (col.val - basisBit col.val j * 2^j - basisBit col.val k * 2^k +
            basisBit col.val j * 2^k + basisBit col.val k * 2^j) % 2^n then 1 else 0

def qftMatrix (n : Nat) : Operator n :=
  (qftSteps n).foldl (fun acc step => sequential acc (stepOperator n step)) 1

/-- This is the target theorem, not an axiom or a completed proof. -/
def QFTCorrect : Prop := ∀ n, qftMatrix n = fourier n

/-- Linking residual Proc loops to this matrix is a separate refinement obligation. -/
def QFTProgramCorrect (executes : (n : Nat) → QASM.IR.Proc → Operator n → Prop)
    (fault : Nat → QASM.IR.Proc → Prop) : Prop :=
  ∀ n, let body := QASM.IR.QFT.body n (max 3 n) (n+2)
    executes n body (fourier n) ∧
    (∀ u, executes n body u → u = fourier n) ∧ ¬ fault n body

theorem canonical_range_safe (n : Nat) : QFTRangeSafe n (max 3 n) (n+2) := by
  refine ⟨le_refl _, by omega, ?_⟩
  have h := (n+1).lt_two_pow_self
  simpa using Nat.lt_trans (Nat.lt_succ_self n) h

@[simp] theorem qftMatrix_zero : qftMatrix 0 = 1 := rfl

@[simp] theorem qft_zero : qftSteps 0 = [] := rfl
@[simp] theorem qft_one : qftSteps 1 = [.hadamard 0] := rfl
end QASMVerification
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
