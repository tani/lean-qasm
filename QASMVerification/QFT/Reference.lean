    import LiterateLean
    import QASMVerification.QFT.Model
    import QASMVerification.Semantics.Gates
    open scoped LiterateLean

# QFT family invariants and base cases

The validity theorem quantifies over every register size and every generated gate.
The successor equation exposes the outer-loop invariant needed for induction on size.
Fourier correctness for the empty register is proved here; the general Fourier equality
is a separate theorem obligation, not supplied as a premise of these invariants.

```lean
noncomputable section
namespace QASMVerification

theorem qftCore_succ (n : Nat) :
    qftCore (n+1) =
      (.hadamard n :: (List.range n).reverse.map (fun k => .controlledPhase k n (n-k))) ++
      qftCore n := by
  simp [qftCore, List.range_succ, List.reverse_append]

theorem qftSteps_valid (n : Nat) : ∀ step ∈ qftSteps n, step.Valid n := by
  intro step member
  rcases List.mem_append.mp member with core | swaps
  · rcases List.mem_flatMap.mp core with ⟨j, hj, hs⟩
    have hjn : j < n := List.mem_range.mp (List.mem_reverse.mp hj)
    rcases List.mem_cons.mp hs with rfl | hs
    · exact hjn
    · rcases List.mem_map.mp hs with ⟨k, hk, rfl⟩
      have hkj : k < j := List.mem_range.mp (List.mem_reverse.mp hk)
      exact ⟨hkj, hjn, rfl⟩
  · rcases List.mem_map.mp swaps with ⟨j, hj, rfl⟩
    have hjn := List.mem_range.mp hj
    change j < n ∧ n-1-j < n
    omega

theorem qftCorrect_zero : qftMatrix 0 = fourier 0 := by
  rw [qftMatrix_zero]
  ext i j
  have hi : i.val = 0 := by have := i.isLt; simp at this; omega
  have hj : j.val = 0 := by have := j.isLt; simp at this; omega
  have hij : i = j := Fin.ext (hi.trans hj.symm)
  simp [fourier, hij, phase_zero, Matrix.one_apply]

theorem fourier_one : fourier 1 = hadamard := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fourier, hadamard]

theorem qftMatrix_one : qftMatrix 1 = hadamard := by
  have hstep : stepOperator 1 (.hadamard 0) = hadamard := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [stepOperator, hadamard, basisBit]
  simp [qftMatrix, qft_one, hstep, sequential]

theorem qftCorrect_one : qftMatrix 1 = fourier 1 :=
  qftMatrix_one.trans fourier_one.symm


```

## Gate-sequence execution

The reference gate-sequence semantics is total and deterministic on valid sequences.
Its accumulator acts on arbitrary input states. The following theorem connects that
operational relation to the defined QFT matrix for every size; translating residual
Proc loops into this sequence remains a separate simulation obligation.

```lean
inductive RunSteps (n : Nat) : List QFTStep → Operator n → Operator n → Prop where
  | nil (initial : Operator n) : RunSteps n [] initial initial
  | cons (valid : step.Valid n)
      (tail : RunSteps n rest (sequential initial (stepOperator n step)) final) :
      RunSteps n (step :: rest) initial final

theorem foldSteps_accumulator (n : Nat) (steps : List QFTStep) (initial : Operator n) :
    steps.foldl (fun acc step => sequential acc (stepOperator n step)) initial =
      steps.foldl (fun acc step => sequential acc (stepOperator n step)) 1 * initial := by
  induction steps generalizing initial with
  | nil => simp
  | cons step rest ih =>
    simp only [List.foldl_cons, sequential_identity_left]
    rw [ih (sequential initial (stepOperator n step)), ih (stepOperator n step)]
    simp [sequential, Matrix.mul_assoc]

theorem runSteps_denotation {n : Nat} {steps : List QFTStep} {initial final : Operator n}
    (h : RunSteps n steps initial final) :
    final = steps.foldl (fun acc step => sequential acc (stepOperator n step)) initial := by
  induction h with
  | nil => rfl
  | cons _ _ ih => exact ih

theorem runSteps_exists {n : Nat} (steps : List QFTStep) (initial : Operator n)
    (valid : ∀ step ∈ steps, step.Valid n) :
    RunSteps n steps initial
      (steps.foldl (fun acc step => sequential acc (stepOperator n step)) initial) := by
  induction steps generalizing initial with
  | nil => exact .nil _
  | cons step rest ih =>
    exact .cons (valid step (by simp)) (ih _ (fun s hs => valid s (by simp [hs])))

theorem runQFT_iff (n : Nat) (initial final : Operator n) :
    RunSteps n (qftSteps n) initial final ↔ final = qftMatrix n * initial := by
  constructor
  · intro h
    rw [runSteps_denotation h, foldSteps_accumulator]
    rfl
  · intro h
    change final = (qftSteps n).foldl (fun acc step => sequential acc (stepOperator n step)) 1 * initial at h
    rw [← foldSteps_accumulator n (qftSteps n) initial] at h
    rw [h]
    exact runSteps_exists _ _ (qftSteps_valid n)

end QASMVerification
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
