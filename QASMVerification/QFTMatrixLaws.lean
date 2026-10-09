    import LiterateLean
    import QASMVerification.FourierLaws
    open scoped LiterateLean

# Matrix reduction of the controlled-phase blocks

These lemmas concern the original `stepOperator` and matrix fold, rather than a
replacement definition of QFT. An entire descending controlled-phase block is reduced
to its exact diagonal action. The remaining core proof must combine that action with
the sparse Hadamard transitions, and the physical swaps must implement bit reversal.

```lean
noncomputable section
namespace QASMVerification

def qftControlFactor (j k : Nat) (x : Nat) : ℂ :=
  if basisBit x k = 1 ∧ basisBit x j = 1 then phase (qftPhase (j-k)) else 1

theorem qft_cp_diagonal {n j k : Nat} (hk : k < j) (hj : j < n) :
    stepOperator n (.controlledPhase k j (j-k)) =
      Matrix.diagonal (fun x : Basis n => qftControlFactor j k x.val) := by
  ext r c
  by_cases h : r = c
  · subst c; simp [stepOperator, qftControlFactor, hk, hj]
  · simp [stepOperator, qftControlFactor, hk, hj, h]

theorem fold_qft_controls {n j : Nat} (hj : j < n) (controls : List Nat)
    (valid : ∀ k ∈ controls, k < j) (initial : Operator n) :
    controls.foldl (fun acc k => sequential acc (stepOperator n (.controlledPhase k j (j-k)))) initial =
      Matrix.diagonal (fun x : Basis n => (controls.map (fun k => qftControlFactor j k x.val)).prod) * initial := by
  induction controls generalizing initial with
  | nil => simp [Matrix.diagonal_one]
  | cons k rest ih =>
    rw [List.foldl_cons, ih (fun k hk => valid k (by simp [hk]))]
    rw [sequential, qft_cp_diagonal (valid k (by simp)) hj, ← Matrix.mul_assoc,
      Matrix.diagonal_mul_diagonal]
    congr 1
    congr 1
    funext x
    simp [List.prod_cons, mul_comm]

```

## The full block for one target

The generated control list is descending. Its matrices are diagonal and commute, so
its product agrees with the finite product indexed by all lower controls.

```lean
theorem fold_qft_control_range {n j : Nat} (hj : j < n) (initial : Operator n) :
    ((List.range j).reverse.map (fun k => QFTStep.controlledPhase k j (j-k))).foldl
      (fun acc step => sequential acc (stepOperator n step)) initial =
      Matrix.diagonal (fun x : Basis n => ∏ k ∈ Finset.range j,
        qftControlFactor j k x.val) * initial := by
  rw [List.foldl_map, fold_qft_controls hj _ (fun k hk =>
    List.mem_range.mp (List.mem_reverse.mp hk))]
  congr 1
  congr 1
  funext x
  rw [List.map_reverse, List.prod_reverse, ← List.prod_toFinset _ (List.nodup_range : (List.range j).Nodup)]
  rw [show (List.range j).toFinset = Finset.range j by
    ext k
    simp only [List.mem_toFinset, List.mem_range, Finset.mem_range]]

theorem qft_target_block {n j : Nat} (hj : j < n) :
    (QFTStep.hadamard j :: (List.range j).reverse.map
      (fun k => QFTStep.controlledPhase k j (j-k))).foldl
        (fun acc step => sequential acc (stepOperator n step)) 1 =
      Matrix.diagonal (fun x : Basis n => ∏ k ∈ Finset.range j,
        qftControlFactor j k x.val) * stepOperator n (.hadamard j) := by
  rw [List.foldl_cons, sequential_identity_left, fold_qft_control_range hj]

```

## The highest target

For every register size, the original sparse Hadamard matrix on the highest bit agrees
with the tensor of identity on the lower register and the native Hadamard. This is an
entrywise theorem about `stepOperator`, with its arithmetic support condition preserved.

```lean
theorem qft_top_hadamard (n : Nat) : stepOperator (n+1) (.hadamard n) = tensor (1 : Operator n) hadamard := by
  have hbit (x : Basis (n+1)) : basisBit x.val n = x.val / 2^n := by
    have hdiv : x.val / 2^n < 2 := by
      apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
      simpa [pow_succ, Nat.mul_comm] using x.isLt
    exact Nat.mod_eq_of_lt hdiv
  have hclear (x : Basis (n+1)) : x.val - basisBit x.val n * 2^n = x.val % 2^n := by
    rw [hbit]
    have hd := Nat.mod_add_div x.val (2^n)
    rw [Nat.mul_comm] at hd
    omega
  ext r c
  simp only [stepOperator]
  rw [hclear r, hclear c]
  by_cases hl : r.val % 2^n = c.val % 2^n
  · simp only [Nat.lt_succ_self, hl, and_self, ↓reduceIte, tensor, Matrix.one_apply, one_mul]
    congr 1 <;> apply Fin.ext
    · exact hbit r
    · exact hbit c
  · simp [tensor, hl]

end QASMVerification
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
