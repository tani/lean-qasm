    import LiterateLean
    import QASMVerification.QFTMatrixLaws
    open scoped LiterateLean

# Sparse Hadamard transitions on arbitrary targets

Replacing one computational-basis bit identifies the two possible predecessors of a
Hadamard transition. The arithmetic below uses the original support condition of
`stepOperator`; it does not replace the QFT gate semantics.

```lean
noncomputable section
namespace QASMVerification
def clearBit (x j : Nat) : Nat := x - basisBit x j * 2^j
def replaceBit (x j b : Nat) : Nat := clearBit x j + b * 2^j
theorem clearBit_decomposition (x j : Nat) : clearBit x j = x % 2^j + 2^(j+1) * (x / 2^(j+1)) := by
 have h := Nat.mod_add_div x (2^(j+1))
 rw [binary_remainder_succ] at h
 unfold clearBit
 rw [Nat.mul_comm (basisBit x j)]
 omega
theorem basisBit_replaceBit (x j : Nat) (b : Nat) (hb : b<2) : basisBit (replaceBit x j b) j = b := by
 have hc := clearBit_decomposition x j
 unfold replaceBit basisBit
 rw [hc, pow_succ]
 have hp : 0 < 2^j := by positivity
 have hd : (x % 2^j + 2^j * 2 * (x / (2^j*2)) + b*2^j) / 2^j =
   2 * (x / (2^j*2)) + b := by
  have he : x % 2^j + 2^j * 2 * (x / (2^j*2)) + b*2^j =
    x % 2^j + (2 * (x / (2^j*2)) + b) * 2^j := by ring
  rw [he, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt (Nat.mod_lt _ hp)]
  simp
 rw [hd]
 omega


theorem basisBit_weight_le (x j : Nat) : basisBit x j * 2^j ≤ x :=
  (Nat.mul_le_mul_right (2^j) (Nat.mod_le _ _)).trans (Nat.div_mul_le_self x (2^j))

theorem clearBit_add_bit (x j : Nat) : clearBit x j + basisBit x j * 2^j = x :=
  Nat.sub_add_cancel (basisBit_weight_le x j)

theorem clearBit_replaceBit (x j b : Nat) (hb : b < 2) :
    clearBit (replaceBit x j b) j = clearBit x j := by
  unfold clearBit
  rw [basisBit_replaceBit _ _ _ hb]
  exact Nat.add_sub_cancel _ _

theorem replaceBit_lt {n j x b : Nat} (hx : x < 2^n) (hj : j < n) (hb : b < 2) :
    replaceBit x j b < 2^n := by
  have hp : 0 < 2^j := by positivity
  have he : j+1+(n-(j+1)) = n := by omega
  have he' : n-(j+1)+(j+1) = n := by omega
  have hhigh : x / 2^(j+1) < 2^(n-(j+1)) := by
    apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
    simpa [← pow_add, he, he', Nat.mul_comm] using hx
  have hlo := Nat.mod_lt x hp
  have hlow : x % 2^j + b*2^j < 2^(j+1) := by
    rw [pow_succ]
    have hc : b = 0 ∨ b = 1 := by omega
    rcases hc with rfl | rfl <;> simp only [Nat.zero_mul, Nat.one_mul] <;> omega
  have hstep : replaceBit x j b < 2^(j+1) * (x / 2^(j+1) + 1) := by
    unfold replaceBit
    rw [clearBit_decomposition]
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hbound := Nat.mul_le_mul_left (2^(j+1)) (show x / 2^(j+1)+1 ≤ 2^(n-(j+1)) by omega)
  rw [← pow_add, he] at hbound
  exact hstep.trans_le hbound

theorem replaceBit_mod (x j b : Nat) : replaceBit x j b % 2^j = x % 2^j := by
  unfold replaceBit
  rw [clearBit_decomposition, pow_succ]
  have he : x % 2^j + 2^j * 2 * (x / (2^j*2)) + b*2^j =
      x % 2^j + (2 * (x / (2^j*2)) + b) * 2^j := by ring
  rw [he]
  simp

theorem replaceBit_div (x j b : Nat) (hb : b < 2) :
    replaceBit x j b / 2^(j+1) = x / 2^(j+1) := by
  have hp : 0 < 2^j := by positivity
  have hlo := Nat.mod_lt x hp
  have hlow : x % 2^j + b*2^j < 2^(j+1) := by
    rw [pow_succ]
    have hc : b = 0 ∨ b = 1 := by omega
    rcases hc with rfl | rfl <;> simp only [Nat.zero_mul, Nat.one_mul] <;> omega
  unfold replaceBit
  rw [clearBit_decomposition]
  have he : x % 2^j + 2^(j+1) * (x / 2^(j+1)) + b*2^j =
      x % 2^j + b*2^j + (x / 2^(j+1)) * 2^(j+1) := by ring
  rw [he, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hlow]
  simp

/-- A valid replacement remains inside the same register. -/
def replaceBasisBit {n : Nat} (x : Basis n) (j b : Nat) (hj : j < n) (hb : b < 2) : Basis n :=
  ⟨replaceBit x.val j b, replaceBit_lt x.isLt hj hb⟩


```

## Row action of the original Hadamard matrix

The matrix multiplication sum has exactly two possible predecessors. The theorem
holds for any target inside any register and any matrix accumulator; no QFT amplitude
formula is assumed. It is the sparse-matrix step needed for the outer-loop invariant.

```lean
theorem hadamard_replace_entry {n : Nat} (r : Basis n) (j b : Nat)
    (hj : j < n) (hb : b < 2) :
    stepOperator n (.hadamard j) r (replaceBasisBit r j b hj hb) =
      hadamard ⟨basisBit r.val j, Nat.mod_lt _ (by decide)⟩ ⟨b, hb⟩ := by
  change (if j < n ∧ clearBit r.val j = clearBit (replaceBit r.val j b) j then
    hadamard ⟨basisBit r.val j, _⟩ ⟨basisBit (replaceBit r.val j b) j, _⟩ else 0) = _
  rw [clearBit_replaceBit _ _ _ hb]
  simp only [hj, and_self, ↓reduceIte]
  congr 1
  apply Fin.ext
  exact basisBit_replaceBit _ _ _ hb

theorem hadamard_row_action {n : Nat} (j : Nat) (hj : j < n)
    (matrix : Operator n) (row col : Basis n) :
    (stepOperator n (.hadamard j) * matrix) row col =
      hadamard ⟨basisBit row.val j, Nat.mod_lt _ (by decide)⟩ 0 *
        matrix (replaceBasisBit row j 0 hj (by decide)) col +
      hadamard ⟨basisBit row.val j, Nat.mod_lt _ (by decide)⟩ 1 *
        matrix (replaceBasisBit row j 1 hj (by decide)) col := by
  let a := replaceBasisBit row j 0 hj (by decide)
  let b := replaceBasisBit row j 1 hj (by decide)
  have hne : a ≠ b := by
    intro h
    have hb := congrArg (fun x : Basis n => basisBit x.val j) h
    change basisBit (replaceBit row.val j 0) j = basisBit (replaceBit row.val j 1) j at hb
    rw [basisBit_replaceBit _ _ _ (by decide), basisBit_replaceBit _ _ _ (by decide)] at hb
    omega
  rw [Matrix.mul_apply]
  have hsum := Finset.sum_subset (show ({a, b} : Finset (Basis n)) ⊆ Finset.univ by simp)
    (f := fun x => stepOperator n (.hadamard j) row x * matrix x col)
  have hz : ∀ x ∈ (Finset.univ : Finset (Basis n)), x ∉ ({a, b} : Finset (Basis n)) →
      stepOperator n (.hadamard j) row x * matrix x col = 0 := by
    intro x hx hnot
    by_cases hc : clearBit row.val j = clearBit x.val j
    · have hex : replaceBit row.val j (basisBit x.val j) = x.val := by
        unfold replaceBit
        rw [hc, clearBit_add_bit]
      have hbit : basisBit x.val j = 0 ∨ basisBit x.val j = 1 := by
        have := Nat.mod_lt (x.val / 2^j) (show 0 < 2 by decide)
        change basisBit x.val j < 2 at this
        omega
      have hmem : x ∈ ({a, b} : Finset (Basis n)) := by
        rcases hbit with hzero | hone
        · have he : x = a := Fin.ext (by simpa only [a, replaceBasisBit, hzero] using hex.symm)
          simp [he]
        · have he : x = b := Fin.ext (by simpa only [b, replaceBasisBit, hone] using hex.symm)
          simp [he]
      exact False.elim (hnot hmem)
    · change (if j < n ∧ clearBit row.val j = clearBit x.val j then
          hadamard ⟨basisBit row.val j, _⟩ ⟨basisBit x.val j, _⟩ else 0) * matrix x col = 0
      simp [hc]
  rw [← hsum hz, Finset.sum_pair hne]
  dsimp only [a, b]
  rw [hadamard_replace_entry, hadamard_replace_entry]
  rfl

end QASMVerification
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
