    import LiterateLean
    import QASMVerification.QFTCoreLaws
    open scoped LiterateLean

# Physical swap matrices and bit reversal

Physical SWAP exchanges two basis bits. Its original arithmetic matrix is related to a
verified self-inverse basis permutation, and the generated disjoint swap list realizes
bit reversal. The final Fourier theorem uses the original QFT gate fold.

```lean
noncomputable section
namespace QASMVerification

def swapBits (x j k : Nat) : Nat :=
  replaceBit (replaceBit x j (basisBit x k)) k (basisBit x j)

theorem basisBit_swapBits (x j k i : Nat) (hne : j ≠ k) :
    basisBit (swapBits x j k) i =
      if i = j then basisBit x k else if i = k then basisBit x j else basisBit x i := by
  unfold swapBits
  by_cases hi : i = k
  · subst i
    rw [basisBit_replaceBit (replaceBit x j (basisBit x k)) k (basisBit x j) (Nat.mod_lt _ (by decide))]
    simp [hne.symm]
  · rw [basisBit_replace_other (replaceBit x j (basisBit x k)) k (basisBit x j) i
      (Nat.mod_lt _ (by decide)) hi]
    by_cases hij : i = j
    · subst i
      rw [basisBit_replaceBit x j (basisBit x k) (Nat.mod_lt _ (by decide))]
      simp
    · rw [basisBit_replace_other x j (basisBit x k) i (Nat.mod_lt _ (by decide)) hij]
      simp [hij, hi]

theorem swapBits_lt {n x j k : Nat} (hx : x < 2^n) (hj : j < n) (hk : k < n) :
    swapBits x j k < 2^n :=
  replaceBit_lt (replaceBit_lt hx hj (Nat.mod_lt _ (by decide))) hk (Nat.mod_lt _ (by decide))

theorem basisBits_ext {x y n : Nat} (hx : x < 2^n) (hy : y < 2^n)
    (bits : ∀ i < n, basisBit x i = basisBit y i) : x = y := by
  rw [← binary_expansion hx, ← binary_expansion hy]
  apply Finset.sum_congr rfl
  intro i hi
  rw [bits i (Finset.mem_range.mp hi)]

theorem swapBits_involution {n x j k : Nat} (hx : x < 2^n) (hj : j < n) (hk : k < n)
    (hne : j ≠ k) : swapBits (swapBits x j k) j k = x := by
  apply basisBits_ext (swapBits_lt (swapBits_lt hx hj hk) hj hk) hx
  intro i hi
  simp only [basisBit_swapBits _ _ _ _ hne]
  by_cases hij : i = j <;> by_cases hik : i = k <;> simp_all

theorem swapBits_arithmetic (x j k : Nat) (hne : j ≠ k) :
    swapBits x j k = x - basisBit x j * 2^j - basisBit x k * 2^k +
      basisBit x j * 2^k + basisBit x k * 2^j := by
  have hclear : basisBit x k * 2^k ≤ clearBit x j := by
    have h := basisBit_weight_le (replaceBit x j 0) k
    rw [basisBit_replace_other _ _ _ _ (by decide) hne.symm] at h
    simpa [replaceBit] using h
  change (replaceBit x j (basisBit x k) -
      basisBit (replaceBit x j (basisBit x k)) k * 2^k) + basisBit x j * 2^k = _
  rw [basisBit_replace_other x j (basisBit x k) k (Nat.mod_lt _ (by decide)) hne.symm]
  unfold replaceBit clearBit at *
  omega

def swapBasis (n j k : Nat) (hj : j < n) (hk : k < n) (hne : j ≠ k) : Equiv.Perm (Basis n) where
  toFun x := ⟨swapBits x.val j k, swapBits_lt x.isLt hj hk⟩
  invFun x := ⟨swapBits x.val j k, swapBits_lt x.isLt hj hk⟩
  left_inv x := Fin.ext (swapBits_involution x.isLt hj hk hne)
  right_inv x := Fin.ext (swapBits_involution x.isLt hj hk hne)


```

## Register reversal from disjoint swaps

The swap-loop invariant records which symmetric positions have already exchanged their
input bits. The midpoint remains fixed for odd widths.

```lean
theorem basisBit_reverseBits {n i : Nat} (x : Nat) (hi : i < n) :
    basisBit (reverseBits n x) i = basisBit x (n-1-i) := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    have hb : basisBit x n < 2 := Nat.mod_lt _ (by decide)
    have hr := reverseBits_succ x n
    by_cases hz : i = 0
    · subst i
      have hm : reverseBits (n+1) x % 2 = basisBit x n := by omega
      simpa [basisBit] using hm
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hz
      have hd : reverseBits (n+1) x / 2 = reverseBits n x := by omega
      rw [← basisBit_shift, hd, ih (by omega)]
      congr 1
      omega

def applySwaps (n m x : Nat) : Nat :=
  (List.range m).foldl (fun acc j => swapBits acc j (n-1-j)) x

theorem applySwaps_bit (n m x : Nat) (hm : m ≤ n/2) (i : Nat) (hi : i < n) :
    basisBit (applySwaps n m x) i =
      if i < m ∨ n-1-i < m then basisBit x (n-1-i) else basisBit x i := by
  induction m generalizing i with
  | zero => simp [applySwaps]
  | succ m ih =>
    have hm0 : m ≤ n/2 := by omega
    have hne : m ≠ n-1-m := by omega
    simp only [applySwaps, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change basisBit (swapBits (applySwaps n m x) m (n-1-m)) i = _
    rw [basisBit_swapBits _ _ _ _ hne]
    by_cases him : i = m
    · subst i
      rw [if_pos rfl, ih hm0 (n-1-m) (by omega)]
      have hsym : n-1-(n-1-m) = m := by omega
      simp only [hsym]
      simp [show ¬n-1-m < m by omega]
    · by_cases hik : i = n-1-m
      · subst i
        rw [if_neg him, if_pos rfl, ih hm0 m (by omega)]
        have hsym : n-1-(n-1-m) = m := by omega
        simp only [hsym]
        simp [show ¬n-1-m < m by omega]
      · rw [if_neg him, if_neg hik, ih hm0 i hi]
        have hp : (i < m+1 ∨ n-1-i < m+1) ↔ (i < m ∨ n-1-i < m) := by omega
        simp only [hp]

theorem applySwaps_eq_reverseBits (n x : Nat) (hx : x < 2^n) :
    applySwaps n (n/2) x = reverseBits n x := by
  have hbound : ∀ m ≤ n/2, applySwaps n m x < 2^n := by
    intro m hm
    induction m with
    | zero => simpa [applySwaps] using hx
    | succ m ih =>
      simp only [applySwaps, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      apply swapBits_lt (ih (by omega)) <;> omega
  apply basisBits_ext (hbound _ (le_refl _)) (reverseBits_lt x n)
  intro i hi
  rw [applySwaps_bit n (n/2) x (le_refl _) i hi, basisBit_reverseBits x hi]
  by_cases hp : i < n/2 ∨ n-1-i < n/2
  · simp [hp]
  · have hmid : n-1-i = i := by omega
    simp [hmid]


```

## Original physical swap matrices

The arithmetic SWAP support condition agrees with the proved permutation. Matrix
multiplication therefore selects the unique swapped predecessor row.

```lean
theorem swap_step_entry {n j k : Nat} (hj : j < n) (hk : k < n) (hne : j ≠ k)
    (row col : Basis n) :
    stepOperator n (.swap j k) row col =
      if row = swapBasis n j k hj hk hne col then 1 else 0 := by
  have ha := swapBits_arithmetic col.val j k hne
  have hb := swapBits_lt col.isLt hj hk
  simp only [stepOperator, hne, ↓reduceIte, hj, hk, true_and]
  rw [← ha, Nat.mod_eq_of_lt hb]
  simp only [Fin.ext_iff, swapBasis, Equiv.coe_fn_mk]

theorem swap_row_action {n j k : Nat} (hj : j < n) (hk : k < n) (hne : j ≠ k)
    (matrix : Operator n) (row col : Basis n) :
    (stepOperator n (.swap j k) * matrix) row col =
      matrix (swapBasis n j k hj hk hne row) col := by
  let p := swapBasis n j k hj hk hne
  have hp (x : Basis n) : p (p x) = x := Fin.ext (swapBits_involution x.isLt hj hk hne)
  rw [Matrix.mul_apply]
  simp_rw [swap_step_entry hj hk hne]
  have he (x : Basis n) : row = p x ↔ p row = x := by
    constructor
    · intro h; rw [h, hp]
    · intro h; rw [← h, hp]
  change (∑ x, (if row = p x then (1 : ℂ) else 0) * matrix x col) = _
  simp_rw [he]
  simp
  rfl

def reverseSwapRows (n m x : Nat) : Nat :=
  (List.range m).foldr (fun j acc => swapBits acc j (n-1-j)) x

theorem reverseSwapRows_succ (n m x : Nat) :
    reverseSwapRows n (m+1) x = reverseSwapRows n m (swapBits x m (n-1-m)) := by
  simp [reverseSwapRows, List.range_succ, List.foldr_append]

theorem reverseSwapRows_bit (n m x : Nat) (hm : m ≤ n/2) (i : Nat) (hi : i < n) :
    basisBit (reverseSwapRows n m x) i =
      if i < m ∨ n-1-i < m then basisBit x (n-1-i) else basisBit x i := by
  induction m generalizing x with
  | zero => simp [reverseSwapRows]
  | succ m ih =>
    have hne : m ≠ n-1-m := by omega
    rw [reverseSwapRows_succ, ih _ (by omega), basisBit_swapBits _ _ _ _ hne,
      basisBit_swapBits _ _ _ _ hne]
    have hsym : n-1-(n-1-i) = i := by omega
    by_cases him : i = m
    · subst i
      simp only [show ¬(m < m ∨ n-1-m < m) by omega,
        show m < m+1 ∨ n-1-m < m+1 by omega,
        ↓reduceIte]
    · by_cases hik : i = n-1-m
      · subst i
        have hrev : n-1-(n-1-m) = m := by omega
        simp only [hrev, show ¬(n-1-m < m ∨ m < m) by omega,
          show n-1-m < m+1 ∨ m < m+1 by omega, hne.symm,
          ↓reduceIte]
      · have hsm : n-1-i ≠ m := by omega
        have hsk : n-1-i ≠ n-1-m := by omega
        have hp : (i < m+1 ∨ n-1-i < m+1) ↔ (i < m ∨ n-1-i < m) := by omega
        simp only [him, hik, hsm, hsk, hp, ↓reduceIte]

theorem reverseSwapRows_lt {n m x : Nat} (hm : m ≤ n/2) (hx : x < 2^n) :
    reverseSwapRows n m x < 2^n := by
  induction m generalizing x with
  | zero => simpa [reverseSwapRows] using hx
  | succ m ih =>
    rw [reverseSwapRows_succ]
    exact ih (by omega) (swapBits_lt hx (by omega) (by omega))

theorem reverseSwapRows_eq_reverseBits (n x : Nat) (hx : x < 2^n) :
    reverseSwapRows n (n/2) x = reverseBits n x := by
  apply basisBits_ext (reverseSwapRows_lt (le_refl _) hx) (reverseBits_lt x n)
  intro i hi
  rw [reverseSwapRows_bit n (n/2) x (le_refl _) i hi, basisBit_reverseBits x hi]
  by_cases hp : i < n/2 ∨ n-1-i < n/2
  · simp [hp]
  · have hmid : n-1-i = i := by omega
    simp [hmid]

theorem swapRange_matrix (n m : Nat) (hm : m ≤ n/2) (initial : Operator n) (row col : Basis n) :
    ((List.range m).map (fun j => QFTStep.swap j (n-1-j))).foldl
      (fun acc step => sequential acc (stepOperator n step)) initial row col =
        initial ⟨reverseSwapRows n m row.val, reverseSwapRows_lt hm row.isLt⟩ col := by
  induction m generalizing row with
  | zero => rfl
  | succ m ih =>
    have hj : m < n := by omega
    have hk : n-1-m < n := by omega
    have hne : m ≠ n-1-m := by omega
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (stepOperator n (.swap m (n-1-m)) *
      ((List.range m).map (fun j => QFTStep.swap j (n-1-j))).foldl
        (fun acc step => sequential acc (stepOperator n step)) initial) row col = _
    rw [swap_row_action hj hk hne, ih (by omega)]
    congr 1
    apply Fin.ext
    exact (reverseSwapRows_succ n m row.val).symm

```

## General QFT correctness

This equality is about the original `qftMatrix` gate product and the independently
defined Fourier exponential matrix. It includes the physical swaps, normalization,
positive Fourier sign, arbitrary input columns, and the empty register.

```lean
theorem qftCorrect (n : Nat) : qftMatrix n = fourier n := by
  ext row col
  unfold qftMatrix qftSteps
  rw [List.foldl_append]
  change ((List.range (n/2)).map (fun j => QFTStep.swap j (n-1-j))).foldl
    (fun acc step => sequential acc (stepOperator n step))
    ((qftCore n).foldl (fun acc step => sequential acc (stepOperator n step)) 1) row col = _
  rw [swapRange_matrix n (n/2) (le_refl _), qftCore_matrix]
  have h := reverseSwapRows_eq_reverseBits n row.val row.isLt
  change qftPathAmplitude n col.val (reverseSwapRows n (n/2) row.val) = _
  rw [h]
  exact qftPathAmplitude_reversed_eq_fourier n row col

theorem qftCorrect_all : QFTCorrect := qftCorrect

end QASMVerification
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
