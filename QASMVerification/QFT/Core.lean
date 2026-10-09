    import LiterateLean
    import QASMVerification.QFT.Sparse
    open scoped LiterateLean

# Matrix invariant for the descending QFT core

The invariant separates the low bits not yet transformed from the phase factors already
created on the high bits. Every update uses the original sparse Hadamard matrix and
controlled-phase matrix fold. The register size remains arbitrary throughout.

```lean
noncomputable section
namespace QASMVerification

theorem basisBit_mod_div (x j : Nat) : basisBit x j = (x % 2^(j+1)) / 2^j := by
  simp only [basisBit, pow_succ, Nat.mod_mul_right_div_self]

theorem basisBit_mod_pow (x j k : Nat) (hk : k < j) :
    basisBit (x % 2^j) k = basisBit x k := by
  rw [basisBit_mod_div, basisBit_mod_div,
    Nat.mod_mod_of_dvd x (Nat.pow_dvd_pow 2 (by omega))]

theorem basisBit_div_pow (x j k : Nat) (hk : j ≤ k) :
    basisBit (x / 2^j) (k-j) = basisBit x k := by
  unfold basisBit
  rw [Nat.div_div_eq_div_mul, ← pow_add, show j+(k-j) = k by omega]

theorem basisBit_replace_other (x j b k : Nat) (hb : b < 2) (hk : k ≠ j) :
    basisBit (replaceBit x j b) k = basisBit x k := by
  by_cases hkj : k < j
  · rw [← basisBit_mod_pow _ j k hkj, replaceBit_mod, basisBit_mod_pow _ j k hkj]
  · have hjk : j+1 ≤ k := by omega
    rw [← basisBit_div_pow _ (j+1) k hjk, replaceBit_div _ _ _ hb,
      basisBit_div_pow _ (j+1) k hjk]

theorem mod_pow_succ_eq (x y j : Nat) :
    x % 2^(j+1) = y % 2^(j+1) ↔
      x % 2^j = y % 2^j ∧ basisBit x j = basisBit y j := by
  constructor
  · intro h
    constructor
    · have hm := congrArg (fun z => z % 2^j) h
      simpa only [pow_succ, Nat.mod_mul_right_mod] using hm
    · have hb := congrArg (fun z => z / 2^j) h
      simpa only [← basisBit_mod_div] using hb
  · rintro ⟨hm, hb⟩
    rw [binary_remainder_succ, binary_remainder_succ, hm, hb]

theorem replaceBit_mod_succ_eq (x y j b : Nat) (hb : b < 2) :
    replaceBit x j b % 2^(j+1) = y % 2^(j+1) ↔
      x % 2^j = y % 2^j ∧ b = basisBit y j := by
  rw [mod_pow_succ_eq, replaceBit_mod, basisBit_replaceBit _ _ _ hb]

def coreFactor (x y j : Nat) : ℂ :=
  phase (qftPhase j * (x : ℝ) * (basisBit y j : ℝ)) / (Real.sqrt 2 : ℂ)

def coreStage (n m : Nat) : Operator n := fun row col =>
  if row.val % 2^m = col.val % 2^m then
    ∏ j ∈ Finset.Ico m n, coreFactor col.val row.val j else 0


```

## One outer-loop update

The two Hadamard predecessors are filtered by the unchanged low-bit prefix. Exactly
one remains whenever that prefix matches the input column. Controlled phases then
supply the next factor of the invariant.

```lean
theorem coreStage_replace {n j : Nat} (hj : j < n) (row col : Basis n)
    (b : Nat) (hb : b < 2) :
    coreStage n (j+1) (replaceBasisBit row j b hj hb) col =
      if row.val % 2^j = col.val % 2^j ∧ b = basisBit col.val j then
        ∏ k ∈ Finset.Ico (j+1) n, coreFactor col.val row.val k else 0 := by
  unfold coreStage
  change (if replaceBit row.val j b % 2^(j+1) = col.val % 2^(j+1) then
    ∏ k ∈ Finset.Ico (j+1) n, coreFactor col.val (replaceBit row.val j b) k else 0) = _
  simp only [replaceBit_mod_succ_eq _ _ _ _ hb]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  unfold coreFactor
  rw [basisBit_replace_other _ _ _ _ hb (by have := Finset.mem_Ico.mp hk; omega)]

theorem coreStage_hadamard {n j : Nat} (hj : j < n) (row col : Basis n) :
    (stepOperator n (.hadamard j) * coreStage n (j+1)) row col =
      if row.val % 2^j = col.val % 2^j then
        phase (Real.pi * (basisBit col.val j : ℝ) * (basisBit row.val j : ℝ)) /
          (Real.sqrt 2 : ℂ) *
          ∏ k ∈ Finset.Ico (j+1) n, coreFactor col.val row.val k else 0 := by
  rw [hadamard_row_action j hj, coreStage_replace hj _ _ 0 (by decide),
    coreStage_replace hj _ _ 1 (by decide)]
  by_cases hm : row.val % 2^j = col.val % 2^j
  · have hb : basisBit col.val j = 0 ∨ basisBit col.val j = 1 := by
      have := Nat.mod_lt (col.val / 2^j) (show 0 < 2 by decide)
      change basisBit col.val j < 2 at this
      omega
    rcases hb with hb | hb
    · simp only [hm, hb, and_self, ↓reduceIte, and_false, one_ne_zero, mul_zero, add_zero]
      have hh := hadamard_bit_phase 0 (basisBit row.val j) (by decide) (Nat.mod_lt _ (by decide))
      simpa using congrArg (fun z => z *
        ∏ k ∈ Finset.Ico (j+1) n, coreFactor col.val row.val k) hh
    · simp only [hm, hb, and_self, ↓reduceIte, and_false, zero_ne_one, mul_zero, zero_add]
      have hh := hadamard_bit_phase 1 (basisBit row.val j) (by decide) (Nat.mod_lt _ (by decide))
      simpa using congrArg (fun z => z *
        ∏ k ∈ Finset.Ico (j+1) n, coreFactor col.val row.val k) hh
  · simp [hm]


theorem coreStage_target {n j : Nat} (hj : j < n) :
    ((QFTStep.hadamard j :: (List.range j).reverse.map
      (fun k => QFTStep.controlledPhase k j (j-k))).foldl
        (fun acc step => sequential acc (stepOperator n step)) 1) * coreStage n (j+1) =
      coreStage n j := by
  rw [qft_target_block hj, Matrix.mul_assoc]
  ext row col
  rw [Matrix.diagonal_mul, coreStage_hadamard hj]
  by_cases hm : row.val % 2^j = col.val % 2^j
  · have hbits (k : Nat) (hk : k < j) : basisBit row.val k = basisBit col.val k := by
      rw [← basisBit_mod_pow _ j k hk, hm, basisBit_mod_pow _ j k hk]
    have hc : (∏ k ∈ Finset.range j, qftControlFactor j k row.val) =
        ∏ k ∈ Finset.range j, phase (qftPhase (j-k) *
          (basisBit col.val k : ℝ) * (basisBit row.val j : ℝ)) := by
      apply Finset.prod_congr rfl
      intro k hk
      unfold qftControlFactor
      rw [controlled_bit_phase (qftPhase (j-k)) (basisBit row.val k) (basisBit row.val j)
        (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)),
        hbits k (Finset.mem_range.mp hk)]
    simp only [hm, ↓reduceIte, coreStage]
    rw [hc, Finset.prod_eq_prod_Ico_succ_bot hj]
    unfold coreFactor
    rw [qft_target_phase j col.val (basisBit row.val j)]
    ring
  · simp [hm, coreStage]

```

## Closing the core induction

Starting at the identity, each descending target block lowers the invariant boundary
by one. The result identifies the original core gate product with its product-state
amplitude for every size, including the empty register.

```lean
theorem coreStage_identity (n : Nat) : coreStage n n = 1 := by
  ext row col
  simp only [coreStage, Finset.Ico_self, Finset.prod_empty,
    Nat.mod_eq_of_lt row.isLt, Nat.mod_eq_of_lt col.isLt, Matrix.one_apply]
  simp only [Fin.ext_iff]

theorem coreStage_zero (n : Nat) (row col : Basis n) :
    coreStage n 0 row col = qftProductAmplitude n col.val row.val := by
  simp [coreStage, Nat.mod_one, Nat.Ico_zero_eq_range, coreFactor, qftProductAmplitude]

theorem qftCore_stage (n m : Nat) (hm : m ≤ n) :
    (qftCore m).foldl (fun acc step => sequential acc (stepOperator n step)) (coreStage n m) =
      coreStage n 0 := by
  induction m with
  | zero => simp [qftCore]
  | succ m ih =>
    rw [qftCore_succ, List.foldl_append]
    rw [foldSteps_accumulator n
      (.hadamard m :: (List.range m).reverse.map (fun k => .controlledPhase k m (m-k)))
      (coreStage n (m+1))]
    rw [coreStage_target (show m < n by omega)]
    exact ih (by omega)

theorem qftCore_matrix (n : Nat) (row col : Basis n) :
    ((qftCore n).foldl (fun acc step => sequential acc (stepOperator n step)) 1) row col =
      qftPathAmplitude n col.val row.val := by
  rw [← coreStage_identity n, qftCore_stage n n (le_refl n), coreStage_zero,
    qftPathAmplitude_eq_product]

end QASMVerification
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
