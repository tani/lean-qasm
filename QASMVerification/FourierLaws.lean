    import LiterateLean
    import QASMVerification.QFTLaws
    open scoped LiterateLean

# Binary factorization of the Fourier matrix

These identities hold for every register size. The Fourier matrix remains the independently
defined exponential matrix from Quantum. Its binary factorization is proved using Euclidean
remainder, finite sums, and the exponential addition law. No circuit equality is assumed.

```lean
noncomputable section
namespace QASMVerification

theorem binary_remainder_succ (x n : Nat) :
    x % 2^(n+1) = x % 2^n + 2^n * basisBit x n := by
  have h := Nat.mod_add_div (x % (2^n * 2)) (2^n)
  rw [Nat.mod_mul_right_mod, Nat.mod_mul_right_div_self] at h
  simpa [pow_succ, basisBit] using h.symm

theorem binary_expansion_mod (x n : Nat) :
    (∑ j ∈ Finset.range n, basisBit x j * 2^j) = x % 2^n := by
  induction n with
  | zero => simp [Nat.mod_one]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, binary_remainder_succ]
    simp [Nat.mul_comm]

theorem binary_expansion {x n : Nat} (h : x < 2^n) :
    (∑ j ∈ Finset.range n, basisBit x j * 2^j) = x := by
  rw [binary_expansion_mod, Nat.mod_eq_of_lt h]

```

## Bit reversal

Reversal is bounded and is its own inverse modulo the register size. This constructs
an actual basis equivalence rather than postulating a permutation.

```lean
theorem basisBit_shift (x j : Nat) : basisBit (x/2) j = basisBit x (j+1) := by
  simp only [basisBit, Nat.div_div_eq_div_mul, pow_succ]
  rw [Nat.mul_comm 2]

theorem reverseBits_succ (x n : Nat) :
    reverseBits (n+1) x = reverseBits n x * 2 + basisBit x n := by
  simp [reverseBits, List.range_succ, List.foldl_append, basisBit]

theorem reverseBits_lt (x n : Nat) : reverseBits n x < 2^n := by
  induction n with
  | zero => simp [reverseBits]
  | succ n ih =>
    have hb := Nat.mod_lt (x / 2^n) (show 0 < 2 by decide)
    rw [reverseBits_succ, pow_succ]
    unfold basisBit
    omega

theorem reverseBits_shift (x n : Nat) :
    reverseBits (n+1) x = 2^n * (x % 2) + reverseBits n (x/2) := by
  induction n with
  | zero => simp [reverseBits]
  | succ n ih =>
    rw [reverseBits_succ x (n+1), ih, reverseBits_succ (x/2) n,
      basisBit_shift, pow_succ]
    ring

theorem reverseBits_involution_mod (x n : Nat) :
    reverseBits n (reverseBits n x) = x % 2^n := by
  induction n generalizing x with
  | zero => simp [reverseBits, Nat.mod_one]
  | succ n ih =>
    have hb : basisBit x n < 2 := Nat.mod_lt _ (by decide)
    have hr := reverseBits_succ x n
    have hmod : reverseBits (n+1) x % 2 = basisBit x n := by omega
    have hdiv : reverseBits (n+1) x / 2 = reverseBits n x := by omega
    rw [reverseBits_shift, hmod, hdiv, ih, binary_remainder_succ]
    omega

theorem reverseBits_involution {x n : Nat} (h : x < 2^n) :
    reverseBits n (reverseBits n x) = x := by
  rw [reverseBits_involution_mod, Nat.mod_eq_of_lt h]

/-- Reversal is a verified change of basis, including the empty register. -/
def bitReversal (n : Nat) : Equiv.Perm (Basis n) where
  toFun x := ⟨reverseBits n x.val, reverseBits_lt x.val n⟩
  invFun x := ⟨reverseBits n x.val, reverseBits_lt x.val n⟩
  left_inv x := Fin.ext (reverseBits_involution x.isLt)
  right_inv x := Fin.ext (reverseBits_involution x.isLt)

```

## Exact phase arithmetic

The exponential addition law and its integer period justify dropping upper input bits.
The target-phase equation matches the Hadamard contribution and all controlled phases
for one iteration of the descending QFT core.

```lean
theorem phase_sum_range (f : Nat → ℝ) (n : Nat) :
    phase (∑ j ∈ Finset.range n, f j) = ∏ j ∈ Finset.range n, phase (f j) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, phase_add, ih, Finset.prod_range_succ]

theorem phase_nat_mul (a : ℝ) (k : Nat) : phase ((k : ℝ) * a) = phase a ^ k := by
  simp only [phase, Complex.ofReal_mul, Complex.ofReal_natCast, mul_assoc]
  exact Complex.exp_nat_mul _ _

@[simp] theorem phase_two_pi_nat (k : Nat) : phase (2 * Real.pi * (k : ℝ)) = 1 := by
  rw [mul_comm (2 * Real.pi), phase_nat_mul]
  simp [phase, Complex.exp_two_pi_mul_I]

theorem phase_add_two_pi_nat (a : ℝ) (k : Nat) :
    phase (a + 2 * Real.pi * (k : ℝ)) = phase a := by
  rw [phase_add, phase_two_pi_nat, mul_one]

theorem phase_binary_product (n x y : Nat) (hy : y < 2^n) :
    phase (2 * Real.pi * (x : ℝ) * (y : ℝ) / (2^n : ℝ)) =
      ∏ j ∈ Finset.range n,
        phase (2 * Real.pi * (x : ℝ) * (basisBit y j : ℝ) * (2^j : ℝ) /
          (2^n : ℝ)) := by
  have hexp : (∑ j ∈ Finset.range n, (basisBit y j : ℝ) * (2^j : ℝ)) = (y : ℝ) := by
    exact_mod_cast binary_expansion hy
  rw [← phase_sum_range]
  congr 1
  calc
    _ = (2 * Real.pi * (x : ℝ) / (2^n : ℝ)) * (y : ℝ) := by ring
    _ = (2 * Real.pi * (x : ℝ) / (2^n : ℝ)) *
        (∑ j ∈ Finset.range n, (basisBit y j : ℝ) * (2^j : ℝ)) := by rw [hexp]
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j hj; ring

theorem fourier_binary_product (n : Nat) (row col : Basis n) :
    fourier n row col =
      (∏ j ∈ Finset.range n,
        phase (2 * Real.pi * (col.val : ℝ) * (basisBit row.val j : ℝ) *
          (2^j : ℝ) / (2^n : ℝ))) / (Real.sqrt (2^n : ℝ) : ℂ) := by
  exact congrArg (fun z : ℂ => z / (Real.sqrt (2^n : ℝ) : ℂ))
    (phase_binary_product n col.val row.val row.isLt)

theorem qftPhase_mod (x j : Nat) : phase (qftPhase j * (x : ℝ)) =
 phase (qftPhase j * ((x % 2^(j+1) : Nat) : ℝ)) := by
 have hd := Nat.mod_add_div x (2^(j+1))
 have hdR : ((x % 2^(j+1) : Nat) : ℝ) + (2^(j+1) : ℝ) * ((x / 2^(j+1) : Nat) : ℝ) = (x : ℝ) := by exact_mod_cast hd
 have hp : (2^j : ℝ) ≠ 0 := by positivity
 have ha : qftPhase j * (x : ℝ) =
   qftPhase j * ((x % 2^(j+1) : Nat) : ℝ) + 2 * Real.pi * ((x / 2^(j+1) : Nat) : ℝ) := by
  rw [← hdR]
  unfold qftPhase
  rw [pow_succ]
  field_simp
  ring
 rw [ha, phase_add_two_pi_nat]

theorem qftPhase_mul_pow {j k : Nat} (h : k ≤ j) :
    qftPhase j * (2^k : ℝ) = qftPhase (j-k) := by
  have he : j = k + (j-k) := by omega
  unfold qftPhase
  conv_lhs => rw [he, pow_add]
  field_simp

theorem qft_target_phase (j x y : Nat) :
    phase (qftPhase j * (x : ℝ) * (y : ℝ)) =
      phase (Real.pi * (basisBit x j : ℝ) * (y : ℝ)) *
      ∏ k ∈ Finset.range j,
        phase (qftPhase (j-k) * (basisBit x k : ℝ) * (y : ℝ)) := by
  have hmod : phase (qftPhase j * (x : ℝ) * (y : ℝ)) =
      phase (qftPhase j * ((x % 2^(j+1) : Nat) : ℝ) * (y : ℝ)) := by
    rw [mul_comm _ (y : ℝ), phase_nat_mul, qftPhase_mod,
      ← phase_nat_mul, mul_comm (y : ℝ)]
  rw [hmod]
  have hexp : ((x % 2^(j+1) : Nat) : ℝ) =
      (∑ k ∈ Finset.range j, (basisBit x k : ℝ) * (2^k : ℝ)) +
        (2^j : ℝ) * (basisBit x j : ℝ) := by
    exact_mod_cast (binary_remainder_succ x j).trans
      (congrArg (fun z => z + 2^j * basisBit x j) (binary_expansion_mod x j).symm)
  have ha : qftPhase j * ((x % 2^(j+1) : Nat) : ℝ) * (y : ℝ) =
      Real.pi * (basisBit x j : ℝ) * (y : ℝ) +
        ∑ k ∈ Finset.range j, qftPhase (j-k) * (basisBit x k : ℝ) * (y : ℝ) := by
    rw [hexp, mul_add, add_mul]
    have hh : qftPhase j * (2^j : ℝ) = Real.pi := by
      simp [qftPhase]
    have hl : qftPhase j * (∑ k ∈ Finset.range j,
          (basisBit x k : ℝ) * (2^k : ℝ)) * (y : ℝ) =
        ∑ k ∈ Finset.range j, qftPhase (j-k) * (basisBit x k : ℝ) * (y : ℝ) := by
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      have hp := qftPhase_mul_pow (Nat.le_of_lt (Finset.mem_range.mp hk))
      calc
        _ = (qftPhase j * (2^k : ℝ)) * (basisBit x k : ℝ) * (y : ℝ) := by ring
        _ = _ := by rw [hp]
    rw [hl]
    have hc : qftPhase j * ((2^j : ℝ) * (basisBit x j : ℝ)) * (y : ℝ) =
        Real.pi * (basisBit x j : ℝ) * (y : ℝ) := by rw [← mul_assoc, hh]
    rw [hc, add_comm]
  rw [ha, phase_add, phase_sum_range]

```

## Product-state amplitudes

Normalization and the reversal recurrence connect the product of single-qubit phases
to the independent Fourier matrix for arbitrary size.

```lean
theorem phase_reversed_binary_product (n x y : Nat) :
    phase (2 * Real.pi * (x : ℝ) * (reverseBits n y : ℝ) / (2^n : ℝ)) =
      ∏ j ∈ Finset.range n,
        phase (qftPhase j * (x : ℝ) * (basisBit y j : ℝ)) := by
  induction n with
  | zero => simp [reverseBits]
  | succ n ih =>
    rw [reverseBits_succ, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, pow_succ]
    have hp : (2^n : ℝ) ≠ 0 := by positivity
    have ha : 2 * Real.pi * (x : ℝ) *
        ((reverseBits n y : ℝ) * 2 + (basisBit y n : ℝ)) / ((2^n : ℝ) * 2) =
        2 * Real.pi * (x : ℝ) * (reverseBits n y : ℝ) / (2^n : ℝ) +
          qftPhase n * (x : ℝ) * (basisBit y n : ℝ) := by
      unfold qftPhase
      field_simp
    rw [ha, phase_add, ih, Finset.prod_range_succ]

theorem sqrt_two_pow (n : Nat) : Real.sqrt (2^n : ℝ) = Real.sqrt 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]

/-- The product-state amplitude predicted by the descending QFT core. -/
def qftProductAmplitude (n x y : Nat) : ℂ :=
    ∏ j ∈ Finset.range n,
      phase (qftPhase j * (x : ℝ) * (basisBit y j : ℝ)) / (Real.sqrt 2 : ℂ)

theorem qftProductAmplitude_eq_fourier (n : Nat) (row col : Basis n) :
    qftProductAmplitude n col.val row.val = fourier n (bitReversal n row) col := by
  unfold qftProductAmplitude fourier
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const, Finset.card_range, ← Complex.ofReal_pow, sqrt_two_pow]
  rw [← phase_reversed_binary_product]
  rfl


```

## Weights from the native gates

The path weight below uses entries of the actual Hadamard and controlled-phase matrices.
Its Fourier equality is proved for every size. The separate sparse-matrix obligation is
to show that the original gate product `qftMatrix` has this weight, and that its physical
swap list implements the verified reversal. Those obligations are not assumed here.

```lean
theorem hadamard_bit_phase (x y : Nat) (hx : x < 2) (hy : y < 2) :
    hadamard ⟨y, hy⟩ ⟨x, hx⟩ = phase (Real.pi * (x : ℝ) * (y : ℝ)) / (Real.sqrt 2 : ℂ) := by
  have hxc : x = 0 ∨ x = 1 := by omega
  have hyc : y = 0 ∨ y = 1 := by omega
  rcases hxc with rfl | rfl <;> rcases hyc with rfl | rfl <;>
    simp [hadamard]

theorem controlled_bit_phase (a : ℝ) (x y : Nat) (hx : x < 2) (hy : y < 2) :
    (if x = 1 ∧ y = 1 then phase a else 1) = phase (a * (x : ℝ) * (y : ℝ)) := by
  have hxc : x = 0 ∨ x = 1 := by omega
  have hyc : y = 0 ∨ y = 1 := by omega
  rcases hxc with rfl | rfl <;> rcases hyc with rfl | rfl <;> simp

/-- Weight of the basis path with output bits y in the descending core. -/
def qftPathAmplitude (n x y : Nat) : ℂ :=
  ∏ j ∈ Finset.range n,
    hadamard ⟨basisBit y j, Nat.mod_lt _ (by decide)⟩
      ⟨basisBit x j, Nat.mod_lt _ (by decide)⟩ *
    ∏ k ∈ Finset.range j,
      if basisBit x k = 1 ∧ basisBit y j = 1 then phase (qftPhase (j-k)) else 1

theorem qftPathAmplitude_eq_product (n x y : Nat) :
    qftPathAmplitude n x y = qftProductAmplitude n x y := by
  unfold qftPathAmplitude qftProductAmplitude
  apply Finset.prod_congr rfl
  intro j hj
  rw [hadamard_bit_phase]
  have hcp (k : Nat) := controlled_bit_phase (qftPhase (j-k)) (basisBit x k)
    (basisBit y j) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
  simp_rw [hcp]
  rw [qft_target_phase]
  ring

/-- Every-size Fourier equality for the gate-path weight, before physical bit reversal. -/
theorem qftPathAmplitude_eq_fourier (n : Nat) (row col : Basis n) :
    qftPathAmplitude n col.val row.val = fourier n (bitReversal n row) col := by
  rw [qftPathAmplitude_eq_product, qftProductAmplitude_eq_fourier]

/-- The final reversal gives the positive-sign Fourier component for any width. -/
theorem qftPathAmplitude_reversed_eq_fourier (n : Nat) (row col : Basis n) :
    qftPathAmplitude n col.val (reverseBits n row.val) = fourier n row col := by
  have h := qftPathAmplitude_eq_fourier n (bitReversal n row) col
  simpa only [bitReversal, Equiv.coe_fn_mk, reverseBits_involution row.isLt] using h

end QASMVerification
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
