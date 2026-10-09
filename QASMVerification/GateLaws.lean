    import LiterateLean
    import QASMVerification.Native
    import Mathlib.Tactic.Ring
    import Mathlib.Tactic.FinCases
    import Mathlib.Tactic.NormNum
    open scoped LiterateLean

# Exact gate algebra

These laws quantify over real angles and arbitrary register sizes. They preserve global
phase and use the actual native matrices, rather than assuming gate correctness as an
axiom. The executable Float backend is not identified with this real-valued model.

```lean
noncomputable section
namespace QASMVerification

@[simp] theorem phase_zero : phase 0 = 1 := by simp [phase]

theorem phase_add (a b : ℝ) : phase (a+b) = phase a * phase b := by
  simp [phase, add_mul, Complex.exp_add]

@[simp] theorem star_phase (a : ℝ) : star (phase a) = phase (-a) := by
  simp [phase, ← Complex.exp_conj, mul_neg]

@[simp] theorem phase_neg_mul (a : ℝ) : phase (-a) * phase a = 1 := by
  rw [← phase_add]; simp

@[simp] theorem phase_mul_neg (a : ℝ) : phase a * phase (-a) = 1 := by
  rw [← phase_add]; simp

@[simp] theorem unitary_identity (n : Nat) : IsUnitary (1 : Operator n) := by
  simp [IsUnitary]

theorem unitary_sequential {n : Nat} {a b : Operator n}
    (ha : IsUnitary a) (hb : IsUnitary b) : IsUnitary (sequential a b) := by
  rcases ha with ⟨ha, ha'⟩
  rcases hb with ⟨hb, hb'⟩
  constructor
  · simp only [sequential, Matrix.conjTranspose_mul]
    calc
      (a.conjTranspose * b.conjTranspose) * (b * a) =
          a.conjTranspose * (b.conjTranspose * b) * a := by simp [Matrix.mul_assoc]
      _ = 1 := by rw [hb]; simpa using ha
  · simp only [sequential, Matrix.conjTranspose_mul]
    calc
      (b * a) * (a.conjTranspose * b.conjTranspose) =
          b * (a * a.conjTranspose) * b.conjTranspose := by simp [Matrix.mul_assoc]
      _ = 1 := by rw [ha']; simpa using hb'

theorem unitary_adjoint {n : Nat} {u : Operator n} (h : IsUnitary u) :
    IsUnitary u.conjTranspose := by
  simpa [IsUnitary, and_comm] using h

theorem unitary_pow {n : Nat} {u : Operator n} (h : IsUnitary u) (k : Nat) :
    IsUnitary (u ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    exact unitary_sequential h ih

theorem unitary_integerPower {n : Nat} {u : Operator n} (h : IsUnitary u) (k : Int) :
    IsUnitary (integerPower u k) := by
  simp only [integerPower]
  split
  · exact unitary_pow (unitary_adjoint h) _
  · exact unitary_pow h _

```

## Diagonal phases

The same proof covers a phase on any computational-basis subset. In particular, P and
controlled P are unitary for every real angle, with their phases retained exactly.

```lean
def diagonalPhase {n : Nat} (angles : Basis n → ℝ) : Operator n :=
  Matrix.diagonal (fun i => phase (angles i))

theorem unitary_diagonalPhase {n : Nat} (angles : Basis n → ℝ) :
    IsUnitary (diagonalPhase angles) := by
  constructor <;>
    simp [diagonalPhase, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal]

theorem phaseGate_eq_diagonal (a : ℝ) :
    phaseGate a = diagonalPhase (fun i : Basis 1 => if i.val = 0 then 0 else a) := by
  ext i j
  simp [phaseGate, diagonalPhase, Matrix.diagonal_apply]
  split_ifs <;> simp_all

theorem controlledPhase_eq_diagonal (a : ℝ) :
    controlledPhase a = diagonalPhase (fun i : Basis 2 => if i.val = 3 then a else 0) := by
  ext i j
  simp [controlledPhase, diagonalPhase, Matrix.diagonal_apply]
  split_ifs <;> simp_all

theorem unitary_phaseGate (a : ℝ) : IsUnitary (phaseGate a) := by
  rw [phaseGate_eq_diagonal]; exact unitary_diagonalPhase _

theorem unitary_controlledPhase (a : ℝ) : IsUnitary (controlledPhase a) := by
  rw [controlledPhase_eq_diagonal]; exact unitary_diagonalPhase _

@[simp] theorem hadamard_adjoint : hadamard.conjTranspose = hadamard := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hadamard, Matrix.conjTranspose_apply]

theorem hadamard_squared : hadamard * hadamard = 1 := by
  have hs : (Real.sqrt 2 : ℂ)^2 = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)))
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamard, Matrix.mul_apply, Basis, Fin.sum_univ_two] <;>
    field_simp [hn] <;> simp_all
  all_goals norm_num

theorem unitary_hadamard : IsUnitary hadamard := by
  simp only [IsUnitary, hadamard_adjoint, hadamard_squared, and_self]

@[simp] theorem swap_adjoint : swapGate.conjTranspose = swapGate := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [swapGate, Matrix.conjTranspose_apply]

theorem swap_squared : swapGate * swapGate = 1 := by
  ext i j
  change (∑ k : Fin 4,
    (if i.val = 2*(k.val%2)+k.val/2 then (1 : ℂ) else 0) *
    (if k.val = 2*(j.val%2)+j.val/2 then (1 : ℂ) else 0)) =
    (if i = j then 1 else 0)
  rw [Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;> norm_num

theorem unitary_swap : IsUnitary swapGate := by
  simp only [IsUnitary, swap_adjoint, swap_squared, and_self]

```

## Native U and standard-gate recipes

The factorization gives a unitarity proof for native U without quotienting out global
phase. The H recipe theorem checks the exact phase correction used by the standard
library; a floating-point implementation requires an additional approximation theorem.

```lean
@[simp] theorem phase_pi : phase Real.pi = -1 := Complex.exp_pi_mul_I

@[simp] theorem phase_half_pi : phase (Real.pi / 2) = Complex.I := by
  simp [phase, Complex.exp_pi_div_two_mul_I]

@[simp] theorem phase_neg_half_pi : phase (-(Real.pi / 2)) = -Complex.I := by
  rw [← star_phase, phase_half_pi]
  simp

/-- Exact factorization, including the native U global phase. -/
theorem nativeU_factorization (theta phi lambda : ℝ) :
    nativeU theta phi lambda =
      phaseGate phi * (phaseGate (Real.pi / 2) *
        (hadamard * (phaseGate theta * hadamard)) * phaseGate (-(Real.pi / 2))) *
      phaseGate lambda := by
  have hs : (Real.sqrt 2 : ℂ)^2 = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)))
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nativeU, phaseGate, hadamard, Matrix.mul_apply, Basis,
      Fin.sum_univ_two, phase_add] <;>
    field_simp [hn] <;> ring_nf <;> norm_num [hs, Complex.I_sq] <;> ring

theorem unitary_nativeU (theta phi lambda : ℝ) :
    IsUnitary (nativeU theta phi lambda) := by
  rw [nativeU_factorization]
  apply unitary_sequential (unitary_phaseGate lambda)
  apply unitary_sequential
  · apply unitary_sequential (unitary_phaseGate (-(Real.pi / 2)))
    apply unitary_sequential
    · apply unitary_sequential
      · exact unitary_sequential unitary_hadamard (unitary_phaseGate theta)
      · exact unitary_hadamard
    · exact unitary_phaseGate (Real.pi / 2)
  · exact unitary_phaseGate phi

theorem phase_quarter_pi : phase (Real.pi / 4) =
    (Real.sqrt 2 : ℂ) / 2 + (Real.sqrt 2 : ℂ) / 2 * Complex.I := by
  unfold phase
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_four, Real.sin_pi_div_four]
  simp

theorem phase_neg_quarter_pi : phase (-(Real.pi / 4)) =
    (Real.sqrt 2 : ℂ) / 2 - (Real.sqrt 2 : ℂ) / 2 * Complex.I := by
  rw [← star_phase, phase_quarter_pi]
  simp [sub_eq_add_neg]

/-- Mathematical refinement of the standard H recipe, retaining global phase. -/
theorem hadamard_nativeRecipe : hadamard =
    fun i j => phase (-(Real.pi / 4)) * nativeU (Real.pi / 2) 0 Real.pi i j := by
  have hs : (Real.sqrt 2 : ℂ)^2 = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)))
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamard, nativeU, phase_neg_quarter_pi] <;>
    field_simp [hn] <;> ring_nf <;> norm_num [hs, Complex.I_sq]

theorem unitary_globalPhase (gamma : ℝ) :
    IsUnitary (fun _ _ : Basis 0 => phase gamma) := by
  have hd : (fun _ _ : Basis 0 => phase gamma) =
      diagonalPhase (fun _ : Basis 0 => gamma) := by
    ext i j
    have hij : i = j := by
      apply Fin.ext
      have hi := i.isLt
      have hj := j.isLt
      change i.val < 1 at hi
      change j.val < 1 at hj
      omega
    simp [diagonalPhase, hij]
  rw [hd]
  exact unitary_diagonalPhase _

```

## The closed primitive profile

Every constructor of NativePrimitive has a unitarity theorem. Unsupported primitives
remain absent from this relation, so the profile theorem has no fallback case.

```lean
theorem nativeProfile_unitary (argument : QASM.IR.Expr → ℝ → Prop)
    (integer : QASM.IR.Expr → Int → Prop) : ProfileUnitary (nativeProfile argument integer) := by
  intro n p u h
  change NativePrimitive argument n p u at h
  cases h with
  | u => exact unitary_nativeU _ _ _
  | gphase => exact unitary_globalPhase _
  | h => exact unitary_hadamard
  | p => exact unitary_phaseGate _
  | cp => exact unitary_controlledPhase _
  | swap => exact unitary_swap
  | id => exact unitary_identity _

end QASMVerification
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
