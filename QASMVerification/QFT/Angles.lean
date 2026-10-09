    import LiterateLean
    import QASM.Runtime
    import QASMVerification.QFT.Model
    import Mathlib.Tactic.NormNum
    import Mathlib.Tactic.Ring
    open scoped LiterateLean

# Exact dyadic-angle refinement

The loop invariant records the actual fixed-width bit pattern after each division.
The real-value theorem requires that the current phase distance is smaller than the
angle width. It does not identify the interpreter's final Float conversion with a real
number. The runtime theorem below addresses the concrete Value.binary implementation.

```lean
noncomputable section
namespace QASMVerification

def thetaBits (width distance : Nat) : Nat := 2 ^ (width - 1 - distance)

theorem thetaBits_half {width distance : Nat} (h : distance + 1 < width) :
    thetaBits width distance / 2 = thetaBits width (distance+1) := by
  have he : width-1-distance = (width-1-(distance+1))+1 := by omega
  simp only [thetaBits, he, pow_succ]
  omega

theorem thetaBits_valid {width distance : Nat} (h : distance < width) :
    ValidBitAngle width (thetaBits width distance) := by
  unfold ValidBitAngle thetaBits
  apply Nat.pow_lt_pow_right (by decide : 1 < (2 : Nat))
  omega

theorem thetaBits_value {width distance : Nat} (h : distance < width) :
    bitAngle width (thetaBits width distance) = qftPhase distance := by
  have he : width-1-distance+distance+1 = width := by omega
  have hp : (2 : ℝ)^width = (2 : ℝ)^(width-1-distance) * 2^distance * 2 := by
    rw [← pow_add, ← pow_succ, he]
  unfold bitAngle thetaBits qftPhase
  push_cast
  rw [hp]
  field_simp

```

## Concrete runtime arithmetic

The first result unfolds the existing Value.binary implementation. Induction then
connects its repeated divisions to the loop invariant, for every admissible distance.

```lean
theorem runtime_angle_half {width bits : Nat} (hw : 0 < width) (hb : bits < 2^width) :
    QASM.Value.binary "/" (.angle width bits) (.uint width 2) =
      .angle width (bits / 2) := by
  simp [QASM.Value.binary, QASM.Value.asInt]
  change QASM.Value.angle width
      ((if width == 0 then 0 else
        (((Int.ofNat bits / 2) % (2 : Int)^width + (2 : Int)^width) % (2 : Int)^width)).natAbs) = _
  simp only [show (width == 0) = false by simp [Nat.ne_of_gt hw], Bool.false_eq_true, ↓reduceIte]
  have hd : bits / 2 < 2^width := lt_of_le_of_lt (Nat.div_le_self _ _) hb
  have hz : Int.ofNat (bits / 2) % (2 : Int)^width = Int.ofNat (bits / 2) := by
    simp only [Int.ofNat_eq_natCast]
    apply Int.emod_eq_of_lt
    · positivity
    · exact_mod_cast hd
  have hdiv : Int.ofNat bits / 2 = Int.ofNat (bits / 2) := by rfl
  rw [hdiv, hz, Int.add_emod, hz, Int.emod_self, Int.add_zero, hz]
  rfl


/-- Uses the concrete runtime operation at every iteration. -/
def runtimeHalves (width : Nat) : Nat → QASM.Value
  | 0 => .angle width (2^(width-1))
  | distance+1 => QASM.Value.binary "/" (runtimeHalves width distance) (.uint width 2)

theorem runtimeHalves_exact {width distance : Nat} (h : distance < width) :
    runtimeHalves width distance = .angle width (thetaBits width distance) := by
  induction distance with
  | zero => simp [runtimeHalves, thetaBits]
  | succ distance ih =>
    have hd : distance < width := by omega
    rw [runtimeHalves, ih hd, runtime_angle_half (by omega) (thetaBits_valid hd),
      thetaBits_half h]

/-- The same invariant serves every CP in every generated QFT size. -/
theorem qft_runtime_phase {n width j k : Nat}
    (hw : n ≤ width) (hj : j < n) (hk : k < j) :
    runtimeHalves width (j-k) = .angle width (thetaBits width (j-k)) ∧
    bitAngle width (thetaBits width (j-k)) = qftPhase (j-k) := by
  have hd : j-k < width := by omega
  exact ⟨runtimeHalves_exact hd, thetaBits_value hd⟩

end QASMVerification
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
