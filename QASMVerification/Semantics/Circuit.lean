    import LiterateLean
    import QASM.IR.Circuit
    import QASMVerification.Semantics.ExactReal
    open scoped LiterateLean

# Checked circuit interpretation

This finite unitary fragment interprets endomorphisms on qubit interfaces. A derivation
checks boundary widths and composition, rejects unsupported nodes, and requires explicit
primitive and integer-expression interpretations. Neither callback is an axiom: a concrete
profile must instantiate them and prove its laws. The native gate equations are defined in
Quantum; completing every standard-gate recipe is a separate obligation.

Tensor order places the left circuit on low bits. Routing permutations require a basis
bijection agreeing with the recorded lane mapping. They change coordinates; a backend
refinement must also track the physical handle map. Negative integer powers use adjoints;
noninteger powers have no rule in this fragment.

```lean
noncomputable section
namespace QASMVerification
open QASM.IR

def QubitBoundary (interface : Interface) (n : Nat) : Prop :=
  interface = List.replicate n .qubit

def tensor {m n : Nat} (a : Operator m) (b : Operator n) : Operator (m+n) :=
  fun row col =>
    a ⟨row.val % 2^m, Nat.mod_lt _ (by positivity)⟩
      ⟨col.val % 2^m, Nat.mod_lt _ (by positivity)⟩ *
    b ⟨row.val / 2^m, by
        have h := row.isLt
        simp only [Nat.pow_add] at h
        exact (Nat.div_lt_iff_lt_mul (by positivity)).mpr (by simpa [Nat.mul_comm] using h)⟩
      ⟨col.val / 2^m, by
        have h := col.isLt
        simp only [Nat.pow_add] at h
        exact (Nat.div_lt_iff_lt_mul (by positivity)).mpr (by simpa [Nat.mul_comm] using h)⟩

def integerPower {n : Nat} (u : Operator n) (k : Int) : Operator n :=
  if k < 0 then u.conjTranspose ^ k.natAbs else u ^ k.natAbs

def controlPattern (polarities : Array ControlPolarity) (bits : Nat) : Prop :=
  ∀ i : Fin polarities.size,
    (bits / 2 ^ i.val) % 2 = if polarities[i] = .positive then 1 else 0

def controlled {k n : Nat} (polarities : Array ControlPolarity) (u : Operator n) :
    Operator (k+n) := by
  classical
  exact fun row col =>
    if row.val % 2^k = col.val % 2^k then
      if controlPattern polarities (col.val % 2^k) then
        u ⟨row.val / 2^k, by
            have h := row.isLt
            simp only [Nat.pow_add] at h
            exact (Nat.div_lt_iff_lt_mul (by positivity)).mpr (by simpa [Nat.mul_comm] using h)⟩
          ⟨col.val / 2^k, by
            have h := col.isLt
            simp only [Nat.pow_add] at h
            exact (Nat.div_lt_iff_lt_mul (by positivity)).mpr (by simpa [Nat.mul_comm] using h)⟩
      else if row = col then 1 else 0
    else 0

def RoutingAgrees {n : Nat} (routing : WirePermutation) (p : Equiv.Perm (Basis n)) : Prop :=
  routing.mapping.size = n ∧
  ∀ x : Basis n, ∀ i : Fin n,
    routing.mapping[i.val]! < n ∧
    ((p x).val / 2^i.val) % 2 = (x.val / 2^(routing.mapping[i.val]!)) % 2

structure CircuitProfile where
  primitive : (n : Nat) → Primitive → Operator n → Prop
  integer : Expr → Int → Prop

inductive CircuitEval (profile : CircuitProfile) :
    (n : Nat) → Circuit → Operator n → Prop where
  | identity (h : QubitBoundary wires n) : CircuitEval profile n (.identity wires) 1
  | primitive (hi : QubitBoundary p.input n) (ho : QubitBoundary p.output n)
      (h : profile.primitive n p u) : CircuitEval profile n (.primitive p) u
  | compose (ha : CircuitEval profile n a u) (hb : CircuitEval profile n b v)
      (h : a.cod = b.dom) : CircuitEval profile n (.compose a b) (sequential u v)
  | tensor (ha : CircuitEval profile m a u) (hb : CircuitEval profile n b v) :
      CircuitEval profile (m+n) (.tensor a b) (tensor u v)
  | permutation (hi : QubitBoundary p.domain n) (ho : QubitBoundary p.codomain n)
      (h : RoutingAgrees p routing) :
      CircuitEval profile n (.permute p) (coordinatePermutation routing)
  | inverse (h : CircuitEval profile n c u) :
      CircuitEval profile n (.inverse c) u.conjTranspose
  | power (h : CircuitEval profile n c u) (hk : profile.integer exponent k) :
      CircuitEval profile n (.power exponent c) (integerPower u k)
  | controlled (h : CircuitEval profile n c u) (hc : QubitBoundary spec.controls k)
      (hp : spec.polarities.size = k) :
      CircuitEval profile (k+n) (.controlled spec c) (controlled spec.polarities u)

/-- A checked circuit carries both an interpretation derivation and a unitarity proof.
    Construction does not manufacture either proof from a callback. -/
structure WellFormedCircuit (profile : CircuitProfile) (n : Nat) where
  circuit : Circuit
  matrix : Operator n
  interpretation : CircuitEval profile n circuit matrix
  unitary : IsUnitary matrix

/-- Mathematical validity is not asserted for an arbitrary callback. -/
def ProfileUnitary (profile : CircuitProfile) : Prop :=
  ∀ n p u, profile.primitive n p u → IsUnitary u
end QASMVerification
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
