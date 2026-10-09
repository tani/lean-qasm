    import LiterateLean
    import QASMVerification.Semantics.Program
    import QASMVerification.Semantics.Gates
    open scoped LiterateLean

# Refinement composition and total-correctness transport

Routing composition cancels the intermediate coordinate map using its proved unitarity.
Total correctness transfers only when both successful behavior and faults refine the
specification. Refinement.Runtime separately establishes successful finite control refinement
for the actual Option interpreter; independent atomic semantics, backend accuracy and
fault freedom are additional premises of this stronger total-correctness transport.

```lean
noncomputable section
namespace QASMVerification
open QASM.IR
open QASM.Execution.Semantics (Flow)

theorem routing_compose {n : Nat}
    {physicalA physicalB logicalA logicalB incoming middle outgoing : Operator n}
    (ha : RoutingInvariant physicalA logicalA incoming middle)
    (hb : RoutingInvariant physicalB logicalB middle outgoing) :
    RoutingInvariant (sequential physicalA physicalB)
      (sequential logicalA logicalB) incoming outgoing := by
  rcases ha with ⟨hi, hm, ha⟩
  rcases hb with ⟨_, ho, hb⟩
  refine ⟨hi, ho, ?_⟩
  rw [sequential, ha, hb]
  calc
    (outgoing.conjTranspose * logicalB * middle) *
        (middle.conjTranspose * logicalA * incoming) =
        outgoing.conjTranspose * logicalB * (middle * middle.conjTranspose) *
          logicalA * incoming := by simp [Matrix.mul_assoc]
    _ = outgoing.conjTranspose * sequential logicalA logicalB * incoming := by
      rw [hm.2]
      simp [sequential, Matrix.mul_assoc]

/-- Every derivable circuit has the promised ordered qubit boundaries. -/
theorem circuitEval_boundaries {profile : CircuitProfile} {n : Nat}
    {circuit : Circuit} {u : Operator n} (h : CircuitEval profile n circuit u) :
    QubitBoundary circuit.dom n ∧ QubitBoundary circuit.cod n := by
  induction h with
  | identity h => exact ⟨h, h⟩
  | primitive hi ho _ => exact ⟨hi, ho⟩
  | compose _ _ _ ihA ihB => exact ⟨ihA.1, ihB.2⟩
  | tensor _ _ ihA ihB =>
    simp_all [QubitBoundary, Circuit.dom, Circuit.cod]
  | permutation hi ho _ => exact ⟨hi, ho⟩
  | inverse _ ih => exact ⟨ih.2, ih.1⟩
  | power _ _ ih => exact ih
  | controlled _ hc _ ih =>
    simp_all [QubitBoundary, Circuit.dom, Circuit.cod]

```

## Transfer with explicit premises

Successful-behavior equivalence alone does not exclude faults. Both relations are
required by this theorem, together with total correctness of the specification.

```lean
def ActualTotalCorrect {State : Type}
    (actual : Proc → State → State → Flow → Prop) (fault : Proc → State → Prop)
    (body : Proc) (initial : State) (post : State → Flow → Prop) : Prop :=
  (∃ final completion, actual body initial final completion) ∧
  (∀ final completion, actual body initial final completion → post final completion) ∧
  ¬ fault body initial

theorem totalCorrect_transfer {n : Nat} {Store : Type}
    (profile : ExecutionProfile n Store)
    (actual : Proc → JointState n Store → JointState n Store → Flow → Prop)
    (actualFault : Proc → JointState n Store → Prop)
    (hs : SuccessfulRefinement profile actual) (hf : FaultRefinement profile actualFault)
    (body : Proc) (initial : JointState n Store) (post : JointState n Store → Flow → Prop)
    (h : QASM.Execution.EffectSemantics.TotalCorrect profile.model profile.fault body initial post) :
    ActualTotalCorrect actual actualFault body initial post := by
  rcases h with ⟨⟨final, completion, hex⟩, hall, hnf⟩
  refine ⟨⟨final, completion, (hs _ _ _ _).mpr hex⟩, ?_, ?_⟩
  · intro final completion hex
    exact hall final completion ((hs _ _ _ _).mp hex)
  · intro hbad
    exact hnf ((hf _ _).mp hbad)

end QASMVerification
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
