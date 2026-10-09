    import LiterateLean
    import QASM.Execution.EffectSemantics
    import QASMVerification.Semantics.Circuit
    open scoped LiterateLean

# Joint classical and quantum execution contracts

A successful finite execution carries the classical store, ordered physical handle
bindings, accumulated unitary, and completion together. The matrix records the action
on arbitrary input states; allocation is therefore outside the transformation contract.
A concrete classical kernel must instantiate the completion-aware model and its fault
relation. No correctness claim follows from providing callbacks alone.

Routing refinement tracks input and output coordinates. Its matrices must themselves
be verified permutations before an adjoint can be used as an inverse. The successful
refinement below is finite-behavior equivalence, and makes no claim about divergence.

```lean
noncomputable section
namespace QASMVerification
open QASM.IR
open QASM.Execution.Semantics (Flow)

structure JointState (n : Nat) (Store : Type) where
  classical : Store
  handles : VarId → List (Fin n)
  action : Operator n

structure ExecutionProfile (n : Nat) (Store : Type) where
  model : QASM.Execution.EffectSemantics.Model (JointState n Store)
  fault : Proc → JointState n Store → Prop

def TotalUnitaryCorrect {n : Nat} {Store : Type} (profile : ExecutionProfile n Store)
    (body : Proc) (initial : JointState n Store) (target : Operator n) : Prop :=
  QASM.Execution.EffectSemantics.TotalCorrect profile.model profile.fault body initial
    (fun final completion => completion = .next ∧ final.action = target * initial.action)

def RoutingInvariant {n : Nat} (physical logical incoming outgoing : Operator n) : Prop :=
  IsUnitary incoming ∧ IsUnitary outgoing ∧
  physical = outgoing.conjTranspose * logical * incoming

def SuccessfulRefinement {n : Nat} {Store : Type} (profile : ExecutionProfile n Store)
    (actual : Proc → JointState n Store → JointState n Store → Flow → Prop) : Prop :=
  ∀ proc initial final completion,
    actual proc initial final completion ↔
      QASM.Execution.EffectSemantics.Exec profile.model proc initial final completion

/-- Refusing faults is separate from agreement on successful executions. -/
def FaultRefinement {n : Nat} {Store : Type} (profile : ExecutionProfile n Store)
    (actualFault : Proc → JointState n Store → Prop) : Prop :=
  ∀ proc initial, actualFault proc initial ↔ profile.fault proc initial
end QASMVerification
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
