    import LiterateLean
    import QASMVerification.Refinement.Proc
    open scoped LiterateLean

# Gate-trace to matrix refinement for structured programs

The event kernel records the effects of each atomic operation and expression evaluation.
Two independently accumulated executions use that same kernel: one appends gate events,
and one multiplies their matrices. Conditions, iteration domains, switches, and returns
may themselves emit events, so their quantum effects cannot disappear at a control-flow
boundary. Scope restoration changes the classical store and preserves quantum action.

The theorem covers every finite Proc derivation, including nested loops and abnormal
completion. The event kernel must still be related to the executable interpreter. This
module does not assert that Float matrices equal their ideal real-valued interpretation.

```lean
noncomputable section
namespace QASMVerification
open QASM.IR
open QASM.Execution.Semantics (Flow)
open QASM.Execution.EffectSemantics

abbrev GateEvents (n : Nat) := List (Operator n)

def eventMatrix {n : Nat} (events : GateEvents n) : Operator n :=
  events.foldl (fun acc gate => gate * acc) 1

theorem eventMatrix_accumulator {n : Nat} (events : GateEvents n) (initial : Operator n) :
    events.foldl (fun acc gate => gate * acc) initial = eventMatrix events * initial := by
  induction events generalizing initial with
  | nil => simp [eventMatrix]
  | cons gate rest ih =>
    change rest.foldl (fun acc gate => gate * acc) (gate * initial) =
      rest.foldl (fun acc gate => gate * acc) (gate * 1) * initial
    rw [Matrix.mul_one, ih (gate * initial), ih gate]
    simp [Matrix.mul_assoc]

theorem eventMatrix_append {n : Nat} (first second : GateEvents n) :
    eventMatrix (first ++ second) = eventMatrix second * eventMatrix first := by
  unfold eventMatrix
  rw [List.foldl_append, eventMatrix_accumulator]
  rfl

```

## Two effect models

Both models use the same atomic events and classical store transitions. The trace
accumulator appends events; the matrix accumulator multiplies them in execution order.

```lean
structure EventKernel (n : Nat) (Store : Type) where
  operation : Op → Store → Store → GateEvents n → Flow → Prop
  condition : Expr → Store → Option Bool → Store → GateEvents n → Prop
  domain : IterationDomain → Store → Option (List QASM.Value) → Store → GateEvents n → Prop
  switchCase : Expr → Array SwitchCase → Option Proc → Store → Option Proc → Store → GateEvents n → Prop
  returnValue : Option Expr → Store → Option QASM.Value → Store → GateEvents n → Flow → Prop
  bindIterator : Var → QASM.Value → Store → Store
  restore : Array Var → Store → Store → Store

def traceModel {n : Nat} {Store : Type} (kernel : EventKernel n Store) :
    Model (Store × GateEvents n) where
  operation op initial final flow := ∃ events,
    kernel.operation op initial.1 final.1 events flow ∧ final.2 = initial.2 ++ events
  condition e initial value final := ∃ events,
    kernel.condition e initial.1 value final.1 events ∧ final.2 = initial.2 ++ events
  domain d initial values final := ∃ events,
    kernel.domain d initial.1 values final.1 events ∧ final.2 = initial.2 ++ events
  switchCase e cases other initial selected final := ∃ events,
    kernel.switchCase e cases other initial.1 selected final.1 events ∧ final.2 = initial.2 ++ events
  returnValue e initial value final flow := ∃ events,
    kernel.returnValue e initial.1 value final.1 events flow ∧ final.2 = initial.2 ++ events
  bindIterator var value state := (kernel.bindIterator var value state.1, state.2)
  restore locals initial final := (kernel.restore locals initial.1 final.1, final.2)

def matrixModel {n : Nat} {Store : Type} (kernel : EventKernel n Store) :
    Model (Store × Operator n) where
  operation op initial final flow := ∃ events,
    kernel.operation op initial.1 final.1 events flow ∧ final.2 = eventMatrix events * initial.2
  condition e initial value final := ∃ events,
    kernel.condition e initial.1 value final.1 events ∧ final.2 = eventMatrix events * initial.2
  domain d initial values final := ∃ events,
    kernel.domain d initial.1 values final.1 events ∧ final.2 = eventMatrix events * initial.2
  switchCase e cases other initial selected final := ∃ events,
    kernel.switchCase e cases other initial.1 selected final.1 events ∧
      final.2 = eventMatrix events * initial.2
  returnValue e initial value final flow := ∃ events,
    kernel.returnValue e initial.1 value final.1 events flow ∧ final.2 = eventMatrix events * initial.2
  bindIterator var value state := (kernel.bindIterator var value state.1, state.2)
  restore locals initial final := (kernel.restore locals initial.1 final.1, final.2)

def interpretTrace {n : Nat} {Store : Type} (state : Store × GateEvents n) : Store × Operator n :=
  (state.1, eventMatrix state.2)

```

## Atomic preservation and lifting

All seven kernel obligations are discharged for these models. In particular, quantum
action survives restoration, and events emitted during expression evaluation are retained.

```lean
theorem traceKernelMap {n : Nat} {Store : Type} (kernel : EventKernel n Store) :
    KernelMap (traceModel kernel) (matrixModel kernel) interpretTrace := by
  constructor
  · intro op initial final flow h
    obtain ⟨events, hk, he⟩ := h
    exact ⟨events, hk, by simp only [interpretTrace, he, eventMatrix_append]⟩
  · intro e initial value final h
    obtain ⟨events, hk, he⟩ := h
    exact ⟨events, hk, by simp only [interpretTrace, he, eventMatrix_append]⟩
  · intro d initial values final h
    obtain ⟨events, hk, he⟩ := h
    exact ⟨events, hk, by simp only [interpretTrace, he, eventMatrix_append]⟩
  · intro e cases other initial selected final h
    obtain ⟨events, hk, he⟩ := h
    exact ⟨events, hk, by simp only [interpretTrace, he, eventMatrix_append]⟩
  · intro e initial value final flow h
    obtain ⟨events, hk, he⟩ := h
    exact ⟨events, hk, by simp only [interpretTrace, he, eventMatrix_append]⟩
  · intros; rfl
  · intros; rfl

theorem trace_proc_refinement {n : Nat} {Store : Type} (kernel : EventKernel n Store)
    {proc : Proc} {initial final : Store × GateEvents n} {flow : Flow}
    (execution : Exec (traceModel kernel) proc initial final flow) :
    Exec (matrixModel kernel) proc (interpretTrace initial) (interpretTrace final) flow :=
  proc_simulation (traceKernelMap kernel) execution


theorem traceKernelLift {n : Nat} {Store : Type} (kernel : EventKernel n Store) :
    KernelLift (traceModel kernel) (matrixModel kernel) interpretTrace := by
  constructor
  · intro op initial final flow h
    obtain ⟨events, hk, he⟩ := h
    refine ⟨(final.1, initial.2 ++ events), ⟨events, hk, rfl⟩, ?_⟩
    apply Prod.ext
    · rfl
    · exact (eventMatrix_append _ _).trans he.symm
  · intro e initial value final h
    obtain ⟨events, hk, he⟩ := h
    refine ⟨(final.1, initial.2 ++ events), ⟨events, hk, rfl⟩, ?_⟩
    apply Prod.ext
    · rfl
    · exact (eventMatrix_append _ _).trans he.symm
  · intro d initial values final h
    obtain ⟨events, hk, he⟩ := h
    refine ⟨(final.1, initial.2 ++ events), ⟨events, hk, rfl⟩, ?_⟩
    apply Prod.ext
    · rfl
    · exact (eventMatrix_append _ _).trans he.symm
  · intro e cases other initial selected final h
    obtain ⟨events, hk, he⟩ := h
    refine ⟨(final.1, initial.2 ++ events), ⟨events, hk, rfl⟩, ?_⟩
    apply Prod.ext
    · rfl
    · exact (eventMatrix_append _ _).trans he.symm
  · intro e initial value final flow h
    obtain ⟨events, hk, he⟩ := h
    refine ⟨(final.1, initial.2 ++ events), ⟨events, hk, rfl⟩, ?_⟩
    apply Prod.ext
    · rfl
    · exact (eventMatrix_append _ _).trans he.symm
  · intros; rfl
  · intros; rfl

```

## Whole-program finite-behavior equivalence

The reverse implication lifts a matrix execution from any chosen initial trace. It
preserves the final classical store, completion, and quantum action. It does not claim
termination or rule out faults of an interpreter that has not been connected to the kernel.

```lean
/-- Full finite-behavior equivalence, without assuming a program-level simulation. -/
theorem trace_proc_refinement_iff {n : Nat} {Store : Type} (kernel : EventKernel n Store)
    (proc : Proc) (initial : Store × GateEvents n) (final : Store × Operator n) (flow : Flow) :
    Exec (matrixModel kernel) proc (interpretTrace initial) final flow ↔
      ∃ traceFinal, Exec (traceModel kernel) proc initial traceFinal flow ∧
        interpretTrace traceFinal = final := by
  constructor
  · intro execution
    exact proc_lifting (traceKernelLift kernel) execution initial rfl
  · rintro ⟨traceFinal, execution, rfl⟩
    exact trace_proc_refinement kernel execution

end QASMVerification
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
