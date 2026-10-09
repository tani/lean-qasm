    import LiterateLean
    import QASMVerification.Program
    open scoped LiterateLean

# Refinement through every structured Proc constructor

A state map must preserve atomic effects and commute with iterator binding and scope
restoration. The simulation below lifts these seven local obligations through the entire
completion-aware Proc semantics. It includes effects from conditions, domains, switch
selection, and return expressions, as well as break, continue, return, and whole-program
termination. The obligations concern the kernel; they do not assume a Proc simulation.

This is a compositional theorem about finite derivations. Instantiating it for the private
partial interpreter requires separate kernel and evaluator correspondence proofs.

```lean
namespace QASMVerification
open QASM.IR
open QASM.Execution.Semantics (Flow)
open QASM.Execution.EffectSemantics

structure KernelMap {S T : Type} (source : Model S) (target : Model T) (map : S → T) : Prop where
  operation : ∀ op s t flow, source.operation op s t flow → target.operation op (map s) (map t) flow
  condition : ∀ e s value t, source.condition e s value t → target.condition e (map s) value (map t)
  domain : ∀ d s values t, source.domain d s values t → target.domain d (map s) values (map t)
  switchCase : ∀ e cases other s selected t, source.switchCase e cases other s selected t →
    target.switchCase e cases other (map s) selected (map t)
  returnValue : ∀ e s value t flow, source.returnValue e s value t flow →
    target.returnValue e (map s) value (map t) flow
  bindIterator : ∀ var value s, map (source.bindIterator var value s) = target.bindIterator var value (map s)
  restore : ∀ locals s t, map (source.restore locals s t) = target.restore locals (map s) (map t)

theorem proc_simulation {S T : Type} {source : Model S} {target : Model T} {map : S → T}
    (laws : KernelMap source target map) {proc : Proc} {initial final : S} {flow : Flow}
    (execution : Exec source proc initial final flow) :
    Exec target proc (map initial) (map final) flow := by
  induction execution using Exec.rec
    (motive_2 := fun procs initial final flow _ => ExecSequence target procs (map initial) (map final) flow)
    (motive_3 := fun iterator body values initial final flow _ =>
      ExecFor target iterator body values (map initial) (map final) flow)
  all_goals intros
  all_goals try simp only [laws.restore, laws.bindIterator] at *
  all_goals first
    | exact ExecFor.exit ‹_› ‹_›
    | try solve_by_elim (maxDepth := 5) [
    laws.operation, laws.condition, laws.domain, laws.switchCase, laws.returnValue,
    Exec.skip, Exec.operation, Exec.operationEnd, Exec.sequence, Exec.scope,
    Exec.branchTrue, Exec.branchFalse, Exec.switch, Exec.forLoop, Exec.whileFalse,
    Exec.whileBreak, Exec.whileNext, Exec.whileExit, Exec.conditionEnd,
    Exec.whileConditionEnd, Exec.domainEnd, Exec.switchEnd, Exec.breakLoop,
    Exec.continueLoop, Exec.returnValue, Exec.returnEnd, Exec.endProgram,
    ExecSequence.nil, ExecSequence.next, ExecSequence.exit,
    ExecFor.nil, ExecFor.next, ExecFor.breakLoop, ExecFor.exit]

  case whileNext => exact .whileNext (laws.condition _ _ _ _ ‹_›) ‹_› ‹_› ‹_›
  case whileExit => exact .whileExit (laws.condition _ _ _ _ ‹_›) ‹_› ‹_›


```

## Lifting a matrix-side derivation

Completeness needs more than forward preservation: every target atomic outcome must
have a source witness from the chosen source state. The theorem lifts an entire finite
derivation from those atomic witnesses. Restore and iterator operations commute with
the state map; no inverse or injectivity of that map is required.

```lean
structure KernelLift {S T : Type} (source : Model S) (target : Model T) (map : S → T) : Prop where
  operation : ∀ op s t flow, target.operation op (map s) t flow →
    ∃ s', source.operation op s s' flow ∧ map s' = t
  condition : ∀ e s value t, target.condition e (map s) value t →
    ∃ s', source.condition e s value s' ∧ map s' = t
  domain : ∀ d s values t, target.domain d (map s) values t →
    ∃ s', source.domain d s values s' ∧ map s' = t
  switchCase : ∀ e cases other s selected t, target.switchCase e cases other (map s) selected t →
    ∃ s', source.switchCase e cases other s selected s' ∧ map s' = t
  returnValue : ∀ e s value t flow, target.returnValue e (map s) value t flow →
    ∃ s', source.returnValue e s value s' flow ∧ map s' = t
  bindIterator : ∀ var value s, map (source.bindIterator var value s) = target.bindIterator var value (map s)
  restore : ∀ locals s t, map (source.restore locals s t) = target.restore locals (map s) (map t)

theorem proc_lifting {S T : Type} {source : Model S} {target : Model T} {map : S → T}
    (laws : KernelLift source target map) {proc : Proc} {initial final : T} {flow : Flow}
    (execution : Exec target proc initial final flow) :
    ∀ sourceInitial, map sourceInitial = initial →
      ∃ sourceFinal, Exec source proc sourceInitial sourceFinal flow ∧ map sourceFinal = final := by
  induction execution using Exec.rec
    (motive_2 := fun procs initial final flow _ => ∀ sourceInitial, map sourceInitial = initial →
      ∃ sourceFinal, ExecSequence source procs sourceInitial sourceFinal flow ∧ map sourceFinal = final)
    (motive_3 := fun iterator body values initial final flow _ =>
      ∀ sourceInitial, map sourceInitial = initial →
      ∃ sourceFinal, ExecFor source iterator body values sourceInitial sourceFinal flow ∧ map sourceFinal = final)
  case skip s => intro s' hs; exact ⟨s', .skip _, hs⟩
  case operation h =>
    intro s hs
    rw [← hs] at h
    obtain ⟨t, ht, he⟩ := laws.operation _ _ _ _ h
    exact ⟨t, .operation ht, he⟩
  case operationEnd h =>
    intro s hs
    rw [← hs] at h
    obtain ⟨t, ht, he⟩ := laws.operation _ _ _ _ h
    exact ⟨t, .operationEnd ht, he⟩
  case sequence h ih =>
    intro s hs
    obtain ⟨t, ht, he⟩ := ih s hs
    exact ⟨t, .sequence ht, he⟩
  case scope locals h ih =>
    intro s hs
    obtain ⟨t, ht, he⟩ := ih s hs
    exact ⟨source.restore locals s t, .scope ht, by rw [laws.restore, hs, he]⟩
  case branchTrue hc h ih =>
    intro s hs
    rw [← hs] at hc
    obtain ⟨m, hm, hem⟩ := laws.condition _ _ _ _ hc
    obtain ⟨t, ht, he⟩ := ih m hem
    exact ⟨t, .branchTrue hm ht, he⟩
  case branchFalse hc h ih =>
    intro s hs
    rw [← hs] at hc
    obtain ⟨m, hm, hem⟩ := laws.condition _ _ _ _ hc
    obtain ⟨t, ht, he⟩ := ih m hem
    exact ⟨t, .branchFalse hm ht, he⟩
  case switch hs h ih =>
    intro s heq
    rw [← heq] at hs
    obtain ⟨m, hm, hem⟩ := laws.switchCase _ _ _ _ _ _ hs
    obtain ⟨t, ht, he⟩ := ih m hem
    exact ⟨t, .switch hm ht, he⟩
  case forLoop iterator body final flow hd h ih =>
    intro s hs
    rw [← hs] at hd
    obtain ⟨m, hm, hem⟩ := laws.domain _ _ _ _ hd
    obtain ⟨t, ht, he⟩ := ih m hem
    exact ⟨source.restore #[iterator] s t, .forLoop hm ht, by rw [laws.restore, hs, he]⟩
  case whileFalse hc =>
    intro s hs
    rw [← hs] at hc
    obtain ⟨t, ht, he⟩ := laws.condition _ _ _ _ hc
    exact ⟨t, .whileFalse ht, he⟩
  case whileBreak hc h ih =>
    intro s hs
    rw [← hs] at hc
    obtain ⟨m, hm, hem⟩ := laws.condition _ _ _ _ hc
    obtain ⟨t, ht, he⟩ := ih m hem
    exact ⟨t, .whileBreak hm ht, he⟩
  case whileNext hc h hf hr ih ihr =>
    intro s hs
    rw [← hs] at hc
    obtain ⟨m, hm, hem⟩ := laws.condition _ _ _ _ hc
    obtain ⟨b, hb, heb⟩ := ih m hem
    obtain ⟨t, ht, he⟩ := ihr b heb
    exact ⟨t, .whileNext hm hb hf ht, he⟩
  case whileExit hc h hf ih =>
    intro s hs
    rw [← hs] at hc
    obtain ⟨m, hm, hem⟩ := laws.condition _ _ _ _ hc
    obtain ⟨t, ht, he⟩ := ih m hem
    exact ⟨t, .whileExit hm ht hf, he⟩
  case conditionEnd h =>
    intro s hs
    rw [← hs] at h
    obtain ⟨t, ht, he⟩ := laws.condition _ _ _ _ h
    exact ⟨t, .conditionEnd ht, he⟩
  case whileConditionEnd h =>
    intro s hs
    rw [← hs] at h
    obtain ⟨t, ht, he⟩ := laws.condition _ _ _ _ h
    exact ⟨t, .whileConditionEnd ht, he⟩
  case domainEnd iterator body h =>
    intro s hs
    rw [← hs] at h
    obtain ⟨t, ht, he⟩ := laws.domain _ _ _ _ h
    exact ⟨source.restore #[iterator] s t, .domainEnd ht, by rw [laws.restore, hs, he]⟩
  case switchEnd h =>
    intro s hs
    rw [← hs] at h
    obtain ⟨t, ht, he⟩ := laws.switchCase _ _ _ _ _ _ h
    exact ⟨t, .switchEnd ht, he⟩
  case breakLoop state => intro s hs; exact ⟨s, .breakLoop _, hs⟩
  case continueLoop state => intro s hs; exact ⟨s, .continueLoop _, hs⟩
  case returnValue h =>
    intro s hs
    rw [← hs] at h
    obtain ⟨t, ht, he⟩ := laws.returnValue _ _ _ _ _ h
    exact ⟨t, .returnValue ht, he⟩
  case returnEnd h =>
    intro s hs
    rw [← hs] at h
    obtain ⟨t, ht, he⟩ := laws.returnValue _ _ _ _ _ h
    exact ⟨t, .returnEnd ht, he⟩
  case endProgram state => intro s hs; exact ⟨s, .endProgram _, hs⟩
  case nil => rename_i s hs; exact ⟨s, .nil _, hs⟩
  case next =>
    rename_i ih iht s hs
    obtain ⟨m, hm, hem⟩ := ih s hs
    obtain ⟨t, ht, he⟩ := iht m hem
    exact ⟨t, .next hm ht, he⟩
  case exit =>
    rename_i ih s hs
    obtain ⟨t, ht, he⟩ := ih s hs
    exact ⟨t, .exit ht ‹_›, he⟩
  case nil => intro s hs; exact ⟨s, .nil _, hs⟩
  case next =>
    intro ih iht s hs
    obtain ⟨m, hm, hem⟩ := ih (source.bindIterator _ _ s) (by rw [laws.bindIterator, hs])
    obtain ⟨t, ht, he⟩ := iht m hem
    exact ⟨t, .next hm ‹_› ht, he⟩
  case breakLoop =>
    intros iterator value initial final rest head ih s hs
    obtain ⟨t, ht, he⟩ := ih (source.bindIterator iterator value s) (by rw [laws.bindIterator, hs])
    exact ⟨t, .breakLoop ht, he⟩
  case exit =>
    intro s hs
    obtain ⟨t, ht, he⟩ := (by assumption : ∀ sourceInitial, map sourceInitial = target.bindIterator _ _ _ → _) (source.bindIterator _ _ s) (by rw [laws.bindIterator, hs])
    exact ⟨t, .exit ht ‹_›, he⟩

end QASMVerification
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
