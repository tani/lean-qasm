    import LiterateLean
    import QASM.Execution.Interpreter
    import QASMVerification.MachineLaws
    open scoped LiterateLean

# Concrete interpreter refinement

The atomic model here is the graph of the actual interpreter callbacks. No whole-program
simulation is assumed. The shared fixed-point machine implements every Proc constructor,
and the public execution boundary preserves exactly its successful finite results.

The bidirectional theorem specializes backend effects to Option. Other backend monads
execute the same transition function; their external-effect and termination models need
separate laws. This contract does not replace finite floating-point gate arguments with
ideal real numbers or assert fault freedom for arbitrary programs.

```lean
namespace QASMVerification
open QASM.IR
open QASM.Execution
open QASM.Execution.EffectSemantics

private theorem atomicKernel_normal
    (operation : Op → ExecM Option qubit error Unit)
    (expression : Expr → ExecM Option qubit error QASM.Value)
    (domain : IterationDomain → ExecM Option qubit error (Array QASM.Value))
    (select : Expr → Array SwitchCase → Option Proc → ExecM Option qubit error Proc) :
    Machine.OperationsNormal (kernelOfAtomic operation expression domain select) := by
  intro op initial final flow h
  simp only [kernelOfAtomic, bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  rcases h with ⟨⟨state, result⟩, _, h⟩
  cases result with
  | error error => simp [Except.map] at h
  | ok value =>
    cases value <;> simp [Except.map] at h
    all_goals rcases h with ⟨_, h⟩; subst flow; simp

theorem runtimeKernel_normal [QASM.QuantumBackend Option qubit error] (program : Program) :
    Machine.OperationsNormal (runtimeKernel (m := Option) (qubit := qubit) (backendError := error) program) :=
  atomicKernel_normal _ _ _ _

def runtimeModel [QASM.QuantumBackend Option qubit error] (program : Program) :
    QASM.Execution.EffectSemantics.Model (ExecutionState qubit) :=
  QASM.Execution.VerifiedControl.model (Machine.project (runtimeKernel (m := Option)
    (qubit := qubit) (backendError := error) program))

theorem runFrom_refinement_iff [QASM.QuantumBackend Option qubit error]
    (program : Program) (proc : Proc) (initial final : ExecutionState qubit) (flow : Flow) :
    runFrom (m := Option) (backendError := error) program proc initial = some (final, .ok flow) ↔
      Exec (runtimeModel (error := error) program) proc initial final flow :=
  Machine.machine_proc_refinement_iff _ (runtimeKernel_normal program) proc initial final flow


theorem run_refinement_iff [QASM.QuantumBackend Option qubit error]
    (program : Program) (inputs : Array (VarId × QASM.Value)) (values : Std.HashMap VarId QASM.Value) :
    QASM.Execution.run (m := Option) (qubit := qubit) (backendError := error) program inputs = some (.ok values) ↔
      ∃ final flow, Exec (runtimeModel (error := error) program) program.body
        (initialState (qubit := qubit) program inputs) final flow ∧ final.values = values := by
  constructor
  · intro h
    simp only [QASM.Execution.run, bind, Option.bind_eq_some_iff, Option.pure_def] at h
    rcases h with ⟨⟨final, outcome⟩, run, h⟩
    cases outcome with
    | error error => simp at h
    | ok flow =>
      simp only [Option.some.injEq, Except.ok.injEq] at h
      exact ⟨final, flow, (runFrom_refinement_iff program program.body _ _ _).mp run, h⟩
  · rintro ⟨final, flow, h, values⟩
    have run := (runFrom_refinement_iff program program.body _ _ _).mpr h
    simp only [QASM.Execution.run, run, bind, Option.bind_some, Option.pure_def, values]


end QASMVerification
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
