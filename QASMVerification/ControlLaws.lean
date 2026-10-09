    import LiterateLean
    import QASM.Execution.VerifiedControl
    open scoped LiterateLean

# Refinement of the fixed-point Proc evaluator

The evaluator and declarative model use the same atomic state-transition kernel.
The proofs quantify over every Proc, every initial store, and every completion. They
use the evaluator's proved fixed-point equations, not an assumed program simulation.
MachineLaws connects the shared frame machine to this model. RuntimeLaws instantiates
that connection with actual Option interpreter callbacks and the public execution boundary.

```lean
namespace QASMVerification
open QASM.IR
open QASM.Execution.Semantics (Flow)
open QASM.Execution.EffectSemantics
open QASM.Execution.VerifiedControl

theorem control_complete (kernel : Kernel State) {proc : Proc} {initial final : State} {flow : Flow}
    (h : Exec (model kernel) proc initial final flow) : eval kernel proc initial = some (final, flow) := by
  induction h using Exec.rec
    (motive_2 := fun steps initial final flow _ => evalSequence kernel steps initial = some (final, flow))
    (motive_3 := fun iterator body values initial final flow _ =>
      evalFor kernel iterator body values initial = some (final, flow))
  all_goals intros
  all_goals try simp only [model] at *
  all_goals try rw [eval.eq_def]
  all_goals try rw [evalSequence.eq_def]
  all_goals try rw [evalFor.eq_def]
  all_goals try simp_all
  all_goals try simp_all
  case whileNext e s middle body afterBody bodyFlow final flow hc h hf hr ih ihr =>
    rcases hf with hf | hf <;> simp_all
  case next body iterator value initial middle bodyFlow rest final flow head hf tail ih iht =>
    rcases hf with hf | hf <;> simp_all


```

## Soundness by fixed-point induction

Successful results of every approximation have declarative derivations. The simultaneous
fixed-point induction preserves this property across all Proc constructors and both loop
helpers. No recursion fuel or assumed whole-program simulation appears in the theorem.

```lean
theorem control_sound (kernel : Kernel State) {proc : Proc} {initial final : State} {flow : Flow}
    (result : eval kernel proc initial = some (final, flow)) :
    Exec (model kernel) proc initial final flow := by
  have all := eval.mutual_partial_correctness kernel
    (fun proc initial result => Exec (model kernel) proc initial result.1 result.2)
    (fun iterator body values initial result => ExecFor (model kernel) iterator body values initial result.1 result.2)
    (fun steps initial result => ExecSequence (model kernel) steps initial result.1 result.2)
    (by
      intro evalApprox forApprox seqApprox ihEval ihFor ihSeq proc initial result h
      rcases result with ⟨final, flow⟩
      cases proc <;> simp only [bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
      case skip => cases h; exact .skip _
      case operation op =>
        rcases h with ⟨⟨middle, completion⟩, atom, h⟩
        cases completion <;> simp only [Option.some.injEq, reduceCtorEq] at h
        · cases h; exact .operation atom
        · cases h; exact .operationEnd atom
      case sequence steps => exact .sequence (ihSeq _ _ _ h)
      case scope locals body =>
        rcases h with ⟨⟨middle, completion⟩, head, h⟩
        cases h; exact .scope (ihEval _ _ _ head)
      case branch e yes no =>
        rcases h with ⟨⟨middle, value⟩, atom, h⟩
        cases value with
        | none => simp only [Option.some.injEq] at h; cases h; exact .conditionEnd atom
        | some value =>
          cases value
          · exact .branchFalse atom (ihEval _ _ _ h)
          · exact .branchTrue atom (ihEval _ _ _ h)
      case switch e cases other =>
        rcases h with ⟨⟨middle, selected⟩, atom, h⟩
        cases selected with
        | none => simp only [Option.some.injEq] at h; cases h; exact .switchEnd atom
        | some selected => exact .switch atom (ihEval _ _ _ h)
      case forLoop iterator domain body =>
        rcases h with ⟨⟨middle, values⟩, atom, h⟩
        cases values with
        | none =>
          simp only [Option.bind_some, Option.some.injEq] at h
          cases h; exact .domainEnd atom
        | some values =>
          rcases Option.bind_eq_some_iff.mp h with ⟨⟨afterLoop, completion⟩, head, h⟩
          simp only [Option.some.injEq] at h
          cases h; exact .forLoop atom (ihFor _ _ _ _ _ head)
      case whileLoop e body =>
        rcases h with ⟨⟨middle, value⟩, atom, h⟩
        cases value with
        | none => simp only [Option.some.injEq] at h; cases h; exact .whileConditionEnd atom
        | some value =>
          cases value with
          | false => simp only [Option.some.injEq] at h; cases h; exact .whileFalse atom
          | true =>
            rcases Option.bind_eq_some_iff.mp h with ⟨⟨afterBody, completion⟩, head, h⟩
            have bodyExec := ihEval _ _ _ head
            cases completion <;> simp only [Option.some.injEq] at h
            · exact .whileNext atom bodyExec (Or.inl rfl) (ihEval _ _ _ h)
            · cases h; exact .whileBreak atom bodyExec
            · exact .whileNext atom bodyExec (Or.inr rfl) (ihEval _ _ _ h)
            · cases h; exact .whileExit atom bodyExec (by simp)
            · cases h; exact .whileExit atom bodyExec (by simp)
      case breakLoop => cases h; exact .breakLoop _
      case continueLoop => cases h; exact .continueLoop _
      case returnValue e =>
        rcases h with ⟨⟨middle, value, ended⟩, atom, h⟩
        cases ended <;> simp only [Bool.false_eq_true, ↓reduceIte] at h
        · cases h; exact .returnValue ⟨false, atom, rfl⟩
        · cases h; exact .returnEnd ⟨true, atom, rfl⟩
      case endProgram => cases h; exact .endProgram _)
    (by
      intro evalApprox forApprox ihEval ihFor iterator body values initial result h
      rcases result with ⟨final, flow⟩
      cases values <;> simp only [bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
      case nil => cases h; exact .nil _
      case cons value rest =>
        rcases h with ⟨⟨middle, completion⟩, head, h⟩
        have bodyExec := ihEval _ _ _ head
        cases completion <;> simp only [Option.some.injEq] at h
        · exact .next bodyExec (Or.inl rfl) (ihFor _ _ _ _ _ h)
        · cases h; exact .breakLoop bodyExec
        · exact .next bodyExec (Or.inr rfl) (ihFor _ _ _ _ _ h)
        · cases h; exact .exit bodyExec (by simp)
        · cases h; exact .exit bodyExec (by simp))
    (by
      intro evalApprox seqApprox ihEval ihSeq steps initial result h
      rcases result with ⟨final, flow⟩
      cases steps <;> simp only [bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
      case nil => cases h; exact .nil _
      case cons head rest =>
        rcases h with ⟨⟨middle, completion⟩, head, h⟩
        have headExec := ihEval _ _ _ head
        cases completion <;> simp only [Option.some.injEq] at h
        · exact .next headExec (ihSeq _ _ _ h)
        all_goals cases h; exact .exit headExec (by simp))
  exact all.1 proc initial (final, flow) result


theorem control_refinement_iff (kernel : Kernel State) (proc : Proc)
    (initial final : State) (flow : Flow) :
    eval kernel proc initial = some (final, flow) ↔ Exec (model kernel) proc initial final flow :=
  ⟨control_sound kernel, control_complete kernel⟩

end QASMVerification
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
