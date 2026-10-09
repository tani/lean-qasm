    import LiterateLean
    import QASM.Execution.ControlMachine
    import QASMVerification.Refinement.Control
    open scoped LiterateLean

# Refinement of the shared control machine

The same finite transition function drives the backend interpreter and its deterministic
Option specialization. Pending frames are interpreted as continuations of the declarative
semantics. The theorem allows failing atomic callbacks and proves both directions for
every successful finite result. Atomic operations may only complete normally or end
the program; Refinement.Runtime discharges this restriction for the actual interpreter.

```lean
namespace QASMVerification
open QASM.IR
open QASM.Execution.Semantics (Flow)
open QASM.Execution.EffectSemantics
namespace Machine
open QASM.Execution.ControlMachine

variable {Error State : Type} [Nonempty State]

def embed (k : QASM.Execution.VerifiedControl.Kernel State) : Kernel Option State Empty where
  operation op state := do
    let (final, flow) ← k.operation op state
    match flow with
    | .next | .ended => some (final, .ok flow)
    | _ => none
  condition e s := (k.condition e s).map (fun (s, v) => (s, .ok v))
  domain d s := (k.domain d s).map (fun (s, v) => (s, .ok v))
  switchCase e cases other s := (k.switchCase e cases other s).map (fun (s, v) => (s, .ok v))
  returnValue e s := (k.returnValue e s).map (fun (s, v, ended) => (s, .ok (v, ended)))
  bindIterator := k.bindIterator
  restore := k.restore

def erase (result : Option (State × Except Error α)) : Option (State × α) := do
  let (final, value) ← result
  match value with
  | .error _ => none
  | .ok value => some (final, value)

omit [Nonempty State] in
@[simp] theorem erase_some (result : Option (State × Except Error α)) (state : State) (value : α) :
    erase result = some (state, value) ↔ result = some (state, .ok value) := by
  cases result with
  | none => simp [erase]
  | some result =>
    rcases result with ⟨final, result⟩
    cases result <;> simp [erase, Prod.mk.injEq]

def project (raw : Kernel Option State Error) : QASM.Execution.VerifiedControl.Kernel State where
  operation op s := erase (raw.operation op s)
  condition e s := erase (raw.condition e s)
  domain d s := erase (raw.domain d s)
  switchCase e cases other s := erase (raw.switchCase e cases other s)
  returnValue e s := erase (raw.returnValue e s)
  bindIterator := raw.bindIterator
  restore := raw.restore

def OperationsNormal (raw : Kernel Option State Error) : Prop :=
  ∀ op initial final flow, raw.operation op initial = some (final, .ok flow) →
    flow = .next ∨ flow = .ended

```

## Frame interpretation

A pending frame restores a saved scope, executes a sequence suffix, resumes a finite
for-loop, or retests a while-loop. Successful completion is propagated without losing
whole-program termination; an error has no successful denotation.

```lean
private def finish (raw : Kernel Option State Error) :
    List (Frame State) → State → Flow → Option (State × Flow)
  | [], state, flow => some (state, flow)
  | .restore locals saved :: rest, state, flow => finish raw rest ((project raw).restore locals saved state) flow
  | .sequence steps :: rest, state, flow => do
    match flow with
    | .next =>
      let (final, result) ← QASM.Execution.VerifiedControl.evalSequence (project raw) steps state
      finish raw rest final result
    | _ => finish raw rest state flow
  | .forLoop iterator body values :: rest, state, flow => do
    match flow with
    | .next | .continueLoop =>
      let (final, result) ← QASM.Execution.VerifiedControl.evalFor (project raw) iterator body values state
      finish raw rest final result
    | .breakLoop => finish raw rest state .next
    | _ => finish raw rest state flow
  | .whileLoop e body :: rest, state, flow => do
    match flow with
    | .next | .continueLoop =>
      let (final, result) ← QASM.Execution.VerifiedControl.eval (project raw) (.whileLoop e body) state
      finish raw rest final result
    | .breakLoop => finish raw rest state .next
    | _ => finish raw rest state flow

private def meaning (raw : Kernel Option State Error)
    (task : QASM.Execution.ControlMachine.Task Error) (stack : List (Frame State)) (initial : State) : Option (State × Flow) := do
  match task with
  | .proc proc =>
    let (final, flow) ← QASM.Execution.VerifiedControl.eval (project raw) proc initial
    finish raw stack final flow
  | .resume (.ok flow) => finish raw stack initial flow
  | .resume (.error _) => none

private def stepMeaning (raw : Kernel Option State Error) :
    Step State Error → Option (State × Flow)
  | .done final (.ok flow) => some (final, flow)
  | .done _ (.error _) => none
  | .more task stack initial => meaning raw task stack initial

```

## Preservation by each transition

One machine transition preserves this continuation meaning. The proof handles both
callback failure and successful expression evaluation; it uses fixed-point equations
only for the outermost structured process.

```lean
omit [Nonempty State] in
private theorem sequence_step (raw : Kernel Option State Error)
    (steps : List Proc) (stack : List (Frame State)) (initial : State) :
    (QASM.Execution.VerifiedControl.evalSequence (project raw) steps initial).bind
      (fun (s, flow) => finish raw stack s flow) =
    (match steps with
      | [] => some (Step.more (.resume (.ok .next)) stack initial)
      | head :: rest => some (Step.more (.proc head) (.sequence rest :: stack) initial)).bind (stepMeaning raw) := by
  rw [QASM.Execution.VerifiedControl.evalSequence.eq_def]
  cases steps with
  | nil => rfl
  | cons head tail =>
    simp only [bind, Option.bind_assoc, Option.bind_some, stepMeaning, meaning, Option.pure_def]
    congr 1
    funext ⟨state, flow⟩
    cases flow <;> rfl

omit [Nonempty State] in
private theorem for_step (raw : Kernel Option State Error)
    (iterator : Var) (body : Proc) (values : List QASM.Value)
    (stack : List (Frame State)) (initial : State) :
    (QASM.Execution.VerifiedControl.evalFor (project raw) iterator body values initial).bind
      (fun (s, flow) => finish raw stack s flow) =
    (match values with
      | [] => some (Step.more (.resume (.ok .next)) stack initial)
      | value :: rest => some (Step.more (.proc body) (.forLoop iterator body rest :: stack)
          ((project raw).bindIterator iterator value initial))).bind (stepMeaning raw) := by
  rw [QASM.Execution.VerifiedControl.evalFor.eq_def]
  cases values with
  | nil => rfl
  | cons value rest =>
    simp only [bind, Option.bind_assoc, Option.bind_some, stepMeaning, meaning, Option.pure_def]
    congr 1
    funext ⟨state, flow⟩
    cases flow <;> rfl

omit [Nonempty State] in
private theorem step_meaning (raw : Kernel Option State Error) (normal : OperationsNormal raw)
    (task : QASM.Execution.ControlMachine.Task Error) (stack : List (Frame State)) (initial : State) :
    meaning raw task stack initial = (step raw task stack initial).bind (stepMeaning raw) := by
  cases task with
  | proc proc =>
    cases proc <;>
      simp only [meaning, step, bind, Option.pure_def, Option.bind_some, Option.bind_assoc, stepMeaning]
    all_goals rw [QASM.Execution.VerifiedControl.eval.eq_def]
    all_goals try simp only [bind, Option.pure_def, Option.bind_some, Option.bind_assoc, finish]
    all_goals try rfl
    case operation op =>
      cases atom : raw.operation op initial with
      | none => simp [project, erase, atom]
      | some result =>
        rcases result with ⟨state, result⟩
        cases result with
        | error error => simp [project, erase, atom]
        | ok flow =>
          have hf := normal op initial state flow atom
          cases flow <;> simp_all [project, erase]
    case sequence steps => exact sequence_step raw _ stack initial
    case branch e yes no =>
      cases atom : raw.condition e initial with
      | none => simp [project, erase, atom]
      | some result =>
        rcases result with ⟨state, result⟩
        cases result with
        | error error => simp [project, erase, atom, stepMeaning, meaning]
        | ok value => cases value with
          | none => simp [project, erase, atom, stepMeaning, meaning]
          | some value => cases value <;> simp [project, erase, atom, stepMeaning, meaning]
    case switch e cases other =>
      cases atom : raw.switchCase e cases other initial with
      | none => simp [project, erase, atom]
      | some result =>
        rcases result with ⟨state, result⟩
        cases result with
        | error error => simp [project, erase, atom, stepMeaning, meaning]
        | ok value => cases value <;> simp [project, erase, atom, stepMeaning, meaning]
    case forLoop iterator domain body =>
      cases atom : raw.domain domain initial with
      | none => simp [project, erase, atom]
      | some result =>
        rcases result with ⟨state, result⟩
        cases result with
        | error error => simp [project, erase, atom, stepMeaning, meaning]
        | ok values => cases values with
          | none => simp [project, erase, atom, stepMeaning, meaning, finish]
          | some values =>
            simp only [project, erase, atom, Option.bind_some, bind, Option.bind_assoc]
            cases values with
            | nil => exact for_step raw iterator body [] (.restore #[iterator] initial :: stack) state
            | cons value rest => exact for_step raw iterator body (value :: rest) (.restore #[iterator] initial :: stack) state
    case whileLoop e body =>
      cases atom : raw.condition e initial with
      | none => simp [project, erase, atom]
      | some result =>
        rcases result with ⟨state, result⟩
        cases result with
        | error error => simp [project, erase, atom, stepMeaning, meaning]
        | ok value => cases value with
          | none => simp [project, erase, atom, stepMeaning, meaning]
          | some value => cases value with
            | false => simp [project, erase, atom, stepMeaning, meaning]
            | true =>
              simp only [project, erase, atom, Option.bind_some, bind, Option.bind_assoc, meaning, stepMeaning]
              congr 1
              funext ⟨afterBody, flow⟩
              cases flow <;> rfl
    case returnValue e =>
      cases atom : raw.returnValue e initial with
      | none => simp [project, erase, atom]
      | some result =>
        rcases result with ⟨state, result⟩
        cases result with
        | error error => simp [project, erase, atom, stepMeaning, meaning]
        | ok value => simp [project, erase, atom, stepMeaning, meaning]
  | resume result =>
    cases result with
    | error error =>
      cases stack with
      | nil => rfl
      | cons frame rest => cases frame <;> rfl
    | ok flow =>
      cases stack with
      | nil => rfl
      | cons frame rest =>
        cases frame <;> cases flow <;> simp only [meaning, step, finish, bind, Option.pure_def,
          Option.bind_some, stepMeaning]
        all_goals try rfl
        case sequence.next steps => exact sequence_step raw steps rest initial
        case forLoop.next iterator body values => exact for_step raw iterator body values rest initial
        case forLoop.continueLoop iterator body values => exact for_step raw iterator body values rest initial


```

## Fixed-point soundness

The successful-result predicate is admissible in the Option order. Fixed-point induction
therefore proves soundness for arbitrary pending frames, rather than assuming termination.

```lean
private theorem drive_sound (raw : Kernel Option State Error) (normal : OperationsNormal raw) :
    ∀ task stack initial final flow,
      drive raw task stack initial = some (final, .ok flow) →
      meaning raw task stack initial = some (final, flow) := by
  apply drive.fixpoint_induct raw
    (fun approximate => ∀ task stack initial final flow,
      approximate task stack initial = some (final, .ok flow) →
      meaning raw task stack initial = some (final, flow))
  · exact Lean.Order.admissible_pi_apply _ (fun task =>
      Lean.Order.admissible_pi_apply _ (fun stack =>
        Lean.Order.admissible_pi_apply _ (fun initial =>
          Lean.Order.admissible_pi _ (fun final =>
            Lean.Order.admissible_pi _ (fun flow => Lean.Order.Option.admissible_eq_some _ (final, (Except.ok flow : Except Error Flow)))))))
  · intro approximate ih task stack initial final flow h
    rcases Option.bind_eq_some_iff.mp h with ⟨next, atom, h⟩
    rw [step_meaning raw normal, atom]
    simp only [Option.bind_some]
    cases next with
    | done after result =>
      simp only [Option.pure_def, Option.some.injEq] at h
      cases h
      rfl
    | more next rest middle => exact ih _ _ _ _ _ h



```

## Completeness from finite executions

The converse uses simultaneous induction on declarative process, sequence and for-loop
executions. Its continuation hypothesis is quantified over every remaining frame stack,
so nested returns, loop transfers and restoration are covered.

```lean
private theorem resume_restore (raw : Kernel Option State Error)
    (locals : Array Var) (saved initial : State) (stack : List (Frame State)) (flow : Flow) :
    drive raw (.resume (.ok flow)) (.restore locals saved :: stack) initial =
      drive raw (.resume (.ok flow)) stack ((project raw).restore locals saved initial) := by
  rw [drive.eq_def]; rfl

private theorem sequence_begin (raw : Kernel Option State Error)
    (steps : Array Proc) (stack : List (Frame State)) (initial : State) :
    drive raw (.proc (.sequence steps)) stack initial =
      drive raw (.resume (.ok .next)) (.sequence steps.toList :: stack) initial := by
  rw [drive.eq_def, drive.eq_def (task := .resume _)]; rfl

private theorem for_begin (raw : Kernel Option State Error)
    (iterator : Var) (body : Proc) (values : List QASM.Value)
    (stack : List (Frame State)) (initial : State) :
    (match values with
    | [] => drive raw (.resume (.ok .next)) stack initial
    | value :: rest => drive raw (.proc body) (.forLoop iterator body rest :: stack)
        ((project raw).bindIterator iterator value initial)) =
      drive raw (.resume (.ok .next)) (.forLoop iterator body values :: stack) initial := by
  apply Eq.symm
  rw [drive.eq_def]
  cases values <;> rfl

private theorem for_continue (raw : Kernel Option State Error)
    (iterator : Var) (body : Proc) (values : List QASM.Value)
    (stack : List (Frame State)) (initial : State) :
    drive raw (.resume (.ok .continueLoop)) (.forLoop iterator body values :: stack) initial =
      drive raw (.resume (.ok .next)) (.forLoop iterator body values :: stack) initial := by
  rw [drive.eq_def, drive.eq_def (task := .resume (.ok .next))]; rfl

private theorem resume_while (raw : Kernel Option State Error)
    (e : Expr) (body : Proc) (initial : State) (stack : List (Frame State)) (flow : Flow) :
    drive raw (.resume (.ok flow)) (.whileLoop e body :: stack) initial =
      match flow with
      | .next | .continueLoop => drive raw (.proc (.whileLoop e body)) stack initial
      | .breakLoop => drive raw (.resume (.ok .next)) stack initial
      | _ => drive raw (.resume (.ok flow)) stack initial := by
  rw [drive.eq_def]; cases flow <;> rfl

private theorem resume_for_break (raw : Kernel Option State Error)
    (iterator : Var) (body : Proc) (values : List QASM.Value) (initial : State)
    (stack : List (Frame State)) :
    drive raw (.resume (.ok .breakLoop)) (.forLoop iterator body values :: stack) initial =
      drive raw (.resume (.ok .next)) stack initial := by rw [drive.eq_def]; rfl

private theorem resume_for_exit (raw : Kernel Option State Error)
    (iterator : Var) (body : Proc) (values : List QASM.Value) (initial : State)
    (stack : List (Frame State)) (flow : Flow)
    (hf : flow ≠ .next ∧ flow ≠ .continueLoop ∧ flow ≠ .breakLoop) :
    drive raw (.resume (.ok flow)) (.forLoop iterator body values :: stack) initial =
      drive raw (.resume (.ok flow)) stack initial := by
  rw [drive.eq_def]; cases flow <;> simp_all [step]

private theorem resume_sequence_exit (raw : Kernel Option State Error)
    (steps : List Proc) (initial : State) (stack : List (Frame State)) (flow : Flow)
    (hf : flow ≠ .next) :
    drive raw (.resume (.ok flow)) (.sequence steps :: stack) initial =
      drive raw (.resume (.ok flow)) stack initial := by
  rw [drive.eq_def]; cases flow <;> simp_all [step]

private theorem drive_complete (raw : Kernel Option State Error)
    {proc : Proc} {initial final : State} {flow : Flow}
    (h : Exec (QASM.Execution.VerifiedControl.model (project raw)) proc initial final flow) :
    ∀ stack result,
      drive raw (.resume (.ok flow)) stack final = some result →
      drive raw (.proc proc) stack initial = some result := by
  induction h using Exec.rec
    (motive_2 := fun steps initial final flow _ => ∀ stack result,
      drive raw (.resume (.ok flow)) stack final = some result →
      drive raw (.resume (.ok .next)) (.sequence steps :: stack) initial = some result)
    (motive_3 := fun iterator body values initial final flow _ => ∀ stack result,
      drive raw (.resume (.ok flow)) stack final = some result →
      drive raw (.resume (.ok .next)) (.forLoop iterator body values :: stack) initial = some result)
  all_goals intros
  all_goals try simp only [QASM.Execution.VerifiedControl.model, project, erase_some] at *
  all_goals try (rw [sequence_begin]; solve_by_elim)
  all_goals rw [drive.eq_def]
  all_goals try simp only [step, bind, Option.pure_def, Option.bind_some]
  all_goals try simp_all
  all_goals try solve_by_elim
  case scope body initial final flow locals stack result ih h tail =>
    apply ih (.restore locals initial :: stack) result.1 result.2
    simpa [resume_restore, project] using tail
  case forLoop domain initial values middle iterator body final flow stack result ih hd h tail =>
    have continued := ih (.restore #[iterator] initial :: stack) result.1 result.2
      (by simpa [resume_restore, project] using tail)
    cases values <;> rw [drive.eq_def] at continued <;>
      simpa only [step, bind, Option.pure_def, Option.bind_some] using continued
  case whileBreak e initial middle body final stack result ih tail hc h =>
    apply ih (.whileLoop e body :: stack) result.1 result.2
    simpa only [resume_while] using tail
  case whileNext e initial middle body afterBody bodyFlow final flow hf stack result ih ihr tail hc h hr =>
    apply ih (.whileLoop e body :: stack) result.1 result.2
    have continued := ihr stack result.1 result.2 tail
    rcases hf with hf | hf <;> subst bodyFlow <;> simpa only [resume_while] using continued
  case whileExit e initial middle body final flow stack result hf ih tail hc h =>
    apply ih (.whileLoop e body :: stack) result.1 result.2
    cases flow <;> simp_all [resume_while]
  case domainEnd e initial final iterator body stack result h tail =>
    change drive raw (.resume (.ok .ended)) (.restore #[iterator] initial :: stack) final = some result
    rw [resume_restore]
    exact tail
  case exit proc initial final flow rest stack result hf ih tail head =>
    apply ih (.sequence rest :: stack) result.1 result.2
    simpa only [resume_sequence_exit raw rest final stack flow hf] using tail
  case next body iterator value initial middle bodyFlow rest final flow hf stack result iht continued head tail ih =>
    apply ih (.forLoop iterator body rest :: stack) result.1 result.2
    have done := iht stack result.1 result.2 continued
    rcases hf with hf | hf <;> subst bodyFlow
    · exact done
    · simpa only [for_continue] using done
  case breakLoop body iterator value initial final rest stack result tail head ih =>
    apply ih (.forLoop iterator body rest :: stack) result.1 result.2
    simpa only [resume_for_break] using tail
  case exit body iterator value initial final flow rest stack result hf tail head ih =>
    apply ih (.forLoop iterator body rest :: stack) result.1 result.2
    simpa only [resume_for_exit raw iterator body rest final stack flow hf] using tail



```

## Bidirectional runtime contract

The driver returns a successful finite result exactly when the declarative graph model
has that execution. The only atomic restriction is the allowed operation completion;
the actual runtime constructor proves that restriction in Refinement.Runtime.

```lean
theorem machine_proc_refinement_iff (raw : Kernel Option State Error)
    (normal : OperationsNormal raw) (proc : Proc) (initial final : State) (flow : Flow) :
    QASM.Execution.ControlMachine.eval raw proc initial = some (final, .ok flow) ↔
      Exec (QASM.Execution.VerifiedControl.model (project raw)) proc initial final flow := by
  constructor
  · intro result
    have h := drive_sound raw normal (.proc proc) [] initial final flow result
    apply control_sound (project raw)
    change (QASM.Execution.VerifiedControl.eval (project raw) proc initial).bind some = some (final, flow) at h
    rwa [Option.bind_fun_some] at h
  · intro h
    apply drive_complete raw h [] (final, .ok flow)
    rw [drive.eq_def]
    rfl


end Machine
end QASMVerification
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
