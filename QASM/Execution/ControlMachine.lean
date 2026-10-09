    import LiterateLean
    import QASM.Execution.VerifiedControl
    open scoped LiterateLean

# Shared structured-control machine

The interpreter and proof-oriented evaluator share this defunctionalized control machine.
A frame records only pending control work and saved lexical stores. Every transition is
finite; the driver recurses in tail position. An atomic error still unwinds restoration
frames, so the store returned on failure respects lexical scope.

```lean
namespace QASM.Execution.ControlMachine
open QASM.IR
open scoped Lean.Order
open QASM.Execution.Semantics (Flow)

structure Kernel (m : Type → Type) (State Error : Type) where
  operation : Op → State → m (State × Except Error Flow)
  condition : Expr → State → m (State × Except Error (Option Bool))
  domain : IterationDomain → State → m (State × Except Error (Option (List QASM.Value)))
  switchCase : Expr → Array SwitchCase → Option Proc → State → m (State × Except Error (Option Proc))
  returnValue : Option Expr → State → m (State × Except Error (Option QASM.Value × Bool))
  bindIterator : Var → QASM.Value → State → State
  restore : Array Var → State → State → State

inductive Frame (State : Type) where
  | sequence (rest : List Proc)
  | restore (locals : Array Var) (saved : State)
  | forLoop (iterator : Var) (body : Proc) (rest : List QASM.Value)
  | whileLoop (condition : Expr) (body : Proc)

inductive Task (Error : Type) where
  | proc (body : Proc)
  | resume (completion : Except Error Flow)

inductive Step (State Error : Type) where
  | more (task : Task Error) (stack : List (Frame State)) (state : State)
  | done (state : State) (completion : Except Error Flow)

instance : Inhabited Flow := ⟨.next⟩

```

## Driver and atomic effects

Runtime operation callbacks restrict completion to normal execution or program termination.
Conditions, domains and switch
selection preserve whole-program termination distinctly from errors. The final store
is returned on every completion, including a backend failure.

```lean
def step [Monad m] (kernel : Kernel m State Error)
    (task : Task Error) (stack : List (Frame State)) (initial : State) :
    m (Step State Error) := do
  match task with
  | .proc proc =>
    match proc with
    | .skip => pure <| .more (.resume (.ok .next)) stack initial
    | .operation op =>
      let (final, result) ← kernel.operation op initial
      pure <| .more (.resume result) stack final
    | .sequence steps =>
      match steps.toList with
      | [] => pure <| .more (.resume (.ok .next)) stack initial
      | head :: rest => pure <| .more (.proc head) (.sequence rest :: stack) initial
    | .scope locals body => pure <| .more (.proc body) (.restore locals initial :: stack) initial
    | .branch e yes no =>
      let (middle, value) ← kernel.condition e initial
      match value with
      | .error error => pure <| .more (.resume (.error error)) stack middle
      | .ok none => pure <| .more (.resume (.ok .ended)) stack middle
      | .ok (some true) => pure <| .more (.proc yes) stack middle
      | .ok (some false) => pure <| .more (.proc (no.getD .skip)) stack middle
    | .switch e cases other =>
      let (middle, selected) ← kernel.switchCase e cases other initial
      match selected with
      | .error error => pure <| .more (.resume (.error error)) stack middle
      | .ok none => pure <| .more (.resume (.ok .ended)) stack middle
      | .ok (some body) => pure <| .more (.proc body) stack middle
    | .forLoop iterator domain body =>
      let (middle, values) ← kernel.domain domain initial
      let stack := .restore #[iterator] initial :: stack
      match values with
      | .error error => pure <| .more (.resume (.error error)) stack middle
      | .ok none => pure <| .more (.resume (.ok .ended)) stack middle
      | .ok (some []) => pure <| .more (.resume (.ok .next)) stack middle
      | .ok (some (value :: rest)) =>
        pure <| .more (.proc body) (.forLoop iterator body rest :: stack)
          (kernel.bindIterator iterator value middle)
    | .whileLoop e body =>
      let (middle, value) ← kernel.condition e initial
      match value with
      | .error error => pure <| .more (.resume (.error error)) stack middle
      | .ok none => pure <| .more (.resume (.ok .ended)) stack middle
      | .ok (some false) => pure <| .more (.resume (.ok .next)) stack middle
      | .ok (some true) => pure <| .more (.proc body) (.whileLoop e body :: stack) middle
    | .breakLoop => pure <| .more (.resume (.ok .breakLoop)) stack initial
    | .continueLoop => pure <| .more (.resume (.ok .continueLoop)) stack initial
    | .returnValue e =>
      let (final, result) ← kernel.returnValue e initial
      match result with
      | .error error => pure <| .more (.resume (.error error)) stack final
      | .ok (value, ended) =>
        pure <| .more (.resume (.ok (if ended then .ended else .returned value))) stack final
    | .endProgram => pure <| .more (.resume (.ok .ended)) stack initial
  | .resume result =>
    match stack with
    | [] => return .done initial result
    | .restore locals saved :: rest =>
      pure <| .more (.resume result) rest (kernel.restore locals saved initial)
    | .sequence steps :: rest =>
      match result with
      | .ok .next =>
        match steps with
        | [] => pure <| .more (.resume (.ok .next)) rest initial
        | head :: tail => pure <| .more (.proc head) (.sequence tail :: rest) initial
      | _ => pure <| .more (.resume result) rest initial
    | .forLoop iterator body values :: rest =>
      match result with
      | .ok .next | .ok .continueLoop =>
        match values with
        | [] => pure <| .more (.resume (.ok .next)) rest initial
        | value :: tail => pure <| .more (.proc body) (.forLoop iterator body tail :: rest) (kernel.bindIterator iterator value initial)
      | .ok .breakLoop => pure <| .more (.resume (.ok .next)) rest initial
      | _ => pure <| .more (.resume result) rest initial
    | .whileLoop e body :: rest =>
      match result with
      | .ok .next | .ok .continueLoop => pure <| .more (.proc (.whileLoop e body)) rest initial
      | .ok .breakLoop => pure <| .more (.resume (.ok .next)) rest initial
      | _ => pure <| .more (.resume result) rest initial

```

## Fixed-point execution and failure restoration

The driver executes the total transition function in tail position, preserving backend
effects through the supplied monad. A failure runs no pending process or condition; it
restores all saved frames before returning the original error and final store.

```lean
attribute [local partial_fixpoint_monotone] Lean.Order.MonadTail.monotone_bind_right

def drive [Nonempty State] [Monad m] [Lean.Order.MonadTail m] (kernel : Kernel m State Error)
    (task : Task Error) (stack : List (Frame State)) (initial : State) :
    m (State × Except Error Flow) := do
  match ← step kernel task stack initial with
  | .done final result => pure (final, result)
  | .more next rest middle => drive kernel next rest middle
partial_fixpoint

def eval [Nonempty State] [Monad m] [Lean.Order.MonadTail m] (kernel : Kernel m State Error) (proc : Proc)
    (initial : State) : m (State × Except Error Flow) := drive kernel (.proc proc) [] initial


def restoreFrames (kernel : Kernel m State Error) : List (Frame State) → State → State
  | [], state => state
  | .restore locals saved :: rest, state => restoreFrames kernel rest (kernel.restore locals saved state)
  | _ :: rest, state => restoreFrames kernel rest state

theorem drive_failure [Nonempty State] [Monad m] [LawfulMonad m] [Lean.Order.MonadTail m]
    (kernel : Kernel m State Error) (error : Error) (stack : List (Frame State)) (initial : State) :
    drive kernel (.resume (.error error)) stack initial = pure (restoreFrames kernel stack initial, .error error) := by
  induction stack generalizing initial with
  | nil => rw [drive.eq_def]; simp [step, restoreFrames]
  | cons frame rest ih =>
    rw [drive.eq_def]
    cases frame <;> simpa only [step, pure_bind, restoreFrames] using ih _


end QASM.Execution.ControlMachine
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
