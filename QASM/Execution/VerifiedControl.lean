    import LiterateLean
    import QASM.Execution.EffectSemantics
    import Lean
    open scoped LiterateLean

# Proof-capable structured control evaluation

This evaluator uses Lean's least fixed-point construction instead of opaque partial
definitions. Atomic effects are supplied by a pure state-transition kernel. `none`
represents the absence of a finite successful result; faults and divergence are not
silently identified with whole-program termination. Conditions and domains carry that
termination explicitly, together with their resulting store.

The executable interpreter uses the shared frame-based ControlMachine. MachineLaws
proves that its Option specialization implements this evaluator's declarative model;
RuntimeLaws instantiates those laws with the actual interpreter callbacks.

```lean
namespace QASM.Execution.VerifiedControl
open QASM.IR
open QASM.Execution.Semantics (Flow)
open QASM.Execution.EffectSemantics (Model)

structure Kernel (State : Type) where
  operation : Op → State → Option (State × Flow)
  condition : Expr → State → Option (State × Option Bool)
  domain : IterationDomain → State → Option (State × Option (List QASM.Value))
  switchCase : Expr → Array SwitchCase → Option Proc → State → Option (State × Option Proc)
  returnValue : Option Expr → State → Option (State × Option QASM.Value × Bool)
  bindIterator : Var → QASM.Value → State → State
  restore : Array Var → State → State → State

def model (kernel : Kernel State) : Model State where
  operation op initial final flow := kernel.operation op initial = some (final, flow)
  condition e initial value final := kernel.condition e initial = some (final, value)
  domain d initial values final := kernel.domain d initial = some (final, values)
  switchCase e cases other initial selected final :=
    kernel.switchCase e cases other initial = some (final, selected)
  returnValue e initial value final flow := ∃ ended,
    kernel.returnValue e initial = some (final, value, ended) ∧
      flow = if ended then .ended else .returned value
  bindIterator := kernel.bindIterator
  restore := kernel.restore

```

## Least fixed-point evaluator

Sequence and for-loop helpers are in the same fixed-point group. Each successful
result preserves completion; scope and iterator bindings are restored on all such
completions. Atomic operation and return callbacks may only produce the completions
allowed by the declarative semantics.

```lean
mutual
  def eval (kernel : Kernel State) (proc : Proc) (initial : State) : Option (State × Flow) := do
    match proc with
    | .skip => return (initial, .next)
    | .operation op =>
      let (final, flow) ← kernel.operation op initial
      match flow with
      | .next | .ended => return (final, flow)
      | _ => none
    | .sequence steps => evalSequence kernel steps.toList initial
    | .scope locals body =>
      let (final, flow) ← eval kernel body initial
      return (kernel.restore locals initial final, flow)
    | .branch e yes no =>
      let (middle, value) ← kernel.condition e initial
      match value with
      | none => return (middle, .ended)
      | some true => eval kernel yes middle
      | some false => eval kernel (no.getD .skip) middle
    | .switch e cases other =>
      let (middle, selected) ← kernel.switchCase e cases other initial
      match selected with
      | none => return (middle, .ended)
      | some body => eval kernel body middle
    | .forLoop iterator domain body =>
      let (middle, values) ← kernel.domain domain initial
      let (final, flow) ← match values with
        | none => some (middle, .ended)
        | some values => evalFor kernel iterator body values middle
      return (kernel.restore #[iterator] initial final, flow)
    | .whileLoop e body =>
      let (middle, value) ← kernel.condition e initial
      match value with
      | none => return (middle, .ended)
      | some false => return (middle, .next)
      | some true =>
        let (afterBody, flow) ← eval kernel body middle
        match flow with
        | .breakLoop => return (afterBody, .next)
        | .next | .continueLoop => eval kernel (.whileLoop e body) afterBody
        | _ => return (afterBody, flow)
    | .breakLoop => return (initial, .breakLoop)
    | .continueLoop => return (initial, .continueLoop)
    | .returnValue e =>
      let (final, value, ended) ← kernel.returnValue e initial
      return (final, if ended then .ended else .returned value)
    | .endProgram => return (initial, .ended)
  partial_fixpoint

  def evalSequence (kernel : Kernel State) (steps : List Proc) (initial : State) : Option (State × Flow) := do
    match steps with
    | [] => return (initial, .next)
    | head :: tail =>
      let (middle, flow) ← eval kernel head initial
      match flow with
      | .next => evalSequence kernel tail middle
      | _ => return (middle, flow)
  partial_fixpoint

  def evalFor (kernel : Kernel State) (iterator : Var) (body : Proc)
      (values : List QASM.Value) (initial : State) : Option (State × Flow) := do
    match values with
    | [] => return (initial, .next)
    | value :: rest =>
      let (middle, flow) ← eval kernel body (kernel.bindIterator iterator value initial)
      match flow with
      | .next | .continueLoop => evalFor kernel iterator body rest middle
      | .breakLoop => return (middle, .next)
      | _ => return (middle, flow)
  partial_fixpoint
end

end QASM.Execution.VerifiedControl
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
