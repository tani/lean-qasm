    import LiterateLean
    import QASM.IR.Program
    import QASM.Runtime
    open scoped LiterateLean

# Relational semantics for structured IR control flow

`Exec` describes successful finite executions without assuming that every `while` loop or
recursive subroutine terminates. Atomic operations, expression evaluation, switch selection,
and binding restoration are supplied by a `Model`; these relations can describe quantum
measurement probabilistically or nondeterministically in a subsequent concrete model.

This module proves control-flow laws for every model and every process. It does not assert
that the existing `partial` runtime interpreter implements this relation: that requires a
separate refinement proof. Runtime errors and divergence are deliberately outside this
successful-execution relation. Equivalence below is therefore finite successful-behavior
equivalence, not a termination-sensitive or probabilistic equivalence.

```lean
namespace QASM.Execution.Semantics

open QASM.IR

inductive Flow where
  | next
  | breakLoop
  | continueLoop
  | returned (value : Option QASM.Value)
  | ended
  deriving Repr, BEq

structure Model (State : Type) where
  operation : Op → State → State → Prop
  condition : Expr → State → Bool → State → Prop
  domain : IterationDomain → State → List QASM.Value → State → Prop
  switchCase : Expr → Array SwitchCase → Option Proc → State → Proc → State → Prop
  returnValue : Option Expr → State → Option QASM.Value → State → Prop
  bindIterator : Var → QASM.Value → State → State
  restore : Array Var → State → State → State

variable {State : Type}

mutual
  inductive Exec (model : Model State) : Proc → State → State → Flow → Prop where
    | skip (state) : Exec model .skip state state .next
    | operation (h : model.operation op initial final) :
        Exec model (.operation op) initial final .next
    | sequence (h : ExecSequence model steps.toList initial final flow) :
        Exec model (.sequence steps) initial final flow
    | scope (h : Exec model body initial final flow) :
        Exec model (.scope locals body) initial (model.restore locals initial final) flow
    | branchTrue (hc : model.condition testExpr initial true intermediate)
        (h : Exec model yes intermediate final flow) :
        Exec model (.branch testExpr yes no) initial final flow
    | branchFalse (hc : model.condition testExpr initial false intermediate)
        (h : Exec model (no.getD .skip) intermediate final flow) :
        Exec model (.branch testExpr yes no) initial final flow
    | switch (hs : model.switchCase scrutinee cases other initial selected intermediate)
        (h : Exec model selected intermediate final flow) :
        Exec model (.switch scrutinee cases other) initial final flow
    | forLoop (hd : model.domain domain initial values intermediate)
        (h : ExecFor model iterator body values intermediate final flow) :
        Exec model (.forLoop iterator domain body) initial
          (model.restore #[iterator] initial final) flow
    | whileFalse (hc : model.condition testExpr initial false final) :
        Exec model (.whileLoop testExpr body) initial final .next
    | whileBreak (hc : model.condition testExpr initial true intermediate)
        (h : Exec model body intermediate final .breakLoop) :
        Exec model (.whileLoop testExpr body) initial final .next
    | whileNext (hc : model.condition testExpr initial true intermediate)
        (h : Exec model body intermediate afterBody bodyFlow)
        (hf : bodyFlow = .next ∨ bodyFlow = .continueLoop)
        (hr : Exec model (.whileLoop testExpr body) afterBody final flow) :
        Exec model (.whileLoop testExpr body) initial final flow
    | whileExit (hc : model.condition testExpr initial true intermediate)
        (h : Exec model body intermediate final flow)
        (hf : flow ≠ .next ∧ flow ≠ .continueLoop ∧ flow ≠ .breakLoop) :
        Exec model (.whileLoop testExpr body) initial final flow
    | breakLoop (state) : Exec model .breakLoop state state .breakLoop
    | continueLoop (state) : Exec model .continueLoop state state .continueLoop
    | returnValue (h : model.returnValue value initial result final) :
        Exec model (.returnValue value) initial final (.returned result)
    | endProgram (state) : Exec model .endProgram state state .ended

  inductive ExecSequence (model : Model State) : List Proc → State → State → Flow → Prop where
    | nil (state) : ExecSequence model [] state state .next
    | next (head : Exec model proc initial intermediate .next)
        (tail : ExecSequence model rest intermediate final flow) :
        ExecSequence model (proc :: rest) initial final flow
    | exit (head : Exec model proc initial final flow) (hf : flow ≠ .next) :
        ExecSequence model (proc :: rest) initial final flow

  inductive ExecFor (model : Model State) :
      Var → Proc → List QASM.Value → State → State → Flow → Prop where
    | nil (state) : ExecFor model iterator body [] state state .next
    | next (head : Exec model body (model.bindIterator iterator value initial) intermediate bodyFlow)
        (hf : bodyFlow = .next ∨ bodyFlow = .continueLoop)
        (tail : ExecFor model iterator body rest intermediate final flow) :
        ExecFor model iterator body (value :: rest) initial final flow
    | breakLoop (head : Exec model body (model.bindIterator iterator value initial) final .breakLoop) :
        ExecFor model iterator body (value :: rest) initial final .next
    | exit (head : Exec model body (model.bindIterator iterator value initial) final flow)
        (hf : flow ≠ .next ∧ flow ≠ .continueLoop ∧ flow ≠ .breakLoop) :
        ExecFor model iterator body (value :: rest) initial final flow
end

```

## Laws available without specializing a program

Leading `skip` is neutral even when the process exits with `return`, `break`, `continue`,
or `end`. These theorems quantify over arbitrary IR data and arbitrary initial state;
no source expansion or numerical instance of a family is needed.

```lean
def Equivalent (model : Model State) (left right : Proc) : Prop :=
  ∀ initial final flow, Exec model left initial final flow ↔ Exec model right initial final flow

@[simp] theorem exec_skip_iff (model : Model State) (initial final : State) (flow : Flow) :
    Exec model .skip initial final flow ↔ final = initial ∧ flow = .next := by
  constructor
  · intro h; cases h; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; exact .skip _

@[simp] theorem sequence_singleton (model : Model State) (proc : Proc) :
    Equivalent model (.sequence #[proc]) proc := by
  intro initial final flow
  constructor
  · intro h
    cases h with
    | sequence h =>
      cases h with
      | next head tail => cases tail; exact head
      | exit head _ => exact head
  · intro h
    apply Exec.sequence
    cases flow <;> first
      | exact .next h (.nil final)
      | exact .exit h (by intro hf; cases hf)

theorem sequence_skip_left (model : Model State) (proc : Proc) :
    Equivalent model (.sequence #[.skip, proc]) proc := by
  intro initial final flow
  constructor
  · intro h
    cases h with
    | sequence h =>
      cases h with
      | next head tail =>
        cases head
        exact (sequence_singleton model proc initial final flow).mp (.sequence tail)
      | exit head hf => cases head; exact (hf rfl).elim
  · intro h
    have singleton := (sequence_singleton model proc initial final flow).mpr h
    cases singleton with
    | sequence tail => exact .sequence (.next (.skip initial) tail)

end QASM.Execution.Semantics
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
