    import LiterateLean
    import QASM.Execution.Semantics
    open scoped LiterateLean

# Completion-aware structured execution

Atomic operations carry completion explicitly. Expression evaluation in a condition,
iteration domain, or switch can end the entire program: `none` means that completion,
not a missing value. Return evaluation also carries completion so a call ending the
program cannot be converted into an ordinary return. The original finite semantics
remains available unchanged. Refinement.Control and Refinement.Machine prove its
correspondence with fixed-point evaluation; Refinement.Runtime specializes it to the
actual Option interpreter. Fault and divergence are represented by absence of a derivation.

```lean
namespace QASM.Execution.EffectSemantics
open QASM.IR
open QASM.Execution.Semantics (Flow)

structure Model (State : Type) where
  operation : Op → State → State → Flow → Prop
  condition : Expr → State → Option Bool → State → Prop
  domain : IterationDomain → State → Option (List QASM.Value) → State → Prop
  switchCase : Expr → Array SwitchCase → Option Proc → State → Option Proc → State → Prop
  returnValue : Option Expr → State → Option QASM.Value → State → Flow → Prop
  bindIterator : Var → QASM.Value → State → State
  restore : Array Var → State → State → State

variable {State : Type}
```

## Finite execution and completion propagation

Only normal completion and whole-program termination may escape an atomic operation.
Return values are consumed at the callable boundary; a return expression can still end
the program. Sequence and loop rules propagate that termination without running a tail.

```lean
mutual
  inductive Exec (model : Model State) : Proc → State → State → Flow → Prop where
    | skip (state) : Exec model .skip state state .next
    | operation (h : model.operation op initial final .next) :
        Exec model (.operation op) initial final .next
    | operationEnd (h : model.operation op initial final .ended) :
        Exec model (.operation op) initial final .ended
    | sequence (h : ExecSequence model steps.toList initial final flow) :
        Exec model (.sequence steps) initial final flow
    | scope (h : Exec model body initial final flow) :
        Exec model (.scope locals body) initial (model.restore locals initial final) flow
    | branchTrue (hc : model.condition testExpr initial (some true) intermediate)
        (h : Exec model yes intermediate final flow) :
        Exec model (.branch testExpr yes no) initial final flow
    | branchFalse (hc : model.condition testExpr initial (some false) intermediate)
        (h : Exec model (no.getD .skip) intermediate final flow) :
        Exec model (.branch testExpr yes no) initial final flow
    | switch (hs : model.switchCase scrutinee cases other initial (some selected) intermediate)
        (h : Exec model selected intermediate final flow) :
        Exec model (.switch scrutinee cases other) initial final flow
    | forLoop (hd : model.domain domain initial (some values) intermediate)
        (h : ExecFor model iterator body values intermediate final flow) :
        Exec model (.forLoop iterator domain body) initial
          (model.restore #[iterator] initial final) flow
    | whileFalse (hc : model.condition testExpr initial (some false) final) :
        Exec model (.whileLoop testExpr body) initial final .next
    | whileBreak (hc : model.condition testExpr initial (some true) intermediate)
        (h : Exec model body intermediate final .breakLoop) :
        Exec model (.whileLoop testExpr body) initial final .next
    | whileNext (hc : model.condition testExpr initial (some true) intermediate)
        (h : Exec model body intermediate afterBody bodyFlow)
        (hf : bodyFlow = .next ∨ bodyFlow = .continueLoop)
        (hr : Exec model (.whileLoop testExpr body) afterBody final flow) :
        Exec model (.whileLoop testExpr body) initial final flow
    | whileExit (hc : model.condition testExpr initial (some true) intermediate)
        (h : Exec model body intermediate final flow)
        (hf : flow ≠ .next ∧ flow ≠ .continueLoop ∧ flow ≠ .breakLoop) :
        Exec model (.whileLoop testExpr body) initial final flow
    | conditionEnd (h : model.condition testExpr initial none final) :
        Exec model (.branch testExpr yes no) initial final .ended
    | whileConditionEnd (h : model.condition testExpr initial none final) :
        Exec model (.whileLoop testExpr body) initial final .ended
    | domainEnd (h : model.domain domain initial none final) :
        Exec model (.forLoop iterator domain body) initial
          (model.restore #[iterator] initial final) .ended
    | switchEnd (h : model.switchCase scrutinee cases other initial none final) :
        Exec model (.switch scrutinee cases other) initial final .ended
    | breakLoop (state) : Exec model .breakLoop state state .breakLoop
    | continueLoop (state) : Exec model .continueLoop state state .continueLoop
    | returnValue (h : model.returnValue value initial result final (.returned result)) :
        Exec model (.returnValue value) initial final (.returned result)
    | returnEnd (h : model.returnValue value initial result final .ended) :
        Exec model (.returnValue value) initial final .ended
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


A total-correctness contract requires a successful execution and excludes faults.
It also constrains every successful outcome; existence alone is insufficient.

```lean
theorem sequence_end_left (model : Model State) (state : State) (tail : Proc) :
    Exec model (.sequence #[.endProgram, tail]) state state .ended :=
  .sequence (.exit (.endProgram state) (by intro h; cases h))

theorem branch_expression_end (model : Model State)
    (h : model.condition condition initial none final) (yes : Proc) (no : Option Proc) :
    Exec model (.branch condition yes no) initial final .ended := .conditionEnd h

def TotalCorrect {State : Type} (model : Model State) (fault : Proc → State → Prop)
    (proc : Proc) (initial : State) (post : State → Flow → Prop) : Prop :=
  (∃ final flow, Exec model proc initial final flow) ∧
  (∀ final flow, Exec model proc initial final flow → post final flow) ∧
  ¬ fault proc initial

end QASM.Execution.EffectSemantics
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
