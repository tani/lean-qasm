    import LiterateLean
    import QASM.Cost.Model
    import QASM.IR.Program
    open scoped LiterateLean

# Static cost report from canonical IR

This projection folds immutable canonical IR without invoking `QASM.Execution.run` or a
`QuantumBackend`. It counts source-level structural nodes: both branch arms and every switch
body are visited once, while loop bodies are visited once without estimating iteration counts.
Measurement, reset, and barrier costs likewise count operation nodes rather than selected wires.

The embedded `Resources.gates` vector is more selective than
`OperationCounts.applications`. A visible `.cx` primitive contributes one CNOT and a visible
standard one-qubit primitive contributes one one-qubit gate. Every remaining primitive is
retained as `otherPrimitive`, rather than being assigned an unjustified CNOT decomposition.
QSVT's `U`, `U†`, and projector-controlled NOT resources cannot be recovered from ordinary
OpenQASM names, so they stay zero in this structural projection and are supplied explicitly with
`Resources.qsvtAlternatingPhase` when the algorithmic contract is known.

Gate and subroutine declaration bodies contribute once as program structure before the main
body. Call sites contribute their own counters but never expand those declarations, which keeps
the measure deterministic and total even when subroutines are recursive. External and unsupported
nodes are recorded rather than rejected.

The folds are ordinary total definitions. Process sequences and switch cases use explicit list
visitors so Lean can see that every recursive call consumes a strict substructure; this keeps the
projection reducible in the kernel as well as executable through compiled evaluation.

```lean
namespace QASM.Cost

open QASM.IR

def primitiveResources : PrimitiveKind → Resources
  | .cx => { gates := { cnot := 1 } }
  | .u | .gphase | .p
  | .x | .y | .z | .h | .s | .sdg | .t | .tdg | .sx | .rx | .ry | .rz
  | .phase | .id | .u1 | .u2 | .u3 => { gates := { oneQubit := 1 } }
  | _ => { gates := { otherPrimitive := 1 } }

def costCircuit : Circuit → CostM Unit
  | .identity _ => pure ()
  | .primitive primitive => charge {
      operations := { applications := 1 }
      resources := primitiveResources primitive.kind }
  | .compose first second => costCircuit first *> costCircuit second
  | .tensor first second => costCircuit first *> costCircuit second
  | .permute _ => pure ()
  | .inverse circuit => costCircuit circuit
  | .power _ circuit => costCircuit circuit
  | .controlled _ circuit => costCircuit circuit
  | .unsupported _ _ _ _ => charge { operations := { unsupported := 1 } }

def costOp : Op → CostM Unit
  | .eval _ => charge { operations := { classical := 1 } }
  | .declare _ _ => charge { operations := { classical := 1 } }
  | .assign _ _ => charge { operations := { classical := 1 } }
  | .apply gate _ => charge {
      operations := { applications := 1 }
      resources := primitiveResources gate.target }
  | .measure _ _ => charge { operations := { measurements := 1 } }
  | .reset _ => charge { operations := { resets := 1 } }
  | .barrier _ => charge { operations := { barriers := 1 } }
  | .allocate decl => charge {
      shape := { allocationSites := 1, allocatedQubits := decl.size } }
  | .call _ _ => charge { operations := { subroutineCalls := 1 } }
  | .emitExtern _ => charge { operations := { externCalls := 1 } }
  | .unsupported _ _ => charge { operations := { unsupported := 1 } }

mutual
  def costProc : Proc → CostM Unit
    | .skip => pure ()
    | .operation op => costOp op
    | .sequence steps => costProcList steps.toList
    | .scope _ body => costProc body
    | .branch _ thenBranch elseBranch => do
        charge { shape := { branchNodes := 1 } }
        costProc thenBranch
        match elseBranch with
        | some body => costProc body
        | none => pure ()
    | .switch _ cases default => do
        charge { shape := { branchNodes := 1 } }
        costSwitchCaseList cases.toList
        match default with
        | some body => costProc body
        | none => pure ()
    | .forLoop _ _ body => charge { shape := { loopNodes := 1 } } *> costProc body
    | .whileLoop _ body => charge { shape := { loopNodes := 1 } } *> costProc body
    | .breakLoop => pure ()
    | .continueLoop => pure ()
    | .returnValue value =>
        match value with
        | some _ => charge { operations := { classical := 1 } }
        | none => pure ()
    | .endProgram => pure ()

  private def costProcList : List Proc → CostM Unit
    | [] => pure ()
    | proc :: rest => costProc proc *> costProcList rest

  private def costSwitchCaseList : List SwitchCase → CostM Unit
    | [] => pure ()
    | .mk _ body :: rest => costProc body *> costSwitchCaseList rest
end

def measure (program : Program) : Report :=
  let action : CostM Unit := do
    charge {
      declarations :=
        { gates := program.gates.size
          subroutines := program.subroutines.size
          externs := program.externs.size } }
    program.gates.forM fun declaration => costCircuit declaration.body
    program.subroutines.forM fun declaration => costProc declaration.body
    costProc program.body
  (action.run {}).2

end QASM.Cost
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
