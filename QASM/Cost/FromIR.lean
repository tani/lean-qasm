    import LiterateLean
    import QASM.Cost.Model
    import QASM.IR.Program
    open scoped LiterateLean

# Cost metrics from canonical IR

This projection folds immutable canonical IR without invoking `QASM.Execution.run` or a
`QuantumBackend`. It counts source-level structural nodes: both branch arms and every switch
body are visited once, while loop bodies are visited once without estimating iteration counts.
Measurement, reset, and barrier costs likewise count operation nodes rather than selected wires.

Gate and subroutine declaration bodies contribute once as program structure before the main
body. Call sites contribute their own counters but never expand those declarations, which keeps
the measure deterministic and total even when subroutines are recursive. External and unsupported
nodes are recorded rather than rejected.

```lean
namespace QASM.Cost

open QASM.IR

partial def costCircuit : Circuit → CostM Unit
  | .identity _ => pure ()
  | .primitive _ => charge { applications := 1 }
  | .compose first second => costCircuit first *> costCircuit second
  | .tensor first second => costCircuit first *> costCircuit second
  | .permute _ => pure ()
  | .inverse circuit => costCircuit circuit
  | .power _ circuit => costCircuit circuit
  | .controlled _ circuit => costCircuit circuit
  | .unsupported _ _ _ _ => charge { unsupported := 1 }

def costOp : Op → CostM Unit
  | .eval _ => charge { classicalOps := 1 }
  | .declare _ _ => charge { classicalOps := 1 }
  | .assign _ _ => charge { classicalOps := 1 }
  | .apply _ _ => charge { applications := 1 }
  | .measure _ _ => charge { measurements := 1 }
  | .reset _ => charge { resets := 1 }
  | .barrier _ => charge { barriers := 1 }
  | .allocate decl => charge { allocations := 1, allocatedQubits := decl.size }
  | .call _ _ => charge { subroutineCalls := 1 }
  | .emitExtern _ => charge { externCalls := 1 }
  | .unsupported _ _ => charge { unsupported := 1 }

partial def costProc : Proc → CostM Unit
  | .skip => pure ()
  | .operation op => costOp op
  | .sequence steps => steps.forM costProc
  | .scope _ body => costProc body
  | .branch _ thenBranch elseBranch => do
      charge { branches := 1 }
      costProc thenBranch
      match elseBranch with
      | some body => costProc body
      | none => pure ()
  | .switch _ cases default => do
      charge { branches := 1 }
      cases.forM (fun | .mk _ body => costProc body)
      match default with
      | some body => costProc body
      | none => pure ()
  | .forLoop _ _ body => charge { loops := 1 } *> costProc body
  | .whileLoop _ body => charge { loops := 1 } *> costProc body
  | .breakLoop => pure ()
  | .continueLoop => pure ()
  | .returnValue value =>
      match value with
      | some _ => charge { classicalOps := 1 }
      | none => pure ()
  | .endProgram => pure ()

def measure (program : Program) : Metrics :=
  let action : CostM Unit := do
    charge {
      gateDeclarations := program.gates.size
      subroutineDeclarations := program.subroutines.size
      externDeclarations := program.externs.size }
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
