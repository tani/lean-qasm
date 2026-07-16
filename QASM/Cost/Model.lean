    import LiterateLean
    import QASM.IR.Program
    open scoped LiterateLean

# Static cost metrics

The cost model is an immutable summary accumulated by a pure state computation. It records
structural facts from canonical `QASM.IR.Program` values and has no execution runtime or quantum
backend dependency. `CostM` therefore carries only `Metrics`: every IR program is
measurable, including programs with unsupported or external nodes.

The fields remain independent counters rather than a scalar score. A weighted total requires a
separate policy, and summing metadata such as allocated qubits together with operation counts
would otherwise impose an ambiguous weighting and risk double-counting.

```lean
namespace QASM.Cost

open QASM.IR

structure Metrics where
  gateDeclarations : Nat := 0
  subroutineDeclarations : Nat := 0
  externDeclarations : Nat := 0
  allocations : Nat := 0
  allocatedQubits : Nat := 0
  applications : Nat := 0
  measurements : Nat := 0
  resets : Nat := 0
  barriers : Nat := 0
  classicalOps : Nat := 0
  branches : Nat := 0
  loops : Nat := 0
  subroutineCalls : Nat := 0
  externCalls : Nat := 0
  unsupported : Nat := 0
  deriving Repr, Inhabited, BEq

protected def Metrics.add (left right : Metrics) : Metrics :=
  { gateDeclarations := left.gateDeclarations + right.gateDeclarations
    subroutineDeclarations := left.subroutineDeclarations + right.subroutineDeclarations
    externDeclarations := left.externDeclarations + right.externDeclarations
    allocations := left.allocations + right.allocations
    allocatedQubits := left.allocatedQubits + right.allocatedQubits
    applications := left.applications + right.applications
    measurements := left.measurements + right.measurements
    resets := left.resets + right.resets
    barriers := left.barriers + right.barriers
    classicalOps := left.classicalOps + right.classicalOps
    branches := left.branches + right.branches
    loops := left.loops + right.loops
    subroutineCalls := left.subroutineCalls + right.subroutineCalls
    externCalls := left.externCalls + right.externCalls
    unsupported := left.unsupported + right.unsupported }

instance : Add Metrics where
  add := Metrics.add

abbrev CostM := StateM Metrics

def charge (delta : Metrics) : CostM Unit :=
  modify fun cost => cost + delta

end QASM.Cost
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
