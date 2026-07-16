    import LiterateLean
    import QASM.IR.Program
    open scoped LiterateLean

# Static cost reports

The cost model is an immutable report accumulated by a pure state computation. It records
structural facts from canonical `QASM.IR.Program` values and has no execution runtime or quantum
backend dependency. `CostM` therefore carries only `Report`: every IR program is measurable,
including programs with unsupported or external nodes.

The report is intentionally hierarchical. Declaration inventory, program shape, operation counts,
and resource estimates answer different questions and evolve independently. A flat record makes
unrelated additions expensive to review and encourages comparing quantities with incompatible
units. The nested layout makes those boundaries part of the API.

```mermaid
flowchart TD
    Report --> Declarations
    Report --> ProgramShape
    Report --> OperationCounts
    Report --> Resources
    Resources --> OracleCalls
    Resources --> GateCounts
    Resources --> Workspace
```

## Structural inventory

`Declarations` records the compilation-unit inventory, while `ProgramShape` records nodes that
describe the shape of execution rather than quantum operations. `allocationSites` is a count of
declarations; `allocatedQubits` is the total requested width. Neither is an elapsed-time estimate.

```lean
namespace QASM.Cost

open QASM.IR

structure Declarations where
  gates : Nat := 0
  subroutines : Nat := 0
  externs : Nat := 0
  deriving Repr, Inhabited, BEq

protected def Declarations.add (left right : Declarations) : Declarations :=
  { gates := left.gates + right.gates
    subroutines := left.subroutines + right.subroutines
    externs := left.externs + right.externs }

instance : Add Declarations where
  add := Declarations.add

structure ProgramShape where
  allocationSites : Nat := 0
  allocatedQubits : Nat := 0
  branchNodes : Nat := 0
  loopNodes : Nat := 0
  deriving Repr, Inhabited, BEq

protected def ProgramShape.add (left right : ProgramShape) : ProgramShape :=
  { allocationSites := left.allocationSites + right.allocationSites
    allocatedQubits := left.allocatedQubits + right.allocatedQubits
    branchNodes := left.branchNodes + right.branchNodes
    loopNodes := left.loopNodes + right.loopNodes }

instance : Add ProgramShape where
  add := ProgramShape.add
```

## Operation counts

`OperationCounts` is the complete source-structural account of effectful IR operations. An
application is counted even when the callee is a user-defined or otherwise opaque gate. This
preserves a total, deterministic measure without pretending to know an implementation that the
IR does not contain.

```lean
structure OperationCounts where
  applications : Nat := 0
  measurements : Nat := 0
  resets : Nat := 0
  barriers : Nat := 0
  classical : Nat := 0
  subroutineCalls : Nat := 0
  externCalls : Nat := 0
  unsupported : Nat := 0
  deriving Repr, Inhabited, BEq

protected def OperationCounts.add (left right : OperationCounts) : OperationCounts :=
  { applications := left.applications + right.applications
    measurements := left.measurements + right.measurements
    resets := left.resets + right.resets
    barriers := left.barriers + right.barriers
    classical := left.classical + right.classical
    subroutineCalls := left.subroutineCalls + right.subroutineCalls
    externCalls := left.externCalls + right.externCalls
    unsupported := left.unsupported + right.unsupported }

instance : Add OperationCounts where
  add := OperationCounts.add
```

## Resource estimates

Resource estimates use three disjoint records. `OracleCalls` captures QSVT-level algorithmic
operations; `GateCounts` captures an elementary-gate view such as CSD; `Workspace` captures peak
space rather than a cumulative operation count. Their combination adds calls and gates but takes
the maximum workspace requirement.

```lean
structure OracleCalls where
  unitary : Nat := 0
  inverseUnitary : Nat := 0
  projectorControlledNot : Nat := 0
  complementaryProjectorControlledNot : Nat := 0
  deriving Repr, Inhabited, BEq

protected def OracleCalls.add (left right : OracleCalls) : OracleCalls :=
  { unitary := left.unitary + right.unitary
    inverseUnitary := left.inverseUnitary + right.inverseUnitary
    projectorControlledNot := left.projectorControlledNot + right.projectorControlledNot
    complementaryProjectorControlledNot :=
      left.complementaryProjectorControlledNot + right.complementaryProjectorControlledNot }

instance : Add OracleCalls where
  add := OracleCalls.add

structure GateCounts where
  cnot : Nat := 0
  oneQubit : Nat := 0
  otherPrimitive : Nat := 0
  deriving Repr, Inhabited, BEq

protected def GateCounts.add (left right : GateCounts) : GateCounts :=
  { cnot := left.cnot + right.cnot
    oneQubit := left.oneQubit + right.oneQubit
    otherPrimitive := left.otherPrimitive + right.otherPrimitive }

instance : Add GateCounts where
  add := GateCounts.add

structure Workspace where
  peakAncillaQubits : Nat := 0
  deriving Repr, Inhabited, BEq

protected def Workspace.add (left right : Workspace) : Workspace :=
  { peakAncillaQubits := max left.peakAncillaQubits right.peakAncillaQubits }

instance : Add Workspace where
  add := Workspace.add

structure Resources where
  oracle : OracleCalls := {}
  gates : GateCounts := {}
  workspace : Workspace := {}
  deriving Repr, Inhabited, BEq

protected def Resources.add (left right : Resources) : Resources :=
  { oracle := left.oracle + right.oracle
    gates := left.gates + right.gates
    workspace := left.workspace + right.workspace }

instance : Add Resources where
  add := Resources.add
```

## Literature-aligned plans

The constructors expose their assumptions rather than hiding them in a scalar. An alternating
QSVT phase sequence of length $`n`$ has $`n`$ total calls chosen from $`U`$ and $`U^\dagger`$;
the alternating order gives $`\lceil n/2 \rceil`$ calls to $`U`$ and $`\lfloor n/2 \rfloor`$ to
$`U^\dagger`$. It also needs $`n`$ calls to each projector-controlled NOT family, $`n`$ phase
gates, and one ancillary qubit. `csdGeneralUnitary` records the CSD paper's reported gate counts
for an unrestricted $`n`$-qubit unitary. It is a synthesis bound, not a claim that every IR
application has already been decomposed this way.

```lean
def Resources.qsvtAlternatingPhase (steps : Nat) : Resources :=
  { oracle :=
      { unitary := (steps + 1) / 2
        inverseUnitary := steps / 2
        projectorControlledNot := steps
        complementaryProjectorControlledNot := steps }
    gates := { oneQubit := steps }
    workspace := { peakAncillaQubits := 1 } }

def Resources.csdGeneralUnitary (qubits : Nat) : Resources :=
  { gates :=
      { cnot := 4 ^ qubits - 2 ^ (qubits + 1)
        oneQubit := 4 ^ qubits } }
```

## The complete report

`Report` is the one state accumulated by `CostM`. Its four top-level fields are stable ownership
boundaries: adding a new operation counter does not alter resource plans, and adding a new
hardware resource does not inflate the source-structural operation API. `charge` accepts a
partial report, so visitors state only the category they can justify.

```lean
structure Report where
  declarations : Declarations := {}
  shape : ProgramShape := {}
  operations : OperationCounts := {}
  resources : Resources := {}
  deriving Repr, Inhabited, BEq

protected def Report.add (left right : Report) : Report :=
  { declarations := left.declarations + right.declarations
    shape := left.shape + right.shape
    operations := left.operations + right.operations
    resources := left.resources + right.resources }

instance : Add Report where
  add := Report.add

abbrev CostM := StateM Report

def charge (delta : Report) : CostM Unit :=
  modify fun report => report + delta

end QASM.Cost
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
