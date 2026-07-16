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

## Resource vectors for two levels of cost

`Resources` keeps the two resource levels used by the accompanying cost literature separate.
The concrete level records CNOT and elementary one-qubit gates, as in cosine-sine decomposition
(CSD) circuit synthesis. The abstract level records calls to a unitary block, its inverse, and
the two projector-controlled NOT operations used by quantum singular value transformation
(QSVT). Neither level is silently converted into the other: a backend or synthesis pass must
provide that conversion.

All operation counters accumulate under sequential composition, whereas `peakAncillas` is a
space requirement and therefore takes a maximum. This is deliberately a resource summary, not a
device-duration prediction: it contains no calibration, scheduling, or connectivity assumptions.

```lean
namespace QASM.Cost

open QASM.IR

structure Resources where
  unitaryCalls : Nat := 0
  inverseUnitaryCalls : Nat := 0
  projectorControlledNots : Nat := 0
  complementaryProjectorControlledNots : Nat := 0
  cnotGates : Nat := 0
  oneQubitGates : Nat := 0
  otherPrimitiveGates : Nat := 0
  peakAncillas : Nat := 0
  deriving Repr, Inhabited, BEq

protected def Resources.add (left right : Resources) : Resources :=
  { unitaryCalls := left.unitaryCalls + right.unitaryCalls
    inverseUnitaryCalls := left.inverseUnitaryCalls + right.inverseUnitaryCalls
    projectorControlledNots := left.projectorControlledNots + right.projectorControlledNots
    complementaryProjectorControlledNots :=
      left.complementaryProjectorControlledNots + right.complementaryProjectorControlledNots
    cnotGates := left.cnotGates + right.cnotGates
    oneQubitGates := left.oneQubitGates + right.oneQubitGates
    otherPrimitiveGates := left.otherPrimitiveGates + right.otherPrimitiveGates
    peakAncillas := max left.peakAncillas right.peakAncillas }

instance : Add Resources where
  add := Resources.add

```

## Literature-aligned resource plans

The constructors below expose the assumptions instead of hiding them in a scalar. An alternating
QSVT phase sequence of length $`n`$ has $`n`$ total calls chosen from $`U`$ and $`U^\dagger`$;
the alternating order gives $`\lceil n/2 \rceil`$ calls to $`U`$ and $`\lfloor n/2 \rfloor`$ to
$`U^\dagger`$. It also needs $`n`$ calls to each projector-controlled NOT family, $`n`$ phase
gates, and one ancillary qubit. `csdGeneralUnitary` records the CSD paper's reported gate counts
for an unrestricted $`n`$-qubit unitary. It is a synthesis bound, not a claim that every IR
application has already been decomposed this way.

```lean
def Resources.qsvtAlternatingPhase (steps : Nat) : Resources :=
  { unitaryCalls := (steps + 1) / 2
    inverseUnitaryCalls := steps / 2
    projectorControlledNots := steps
    complementaryProjectorControlledNots := steps
    oneQubitGates := steps
    peakAncillas := 1 }

def Resources.csdGeneralUnitary (qubits : Nat) : Resources :=
  { cnotGates := 4 ^ qubits - 2 ^ (qubits + 1)
    oneQubitGates := 4 ^ qubits }

```

## Structural metrics

`Metrics.resources` is filled only when the canonical IR makes a primitive classification
observable. In particular, it can count a literal CNOT or a literal one-qubit primitive, but it
does not guess that an arbitrary user gate is a QSVT block or expand calls recursively. The
generic `applications` counter remains the complete source-structural measure; `resources` is a
more specific, intentionally partial refinement.

```lean
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
  resources : Resources := {}
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
    unsupported := left.unsupported + right.unsupported
    resources := left.resources + right.resources }

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
