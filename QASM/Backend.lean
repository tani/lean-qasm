    import QASM.Runtime
    open scoped LiterateLean

# Deterministic trace backend

This module provides a reusable backend that records quantum operations and returns
deterministic measurement outcomes. It is an execution trace, not a physical simulator.

```lean
namespace QASM

namespace TraceBackend

inductive MeasurementPolicy where
  | parity
  | constant (value : Bool)
  deriving Repr, Inhabited, BEq

namespace MeasurementPolicy

def measure : MeasurementPolicy → Nat → Bool
  | .parity, qubit => qubit % 2 == 1
  | .constant value, _ => value

end MeasurementPolicy

structure State where
  nextQubit : Nat := 0
  scheduledMeasurements : Array Bool := #[]
  measurementCursor : Nat := 0
  measurementPolicy : MeasurementPolicy := .parity
  operations : Array String := #[]
  allocations : Array (Nat × Array Nat) := #[]
  applied : Array (Unitary Nat) := #[]
  observedMeasurements : Array (Nat × Bool) := #[]
  resets : Array Nat := #[]
  barriers : Array (Barrier Nat) := #[]

abbrev M := StateM State
abbrev Qubit := Nat
abbrev Error := Empty

def unitaryLabel : Unitary Nat → String
  | .U .. => "U"
  | .gphase _ => "gphase"
  | .named name _ _ => name
  | .sequence _ => "sequence"
  | .inverse operation => "inv:" ++ unitaryLabel operation
  | .power _ operation => "pow:" ++ unitaryLabel operation
  | .controlled _ controls operation =>
      s!"ctrl{controls.size}:" ++ unitaryLabel operation

def initial (scheduledMeasurements : Array Bool := #[])
    (measurementPolicy : MeasurementPolicy := .parity) : State :=
  { scheduledMeasurements, measurementPolicy }

def run (program : M α) (state : State := {}) : α × State :=
  Id.run (program.run state)

instance : QuantumBackend M Nat Empty where
  allocate count := do
    let state ← get
    let qubits := Array.range count |>.map (fun index => state.nextQubit + index)
    set { state with
      nextQubit := state.nextQubit + count
      operations := state.operations.push s!"allocate:{count}"
      allocations := state.allocations.push (count, qubits) }
    pure (.ok qubits)
  apply operation := do
    modify fun state => { state with
      operations := state.operations.push (unitaryLabel operation)
      applied := state.applied.push operation }
    pure (.ok ())
  measure qubit := do
    let state ← get
    let value := state.scheduledMeasurements[state.measurementCursor]?.getD
      (state.measurementPolicy.measure qubit)
    set { state with
      measurementCursor := state.measurementCursor + 1
      operations := state.operations.push s!"measure:{qubit}"
      observedMeasurements := state.observedMeasurements.push (qubit, value) }
    pure (.ok value)
  reset qubit := do
    modify fun state => { state with
      operations := state.operations.push s!"reset:{qubit}"
      resets := state.resets.push qubit }
    pure (.ok ())
  barrier barrier := do
    modify fun state => { state with
      operations := state.operations.push "barrier"
      barriers := state.barriers.push barrier }
    pure (.ok ())

end TraceBackend

end QASM
```
