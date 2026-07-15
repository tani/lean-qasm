    import QASM.Runtime
    open scoped LiterateLean

# Deterministic trace backend

A generated `qasm!` program does not know how qubits are represented or how a
quantum operation is executed. It knows only the `QuantumBackend` interface from
`QASM.Runtime`. This module supplies one small, reusable implementation of that
interface.

The implementation is deliberately a *trace backend*. It allocates stable numeric
qubit identifiers, records every effect in execution order, and chooses measurement
results deterministically. It does not maintain amplitudes, evolve a quantum state,
or approximate a physical device. This narrower contract makes it useful for examples,
tests, and inspection of generated programs.

We keep the backend under `QASM.TraceBackend`, while opening `QASM` first so the
runtime types can be used without repeating their qualifier.

```lean
namespace QASM

namespace TraceBackend
```

## Choosing measurement results

Measurement is the only backend operation that must synthesize a value consumed by
the generated classical program. A trace backend therefore needs an explicit rule for
choosing that value.

The default `parity` policy returns `false` for even qubit identifiers and `true` for
odd identifiers. It is deterministic while still making adjacent qubits distinguishable.
The `constant` policy is useful when every unscheduled measurement should take the same
branch.

```lean
inductive MeasurementPolicy where
  | parity
  | constant (value : Bool)
  deriving Repr, Inhabited, BEq
```

The policy interpreter is intentionally separate from the backend instance. Besides
keeping the instance readable, this gives callers a direct, pure description of the
fallback behavior. Scheduled outcomes, introduced below, take precedence over this
function.

```lean
namespace MeasurementPolicy

def measure : MeasurementPolicy → Nat → Bool
  | .parity, qubit => qubit % 2 == 1
  | .constant value, _ => value

end MeasurementPolicy
```

## State as both configuration and trace

One `State` value contains two kinds of information:

* **Configuration** tells future measurements what to return. The cursor consumes
  `scheduledMeasurements` from left to right; after the schedule is exhausted,
  `measurementPolicy` supplies the result.
* **Execution state** assigns fresh qubit identifiers and retains what has already
  happened.

The `operations` array is the compact, chronological view intended for quick assertions
and human inspection. The remaining arrays preserve structured data: allocation results,
complete `Unitary` trees, measured values, reset targets, and complete barriers. Keeping
both views avoids forcing callers to parse display labels when they need semantic data.

`nextQubit` is always the first unallocated identifier. Since allocation returns a
contiguous range and then advances this counter, identifiers are stable for the lifetime
of a run. `measurementCursor` advances once for every measurement request, including
requests that fall back to the policy.

```lean
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
```

## Runtime types

The backend is pure: `M` is just `StateM State`, so running a program requires no
`IO`. Qubits are natural-number handles. `Error` is `Empty` because every operation
defined here succeeds; generated programs can still report their own `RunError` cases
such as an invalid index or shape mismatch.

These abbreviations also make the intended instantiation concise:
`Example.run (qasmM := TraceBackend.M) inputs`.

```lean
abbrev M := StateM State
abbrev Qubit := Nat
abbrev Error := Empty
```

## Compact unitary labels

`Unitary` retains the complete portable operation tree, and `State.applied` stores that
tree unchanged. For the chronological `operations` view we additionally compute a short
label.

Primitive `U` and global phase operations have fixed names. Source-level named operations
keep their name. A sequence is summarized as `"sequence"` rather than recursively
flattened, while inverse, power, and control modifiers prefix the label of the operation
they wrap. The control label records the number of controls; the complete polarities,
controls, parameters, and targets remain available in `State.applied`.

```lean
def unitaryLabel : Unitary Nat → String
  | .U .. => "U"
  | .gphase _ => "gphase"
  | .named name _ _ => name
  | .sequence _ => "sequence"
  | .inverse operation => "inv:" ++ unitaryLabel operation
  | .power _ operation => "pow:" ++ unitaryLabel operation
  | .controlled _ controls operation =>
      s!"ctrl{controls.size}:" ++ unitaryLabel operation
```

## Constructing and running traces

`initial` changes only measurement configuration. All trace arrays and counters use the
defaults declared by `State`, so each call starts with a clean execution history.

`run` unwraps the pure state monad and returns the program result beside its final trace.
Its optional state argument supports both the common empty-state case and explicitly
configured runs:

```text
let state := TraceBackend.initial #[true, false] (.constant false)
let (result, trace) := TraceBackend.run program state
```

```lean
def initial (scheduledMeasurements : Array Bool := #[])
    (measurementPolicy : MeasurementPolicy := .parity) : State :=
  { scheduledMeasurements, measurementPolicy }

def run (program : M α) (state : State := {}) : α × State :=
  Id.run (program.run state)
```

## Implementing `QuantumBackend`

The instance follows a single rule for every method: update the structured trace and the
chronological label together, then return success.

* `allocate` returns a fresh contiguous range and records both the requested count and
  the resulting handles.
* `apply` stores the complete unitary tree as well as its compact label.
* `measure` first looks at the next scheduled result. If none exists, it invokes the
  fallback policy. The exact `(qubit, value)` pair is retained.
* `reset` records its target.
* `barrier` uses one compact `"barrier"` label, while preserving the complete `Barrier`
  value separately.

No method can produce the backend error branch because the error type is `Empty`.

```lean
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
```

The namespace closures are executable Lean as well, so they live in their own final code
block rather than being hidden in prose.

```lean
end TraceBackend

end QASM
```
