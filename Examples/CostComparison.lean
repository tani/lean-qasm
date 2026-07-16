    import LiterateLean
    import QASM
    open scoped LiterateLean

# Static cost comparison for constrained connectivity

This executable example compares two canonical OpenQASM programs that implement the same
logical operation: prepare `q[0]` in the `|+⟩` state and apply a controlled X from `q[0]` to
`q[2]`. The direct form assumes that the hardware can connect those two qubits. The routed
form assumes that only adjacent pairs are usable, so it mediates the logical controlled X
through `q[1]` while restoring that intermediate qubit.

The purpose is not to predict a device's elapsed time. `QASM.Cost.measure` is a static,
source-structural measure: it makes the extra primitive applications introduced by routing
visible before choosing a backend or executing the circuit.

```mermaid
flowchart LR
    q0a["q[0]"] --> Direct["direct cx"] --> q2a["q[2]"]
    q0b["q[0]"] --> Left["cx 0,1"] --> Middle["cx 1,2"] --> Right["restore q[1]"] --> q2b["q[2]"]
```

## A direct two-qubit interaction

When the target hardware exposes the edge `q[0] → q[2]`, preparation and the desired
interaction require two gate applications.

```lean
qasm! DirectRemoteCNOT {
  OPENQASM 3.0;
  include "stdgates.inc";
  qubit[3] q;
  h q[0];
  cx q[0], q[2];
}

#html DirectRemoteCNOT.program
```

## Routing through an adjacent qubit

The following four controlled-X operations implement the remote controlled X using only
the edges `q[0] → q[1]` and `q[1] → q[2]`. Over bit values `a`, `b`, and `c`, the sequence
has the invariant that `q[1]` is restored and the target becomes `c ⊕ a`.

```math
(a,b,c) \longmapsto (a,b,c \mathbin{\oplus} a).
```

```lean
qasm! RoutedRemoteCNOT {
  OPENQASM 3.0;
  include "stdgates.inc";
  qubit[3] q;
  h q[0];
  cx q[0], q[1];
  cx q[1], q[2];
  cx q[0], q[1];
  cx q[1], q[2];
}

#html RoutedRemoteCNOT.program
```

## Inspecting the decision-relevant difference

The fixed `qasm!` declarations lower to canonical `QASM.IR.Program` values. The metric
projection counts one allocation in each program, but it exposes three extra gate
applications in the routed form. This is exactly the structural difference a mapper or a
human circuit author needs to notice before assigning hardware-specific weights.

```lean
def directMetrics := QASM.Cost.measure DirectRemoteCNOT.program
def routedMetrics := QASM.Cost.measure RoutedRemoteCNOT.program

example : directMetrics.allocations = 1 := by native_decide
example : routedMetrics.allocations = 1 := by native_decide
example : directMetrics.allocatedQubits = 3 := by native_decide
example : routedMetrics.allocatedQubits = 3 := by native_decide
example : directMetrics.applications = 2 := by native_decide
example : routedMetrics.applications = 5 := by native_decide

example: directMetrics.applications < routedMetrics.applications := by native_decide

#eval directMetrics
#eval routedMetrics

```

The comparison deliberately does not call `execute`: static metrics answer a different
question from simulation. They identify the resource-shape penalty of routing, while a
backend-specific model can later turn that difference into depth, fidelity, or duration.

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
