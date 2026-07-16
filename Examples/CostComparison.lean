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
applications and three extra literal CNOT gates in the routed form. This is exactly the
structural difference a mapper or a human circuit author needs to notice before assigning
hardware-specific weights. `resources.gates.oneQubit` and `resources.gates.cnot` are not a decomposition pass: they
only classify primitive nodes that are already visible in the canonical IR.

```lean
def directMetrics := QASM.Cost.measure DirectRemoteCNOT.program
def routedMetrics := QASM.Cost.measure RoutedRemoteCNOT.program

example : directMetrics.shape.allocationSites = 1 := by decide
example : routedMetrics.shape.allocationSites = 1 := by decide
example : directMetrics.shape.allocatedQubits = 3 := by decide
example : routedMetrics.shape.allocatedQubits = 3 := by decide
example : directMetrics.operations.applications = 2 := by decide
example : routedMetrics.operations.applications = 5 := by decide
example : directMetrics.resources.gates.oneQubit = 1 := by decide
example : routedMetrics.resources.gates.oneQubit = 1 := by decide
example : directMetrics.resources.gates.cnot = 1 := by decide
example : routedMetrics.resources.gates.cnot = 4 := by decide

example : directMetrics.operations.applications < routedMetrics.operations.applications := by decide
example : directMetrics.resources.gates.cnot < routedMetrics.resources.gates.cnot := by decide

#eval directMetrics
#eval routedMetrics

```

The comparison deliberately does not call `execute`: static metrics answer a different
question from simulation. They identify the resource-shape penalty of routing, while a
backend-specific model can later turn that difference into depth, fidelity, or duration.

## Keeping algorithmic and synthesized costs distinct

The same resource vector can document a cost model before an OpenQASM program exists. For an
alternating QSVT sequence of length five [^gilyen2018], the unitary calls alternate as three uses
of $`U`$ and two uses of $`U^\dagger`$; each projector-controlled NOT family and the phase-gate
family occur five times, and the construction requires one ancillary qubit. These are algorithmic
costs, so they should not be mistaken for a CNOT count without an implementation of `U` and its
projector oracles.

```lean
def qsvtFiveSteps := QASM.Cost.Resources.qsvtAlternatingPhase 5

example : qsvtFiveSteps.oracle.unitary = 3 := by decide
example : qsvtFiveSteps.oracle.inverseUnitary = 2 := by decide
example : qsvtFiveSteps.oracle.projectorControlledNot = 5 := by decide
example : qsvtFiveSteps.oracle.complementaryProjectorControlledNot = 5 := by decide
example : qsvtFiveSteps.gates.oneQubit = 5 := by decide
example : qsvtFiveSteps.workspace.peakAncillaQubits = 1 := by decide
```

Cosine-sine decomposition instead starts with an unrestricted $`n`$-qubit unitary and reports
the synthesized elementary-gate totals [^mottonen2004]. For three qubits its formula gives 48
CNOTs and 64 one-qubit gates. This is a whole-unitary synthesis result; it is not comparable
directly with the five QSVT steps above, because their `U` calls still stand for unspecified
subcircuits.

```lean
def csdThreeQubits := QASM.Cost.Resources.csdGeneralUnitary 3

example : csdThreeQubits.gates.cnot = 48 := by decide
example : csdThreeQubits.gates.oneQubit = 64 := by decide

#eval qsvtFiveSteps
#eval csdThreeQubits
```

[^gilyen2018]: A. Gilyén, Y. Su, G. H. Low, and N. Wiebe, "Quantum singular value transformation
    and beyond: Exponential improvements for quantum matrix arithmetics," arXiv:1806.01838, 2018.
    [Online]. Available: <https://arxiv.org/abs/1806.01838>.
[^mottonen2004]: M. Möttönen, J. J. Vartiainen, V. Bergholm, and M. M. Salomaa, "Quantum circuits
    for general multi-qubit gates," arXiv:quant-ph/0404089, 2004. [Online]. Available:
    <https://arxiv.org/abs/quant-ph/0404089>.

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
