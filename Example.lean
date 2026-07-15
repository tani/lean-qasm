    import LiterateLean
    import QASM
    open scoped LiterateLean

# Bell-state example

This executable example exercises the public API end to end: inline OpenQASM lowers to
canonical IR, `#html` derives a static diagram from that IR, and the generated wrapper runs
through the deterministic trace backend.

## Declaring the circuit

The circuit allocates two qubits, applies Hadamard to the first, then entangles the pair
with controlled X. Explicit options demonstrate the configuration syntax even though this
program does not depend on classical target widths or the extended dialect.

```lean
qasm! Bell {
  OPENQASM 3.0;
  include "stdgates.inc";
  qubit[2] q;
  h q[0];
  cx q[0], q[1];
} using {
  target := { intWidth := 32, uintWidth := 32, floatWidth := 64, angleWidth := 64 }
  dialect := .extended
}

```

## Static inspection

HTML evaluation reads `Bell.program` only; it does not allocate qubits or execute gates.

```lean
#html Bell.program

```

## Deterministic execution

The trace backend assigns numeric qubits and records the backend effects produced by the
IR interpreter. Inspecting allocations keeps this example independent of any simulator or
device semantics.

```lean
def bellRun :=
  QASM.TraceBackend.run (Bell.execute (qasmM := QASM.TraceBackend.M) {})

#eval bellRun.2.allocations
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
