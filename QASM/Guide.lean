    import LiterateLean
    import QASM

    open scoped LiterateLean

# QASM to Lean 4 elaboration guide

This module is documentation and checked Lean source. The embedded block is a
raw `String`; `elab_qasm` parses it at compile time and adds ordinary Lean
declarations to the environment.

```lean
namespace QASM.Guide

def controlSource : String :=
  begin_qasm
OPENQASM 3.0;
input int[32] limit;
output int[32] result;
int[32] value = 0;
for uint i in [0:limit] {
  if (i == 2) { continue; }
  value += 1;
}
while (value < 5) { value += 1; }
result = value;
  end_qasm

elab_qasm NativeControl (controlSource)
```

The generated input/output structures form the program boundary. Internally,
QASM structured control is emitted as Lean `for`, `if`, and `while` code.

Quantum statements use the same path, but execution is parameterized by
`QuantumBackend`. User gates and subroutines become generated Lean functions;
primitive gates, measurement, reset, and barriers cross the backend interface.

```lean
def bellSource : String :=
  begin_qasm
OPENQASM 3.0;
include "stdgates.inc";
gate bell_pair a, b { h a; cx a, b; }
output bit[2] result;
qubit[2] q;
bit[2] measured;
bell_pair q[0], q[1];
measured = measure q;
result = measured;
  end_qasm

elab_qasm Bell (bellSource)

end QASM.Guide
```

Calibration, target-relative timing, extern calls, and physical qubits are
accepted by the standalone frontend but deliberately rejected by portable
elaboration because their meaning depends on the target backend. SI duration
literals and ordinary duration arithmetic remain portable Lean values.

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
