    import LiterateLean
    import QASM.Basic

    open scoped LiterateLean

# QASM literate guide

This module is both documentation and checked Lean source. LiterateLean treats
the surrounding Markdown as prose while elaborating every fenced Lean block.
The examples therefore stay synchronized with the library API.

## Constructing a program

Importing `QASM.Basic` provides the `QASM` data model and the `qasm` term
syntax. A program is a list of statements, but the embedded syntax keeps the
program close to ordinary OpenQASM source.

```lean
namespace QASM.Guide

def bell : QASM.Program :=
  begin_qasm
    OPENQASM 3.0;
    include "stdgates.inc";

    qubit[2] q;
    bit[2] c;

    h q[0];
    cx q[0], q[1];
    measure q -> c;
  end_qasm
```

Register operations accept either an indexed element such as `q[0]` or a
whole register such as `q`. Register wide measurement pairs elements by their
zero based index, so both registers must have the same size.

## Validation and serialization

Validation checks the required version declaration, OpenQASM identifiers,
include filenames, unique positive register declarations, register kinds, and
index bounds. It reports the first problem as an `Except String Unit` value.
Serialization returns `Except String String` and only emits validated programs.

```lean
#eval bell.validate
#eval bell.toQasm
```

## Simulation

Simulation validates first and then interprets the supported `id`, `x`, `h`,
`z`, and `cx` gates. Measurement is an `IO` operation because it samples an
outcome and collapses the state vector.

Qubit zero is the least significant bit of a basis index. For two qubits, the
amplitude array is ordered as `|00>`, `|01>`, `|10>`, and `|11>`.

```lean
def runBell : IO (Except String QASM.ExecutionResult) :=
  simulate bell with {}

end QASM.Guide
```

Call `QASM.Guide.runBell` from an `IO` context to inspect the final amplitudes
and classical register snapshot. For a Bell state the two measured bits are
always correlated, although either `00` or `11` may be sampled.

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
