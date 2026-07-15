# LeanQASM

LeanQASM is a compile-time OpenQASM 3.0 to Lean 4 elaborator. It parses the
OpenQASM grammar, emits native Lean definitions for the portable language, and
keeps device behavior behind a small `QuantumBackend` interface.

## Build and test

```sh
lake build
lake test
```


## Quotation interface

Use `qasm% { ... }` for inline OpenQASM source. The quotation is a Lean term of type `String`; nested braces, strings, and comments are preserved. `qasmFile% "path.qasm"` provides a path literal for file-oriented tooling.

```lean
def source : String := qasm% {
OPENQASM 3.0;
if (true) { x; }
}
```

## Embedded source and elaboration

`qasm% { ... }` is a raw Lean term of type `String`. The text between
the delimiter lines is retained verbatim, including comments and indentation,
and can be stored, transformed, parsed, or passed to a named `qasm%` command.

```lean
import QASM

open QASM

def source : String :=
  qasm% {
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
  }

qasm% Example from source
```

The command creates:

- `Example.Inputs` and `Example.Outputs`, with native typed fields such as
  `QASM.SInt 32`, `BitVec n`, `Float`, or `QASM.FixedArray element shape`;
- `Example.program : QASM.CheckedProgramInfo`, containing target and source
  metadata;
- native Lean functions for QASM `def` and user-defined `gate` declarations;
- `Example.run`, whose `for`, `if`, `while`, `switch`, `break`, and `continue`
  are generated as Lean control flow.

```lean
#check Example.Inputs
#check Example.Outputs
#check Example.program
#check Example.run
```

Use `using` for target widths and the opt-in extended dialect. Strict
OpenQASM 3.0 is the default; `switch` and `nop` require `.extended`.

```lean
def options : QASM.ElabOptions := {
  target := { intWidth := 32, uintWidth := 32, floatWidth := 64, angleWidth := 64 }
  dialect := .extended
}

qasm% Configured from source using options
```

Files are resolved relative to the current Lean source file. Nested QASM
`include` statements are expanded relative to their containing file and then
through `ElabOptions.includePaths`. `stdgates.inc` is intrinsic.

```lean
qasmFile% FromFile "circuits/example.qasm"
```

## Backend boundary

Generated programs are polymorphic over a monad, qubit representation, and
backend error type:

```lean
class QASM.QuantumBackend (m : Type u -> Type v) (Qubit Error : outParam (Type u)) where
  allocate : Nat -> m (Except Error (Array Qubit))
  apply : QASM.Unitary Qubit -> m (Except Error Unit)
  measure : Qubit -> m (Except Error Bool)
  reset : Qubit -> m (Except Error Unit)
  barrier : QASM.Barrier Qubit -> m (Except Error Unit)
```

Qubit allocation, gates and modifiers, measurement, reset, and barriers are
delegated through this interface. Classical expressions, arrays and slices,
subroutines, aliases, casts, complex values, ranges, and structured control
flow remain portable generated Lean code.

OpenQASM features whose meaning is explicitly backend-dependent are parsed and
represented by the frontend, but portable elaboration rejects them with a
compile-time diagnostic. These are `extern`, calibration/OpenPulse,
target-relative timing (`dt`, `delay`, designators, `durationof`, `stretch`),
and physical `$n` qubits. SI duration literals and classical duration arithmetic
remain portable. Pragmas and annotations are retained in `CheckedProgramInfo`.

User gates, including modified user gates, are lowered to backend-independent
`Unitary` trees. The intrinsic standard library is enabled by
`include "stdgates.inc";` and is decomposed to `U`, `gphase`, sequences, and
modifiers rather than delegated as opaque target gate names.

## Standalone frontend

Parsing and normalized printing remain available without elaborating a
program:

```lean
match QASM.parse "OPENQASM 3.0; qubit q; h q;" with
| .ok program => IO.println program.toQasm
| .error error => IO.eprintln s!"{error}"

#check QASM.parseFile
```

The exact support matrix, backend boundary, and remaining semantic limitations
are tracked in [CONFORMANCE.md](CONFORMANCE.md).

## Acknowledgements

This project is developed under the umbrella of the AutoRes Lean-Quantum
Project.
