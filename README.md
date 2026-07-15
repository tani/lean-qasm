# LeanQASM

LeanQASM is a compile-time OpenQASM 3.0 to Lean 4 elaborator. It parses the
OpenQASM grammar, emits native Lean definitions for the portable language, and
keeps device behavior behind a small `QuantumBackend` interface.

## Build and test

```sh
lake build
lake test
```


## The `qasm!` interface

Inline programs name their generated Lean namespace explicitly. The OpenQASM body is
scanned as a balanced raw block, so nested braces, strings, and comments are not tokenized
as Lean. `using` accepts an ordinary `QASM.ElabOptions` term when configuration is
needed; omitting it selects the portable OpenQASM 3.0 defaults.

Inline bodies conventionally use two additional spaces relative to the surrounding
`qasm!` command.

```lean
import QASM

open QASM

qasm! Example {
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
```

The command creates:

- `Example.Inputs` and `Example.Outputs`, with native typed fields such as
  `QASM.SInt 32`, `BitVec n`, `Float`, or `QASM.FixedArray element shape`;
- `Example.program : QASM.CheckedProgramInfo`, containing target and source
  metadata plus a static `.diagram`;
- native Lean functions for QASM `def` and user-defined `gate` declarations;
- `Example.run`, whose `for`, `if`, `while`, `switch`, `break`, and `continue`
  are generated as Lean control flow.

```lean
#check Example.Inputs
#check Example.Outputs
#check Example.program
#check Example.run
```

### Circuit diagrams

`#html Example.program` renders the program's static circuit diagram in the Lean
infoview. For example:

```lean
qasm! Bell {
  OPENQASM 3.0;
  include "stdgates.inc";
  qubit[2] q;
  h q[0];
  cx q[0], q[1];
}

#html Bell.program
```

Diagrams are static source views. They show every control-flow branch and loop body
once; gate and quantum-subroutine calls remain opaque and named. Exact controlled gates
and swaps use conventional glyphs, while other or ineligible operations use labeled
boxes. Dynamic target sets are marked approximately. Rendering never executes inputs or
measurements, chooses outcomes, or selects a control-flow path.

Target widths and the opt-in extended dialect are supplied directly after `using`. Strict
OpenQASM 3.0 is the default; `switch` and `nop` require `.extended`.

```lean
qasm! ExtendedExample {
  OPENQASM 3.0;
  output int[32] result;
  switch (1) {
    case 1 { result = 42; }
  }
} using {
  target := { intWidth := 32, uintWidth := 32, floatWidth := 64, angleWidth := 64 }
  dialect := .extended
}
```

The file form resolves its path relative to the current Lean source file. It derives the
generated namespace from the sanitized file stem: the example below creates `example.run`.
Nested `include` statements are resolved relative to their containing file and then through
`ElabOptions.includePaths`; `stdgates.inc` is intrinsic.

```lean
qasm! "circuits/example.qasm"
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
