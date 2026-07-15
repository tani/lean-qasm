    import LiterateLean
    import QASM
    open scoped LiterateLean

# Elaboration command matrix

This compilation-only matrix keeps representative `qasm!` declarations in one module.
Each declaration must parse, type-check, lower to `QASM.IR.Program`, and generate its typed
boundary wrapper. Runtime behavior is asserted separately in `Tests.Main`.

## Classical control and typed input

These programs cover structured process IR and native Lean types at the generated I/O
boundary. Their historical `Native` names identify fixtures; execution itself uses the
canonical IR interpreter.

```lean
qasm! NativeControl {
  OPENQASM 3.0;
  output int[32] result;
  int[32] x = 0;
  for uint i in [0:3] {
    if (i == 2) { continue; }
    x += 1;
  }
  while (x < 10) {
    x += 1;
    if (x == 5) { break; }
  }
  result = x;
}

qasm! NativeInput {
  OPENQASM 3.0;
  input int[32] value;
  output int[32] result;
  result = value + 1;
}

```

## Quantum effects and callable declarations

The next declarations cover backend operations, user gates, subroutine calls, mutable
array-reference writeback, and recursive include expansion.

```lean
qasm! PortableQuantum {
  OPENQASM 3.0;
  include "stdgates.inc";
  const int[32] repetitions = 1;
  gate pair a, b {
    for uint i in [0:repetitions - 1] { h a; cx a, b; }
  }
  output bit[2] result;
  qubit[2] q;
  bit[2] c;
  let selected = q[{0, 1}];
  pair q[0], q[1];
  inv @ cx q[0], q[1];
  ctrl @ x selected[0], selected[1];
  barrier q;
  reset q[0];
  c = measure q;
  result = c;
}

qasm! NativeSubroutine {
  OPENQASM 3.0;
  def bump(int[32] value) -> int[32] {
    value += 1;
    return value;
  }
  output int[32] result;
  result = bump(20) + bump(20);
}

qasm! MutableArrayReference {
  OPENQASM 3.0;
  def update(mutable array[int[32], 2] values) {
    values[0] = 20;
    values[1] = 22;
  }
  output int[32] result;
  array[int[32], 2] values = {0, 0};
  update(values);
  result = values[0] + values[1];
}

```

## Files, arrays, metadata, and diagrams

File elaboration derives a namespace from the source path. The remaining programs exercise
fixed-shape arrays, retained directives, and static diagram regions without executing the
program while rendering.

```lean
qasm! "Tests/Fixtures/Elab/file_program.qasm"

qasm! NativeArrays {
  OPENQASM 3.0;
  output int[32] sum;
  output int[32] second_dimension;
  array[int[32], 4] values = {5, 6, 7, 8};
  array[int[32], 2, 3] matrix;
  values[0:1] = {20, 22};
  sum = values[0] + values[1];
  second_dimension = sizeof(matrix, 1);
}

qasm! MetadataProgram {
  OPENQASM 3.0;
  pragma compiler optimize
  @tool.note preserve
  int[32] value = 1;
}

qasm! DiagramProgram {
  OPENQASM 3.0;
  include "stdgates.inc";
  bit[2] result;
  qubit[2] q;
  for uint i in [0:1] {
    h q[i];
  }
  if (true) {
    cx q[0], q[1];
  } else {
    reset q;
  }
  negctrl @ x q[0], q[1];
  swap q[0], q[1];
  result = measure q;
}

```

## Scalar and extended-language coverage

Complex values, duration arithmetic, typed arrays, casts, scalar iteration, and opt-in
`switch` ensure target-resolved types survive lowering into the interpreter boundary.

```lean
qasm! NativeComplex {
  OPENQASM 3.0;
  output float[64] real_part;
  output float[64] imaginary_part;
  complex value = 2.5 + 3.5im;
  real_part = real(value);
  imaginary_part = imag(value);
}

qasm! ExtendedSwitch {
  OPENQASM 3.0;
  output int[32] result;
  int[32] value = 2;
  switch (value) {
    case 1 { result = 10; }
    case 2 { result = 20; }
    default { result = 30; }
  }
} using { dialect := .extended }

qasm! NativeDuration {
  OPENQASM 3.0;
  output duration elapsed;
  elapsed = 5ns + 2us;
}

qasm! TypedArrayIO {
  OPENQASM 3.0;
  input array[int[8], 2] values;
  output array[int[8], 2] result;
  result = values;
}

qasm! NativeArrayCast {
  OPENQASM 3.0;
  output array[uint[8], 2] result;
  array[int[16], 2] values = {20, 22};
  result = array[uint[8], 2](values);
}

qasm! NativeScalarFor {
  OPENQASM 3.0;
  output float[64] result;
  result = 0.0;
  for float[64] value in {20, 22} {
    result += value;
  }
}

```

## Modified gates, recursion, and measurement

These declarations stress complete-gate modifiers, recursive IR calls, indexed
measurement targets, and deterministic scheduled measurement results.

```lean
qasm! ModifiedUserGate {
  OPENQASM 3.0;
  include "stdgates.inc";
  gate pair a, b { h a; x b; }
  qubit[3] q;
  ctrl @ pair q[0], q[1], q[2];
  inv @ pair q[1], q[2];
}

qasm! RecursiveSubroutine {
  OPENQASM 3.0;
  def factorial(int[32] value) -> int[32] {
    if (value <= 1) { return 1; }
    return value * factorial(value - 1);
  }
  output int[32] result;
  result = factorial(5);
}

qasm! IndexedMeasurement {
  OPENQASM 3.0;
  output bit[2] result;
  qubit[2] q;
  bit[2] measured;
  measure q[1] -> measured[0];
  measured[1] = measure q[1];
  result = measured;
}

qasm! ScheduledMeasurements {
  OPENQASM 3.0;
  output bit[3] result;
  qubit[3] q;
  result = measure q;
}

```

## Persistent declaration checks

Every command above must expose a canonical program value. These checks deliberately say
nothing about per-program native control flow: `execute` is the interpreter wrapper tested
elsewhere.

```lean
#check (NativeControl.program : QASM.IR.Program)
#check (NativeInput.program : QASM.IR.Program)
#check (PortableQuantum.program : QASM.IR.Program)
#check (NativeSubroutine.program : QASM.IR.Program)
#check (MutableArrayReference.program : QASM.IR.Program)
#check (file_program.program : QASM.IR.Program)
#check (NativeArrays.program : QASM.IR.Program)
#check (MetadataProgram.program : QASM.IR.Program)
#check (DiagramProgram.program : QASM.IR.Program)
#check (NativeComplex.program : QASM.IR.Program)
#check (ExtendedSwitch.program : QASM.IR.Program)
#check (NativeDuration.program : QASM.IR.Program)
#check (TypedArrayIO.program : QASM.IR.Program)
#check (NativeArrayCast.program : QASM.IR.Program)
#check (NativeScalarFor.program : QASM.IR.Program)
#check (ModifiedUserGate.program : QASM.IR.Program)
#check (RecursiveSubroutine.program : QASM.IR.Program)
#check (IndexedMeasurement.program : QASM.IR.Program)
#check (ScheduledMeasurements.program : QASM.IR.Program)
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
