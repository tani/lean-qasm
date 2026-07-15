    import LiterateLean
    import QASM
    import QASM.Emit.OpenQASM
    import QASM.IR.Equiv
    open scoped LiterateLean

# Canonical emitter round trip

This executable smoke scenario starts from an elaborated program, emits deterministic
OpenQASM, reparses and lowers that text, then compares the two canonical programs under
both alpha and semantic-shape equality.

## Source program

The fixture includes a user gate, a standard gate, a modifier, classical output, and
measurement so circuit declarations and process effects both cross the round-trip
boundary.

```lean
open QASM

qasm! EmitterRoundtrip {
  OPENQASM 3.0;
  include "stdgates.inc";
  const float[64] theta0 = 3.141592653589793;
  gate pair(theta) a, b { rx(theta) a; ctrl @ x a, b; }
  output bit[2] result;
  qubit[2] q;
  pair(theta0 / 2.0) q[0], q[1];
  result = measure q;
}

```

## Reparse and lower

Emission preserves the resolved target widths in the persistent program, so the second
type-analysis pass reuses those widths. Source origins and concrete IDs may differ after
reparsing; the equality relations define which differences are acceptable.

```lean
private def emitted := QASM.Emit.OpenQASM.emit EmitterRoundtrip.program

private def roundtrip : Except String QASM.IR.Program := do
  let parsed ← QASM.parse emitted |>.mapError toString
  let target : QASM.TargetConfig := {
    intWidth := EmitterRoundtrip.program.target.intWidth
    uintWidth := EmitterRoundtrip.program.target.uintWidth
    floatWidth := EmitterRoundtrip.program.target.floatWidth
    angleWidth := EmitterRoundtrip.program.target.angleWidth }
  let analysis ← QASM.analyzeTypes target parsed |>.mapError reprStr
  QASM.Lowering.program parsed analysis |>.mapError (·.message)

```

## Executable equivalence check

Both comparisons must hold. A mismatch prints the original and reconstructed IR so the
first structural divergence is available in the build output.

```lean
#eval match roundtrip with
  | .ok program =>
      if EmitterRoundtrip.program.alphaEq program &&
          EmitterRoundtrip.program.semanticShapeEq program then
        true
      else
        panic! s!"roundtrip mismatch:\n{reprStr EmitterRoundtrip.program}\n{reprStr program}"
  | .error message => panic! message
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
