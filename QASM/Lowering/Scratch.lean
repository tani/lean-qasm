    import LiterateLean
    import QASM.Lowering.Program
    open scoped LiterateLean

# Direct lowering smoke scenario


This scenario exercises the public lowering function without command elaboration. The
source combines includes, gates, subroutines, arrays, measurement, branches, and loops so
one evaluation checks that all major declaration and process categories reach canonical
IR together.

```lean
open QASM

private def source := String.intercalate "\n" [
  "OPENQASM 3.0;",
  "include \"stdgates.inc\";",
  "const int[32] repetitions = 2;",
  "gate pair a, b { for uint i in [0:repetitions - 1] { h a; cx a, b; } }",
  "def bump(int[32] value) -> int[32] { return value + 1; }",
  "output bit[2] result;",
  "qubit[2] q;",
  "bit[2] c;",
  "array[int[32], 4] values = {0, 1, 2, 3};",
  "pair q[0], q[1];",
  "c = measure q;",
  "if (c[0]) { reset q[0]; }",
  "for uint i in [0:1] { values[i] += bump(1); }",
  "result = c;"
]

private def lowered : Except String QASM.IR.Program := do
  let parsed ← QASM.parse source |>.mapError toString
  let analysis ← QASM.analyzeTypes {} parsed |>.mapError reprStr
  QASM.Lowering.program parsed analysis
    { origins := #[("<smoke>", hash source)] } |>.mapError (·.message)

#eval match lowered with
  | .ok program => (program.gates.size, program.subroutines.size,
      program.outputs.size, program.exactEq program, (reprStr program.body).length != 0)
  | .error message => panic! message
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
