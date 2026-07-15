    import LiterateLean
    import QASM
    open scoped LiterateLean

# Inspecting a generated IR declaration

This small inspection program checks the public shape of a `qasm!` expansion without
claiming that the source body becomes native Lean control flow. The declaration stores
canonical IR and the wrapper delegates execution to the shared interpreter.

```lean
qasm! IRDeclared {
  OPENQASM 3.0;
  include "stdgates.inc";
  output float[64] result;
  qubit[2] q;
  h q[0];
  cx q[0], q[1];
  result = 2.5;
}

```

## Generated boundary

The checks expose the persistent IR value and typed execution wrapper. The final
evaluation inspects declaration metadata only and performs no quantum effects.

```lean
#check (IRDeclared.program : QASM.IR.Program)
#check IRDeclared.execute
#eval (IRDeclared.program.gates.size, IRDeclared.program.outputs.size,
  IRDeclared.program.exactEq IRDeclared.program)
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
