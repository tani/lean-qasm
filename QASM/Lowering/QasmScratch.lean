    import LiterateLean
    import QASM.Elab
    open scoped LiterateLean

# Embedded declaration smoke scenario


This scenario exercises the `qasm!` command boundary rather than calling lowering
directly. It checks that elaboration persists canonical IR, exposes the typed execution
wrapper, and retains gate and output declarations for inspection.

```lean
open QASM

qasm! IRDeclared {
  OPENQASM 3.0;
  include "stdgates.inc";
  output float[64] result;
  qubit[2] q;
  h q[0];
  cx q[0], q[1];
  result = 2.5;
}

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
