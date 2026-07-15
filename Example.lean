import QASM

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

#html Bell.program

def bellRun :=
  QASM.TraceBackend.run (Bell.execute (qasmM := QASM.TraceBackend.M) {})

#eval bellRun.2.operations
