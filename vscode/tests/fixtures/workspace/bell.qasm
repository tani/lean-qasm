OPENQASM 3.0;
include "stdgates.inc";

qubit[3] q;
bit[2] c;

h q[1];
cx q[1], q[0];
CX q[2], q[0];
ch q[2], q[0];
c[0] = measure q[0];
