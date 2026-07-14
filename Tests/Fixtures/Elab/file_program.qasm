OPENQASM 3.0;
include "gates.inc";
output bit result;
qubit q;
included_x q;
result = measure q;
