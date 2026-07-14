import Qasmv

```lean
namespace QasmvTests

open Qasm

private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do
    throw (IO.userError message)

private def assertError
    (actual : Except String Unit)
    (expected : String) : IO Unit :=
  match actual with
  | .error message =>
      assertTrue (message == expected) s!"expected error '{expected}', got '{message}'"
  | .ok () =>
      throw (IO.userError s!"expected error '{expected}', got success")

private def assertOk (actual : Except String Unit) (message : String) : IO Unit :=
  match actual with
  | .ok () =>
      pure ()
  | .error error =>
      throw (IO.userError s!"{message}: {error}")

private def bell : Qasm.Program :=
  qasm {
    OPENQASM 2.0;
    include "qelib1.inc";

    qreg q[2];
    creg c[2];

    h q[0];
    cx q[0], q[1];

    measure q[0] -> c[0];
    measure q[1] -> c[1];
  }

private def xProgram : Qasm.Program :=
  qasm {
    OPENQASM 2.0;
    qreg q[1];
    x q[0];
  }

private def unsupportedGateProgram : Qasm.Program :=
  qasm {
    OPENQASM 2.0;
    qreg q[1];
    y q[0];
  }

private def expectedBellQasm : String :=
  "OPENQASM 2.0;\n" ++
  "include \"qelib1.inc\";\n" ++
  "qreg q[2];\n" ++
  "creg c[2];\n" ++
  "h q[0];\n" ++
  "cx q[0], q[1];\n" ++
  "measure q[0] -> c[0];\n" ++
  "measure q[1] -> c[1];"

private def testValidation : IO Unit := do
  assertOk bell.validate "the Bell program should validate"
  assertError
    (Qasm.Program.validate ([] : Qasm.Program))
    "empty OpenQASM program"
  assertError
    (Qasm.Program.validate ([Qasm.Stmt.qreg "q" 1] : Qasm.Program))
    "the first statement must be `OPENQASM 2.0;`"

private def testPrettyPrinting : IO Unit :=
  assertTrue (bell.toQasm == expectedBellQasm) "Bell program pretty-print mismatch"

private def testDeterministicExecution : IO Unit := do
  match ← execute xProgram with
  | .error message =>
      throw (IO.userError s!"x program failed: {message}")
  | .ok result =>
      assertTrue (result.qubitCount == 1) "x program should allocate one qubit"
      assertTrue (result.amplitudes.size == 2) "x program should have two amplitudes"
      assertTrue
        (result.amplitudes[0]!.re == 0.0 && result.amplitudes[0]!.im == 0.0)
        "x program should clear the |0> amplitude"
      assertTrue
        (result.amplitudes[1]!.re == 1.0 && result.amplitudes[1]!.im == 0.0)
        "x program should produce the |1> state"

private def testBellMeasurement : IO Unit := do
  match ← execute bell with
  | .error message =>
      throw (IO.userError s!"Bell program failed: {message}")
  | .ok result =>
      match result.classical with
      | [(name, bits)] =>
          assertTrue (name == "c") "Bell result should contain classical register c"
          assertTrue (bits.size == 2) "classical register c should have two bits"
          assertTrue (bits[0]! == bits[1]!) "Bell measurements should be correlated"
      | _ =>
          throw (IO.userError "Bell result should contain exactly one classical register")

private def testRuntimeError : IO Unit := do
  match ← execute unsupportedGateProgram with
  | .error message =>
      assertTrue
        (message == "unsupported one-qubit gate: y")
        s!"unexpected unsupported-gate error: {message}"
  | .ok _ =>
      throw (IO.userError "unsupported gate should fail during execution")

def run : IO Unit := do
  testValidation
  testPrettyPrinting
  testDeterministicExecution
  testBellMeasurement
  testRuntimeError

end QasmvTests

def main : IO Unit :=
  QasmvTests.run
```
