import QASM

namespace QASMTests

open QASM

private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do
    throw (IO.userError message)

private def assertError
    {α : Type}
    (actual : Except String α)
    (expected : String) : IO Unit :=
  match actual with
  | .error message =>
      assertTrue (message == expected) s!"expected error '{expected}', got '{message}'"
  | .ok _ =>
      throw (IO.userError s!"expected error '{expected}', got success")

private def assertOk (actual : Except String Unit) (message : String) : IO Unit :=
  match actual with
  | .ok () =>
      pure ()
  | .error error =>
      throw (IO.userError s!"{message}: {error}")

private def bell : QASM.Program :=
  qasm {
    OPENQASM 3.0;
    include "stdgates.inc";

    qubit[2] q;
    bit[2] c;

    h q[0];
    cx q[0], q[1];

    measure q[0] -> c[0];
    measure q[1] -> c[1];
  }

private def xProgram : QASM.Program :=
  qasm {
    OPENQASM 3.0;
    qubit[1] q;
    x q[0];
  }

private def unsupportedGateProgram : QASM.Program :=
  qasm {
    OPENQASM 3.0;
    qubit[1] q;
    y q[0];
  }

private def expectedBellQasm : String :=
  "OPENQASM 3.0;\n" ++
  "include \"stdgates.inc\";\n" ++
  "qubit[2] q;\n" ++
  "bit[2] c;\n" ++
  "h q[0];\n" ++
  "cx q[0], q[1];\n" ++
  "measure q[0] -> c[0];\n" ++
  "measure q[1] -> c[1];"

private def testValidation : IO Unit := do
  assertTrue (QASM.isValidIdentifier "_q2") "ASCII subset identifier should validate"
  assertTrue (!QASM.isValidIdentifier "im") "lexer token im should be reserved"
  assertTrue
    (!QASM.isValidIncludeFilename "bad\nfile")
    "include filenames should reject newlines"
  assertTrue
    (!QASM.isValidIncludeFilename "bad\tfile")
    "include filenames should reject tabs"
  assertOk bell.validate "the Bell program should validate"
  assertError
    (QASM.Program.validate ([] : QASM.Program))
    "empty OpenQASM program"
  assertError
    (QASM.Program.validate ([QASM.Stmt.qubit "q" 1] : QASM.Program))
    "the first statement must be `OPENQASM 3.0;`"
  assertError
    (QASM.Program.validate [QASM.Stmt.version 2 0])
    "unsupported OpenQASM version: 2.0"
  assertError
    (QASM.Program.validate [QASM.Stmt.version 3 0, QASM.Stmt.version 3 0])
    "duplicate OpenQASM version declaration"
  assertError
    (QASM.Program.validate [QASM.Stmt.version 3 0, QASM.Stmt.qubit "bad-name" 1])
    "invalid OpenQASM identifier: bad-name"
  assertError
    (QASM.Program.validate [QASM.Stmt.version 3 0, QASM.Stmt.qubit "measure" 1])
    "invalid OpenQASM identifier: measure"
  assertError
    (QASM.Program.validate [QASM.Stmt.version 3 0, QASM.Stmt.qubit "im" 1])
    "invalid OpenQASM identifier: im"
  assertError
    (QASM.Program.validate [QASM.Stmt.version 3 0, QASM.Stmt.includeFile ""])
    "invalid OpenQASM include filename: "
  assertError
    (QASM.Program.validate [QASM.Stmt.version 3 0, QASM.Stmt.includeFile "bad\"file"])
    "invalid OpenQASM include filename: bad\"file"
  assertError
    (QASM.Program.validate [
      QASM.Stmt.version 3 0,
      QASM.Stmt.qubit "q" 1,
      QASM.Stmt.gate1 "bad-gate" ⟨"q", none⟩
    ])
    "invalid OpenQASM identifier: bad-gate"

private def testPrettyPrinting : IO Unit := do
  match bell.toQasm with
  | .error message =>
      throw (IO.userError s!"Bell serialization failed: {message}")
  | .ok source =>
      assertTrue (source == expectedBellQasm) "Bell program pretty-print mismatch"

  assertError
    (QASM.Program.toQasm [QASM.Stmt.version 3 0, QASM.Stmt.bit "bit" 1])
    "invalid OpenQASM identifier: bit"

private def testDeterministicExecution : IO Unit := do
  match ← simulate xProgram with
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
  match ← simulate bell with
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
  match ← simulate unsupportedGateProgram with
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

end QASMTests

def main : IO Unit :=
  QASMTests.run
