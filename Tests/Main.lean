import QASM

namespace QASMTests

open Qasm

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

private def bell : Qasm.Program :=
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

private def xProgram : Qasm.Program :=
  qasm {
    OPENQASM 3.0;
    qubit[1] q;
    x q[0];
  }

private def unsupportedGateProgram : Qasm.Program :=
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
  assertTrue (Qasm.isValidIdentifier "_q2") "ASCII subset identifier should validate"
  assertTrue (!Qasm.isValidIdentifier "im") "lexer token im should be reserved"
  assertTrue
    (!Qasm.isValidIncludeFilename "bad\nfile")
    "include filenames should reject newlines"
  assertTrue
    (!Qasm.isValidIncludeFilename "bad\tfile")
    "include filenames should reject tabs"
  assertOk bell.validate "the Bell program should validate"
  assertError
    (Qasm.Program.validate ([] : Qasm.Program))
    "empty OpenQASM program"
  assertError
    (Qasm.Program.validate ([Qasm.Stmt.qubit "q" 1] : Qasm.Program))
    "the first statement must be `OPENQASM 3.0;`"
  assertError
    (Qasm.Program.validate [Qasm.Stmt.version 2 0])
    "unsupported OpenQASM version: 2.0"
  assertError
    (Qasm.Program.validate [Qasm.Stmt.version 3 0, Qasm.Stmt.version 3 0])
    "duplicate OpenQASM version declaration"
  assertError
    (Qasm.Program.validate [Qasm.Stmt.version 3 0, Qasm.Stmt.qubit "bad-name" 1])
    "invalid OpenQASM identifier: bad-name"
  assertError
    (Qasm.Program.validate [Qasm.Stmt.version 3 0, Qasm.Stmt.qubit "measure" 1])
    "invalid OpenQASM identifier: measure"
  assertError
    (Qasm.Program.validate [Qasm.Stmt.version 3 0, Qasm.Stmt.qubit "im" 1])
    "invalid OpenQASM identifier: im"
  assertError
    (Qasm.Program.validate [Qasm.Stmt.version 3 0, Qasm.Stmt.includeFile ""])
    "invalid OpenQASM include filename: "
  assertError
    (Qasm.Program.validate [Qasm.Stmt.version 3 0, Qasm.Stmt.includeFile "bad\"file"])
    "invalid OpenQASM include filename: bad\"file"
  assertError
    (Qasm.Program.validate [
      Qasm.Stmt.version 3 0,
      Qasm.Stmt.qubit "q" 1,
      Qasm.Stmt.gate1 "bad-gate" ⟨"q", none⟩
    ])
    "invalid OpenQASM identifier: bad-gate"

private def testPrettyPrinting : IO Unit := do
  match bell.toQasm with
  | .error message =>
      throw (IO.userError s!"Bell serialization failed: {message}")
  | .ok source =>
      assertTrue (source == expectedBellQasm) "Bell program pretty-print mismatch"

  assertError
    (Qasm.Program.toQasm [Qasm.Stmt.version 3 0, Qasm.Stmt.bit "bit" 1])
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
