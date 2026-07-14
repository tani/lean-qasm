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
  begin_qasm
    OPENQASM 3.0;
    include "stdgates.inc";

    qubit[2] q;
    bit[2] c;

    h q[0];
    cx q[0], q[1];

    measure q[0] -> c[0];
    measure q[1] -> c[1];
  end_qasm

private def xProgram : QASM.Program :=
  begin_qasm
    OPENQASM 3.0;
    qubit[1] q;
    x q[0];
  end_qasm

private def unsupportedGateProgram : QASM.Program :=
  begin_qasm
    OPENQASM 3.0;
    qubit[1] q;
    y q[0];
  end_qasm

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
  match ← simulate xProgram with {} with
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
  match ← simulate bell with {} with
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
  match ← simulate unsupportedGateProgram with {} with
  | .error message =>
      assertTrue
        (message == "unsupported one-qubit gate: y")
        s!"unexpected unsupported-gate error: {message}"
  | .ok _ =>
      throw (IO.userError "unsupported gate should fail during execution")

  match ← simulate xProgram with { maxQubits := 0 } with
  | .error message =>
      assertTrue
        (message == "simulation requires 1 qubits, exceeding maxQubits=0")
        s!"unexpected max-qubit error: {message}"
  | .ok _ =>
      throw (IO.userError "maxQubits should be enforced before allocation")

private def testFrontend20 : IO Unit := do
  let source :=
    "OPENQASM 3.0;\n" ++
    "include \"stdgates.inc\";\n" ++
    "qubit[2] 量子; // Unicode identifier\n" ++
    "bit[2] c;\n" ++
    "h 量子[0];\n" ++
    "cx 量子[0], 量子[1];\n" ++
    "barrier 量子;\n" ++
    "measure 量子 -> c;"
  match QASM.parse source with
  | .error error =>
      throw (IO.userError s!"20% frontend parse failed: {error}")
  | .ok program =>
      assertTrue (program.version == some ⟨3, 0⟩) "frontend should retain version 3.0"
      assertTrue (program.statements.size == 7) "frontend statement count mismatch"
      match QASM.parse program.toQasm with
      | .error error =>
          throw (IO.userError s!"frontend round trip failed: {error}")
      | .ok reparsed =>
          assertTrue (reparsed == program) "frontend normalized round trip mismatch"

  match QASM.parse "qubit q; reset $0;" with
  | .error error => throw (IO.userError s!"version-optional parse failed: {error}")
  | .ok program => assertTrue program.version.isNone "version should be optional"

private def testFrontend40 : IO Unit := do
  let source :=
    "OPENQASM 3.0;\n" ++
    "const int[32] n = 2 + 3 * 4;\n" ++
    "input angle[64] theta;\n" ++
    "bit[4] c = \"0011\";\n" ++
    "uint[8] x = int[8](n) << 1;\n" ++
    "let low = c[0];\n" ++
    "x += 2;\n" ++
    "foo(n, theta);"
  match QASM.parse source with
  | .error error => throw (IO.userError s!"40% frontend parse failed: {error}")
  | .ok program =>
      assertTrue (program.statements.size == 7) "40% frontend statement count mismatch"
      match QASM.parse program.toQasm with
      | .error error => throw (IO.userError s!"40% frontend round trip failed: {error}")
      | .ok reparsed => assertTrue (reparsed == program) "40% frontend round trip mismatch"
      match QASM.check program with
      | .error diagnostics =>
          throw (IO.userError s!"40% semantic check failed: {repr diagnostics}")
      | .ok checked =>
          assertTrue (checked.constants.length == 1) "constant environment mismatch"

private def testFrontend60 : IO Unit := do
  let source :=
    "OPENQASM 3.0;\n" ++
    "def parity(int[32] n) -> bit {\n" ++
    "  bit result = false;\n" ++
    "  for uint i in [0:n - 1] {\n" ++
    "    if (i == 2) { continue; }\n" ++
    "    while (result == false) { break; }\n" ++
    "  }\n" ++
    "  return result;\n" ++
    "}\n" ++
    "extern vote(bit[3]) -> bit;\n" ++
    "gate pair(theta) a, b { h a; cx a, b; }"
  match QASM.parse source with
  | .error error => throw (IO.userError s!"60% frontend parse failed: {error}")
  | .ok program =>
      assertTrue (program.statements.size == 3) "60% frontend statement count mismatch"
      match QASM.parse program.toQasm with
      | .error error => throw (IO.userError s!"60% frontend round trip failed: {error}")
      | .ok reparsed => assertTrue (reparsed == program) "60% frontend round trip mismatch"
      match QASM.check program with
      | .error diagnostics =>
          throw (IO.userError s!"60% semantic check failed: {repr diagnostics}")
      | .ok _ => pure ()

  match QASM.parse "break;" with
  | .error error => throw (IO.userError s!"break syntax should parse: {error}")
  | .ok program =>
      match QASM.check program with
      | .ok _ => throw (IO.userError "top-level break should fail static semantics")
      | .error diagnostics =>
          assertTrue
            (diagnostics.any fun diagnostic =>
              diagnostic.message == "'break' is only valid inside a loop")
            "top-level break diagnostic mismatch"

private def testFrontend80 : IO Unit := do
  let source :=
    "OPENQASM 3.0;\n" ++
    "defcalgrammar \"openpulse\";\n" ++
    "pragma compiler optimize\n" ++
    "@tool.note preserve\n" ++
    "inv @ ctrl(2) @ phase(pi) q;\n" ++
    "gphase(pi);\n" ++
    "reset $0;\n" ++
    "box[20ns] { delay[5ns] q; nop q; }\n" ++
    "cal { play drive($0), gaussian(...); }\n" ++
    "defcal x $0 { play drive($0), gaussian(...); }"
  match QASM.parse source with
  | .error error => throw (IO.userError s!"80% frontend parse failed: {error}")
  | .ok program =>
      assertTrue (program.statements.size == 8) "80% frontend statement count mismatch"
      match QASM.parse program.toQasm with
      | .error error => throw (IO.userError s!"80% frontend round trip failed: {error}")
      | .ok reparsed => assertTrue (reparsed == program) "80% frontend round trip mismatch"
      match QASM.check program with
      | .error diagnostics =>
          throw (IO.userError s!"80% semantic check failed: {repr diagnostics}")
      | .ok checked =>
          assertTrue
            (checked.requiredCapabilities.contains .calibration)
            "calibration capability should be reported"
          assertTrue
            (checked.requiredCapabilities.contains .timing)
            "timing capability should be reported"
          assertTrue
            (checked.requiredCapabilities.contains .physicalQubit)
            "physical-qubit capability should be reported"

private def testFrontend100 : IO Unit := do
  let source :=
    "OPENQASM 3;\n" ++
    "bit[4] c;\n" ++
    "c[:1] = c[2:];\n" ++
    "delay[5 ns];\n" ++
    "switch (c[0]) {\n" ++
    "  case 0, 1 { c[0] = measure $0; }\n" ++
    "  default { end; }\n" ++
    "}"
  match QASM.parse source with
  | .error error => throw (IO.userError s!"100% frontend parse failed: {error}")
  | .ok program =>
      match QASM.parse program.toQasm with
      | .error error => throw (IO.userError s!"100% frontend round trip failed: {error}")
      | .ok reparsed => assertTrue (reparsed == program) "100% frontend round trip mismatch"

private def testOfficialExamples : IO Unit := do
  let root : System.FilePath := "Tests/Fixtures/OpenQASM30/examples"
  let paths ← root.walkDir
  let mut failures : Array String := #[]
  for path in paths do
    if path.extension == some "qasm" then
      match ← QASM.parseFile path with
      | .ok _ => pure ()
      | .error error => failures := failures.push s!"{path}: {error}"
  unless failures.isEmpty do
    throw (IO.userError
      ("official OpenQASM 3.0 fixture failures:\n" ++
        String.intercalate "\n" failures.toList))

private def testOfficialInvalidFixtures : IO Unit := do
  let root : System.FilePath :=
    "Tests/Fixtures/OpenQASM30/source/grammar/tests/invalid"
  let paths ← root.walkDir
  let mut accepted : Array String := #[]
  for path in paths do
    if path.extension == some "qasm" then
      match ← QASM.parseFile path with
      | .error _ => pure ()
      | .ok _ => accepted := accepted.push s!"{path}"
  unless accepted.isEmpty do
    throw (IO.userError
      ("invalid OpenQASM 3.0 fixtures unexpectedly accepted:\n" ++
        String.intercalate "\n" accepted.toList))

def run : IO Unit := do
  testValidation
  testPrettyPrinting
  testDeterministicExecution
  testBellMeasurement
  testRuntimeError
  testFrontend20
  testFrontend40
  testFrontend60
  testFrontend80
  testFrontend100
  testOfficialExamples
  testOfficialInvalidFixtures

end QASMTests

def main : IO Unit :=
  QASMTests.run
