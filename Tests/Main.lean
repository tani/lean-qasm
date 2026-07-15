import QASM

namespace QASMTests

open QASM

private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

qasm! NativeControl {
  OPENQASM 3.0;
  output int[32] result;
  int[32] x = 0;
  for uint i in [0:3] {
    if (i == 2) { continue; }
    x += 1;
  }
  while (x < 10) {
    x += 1;
    if (x == 5) { break; }
  }
  result = x;
}

qasm! NativeInput {
  OPENQASM 3.0;
  input int[32] value;
  output int[32] result;
  result = value + 1;
}

qasm! PortableQuantum {
  OPENQASM 3.0;
  include "stdgates.inc";
  const int[32] repetitions = 1;
  gate pair a, b {
    for uint i in [0:repetitions - 1] { h a; cx a, b; }
  }
  output bit[2] result;
  qubit[2] q;
  bit[2] c;
  let selected = q[{0, 1}];
  pair q[0], q[1];
  inv @ cx q[0], q[1];
  ctrl @ x selected[0], selected[1];
  barrier q;
  reset q[0];
  c = measure q;
  result = c;
}

qasm! NativeSubroutine {
  OPENQASM 3.0;
  def bump(int[32] value) -> int[32] {
    value += 1;
    return value;
  }
  output int[32] result;
  result = bump(20) + bump(20);
}

qasm! MutableArrayReference {
  OPENQASM 3.0;
  def update(mutable array[int[32], 2] values) {
    values[0] = 20;
    values[1] = 22;
  }
  output int[32] result;
  array[int[32], 2] values = {0, 0};
  update(values);
  result = values[0] + values[1];
}

qasm! "Fixtures/Elab/file_program.qasm"

qasm! NativeArrays {
  OPENQASM 3.0;
  output int[32] sum;
  output int[32] second_dimension;
  array[int[32], 4] values = {5, 6, 7, 8};
  array[int[32], 2, 3] matrix;
  values[0:1] = {20, 22};
  sum = values[0] + values[1];
  second_dimension = sizeof(matrix, 1);
}

qasm! MetadataProgram {
  OPENQASM 3.0;
  pragma compiler optimize
  @tool.note preserve
  int[32] value = 1;
}

qasm! DiagramProgram {
  OPENQASM 3.0;
  include "stdgates.inc";
  bit[2] result;
  qubit[2] q;
  for uint i in [0:1] {
    h q[i];
  }
  if (true) {
    cx q[0], q[1];
  } else {
    reset q;
  }
  negctrl @ x q[0], q[1];
  swap q[0], q[1];
  result = measure q;
}

#html DiagramProgram.program
#html MetadataProgram.program

qasm! NativeComplex {
  OPENQASM 3.0;
  output float[64] real_part;
  output float[64] imaginary_part;
  complex value = 2.5 + 3.5im;
  real_part = real(value);
  imaginary_part = imag(value);
}

qasm! ExtendedSwitch {
  OPENQASM 3.0;
  output int[32] result;
  int[32] value = 2;
  switch (value) {
    case 1 { result = 10; }
    case 2 { result = 20; }
    default { result = 30; }
  }
} using { dialect := .extended }

qasm! NativeDuration {
  OPENQASM 3.0;
  output duration elapsed;
  elapsed = 5ns + 2us;
}

qasm! TypedArrayIO {
  OPENQASM 3.0;
  input array[int[8], 2] values;
  output array[int[8], 2] result;
  result = values;
}

qasm! NativeArrayCast {
  OPENQASM 3.0;
  output array[uint[8], 2] result;
  array[int[16], 2] values = {20, 22};
  result = array[uint[8], 2](values);
}

qasm! NativeScalarFor {
  OPENQASM 3.0;
  output float[64] result;
  result = 0.0;
  for float[64] value in {20, 22} {
    result += value;
  }
}

qasm! ModifiedUserGate {
  OPENQASM 3.0;
  include "stdgates.inc";
  gate pair a, b { h a; x b; }
  qubit[3] q;
  ctrl @ pair q[0], q[1], q[2];
  inv @ pair q[1], q[2];
}

qasm! RecursiveSubroutine {
  OPENQASM 3.0;
  def factorial(int[32] value) -> int[32] {
    if (value <= 1) { return 1; }
    return value * factorial(value - 1);
  }
  output int[32] result;
  result = factorial(5);
}

qasm! IndexedMeasurement {
  OPENQASM 3.0;
  output bit[2] result;
  qubit[2] q;
  bit[2] measured;
  measure q[1] -> measured[0];
  measured[1] = measure q[1];
  result = measured;
}

qasm! ScheduledMeasurements {
  OPENQASM 3.0;
  output bit[3] result;
  qubit[3] q;
  result = measure q;
}

abbrev TestM := TraceBackend.M

private def runNative :=
  Id.run ((NativeControl.run (qasmM := TestM) {}) |>.run {})

private def runInput :=
  Id.run ((NativeInput.run (qasmM := TestM) { value := SInt.ofInt 41 }) |>.run {})

private def runQuantum :=
  Id.run ((PortableQuantum.run (qasmM := TestM) {}) |>.run {})

private def runSubroutine :=
  Id.run ((NativeSubroutine.run (qasmM := TestM) {}) |>.run {})

private def runMutableArray :=
  Id.run ((MutableArrayReference.run (qasmM := TestM) {}) |>.run {})

private def runIncludedFile :=
  Id.run ((file_program.run (qasmM := TestM) {}) |>.run {})

private def runArrays :=
  Id.run ((NativeArrays.run (qasmM := TestM) {}) |>.run {})

private def runComplex :=
  Id.run ((NativeComplex.run (qasmM := TestM) {}) |>.run {})

private def runExtended :=
  Id.run ((ExtendedSwitch.run (qasmM := TestM) {}) |>.run {})

private def runDuration :=
  Id.run ((NativeDuration.run (qasmM := TestM) {}) |>.run {})

private def typedArrayInput : FixedArray (SInt 8) [2] :=
  ⟨#[SInt.ofInt 20, SInt.ofInt 22], by decide⟩

private def runTypedArrayIO :=
  Id.run ((TypedArrayIO.run (qasmM := TestM) { values := typedArrayInput }) |>.run {})

private def runArrayCast :=
  Id.run ((NativeArrayCast.run (qasmM := TestM) {}) |>.run {})

private def runScalarFor :=
  Id.run ((NativeScalarFor.run (qasmM := TestM) {}) |>.run {})

private def runModifiedUserGate :=
  Id.run ((ModifiedUserGate.run (qasmM := TestM) {}) |>.run {})

private def runRecursive :=
  Id.run ((RecursiveSubroutine.run (qasmM := TestM) {}) |>.run {})

private def runIndexedMeasurement :=
  Id.run ((IndexedMeasurement.run (qasmM := TestM) {}) |>.run {})

private def runScheduledMeasurements :=
  Id.run ((ScheduledMeasurements.run (qasmM := TraceBackend.M) {}) |>.run
    (TraceBackend.initial #[true, false, true] (.constant false)))

private def testNativeControl : IO Unit := do
  match runNative.1 with
  | .error _ => throw (IO.userError "native control-flow program returned an error")
  | .ok outputs =>
      assertTrue (outputs.result.toInt == 5)
        "for/if/continue/while/break did not execute with native Lean semantics"

private def testInput : IO Unit := do
  match runInput.1 with
  | .error _ => throw (IO.userError "native input program returned an error")
  | .ok outputs =>
      assertTrue (outputs.result.toInt == 42) "generated typed Inputs value was not bound"

private def testQuantumBackend : IO Unit := do
  match runQuantum.1 with
  | .error _ => throw (IO.userError "portable quantum program returned an error")
  | .ok outputs =>
      assertTrue (outputs.result.toNat == 2) "measurement output mismatch"
  let operations := runQuantum.2.operations
  assertTrue (operations.contains "allocate:2") "qubit allocation was not delegated"
  assertTrue (operations.contains "sequence") "h was not lowered to portable U/gphase IR"
  assertTrue (operations.contains "inv:ctrl1:sequence")
    "inverse standard-gate modifier was not retained"
  assertTrue (operations.contains "ctrl1:sequence")
    "control modifier did not separate one control from the gate target"
  assertTrue (operations.contains "barrier") "barrier was not delegated"
  assertTrue (operations.contains "reset:0") "reset was not delegated"
  assertTrue (operations.contains "measure:0" && operations.contains "measure:1")
    "measurement was not delegated per qubit"

private def testSubroutine : IO Unit := do
  match runSubroutine.1 with
  | .error _ => throw (IO.userError "native subroutine program returned an error")
  | .ok outputs =>
      assertTrue (outputs.result.toInt == 42)
        "OpenQASM def/call/return was not lowered to a native Lean function"

private def testMutableArrayReference : IO Unit := do
  match runMutableArray.1 with
  | .error _ => throw (IO.userError "mutable array-reference program returned an error")
  | .ok outputs =>
      assertTrue (outputs.result.toInt == 42)
        "mutable array-reference changes were not written back to the caller"

private def testFileAndInclude : IO Unit := do
  match runIncludedFile.1 with
  | .error _ => throw (IO.userError "file/include program returned an error")
  | .ok outputs =>
      assertTrue (!outputs.result.value)
        "included file measurement output mismatch"
  assertTrue (runIncludedFile.2.operations.contains "sequence")
    "relative include gate was not resolved and transpiled"
  assertTrue (file_program.program.origins.size == 2)
    "root and recursively expanded include origins were not retained"

private def testArrays : IO Unit := do
  match runArrays.1 with
  | .error _ => throw (IO.userError "portable array program returned an error")
  | .ok outputs =>
      assertTrue (outputs.sum.toInt == 42) "array slice assignment/indexing failed"
      assertTrue (outputs.second_dimension.toInt == 3)
        "multidimensional default shape or sizeof dimension failed"

private def testMetadata : IO Unit := do
  assertTrue (MetadataProgram.program.pragmas == #["compiler optimize"])
    "pragma metadata was not retained"
  assertTrue (MetadataProgram.program.annotations == #["@tool.note preserve"])
    "annotation metadata was not retained"

private partial def flattenDiagramItems (items : Array DiagramItem) : Array DiagramItem :=
  items.foldl (fun flattened item => match item with
    | .operation _ => flattened.push item
    | .region _ children => flattened.push item ++ flattenDiagramItems children) #[]

private def testDiagram : IO Unit := do
  let flattened := flattenDiagramItems DiagramProgram.program.diagram.items
  let regions := flattened.filterMap fun item => match item with
    | .region label _ => some label
    | .operation _ => none
  let leaves := flattened.filterMap fun item => match item with
    | .operation operation => some operation
    | .region _ _ => none
  assertTrue (DiagramProgram.program.diagram.wires == #["q[0]", "q[1]"])
    "diagram wires do not preserve the quantum register"
  assertTrue (regions == #["for i in [0:1]", "if true", "else"])
    "diagram regions do not preserve static control flow"
  assertTrue (leaves.map (·.label) == #["h", "cx", "reset", "negctrl @ x", "swap", "M"])
    "diagram leaves do not preserve source order"
  let h := leaves[0]!
  assertTrue (h.operands.size == 1 && h.operands[0]!.wires == #[0, 1] &&
      h.operands[0]!.approximate)
    "dynamic loop index did not produce an approximate two-wire operand"
  let cx := leaves[1]!
  assertTrue (cx.operands.size == 2 && cx.operands[0]!.wires == #[0] &&
      cx.operands[1]!.wires == #[1] && !cx.operands[0]!.approximate &&
      !cx.operands[1]!.approximate && cx.glyph == .controlledX #[.positive])
    "cx diagram glyph or exact operands are incorrect"
  let negctrlX := leaves[3]!
  assertTrue (negctrlX.operands.size == 2 && negctrlX.operands[0]!.wires == #[0] &&
      negctrlX.operands[1]!.wires == #[1] &&
      negctrlX.glyph == .controlledX #[.negative])
    "negative controlled-X diagram glyph is incorrect"
  let swap := leaves[4]!
  assertTrue (swap.operands.size == 2 && swap.operands[0]!.wires == #[0] &&
      swap.operands[1]!.wires == #[1] && swap.glyph == .swap #[])
    "swap diagram glyph is incorrect"
  assertTrue (MetadataProgram.program.diagram.wires.isEmpty &&
      MetadataProgram.program.diagram.items.isEmpty)
    "classical metadata program should have an empty circuit diagram"

private def testComplex : IO Unit := do
  match runComplex.1 with
  | .error _ => throw (IO.userError "portable complex program returned an error")
  | .ok outputs =>
      assertTrue (outputs.real_part == 2.5) "complex real() result mismatch"
      assertTrue (outputs.imaginary_part == 3.5) "complex imag() result mismatch"

private def testExtendedDialect : IO Unit := do
  match runExtended.1 with
  | .error _ => throw (IO.userError "extended switch program returned an error")
  | .ok outputs =>
      assertTrue (outputs.result.toInt == 20) "extended switch selected the wrong case"

private def testDuration : IO Unit := do
  match runDuration.1 with
  | .error _ => throw (IO.userError "portable SI-duration program returned an error")
  | .ok outputs =>
      assertTrue ((outputs.elapsed.seconds - 0.000002005).abs < 0.000000000001)
        "SI duration literals were not converted to seconds"

private def testTypedArrayIO : IO Unit := do
  match runTypedArrayIO.1 with
  | .error _ => throw (IO.userError "typed fixed-array I/O program returned an error")
  | .ok outputs =>
      assertTrue (outputs.result.data.map SInt.toInt == #[20, 22])
        "fixed-array ValueCodec did not preserve shape or elements"

private def testArrayCast : IO Unit := do
  match runArrayCast.1 with
  | .error _ => throw (IO.userError "array-cast program returned an error")
  | .ok outputs =>
      assertTrue (outputs.result.data.map UInt.toNat == #[20, 22])
        "array cast did not convert every element or preserve shape"

private def testScalarFor : IO Unit := do
  match runScalarFor.1 with
  | .error _ => throw (IO.userError "scalar for-loop program returned an error")
  | .ok outputs =>
      assertTrue (outputs.result == 42.0)
        "for-loop values were not converted to the declared iterator type"

private def testModifiedUserGate : IO Unit := do
  match runModifiedUserGate.1 with
  | .error _ => throw (IO.userError "modified user-gate program returned an error")
  | .ok _ => pure ()
  assertTrue (runModifiedUserGate.2.operations.contains "ctrl1:sequence")
    "control modifier did not wrap the recorded user-gate definition"
  assertTrue (runModifiedUserGate.2.operations.contains "inv:sequence")
    "inverse modifier did not wrap the recorded user-gate definition"

private def testRecursiveSubroutine : IO Unit := do
  match runRecursive.1 with
  | .error _ => throw (IO.userError "recursive subroutine returned an error")
  | .ok outputs =>
      assertTrue (outputs.result.toInt == 120)
        "direct recursive subroutine was not lowered to a recursive Lean function"

private def testIndexedMeasurement : IO Unit := do
  match runIndexedMeasurement.1 with
  | .error _ => throw (IO.userError "indexed-measurement program returned an error")
  | .ok outputs =>
      assertTrue (outputs.result.toNat == 3)
        "measurement did not update the selected classical bit"

private def testScheduledMeasurements : IO Unit := do
  match runScheduledMeasurements.1 with
  | .error error => throw (IO.userError s!"scheduled-measurement program returned an error: {repr error}")
  | .ok outputs =>
      assertTrue (outputs.result.toNat == 5)
        "scheduled measurement outcomes were not decoded in qubit order"
  assertTrue (runScheduledMeasurements.2.operations ==
      #["allocate:3", "measure:0", "measure:1", "measure:2"])
    "trace backend did not record scheduled measurements in execution order"
  assertTrue (runScheduledMeasurements.2.observedMeasurements ==
      #[(0, true), (1, false), (2, true)])
    "trace backend did not retain measured values"

private def testRuntimeValues : IO Unit := do
  assertTrue ((Value.integerLiteral "0xff").asInt == 255) "hex literal conversion failed"
  assertTrue ((Value.binary "+" (.integer 20) (.integer 22)).asInt == 42)
    "integer addition failed"
  assertTrue (Value.range (.integer 3) (.integer (-1)) (.integer 1) ==
    #[.integer 3, .integer 2, .integer 1]) "descending range failed"
  assertTrue ((Value.cast "uint" 4 (.integer 17)).asInt == 1)
    "fixed-width uint cast did not wrap"
  assertTrue ((Value.cast "int" 4 (.integer 15)).asInt == -1)
    "fixed-width signed cast did not use two's complement"
  assertTrue ((Value.builtin "mod" #[.integer 43, .integer 5]).asInt == 3)
    "mod builtin failed"
  assertTrue ((Value.builtin "rotl" #[.bits #[true, false, false, false], .integer 1]).asInt == 2)
    "rotl builtin failed"
  match TargetConfig.validate { floatWidth := 16 } with
  | .error _ => pure ()
  | .ok () => throw (IO.userError "unsupported target float width must be rejected")

private def testFrontendRoundTrip : IO Unit := do
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
    "gate pair(theta) a, b { h a; cx a, b; }"
  match QASM.parse source with
  | .error error => throw (IO.userError s!"frontend parse failed: {error}")
  | .ok program =>
      match QASM.parse program.toQasm with
      | .error error => throw (IO.userError s!"frontend round trip failed: {error}")
      | .ok reparsed =>
          assertTrue (reparsed == program) "frontend normalized round trip mismatch"

  let complexCast := "OPENQASM 3.0; complex[float[32]] value = complex[float[32]](1.0);"
  match QASM.parse complexCast with
  | .error error => throw (IO.userError s!"complex cast parse failed: {error}")
  | .ok program =>
      match QASM.parse program.toQasm with
      | .error error => throw (IO.userError s!"complex cast round trip failed: {error}")
      | .ok reparsed => assertTrue (program == reparsed) "complex type/cast round trip mismatch"

  let arrayCast :=
    "OPENQASM 3.0; array[int[16], 2] a = {1, 2}; " ++
    "array[uint[8], 2] b = array[uint[8], 2](a);"
  match QASM.parse arrayCast with
  | .error error => throw (IO.userError s!"array cast parse failed: {error}")
  | .ok program =>
      match QASM.parse program.toQasm with
      | .error error => throw (IO.userError s!"array cast round trip failed: {error}")
      | .ok reparsed => assertTrue (program == reparsed) "array cast round trip mismatch"

private def testCapabilityBoundary : IO Unit := do
  let source :=
    "OPENQASM 3.0;\n" ++
    "extern lookup(int[32]) -> int[32];\n" ++
    "defcalgrammar \"openpulse\";\n" ++
    "delay[5ns] $0;"
  match QASM.parse source with
  | .error error => throw (IO.userError s!"capability sample failed to parse: {error}")
  | .ok program =>
      match QASM.check program with
      | .error diagnostics => throw (IO.userError s!"capability check failed: {repr diagnostics}")
      | .ok checked =>
          assertTrue (checked.requiredCapabilities.contains .externalFunction)
            "extern capability was not detected"
          assertTrue (checked.requiredCapabilities.contains .calibration)
            "calibration capability was not detected"
          assertTrue (checked.requiredCapabilities.contains .timing)
            "timing capability was not detected"
          assertTrue (checked.requiredCapabilities.contains .physicalQubit)
            "physical-qubit capability was not detected"

private def testOfficialExamples : IO Unit := do
  let root : System.FilePath := "Tests/Fixtures/OpenQASM30/examples"
  let paths <- root.walkDir
  let mut failures : Array String := #[]
  for path in paths do
    if path.extension == some "qasm" then
      match <- QASM.parseFile path with
      | .ok _ => pure ()
      | .error error => failures := failures.push s!"{path}: {error}"
  unless failures.isEmpty do
    throw (IO.userError ("official fixture failures:\n" ++
      String.intercalate "\n" failures.toList))

private def testOfficialInvalidFixtures : IO Unit := do
  let root : System.FilePath := "Tests/Fixtures/OpenQASM30/source/grammar/tests/invalid"
  let paths <- root.walkDir
  let mut accepted : Array String := #[]
  for path in paths do
    if path.extension == some "qasm" then
      match <- QASM.parseFile path with
      | .error _ => pure ()
      | .ok _ => accepted := accepted.push s!"{path}"
  unless accepted.isEmpty do
    throw (IO.userError ("invalid fixtures unexpectedly accepted:\n" ++
      String.intercalate "\n" accepted.toList))

def run : IO Unit := do
  testNativeControl
  testInput
  testQuantumBackend
  testSubroutine
  testMutableArrayReference
  testFileAndInclude
  testArrays
  testMetadata
  testDiagram
  testComplex
  testExtendedDialect
  testDuration
  testTypedArrayIO
  testArrayCast
  testScalarFor
  testModifiedUserGate
  testRecursiveSubroutine
  testIndexedMeasurement
  testScheduledMeasurements
  testRuntimeValues
  testFrontendRoundTrip
  testCapabilityBoundary
  testOfficialExamples
  testOfficialInvalidFixtures

end QASMTests

def main : IO Unit := QASMTests.run
