import QASM

namespace QASMTests

open QASM

private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def nativeSource : String :=
  qasm% {
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

qasm% NativeControl from nativeSource

def inputSource : String :=
  qasm% {
OPENQASM 3.0;
input int[32] value;
output int[32] result;
result = value + 1;
  }

qasm% NativeInput from inputSource

def quantumSource : String :=
  qasm% {
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

qasm% PortableQuantum from quantumSource

def subroutineSource : String :=
  qasm% {
OPENQASM 3.0;
def bump(int[32] value) -> int[32] {
  value += 1;
  return value;
}
output int[32] result;
result = bump(20) + bump(20);
  }

qasm% NativeSubroutine from subroutineSource

def mutableArraySource : String :=
  qasm% {
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

qasm% MutableArrayReference from mutableArraySource

qasmFile% IncludedFile "Fixtures/Elab/file_program.qasm"

def arraySource : String :=
  qasm% {
OPENQASM 3.0;
output int[32] sum;
output int[32] second_dimension;
array[int[32], 4] values = {5, 6, 7, 8};
array[int[32], 2, 3] matrix;
values[0:1] = {20, 22};
sum = values[0] + values[1];
second_dimension = sizeof(matrix, 1);
  }

qasm% NativeArrays from arraySource

def metadataSource : String :=
  qasm% {
OPENQASM 3.0;
pragma compiler optimize
@tool.note preserve
int[32] value = 1;
  }

qasm% MetadataProgram from metadataSource

def complexSource : String :=
  qasm% {
OPENQASM 3.0;
output float[64] real_part;
output float[64] imaginary_part;
complex value = 2.5 + 3.5im;
real_part = real(value);
imaginary_part = imag(value);
  }

qasm% NativeComplex from complexSource

def extendedSource : String :=
  qasm% {
OPENQASM 3.0;
output int[32] result;
int[32] value = 2;
switch (value) {
  case 1 { result = 10; }
  case 2 { result = 20; }
  default { result = 30; }
}
  }

def extendedOptions : ElabOptions := { dialect := .extended }

qasm% ExtendedSwitch from extendedSource using extendedOptions

def durationSource : String :=
  qasm% {
OPENQASM 3.0;
output duration elapsed;
elapsed = 5ns + 2us;
  }

qasm% NativeDuration from durationSource

def typedArrayIOSource : String :=
  qasm% {
OPENQASM 3.0;
input array[int[8], 2] values;
output array[int[8], 2] result;
result = values;
  }

qasm% TypedArrayIO from typedArrayIOSource

def arrayCastSource : String :=
  qasm% {
OPENQASM 3.0;
output array[uint[8], 2] result;
array[int[16], 2] values = {20, 22};
result = array[uint[8], 2](values);
  }

qasm% NativeArrayCast from arrayCastSource

def scalarForSource : String :=
  qasm% {
OPENQASM 3.0;
output float[64] result;
result = 0.0;
for float[64] value in {20, 22} {
  result += value;
}
  }

qasm% NativeScalarFor from scalarForSource

def modifiedUserGateSource : String :=
  qasm% {
OPENQASM 3.0;
include "stdgates.inc";
gate pair a, b { h a; x b; }
qubit[3] q;
ctrl @ pair q[0], q[1], q[2];
inv @ pair q[1], q[2];
  }

qasm% ModifiedUserGate from modifiedUserGateSource

def recursiveSource : String :=
  qasm% {
OPENQASM 3.0;
def factorial(int[32] value) -> int[32] {
  if (value <= 1) { return 1; }
  return value * factorial(value - 1);
}
output int[32] result;
result = factorial(5);
  }

qasm% RecursiveSubroutine from recursiveSource

def indexedMeasurementSource : String :=
  qasm% {
OPENQASM 3.0;
output bit[2] result;
qubit[2] q;
bit[2] measured;
measure q[1] -> measured[0];
measured[1] = measure q[1];
result = measured;
  }

qasm% IndexedMeasurement from indexedMeasurementSource

structure TestState where
  nextQubit : Nat := 0
  operations : Array String := #[]
  deriving Repr

abbrev TestM := StateM TestState

private def unitaryLabel : Unitary Nat -> String
  | .U .. => "U"
  | .gphase _ => "gphase"
  | .named name _ _ => name
  | .sequence _ => "sequence"
  | .inverse operation => "inv:" ++ unitaryLabel operation
  | .power _ operation => "pow:" ++ unitaryLabel operation
  | .controlled _ controls operation =>
      s!"ctrl{controls.size}:" ++ unitaryLabel operation

instance : QuantumBackend TestM Nat String where
  allocate count := do
    let state <- get
    set { state with nextQubit := state.nextQubit + count }
    modify fun state =>
      { state with operations := state.operations.push s!"allocate:{count}" }
    pure (.ok (Array.range count |>.map (fun index => state.nextQubit + index)))
  apply operation := do
    modify fun state => { state with operations := state.operations.push (unitaryLabel operation) }
    pure (.ok ())
  measure qubit := do
    modify fun state => { state with operations := state.operations.push s!"measure:{qubit}" }
    pure (.ok (qubit % 2 == 1))
  reset qubit := do
    modify fun state => { state with operations := state.operations.push s!"reset:{qubit}" }
    pure (.ok ())
  barrier _ := do
    modify fun state => { state with operations := state.operations.push "barrier" }
    pure (.ok ())

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
  Id.run ((IncludedFile.run (qasmM := TestM) {}) |>.run {})

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

private def testRawSource : IO Unit := do
  let expected :=
    "OPENQASM 3.0;\n" ++
    "output int[32] result;\n" ++
    "int[32] x = 0;\n" ++
    "for uint i in [0:3] {\n" ++
    "  if (i == 2) { continue; }\n" ++
    "  x += 1;\n" ++
    "}\n" ++
    "while (x < 10) {\n" ++
    "  x += 1;\n" ++
    "  if (x == 5) { break; }\n" ++
    "}\n" ++
    "result = x;\n"
  assertTrue (nativeSource == expected)
    "qasm% must preserve the raw OpenQASM source"

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
  assertTrue (IncludedFile.program.origins.size == 2)
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
  testRawSource
  testNativeControl
  testInput
  testQuantumBackend
  testSubroutine
  testMutableArrayReference
  testFileAndInclude
  testArrays
  testMetadata
  testComplex
  testExtendedDialect
  testDuration
  testTypedArrayIO
  testArrayCast
  testScalarFor
  testModifiedUserGate
  testRecursiveSubroutine
  testIndexedMeasurement
  testRuntimeValues
  testFrontendRoundTrip
  testCapabilityBoundary
  testOfficialExamples
  testOfficialInvalidFixtures

end QASMTests

def main : IO Unit := QASMTests.run
