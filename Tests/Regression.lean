    import LiterateLean
    import QASM
    open scoped LiterateLean

# Regression tests for runtime and frontend review findings

These cases exercise observable outputs, backend effects, typed host boundaries, rejected
source programs, and emission followed by execution. They cover every P1 and P2 finding
from the full review, including interactions between selector effects and reference calls.

```lean
namespace QASMTests.Regression

open QASM

private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def lower (source : String) : IO IR.Program := do
  let parsed ← match QASM.parse source with
    | .ok parsed => pure parsed
    | .error error => throw (IO.userError s!"regression parse failure: {error}")
  let analysis ← match QASM.analyzeTypes .default parsed with
    | .ok analysis => pure analysis
    | .error errors => throw (IO.userError s!"regression type failure: {repr errors}")
  match Lowering.program parsed analysis with
  | .ok program => pure program
  | .error errors => throw (IO.userError s!"regression lowering failure: {repr errors}")

private def execute (program : IR.Program) (measurements : Array Bool := #[]) :
    IO (Std.HashMap IR.VarId Value × TraceBackend.State) := do
  let (result, trace) := TraceBackend.run (Execution.run program #[]) (TraceBackend.initial measurements)
  match result with
  | .ok values => pure (values, trace)
  | .error error => throw (IO.userError s!"regression execution failure: {repr error}")

private def output (program : IR.Program) (values : Std.HashMap IR.VarId Value)
    (name : String := "result") : Value :=
  (program.outputs.find? (·.var.name == name)).bind (fun declaration => values[declaration.var.id]?) |>.getD .unit

qasm! HostBoundaries {
  OPENQASM 3.0;
  input angle[64] theta;
  output angle[64] copied;
  output angle[64] half_turn;
  output bit[3] bits;
  output uint[8] number;
  copied = theta;
  half_turn = pi;
  bits = "100";
  number = uint[8](bits);
}

qasm! ExtendedNop {
  OPENQASM 3.0;
  qubit q;
  nop q;
  nop;
} using { dialect := .extended }

```

## Classical values and call effects

Asymmetric bit patterns detect reversed literals and iteration order. Narrow constants
and return values must wrap before participating in subsequent arithmetic. The recursive
and reference cases ensure callers are evaluated before parameter bindings are installed.

```lean
private def testOutputs : IO Unit := do
  for (source, expected) in [
    ("const uint[8] n = 255; uint[8] one = 1; result = n + one;", 0),
    ("def f() -> uint[8] { return 255; } uint[8] one = 1; result = f() + one;", 0),
    ("bit[3] b = \"100\"; result = uint[8](b);", 4),
    ("bit[3] b = \"100\"; for bit x in b { result = result * 2 + int[32](x); }", 1),
    ("array[int[32],2,2] a = {{1,2},{3,4}}; a[0,1] = 9; result = a[0,1] + a[1,0];", 12),
    ("array[int[32],2,2] a = {{1,2},{3,4}}; a[1][0] = 9; result = a[1,0];", 9),
    ("array[int[32],2,2] a = {{1,2},{3,4}}; a[0:1][0,1] = 9; result = a[0,1] + a[1,1];", 13),
    ("def f(mutable array[int[32],2] a) -> int[32] { a[1] = 9; return 0; } array[int[32],2,2] a = {{1,2},{3,4}}; f(a[0:1][0]); result = a[0,1] + a[1,1];", 13),
    ("const int n = 2; def f() -> int[32] { const int n = 3; return n; } result = f();", 3),
    ("if (true) { const int n = 3; result = n; }", 3),
    ("const int n = 2; if (true) { const int n = 3; array[int[32],n] a = {1,2,9}; result = a[2]; }", 9),
    ("if (true) { const int n = 3; result = n; } if (true) { const int n = 2; array[int[32],n] a = {1,9}; result += a[1]; }", 12),
    ("def f() -> int[32] { const int n = 3; array[int[32],n] a = {1,2,9}; return a[2]; } result = f();", 9),
    ("def f(mutable array[int[32],2] a) -> int[32] { a[0] = 9; return a[0]; } array[int[32],2] a = {1,2}; result = f(a) + a[0];", 18),
    ("def index(mutable array[int[32],2] b) -> int[32] { b[0] = 9; return 0; } array[int[32],2] a = {1,2}; array[int[32],2] b = {1,2}; a[index(b)] = 7; result = b[0] + a[0];", 16),
    ("def f(int[32] a, int[32] b) -> int[32] { if (a > 0) { return f(a-1,a); } return b; } result = f(1,0);", 1),
    ("const uint[8] n = 258; array[int[32],n] a = {3,9}; result = a[1];", 9),
    ("array[int[32],uint[8](258)] a = {3,9}; result = a[1];", 9)
  ] do
    let program ← lower ("OPENQASM 3.0; output int[32] result; " ++ source)
    let (values, _) ← execute program
    assertTrue ((output program values).asInt == expected) s!"wrong result for {source}"
    let reparsed ← lower (toString program)
    let (values, _) ← execute reparsed
    assertTrue ((output reparsed values).asInt == expected) s!"emission changed result for {source}"
  for (expression, expected) in [("1.0 % 0.3", 0.1), ("1.0 / 0.5", 2.0), ("10ns / 2ns", 5.0), ("1.0 / 0.0001", 10000.0)] do
    let program ← lower s!"OPENQASM 3.0; output float[64] result; result = {expression};"
    let (values, _) ← execute program
    assertTrue (((output program values).asFloat - expected).abs < 0.000001) "nonzero divisor was rejected"
  let program ← lower "OPENQASM 3.0; output complex[float[64]] result; result = 1.0 / 1.0im;"
  let (values, _) ← execute program
  assertTrue ((output program values).asComplex == (0.0, -1.0)) "imaginary divisor was treated as zero"
  for source in [
    "output int[32] result; result = 1 / 0;",
    "output float[64] result; result = 1.0 / 0.0;",
    "output float[64] result; result = 1.0 % 0.0;",
    "output complex[float[64]] result; result = 1.0 / 0.0im;",
    "output float[64] result; result = 1ns / 0ns;"
  ] do
    let program ← lower ("OPENQASM 3.0; " ++ source)
    let (result, _) := TraceBackend.run (Execution.run program #[])
    assertTrue (result matches .error .divisionByZero) "zero divisor did not report divisionByZero"

private def testCalls : IO Unit := do
  let program ← lower "OPENQASM 3.0; def read(qubit q) -> bit { return measure q; } qubit q; output bit result; result = read(q);"
  let (values, trace) ← execute program #[true]
  assertTrue ((output program values).truthy && trace.operations == #["allocate:1", "measure:0"])
    "expression call lost its quantum argument"
  let program ← lower "OPENQASM 3.0; def f(int[32] a, int[32] b) { if (a > 0) { f(a-1,a); } else { gphase(float[64](b)); } } f(1,0);"
  let (_, trace) ← execute program
  assertTrue (match trace.applied with | #[.gphase gamma] => gamma == 1.0 | _ => false) "recursive statement arguments used callee bindings"
  for source in [
    "def stop() { end; } stop();",
    "def stop() { end; } def outer() { stop(); gphase(2); } outer();",
    "def stop() -> int[32] { end; return 9; } result = stop() + 1;",
    "def stop() -> int[32] { end; return 0; } array[int[32],2] a = {1,2}; a[stop()] = 9;",
    "def stop() { end; } for uint i in [0:2] { stop(); gphase(2); }"
  ] do
    let program ← lower ("OPENQASM 3.0; output int[32] result; result = 7; " ++ source ++ " gphase(1); result = 9;")
    let (values, trace) ← execute program
    assertTrue ((output program values).asInt == 7 && trace.applied.isEmpty)
      s!"end did not terminate the whole program: {source}"

```

## Typed boundaries and static rejection

Host angle codecs preserve all bits without a float round trip. Annotated declarations
remain visible to every frontend pass, while illegal comparisons and logical operands
fail during analysis rather than at runtime.

```lean
private def testBoundaries : IO Unit := do
  let original : Angle 64 := Angle.ofNat (2^63 + 17)
  let (result, _) := TraceBackend.run (HostBoundaries.execute { theta := original })
  match result with
  | .error error => throw (IO.userError s!"host boundary failure: {repr error}")
  | .ok outputs =>
      assertTrue (outputs.copied.toNat == original.toNat) "angle codec changed low bits"
      assertTrue (outputs.half_turn.toNat == 2^63) "angle[64](pi) was not a half turn"
      assertTrue (outputs.bits.toNat == 4 && outputs.number.toNat == 4) "bit literal host output was reversed"
  for width in [32,64,80] do
    let angle := Value.cast "angle" width (.float 3.141592653589793)
    assertTrue (angle == .angle width (2^(width-1))) "angle scale overflowed"
    assertTrue ((angle.asFloat - 3.141592653589793).abs < 0.000000001) "angle to radians failed"
  let program ← lower "OPENQASM 3.0; gate rotation(theta) a { U(theta,0,0) a; } qubit q; rotation(pi) q;"
  let (_, trace) ← execute program
  assertTrue (match trace.applied with | #[.U theta phi lambda 0] => theta == 3.141592653589793 && phi == 0.0 && lambda == 0.0 | _ => false) "default gate angle was corrupted"
  let (result, trace) := TraceBackend.run (ExtendedNop.execute {})
  assertTrue ((result matches .ok _) && trace.operations == #["allocate:1"]) "extended nop required a backend"

private def testFrontend : IO Unit := do
  for source in [
    "@tag\noutput int[32] result;\nresult = 42;",
    "@tag keep\nconst int n = 42;\noutput int[32] result; result = n;",
    "@tag keep\ndef f() -> int[32] { return 42; }\noutput int[32] result; result = f();"
  ] do
    let program ← lower ("OPENQASM 3.0;\n" ++ source)
    let (values, _) ← execute program
    assertTrue ((output program values).asInt == 42) "annotated declaration disappeared"
  let program ← lower "OPENQASM 3.0;\n@tag keep\ngate g a { U(0,0,0) a; }\nqubit q; g q;"
  let (_, trace) ← execute program
  assertTrue (trace.applied.size == 1) "annotated gate was not resolved"
  for source in [
    "qubit q; bool result = q == q;",
    "complex[float[64]] a = 1.0im; bool result = a < a;",
    "array[int[32],2] a = {1,2}; bool result = a && a;",
    "qubit q; bool result = !q;",
    "array[int[32],2] a = {1,2}; bool result = a == a;"
  ] do
    let .ok parsed := QASM.parse ("OPENQASM 3.0; " ++ source)
      | throw (IO.userError "invalid rejection fixture")
    assertTrue ((QASM.analyzeTypes .default parsed) matches .error _) s!"invalid operand types were accepted: {source}"
  let program ← lower "OPENQASM 3.0; output bool result; result = 1.0im == 1.0im;"
  let (values, _) ← execute program
  assertTrue ((output program values).truthy) "complex equality was rejected"
  let .ok parsed := QASM.parse "OPENQASM 3.0;\n@tag\nbreak;"
    | throw (IO.userError "annotation control fixture did not parse")
  assertTrue ((QASM.check parsed) matches .error _) "annotation hid illegal control flow"

```

## Compound powers across emission

Noncommuting rotations distinguish a power of a sequence from a sequence of powered
factors. Backend unitary syntax must agree before and after emitting the canonical IR;
the comparison includes grouping, exponent, parameters, and wire order.

```lean
private partial def unitaryKey : Unitary Nat → String
  | .U theta phi lambda wire => s!"U:{theta}:{phi}:{lambda}:{wire}"
  | .gphase gamma => s!"phase:{gamma}"
  | .named name parameters wires => s!"{name}:{parameters}:{wires}"
  | .sequence operations => s!"seq:{operations.map unitaryKey}"
  | .inverse operation => s!"inv:{unitaryKey operation}"
  | .power exponent operation => s!"pow:{exponent}:{unitaryKey operation}"
  | .controlled polarity wires operation => s!"ctrl:{repr polarity}:{wires}:{unitaryKey operation}"

private def testEmission : IO Unit := do
  let program ← lower "OPENQASM 3.0; gate pair(theta) a { U(theta,0,pi) a; U(pi/2,0,pi) a; } gate __qasm_power_2 a { U(0,0,0) a; } qubit q; pair(pi) q;"
  let exponent : IR.Expr := { type := .scalar (.float 64), node := .floatLit 2.0 }
  let program := { program with gates := program.gates.map fun gate =>
    if gate.name == "pair" then { gate with body := .power exponent gate.body } else gate }
  let (_, before) ← execute program
  let reparsed ← lower (toString program)
  let (_, after) ← execute reparsed
  assertTrue (before.applied.map unitaryKey == after.applied.map unitaryKey)
    "emission distributed a compound power or lost its captured parameters"

private def testExactSyntax : IO Unit := do
  let .ok literal := IR.DecimalLiteral.parse "0.10000000000000000000000000000000000001"
    | throw (IO.userError "exact decimal rejected")
  assertTrue (literal.significand == 10000000000000000000000000000000000001 &&
      literal.exponent10 == -38) "decimal was rounded before lowering"
  let program ← lower "OPENQASM 3.0; output float[64] result; result = 0.10000000000000000000000000000000000001;"
  assertTrue (((toString program).splitOn literal.toQasm).length > 1)
    "canonical emission lost exact digits"
  let program ← lower "OPENQASM 3.0; output angle[64] result; result = pi + pi / 4611686018427387904;"
  let (values, _) ← execute program
  assertTrue (output program values == .angle 64 (2^63 + 2))
    "exact representable angle was rounded through Float"
  let reparsed ← lower (toString program)
  let (values, _) ← execute reparsed
  assertTrue (output reparsed values == .angle 64 (2^63 + 2))
    "exact angle changed after emission"
  let finite ← lower "OPENQASM 3.0; output angle[64] result; result = float[64](pi + pi / 4611686018427387904);"
  let (finiteValues, _) ← execute finite
  assertTrue (output finite finiteValues == .angle 64 (2^63))
    "an explicit finite-precision cast was reinterpreted symbolically"
  let program ← lower "OPENQASM 3.0; gate rotate(theta) q { U(theta,0,0) q; } qubit q; rotate(1e-20) q;"
  assertTrue (program.gates[0]!.parameters[0]!.type == .scalar .gateAngle)
    "gate parameter was assigned a fixed precision"
  let (_, trace) ← execute program
  assertTrue (trace.applied.any fun operation => match operation with
    | .U theta _ _ _ => theta > 0 && theta < 1e-19
    | _ => false) "small gate angle was quantized to zero"

private def testQFTLoops : IO Unit := do
  for n in List.range 7 do
    let program := IR.QFT.canonical n
    let (_, trace) ← execute program
    let expected := n + n*(n-1)/2 + n/2
    assertTrue (trace.applied.size == expected) s!"QFT gate count incorrect at {n}"
    let reparsed ← lower (toString program)
    let (_, emittedTrace) ← execute reparsed
    assertTrue (trace.applied.map unitaryKey == emittedTrace.applied.map unitaryKey)
      s!"QFT loops or dyadic angles changed after emission at {n}"

private def testFailureRestoration : IO Unit := do
  let localVar : IR.Var := { id := ⟨100⟩, name := "local", type := .scalar (.sint 64) }
  let global : IR.Var := { id := ⟨101⟩, name := "global", type := .scalar (.sint 64) }
  let literal := fun value => { type := localVar.type, node := IR.ExprNode.intLit value : IR.Expr }
  let assign := fun value => IR.Proc.operation (IR.Op.assign
    { root := global.id, type := global.type } (literal value))
  let proc := IR.Proc.scope #[localVar] (.sequence #[
    .operation (.declare localVar (some (literal 7))), assign 8,
    .operation (.unsupported .calibration "stop"), assign 9])
  let initial : Execution.ExecutionState Nat := {
    values := (({} : Std.HashMap IR.VarId Value).insert localVar.id (.integer 42)).insert global.id (.integer 0) }
  let ((final, outcome), _) := TraceBackend.run (Execution.runFrom ({} : IR.Program) proc initial)
  assertTrue (final.values[localVar.id]? == some (.integer 42)) "failure did not restore lexical binding"
  assertTrue ((final.values[global.id]?.getD .unit).asInt == 8) "failure executed the sequence tail"
  assertTrue (match outcome with | .error (.internal "stop") => true | _ => false)
    "failure was converted into whole-program termination"


def run : IO Unit := do
  testOutputs
  testCalls
  testBoundaries
  testFrontend
  testEmission
  testExactSyntax
  testQFTLoops
  testFailureRestoration

end QASMTests.Regression
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
