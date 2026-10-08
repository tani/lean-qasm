    import LiterateLean
    import QASM
    open scoped LiterateLean

# Parameterized QASM regression tests and kernel proofs

These families test residual allocation sizes, dependent I/O, multiple parameters, symbolic
constant aliases, runtime loop bounds, and scoped declarations. The proof cases quantify
over Lean variables; no concrete size is chosen while proving the generated IR equations.

```lean
namespace QASMTests.Parametric

open QASM

qasm! Allocate (n : Nat) {
  OPENQASM 3.0;
  qubit[n] q;
}

qasm! Rotate (n : Nat) {
  OPENQASM 3.0;
  include "stdgates.inc";
  input float[64] theta;
  qubit[n] q;
  for uint i in [0:n - 1] { rz(theta) q[i]; }
}

qasm! Copy (n : Nat) {
  OPENQASM 3.0;
  input bit[n] value;
  output bit[n] result;
  result = value;
}

qasm! Arrays (n : Nat) (m : Nat) {
  OPENQASM 3.0;
  const uint extent = n + m;
  input array[int[32], extent] values;
  output array[int[32], extent] result;
  result = values;
}

qasm! Nested (n : Nat) {
  OPENQASM 3.0;
  if (true) { qubit[n + 1] q; }
}

qasm! Slice (n : Nat) {
  OPENQASM 3.0;
  input array[int[32], n + 1] values;
  output array[int[32], n + 1] result;
  result = values[0:n];
}

qasm! Subroutine (n : Nat) {
  OPENQASM 3.0;
  def getParameter() -> uint { return n; }
  output uint result;
  result = getParameter();
}

qasm! ParameterGate (n : Nat) {
  OPENQASM 3.0;
  include "stdgates.inc";
  gate rotate a { rz(n) a; }
  qubit q;
  rotate q;
}

qasm! Hygiene (inputs : Nat) (qasmM : Nat) (_valid : Nat) {
  OPENQASM 3.0;
  qubit[inputs + qasmM + _valid + 1] q;
}

-- The generated allocation contains the variable itself, not a chosen instance.
theorem allocate_size (n : Nat) :
    (Allocate.program n).body = .operation (.allocate
      { var := ⟨0⟩, name := "q", size := n, origin := { fileName := "<qasm!>" } }) := by
  rfl

theorem allocate_valid (n : Nat) : Allocate.Valid (n + 1) := by
  simp [Allocate.Valid] <;> omega

theorem allocate_zero_invalid : ¬ Allocate.Valid 0 := by
  simp [Allocate.Valid]

theorem copy_input_width (n : Nat) :
    ((Copy.program n).inputs[0]!).var.type = .scalar (.bit (some n)) := by
  rfl

theorem copy_output_width (n : Nat) :
    ((Copy.program n).outputs[0]!).var.type = .scalar (.bit (some n)) := by
  rfl

-- A control-flow optimization law applies to an open family just as to arbitrary IR.
theorem rotate_skip_neutral (n : Nat) {State : Type}
    (model : Execution.Semantics.Model State) :
    Execution.Semantics.Equivalent model
      (.sequence #[.skip, (Rotate.program n).body]) (Rotate.program n).body :=
  Execution.Semantics.sequence_skip_left model _

end QASMTests.Parametric
```

## Concrete execution and diagnostics

Execution supplies numerical parameters only at the call site. The generated wrappers
require proof of positive residual dimensions. Rejected examples exercise symbolic shape
mismatch, unsupported symbolic arithmetic, and contexts requiring a fixed circuit arity.

```lean
namespace QASMTests.Parametric

open QASM

private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def run : IO Unit := do
  for predecessor in [0, 1, 4] do
    let n := predecessor + 1
    let valid : Allocate.Valid n := allocate_valid predecessor
    let (result, trace) := TraceBackend.run (Allocate.execute n valid {})
    assertTrue (result matches .ok _) s!"allocation family failed at {n}"
    assertTrue (trace.operations == #[s!"allocate:{n}"]) "allocation family lost its size"
  let valid : Copy.Valid 5 := by decide
  let (result, _) := TraceBackend.run
    (Copy.execute 5 valid { value := BitVec.ofNat 5 19 })
  match result with
  | .ok output => assertTrue (output.result.toNat == 19) "dependent bit I/O changed its value"
  | .error error => throw (IO.userError s!"dependent bit I/O failed: {repr error}")
  let valid : Rotate.Valid 3 := by decide
  let (result, trace) := TraceBackend.run (Rotate.execute 3 valid { theta := 0.5 })
  assertTrue (result matches .ok _) "parameterized loop failed"
  assertTrue (trace.operations.size == 4) "parameterized loop was expanded at elaboration"
  let valid : Arrays.Valid 2 3 := by decide
  let values : FixedArray (SInt 32) [5] := ⟨#[1, 2, 3, 4, 5].map (SInt.ofInt (width := 32)), by simp⟩
  let (result, _) := TraceBackend.run (Arrays.execute 2 3 valid { values })
  match result with
  | .ok output => assertTrue (output.result.data == values.data) "symbolic array extent changed its data"
  | .error error => throw (IO.userError s!"symbolic array I/O failed: {repr error}")
  let valid : Slice.Valid 4 := by decide
  let (result, _) := TraceBackend.run (Slice.execute 4 valid { values })
  match result with
  | .ok output => assertTrue (output.result.data == values.data) "symbolic slice shape was lost"
  | .error error => throw (IO.userError s!"symbolic slice failed: {repr error}")
  let (result, _) := TraceBackend.run (Subroutine.execute 7 (by decide) {})
  match result with
  | .ok output => assertTrue (output.result.toNat == 7) "subroutine lost its family parameter"
  | .error error => throw (IO.userError s!"parameterized subroutine failed: {repr error}")
  let (result, _) := TraceBackend.run (ParameterGate.execute 2 (by decide) {})
  assertTrue (result matches .ok _) "gate expression lost its family parameter"
  let (result, trace) := TraceBackend.run (Hygiene.execute 1 2 3 (by decide) {})
  assertTrue (result matches .ok _) "generated binders captured a family parameter"
  assertTrue (trace.operations == #["allocate:7"]) "generated binder hygiene changed a size"
  let source := "OPENQASM 3.0; array[int[32], n] a; array[int[32], m] b; a = b;"
  let .ok parsed := QASM.parse source | throw (IO.userError "bad diagnostic fixture")
  assertTrue ((Frontend.analyzeTypes .default parsed #["n", "m"]) matches .error _)
    "distinct symbolic shapes were accepted as equal"
  let source := "OPENQASM 3.0; qubit[n / 2] q;"
  let .ok parsed := QASM.parse source | throw (IO.userError "bad arithmetic fixture")
  assertTrue ((Frontend.analyzeTypes .default parsed #["n"]) matches .error _)
    "unsupported symbolic arithmetic was silently approximated"
  for source in [
      "OPENQASM 3.0; float[n] x;",
      "OPENQASM 3.0; if (true) { uint n = 1; qubit[n] q; }",
      "OPENQASM 3.0; qubit q; ctrl(n) @ U(0,0,0) q;"
    ] do
    let .ok parsed := QASM.parse source | throw (IO.userError "bad rejection fixture")
    assertTrue ((Frontend.analyzeTypes .default parsed #["n"]) matches .error _)
      s!"invalid symbolic context was accepted: {source}"
  let source := "OPENQASM 3.0; gate repeat a { for uint i in [0:n] { U(0,0,0) a; } }"
  let .ok parsed := QASM.parse source | throw (IO.userError "bad gate-loop fixture")
  let .ok analysis := Frontend.analyzeTypes .default parsed #["n"]
    | throw (IO.userError "gate-loop fixture failed before lowering")
  assertTrue ((Lowering.template parsed analysis) matches .error _)
    "symbolic gate loop was expanded using a representative value"

end QASMTests.Parametric
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
