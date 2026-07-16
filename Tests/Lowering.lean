    import LiterateLean
    import QASM.Lowering.Program
    open scoped LiterateLean

# Lowering regression corpus

The official grammar corpus contains many constructs that are grammatically valid but not
portable on the default backend. This standalone audit embeds the relevant source text so
the parse/check/lower classification is deterministic and performs no filesystem I/O
during `#eval`.

Each corpus entry follows one classification path:

```mermaid
flowchart LR
    Source --> Parse
    Parse -->|syntax error| ParseRejected
    Parse -->|AST| Check
    Check -->|diagnostic| CheckRejected
    Check -->|analysis| Lower
    Lower -->|portable program| Lowered
    Lower -->|capability boundary| Nonportable
    Lower -->|lowering diagnostic| LoweringRejected
```

The category counts form a partition of the audited inputs, so with counts $`n_i`$,

```math
N_{\mathrm{audited}} = \sum_i n_i.
```

```lean
open QASM

private def validSources : Array (String × String) := #[
  ("Tests/Fixtures/OpenQASM30/source/grammar/tests/reference/assignment/alias.yaml", "bit[2] a;\ncreg b[2];\nqubit[5] q1;\nqreg q2[7];\nlet q = q1 ++ q2;\nlet c = a[{0,1}] ++ b[1:2];\nlet qq = q1[{1,3,4}];\nlet qqq = qq ++ q2[1:2:6];\nlet d = c;\nlet e = d[1];\n"),
  ("Tests/Fixtures/OpenQASM30/source/grammar/tests/reference/assignment/assignment.yaml", "bit[2] a;\ncreg b[2];\nqubit[3] q;\nint[10] x = 12;\na[0] = b[1];\nx += int[10](a[1]);\nmeasure q[1] -> a[0];\na = measure q[1:2];\nmeasure q[0];\nb = a == 0;\n"),
  ("Tests/Fixtures/OpenQASM30/source/grammar/tests/reference/assignment/slices.yaml", "array[uint[16], 2, 2] a = {{1, 2}, {3, 4}};\narray[uint[16], 2, 4] b = {{1, 2, 3, 4}, {5, 6, 7, 8}};\n// Various forms of testing that assignments can be made to indexed\n// identifiers, and from indexed identifiers.\na = b[0:1][0:1];\na[0:1] = b[0:1][0:1];\na[0] = b[0][0:1];\na[0][0] = b[0][0];\na[0][0:1] = b[1][1:2:3];\na[0:1][0] = b[0:1][0];\na[0:1][0:1] = b[0:1][0:1];\n"),
  ("Tests/Fixtures/OpenQASM30/source/grammar/tests/reference/control_flow/branch_binop.yaml", "if(spec[i] == 0 && spec[n+i] == 1) {\n  x q[i];\n}\n"),
  ("Tests/Fixtures/OpenQASM30/source/grammar/tests/reference/control_flow/branching.yaml", "if (x == a) {\n  for uint i in [0:2:4] x[i] += 1;\n}\nelse CX x[0], x[1];\n"),
  ("Tests/Fixtures/OpenQASM30/source/grammar/tests/reference/control_flow/loop.yaml", "while (i < 10) {\n  for uint j in {1, 4, 6} reset q[j];\n  if (i == 8) break;\n  else continue;\n}\nend;\n"),
  ("Tests/Fixtures/OpenQASM30/source/grammar/tests/reference/declaration/array.yaml", "array[uint[16], 1] x;\narray[int[8], 4] x;\narray[float[64], 4, 2] x;\narray[angle[32], 4, 3, 2] x;\narray[bit[8], 2] x;\narray[bit[16], 2, 2] x;\narray[complex[float[32]], 4] x;\narray[bool, 3] x;\narray[int[8], 4] x = {1, 2, 3, 4};\narray[int[8], 4] x = y;\narray[int[8], 2] x = {y, y+y};\narray[uint[32], 2, 2] x = {{3, 4}, {2-3, 5*y}};\narray[uint[32], 2, 2] x = {z, {2-3, 5*y}};\narray[uint[32], 2, 2] x = {2*z, {1, 2}};\narray[uint[32], 2, 2] x = y;\n"),
  ("Tests/Fixtures/OpenQASM30/source/grammar/tests/reference/declaration/complex.yaml", "complex[float] a;\ncomplex[float] b = 4 - 5.5im;\ncomplex[float[64]] d = a + 3 im;\ncomplex[float[32]] c = a ** b;\ncomplex z;\n"),
  ("Tests/Fixtures/OpenQASM30/source/grammar/tests/reference/declaration/declaration.yaml", "int[10] x;\nint[10] y;\nuint[32] z = 0xFa_1F;\nuint[32] z = 0XFa_1F;\nuint[16] z = 0o12_34;\nuint[16] z = 0b1001_1001;\nuint[16] z = 0B1001_1001;\nuint x;\nqubit[6] q1;\nqubit q2;\nbit[4] b1=\"0100\";\nbit[8] b2=\"1001_0100\";\nbit b2 = \"1\";\nbool m=true;\nbool n=bool(b2);\nbool o=false;\nconst float[64] c = 5.5e3;\nconst float[64] d=5;\nfloat[32] f = .1e+3;\nduration dur = 1000dt;\nduration dur2 = dur + 200ns;\nstretch s;\n"),
  ("Tests/Fixtures/OpenQASM30/source/grammar/tests/reference/directives/annotations.yaml", "@bind [2:3]\ninput uint[16] x;\n\n@rename other\noutput float[64] var;\n\n@hello world\nint[8] x;\n\n@outer\ndef fn() {\n  @inner word1\n  uint[16] x;\n  @inner word2\n  return;\n}\n\n@first\n@second @not_third\nuint[16] x;\n\n@binds tightly\nx = 1; x = 2;\n"),
  ("Tests/Fixtures/OpenQASM30/source/grammar/tests/reference/directives/pragma.yaml", "pragma IO_BIND[2:3]\n#pragma  __directive_info__ 0\n"),
  ("Tests/Fixtures/OpenQASM30/source/grammar/tests/reference/expression/binary_expr.yaml", "2+2;\n2**2;\nx << y;\n"),
  ("Tests/Fixtures/OpenQASM30/source/grammar/tests/reference/expression/built_in_call.yaml", "int[32](10);\nsin(π);\narcsin(π);\ncos(π);\narccos(π);\ntan(π);\narctan(π);\nexp(π);\nln(π);\nsqrt(π);\nrotl(π);\nrotr(π);\npopcount(π);\nsizeof(x);\nsizeof(x, 0);\nsizeof(x, 1);\n"),
  ("Tests/Fixtures/OpenQASM30/source/grammar/tests/reference/expression/order_of_ops.yaml", "a[1]+2|c*(sin(y)^!3.5*d[3]);\nb = bit[8](a)[2:4];\n"),
  ("Tests/Fixtures/OpenQASM30/source/grammar/tests/reference/expression/sub_and_extern_call.yaml", "bit x = sub_call(10, \"01\", q1[0], q2);\nint[2] y = extern_call(0.5, 10dt);\nambiguous_call(pi);\n"),
  ("Tests/Fixtures/OpenQASM30/source/grammar/tests/reference/expression/unary_expr.yaml", "!my_var;\n"),
  ("Tests/Fixtures/OpenQASM30/source/grammar/tests/reference/gate/gate_modifiers.yaml", "qubit q;\ngate g q {}\nctrl(2) @ g q;\nnegctrl(3) @ g q;\npow(-1/2) @ g q;\ninv @ g q;\n"),
  ("Tests/Fixtures/OpenQASM30/source/grammar/tests/reference/gate/quantum_gate.yaml", "gate test_gate(theta) a, b {\n  reset a;\n  barrier b;\n  gphase(-theta/2);\n  CX a, b;\n  barrier;\n}\n"),
  ("Tests/Fixtures/OpenQASM30/source/grammar/tests/reference/header.yaml", "OPENQASM 3.0;\ninclude \"std_gates.inc\";\ninput angle[32] param1;\ninput angle[32] param2;\noutput bit result;\n"),
  ("Tests/Fixtures/OpenQASM30/source/grammar/tests/reference/pulse/cal.yaml", "cal {}\ncal {One long, otherwise invalid token.}\ncal {Outer {nested} outer}\n"),
  ("Tests/Fixtures/OpenQASM30/source/grammar/tests/reference/pulse/defcal.yaml", "defcal x $0 {}\ndefcal measure $0 -> bit {Outer {nested} outer}\ndefcal rz(angle[20] theta) q {£$&£*(\")}\ndefcal rz(pi / 2) q {Symbolic expression.}\n"),
  ("Tests/Fixtures/OpenQASM30/source/grammar/tests/reference/subroutine/array.yaml", "def test_array_1(mutable array[uint[16], 4, 2] a) {}\ndef test_array_2(readonly array[uint[16], 4, 2] a) {}\ndef test_array_3(mutable array[uint[16], #dim=2] a) {}\ndef test_array_4(readonly array[uint[16], #dim=2*n] a) {}\ndef test_array_5(readonly array[int[8], #dim=1] a, mutable array[complex[float[64]], #dim=3] b, readonly array[complex[float[64]], 2, 2] c) -> int[8] {}\n"),
  ("Tests/Fixtures/OpenQASM30/source/grammar/tests/reference/subroutine/extern.yaml", "extern test_kern(bit[5], uint[10], float[16], complex[float[64]]) -> float[6];\n"),
  ("Tests/Fixtures/OpenQASM30/source/grammar/tests/reference/subroutine/subroutine.yaml", "def test_sub1(int[5] i, qubit[2] q1, qreg q2[5]) -> int[10] {\n  int[10] result;\n  if (result == 2) return 1 + result;\n  return result;\n}\ndef test_sub2(int[5] i, bit[2] b, creg c[3]) {\n  for int[5] j in {2, 3}\n    i += j;\n  return i+1;\n}\ndef returns_a_measure(qubit q) {\n  return measure q;\n}\n")
]

```

## Invalid grammar corpus

Invalid fixtures must fail in the frontend before semantic checking or lowering. Keeping
their labels beside the source makes an unexpected acceptance identify the originating
official fixture.

```lean
private def invalidSources : Array (String × String) := #[
  ("Tests/Fixtures/OpenQASM30/source/grammar/tests/invalid/statements/branch.qasm", "if true x $0;\nif false { x $0; }\nif (myvar += 1) { x $0; }\nif (int[8] myvar = 1) { x $0; }\nif (true);\nif (true) else x $0;\nif (true) else (false) x $0;\nif (reset $0) { x $1; }\n"),
  ("Tests/Fixtures/OpenQASM30/source/grammar/tests/invalid/statements/calibration.qasm", "defcalgrammar \"openpulse\" defcalgrammar \"openpulse\";\ndefcalgrammar 3;\ndefcal x $0 -> int[8] -> int[8] {}\n"),
  ("Tests/Fixtures/OpenQASM30/source/grammar/tests/invalid/statements/const.qasm", "const myvar;\nconst myvar = ;\nconst myvar = 8.0;\ninput const myvar = 8;\noutput const myvar = 8;\nconst input myvar = 8;\nconst output myvar = 8;\n"),
  ("Tests/Fixtures/OpenQASM30/source/grammar/tests/invalid/statements/declarations.qasm", "// Not specifying the variable.\nfloat;\nuint[8];\nqreg[4];\ncreg[4];\ncomplex[float[32]];\n\n// Incorrect designators.\nint[8, 8] myvar;\nuint[8, 8] myvar;\nfloat[8, 8] myvar;\nangle[8, 8] myvar;\nbool[4] myvar;\nbool[4, 4] myvar;\nbit[4, 4] myvar;\ncreg[2] myvar;\ncreg[2, 2] myvar;\nqreg[2] myvar;\nqreg[2, 2] myvar;\ncomplex[32] myvar;\ncomplex[mytype] myvar;\ncomplex[float[32], float[32]] myvar;\ncomplex[qreg] myvar;\ncomplex[creg] myvar;\ncomplex[qreg[8]] myvar;\ncomplex[creg[8]] myvar;\n\n// Bad array specifiers.\narray myvar;\narray[8] myvar;\narray[not_a_type, 4] myvar;\narray[int[8], int[8], 2] myvar;\n\n// Invalid identifiers.\nint[8] int;\nint[8] def;\nint[8] 0;\nint[8] input;\n\n// Bad assignments.\nint[8] myvar = end;\nint[8] myvar =;\nfloat[32] myvar_f = int[32] myvar_i = 2;\n// array initialiser uses {}\narray[uint[8], 4] myvar = [4, 5, 6, 7];\n// can't use arithmetic on the entire initialiser\narray[uint[8], 4] myvar = 2 * {1, 2, 3, 4};\n// backed arrays can't use #dim\narray[uint[8], #dim=2] myvar;\n// can't have more than one type specification\narray[int[8], int[8]] myvar;\n\n// Incorrect orders.\nmyvar: int[8];\nmyvar int[8];\nint myvar[8];\nuint myvar[8];\nfloat myvar[32];\n\n// Compound assignments.\nint[8] myvar1, myvar2;\nint[8] myvari, float[32] myvarf;\nint[8] myvari float[32] myvarf;\n"),
  ("Tests/Fixtures/OpenQASM30/source/grammar/tests/invalid/statements/gate_applications.qasm", "U (1)(2) $0;\nnotmodifier @ x $0;\npow @ x $0;\npow(2, 3) @ x $0;\nctrl(2, 3) @ x $0, $1;\nnegctrl(2, 3) @ x $0, $1;\ninv(1) @ ctrl @ x $0, $1;\n\n// Global phase is defined in the grammar to be the last modifier.\ngphase(pi) @ ctrl @ x $0, $1;\n"),
  ("Tests/Fixtures/OpenQASM30/source/grammar/tests/invalid/statements/headers.qasm", "OPENQASM int;\nOPENQASM 'hello, world';\nOPENQASM 3 3;\nOPENQASM 3.x;\ninclude 3;\ninclude include;\ninclude def;\ninclude \"hello;\n"),
  ("Tests/Fixtures/OpenQASM30/source/grammar/tests/invalid/statements/io.qasm", "input int[8];\noutput int[8];\ninput qreg myvar[4];\noutput qreg myvar[4];\ninput int[8] myvar = 32;\noutput int[8] myvar = 32;\ninput myvar;\noutput myvar;\n"),
  ("Tests/Fixtures/OpenQASM30/source/grammar/tests/invalid/statements/loop.qasm", "for myvar in { 1, 2, 3 };\nfor myvar1, myvar2 in { 1, 2, 3 } { x $0; }\nfor myvar in { x $0; } { x $0; }\nfor myvar in for { x $0; }\nfor myvar { x $0; }\nfor (true) { x $0; }\nfor { x $0; }\nfor for in { 1, 2, 3 } { x $0; }\nfor in { 1, 2, 3 } { x $0; }\nwhile true { x $0; }\nwhile (true) (true) { x $0; }\nwhile x in { 1, 2, 3 } { x $0; }\nwhile (true);\n// Anonymous scopes are forbidden.\n{ x $0; z $1; }\n"),
  ("Tests/Fixtures/OpenQASM30/source/grammar/tests/invalid/statements/measure.qasm", "measure $0, $1;\na[0:1] = measure $0, $1;\na = measure $0 -> b;\ncreg a[1] = measure $0;\nmeasure $0 -> creg a[1];\nmeasure $0 -> bit[1] a;\n// Measure can't be used in sub-expressions.\na = 2 * measure $0;\na = (measure $0) + (measure $1);\n"),
  ("Tests/Fixtures/OpenQASM30/source/grammar/tests/invalid/statements/tokens.qasm", "#;\n3x;\nx@x;\n3.4.3;\n3.4e3e3;\n// Bad integer literals.\n3__4;\n3_4_;\n0b123;\n0B123;\n0o789;\n0O789;\n0x12g;\n0X12g;\n12af;\n")
]

```

## Classification passes

Valid grammar references are classified at every implemented boundary rather than assumed
to be executable programs. The summary separates frontend or semantic gaps from accepted
but target-dependent programs and from portable canonical lowering. Invalid references
remain strict: accepting one is a compile-time failure.

```lean
private structure ValidSummary where
  lowered : Nat := 0
  nonportable : Nat := 0
  parseRejected : Nat := 0
  checkRejected : Nat := 0
  loweringRejected : Nat := 0
  deriving Repr, BEq, Inhabited

private def classifyValid : ValidSummary := Id.run do
  let mut summary : ValidSummary := {}
  for (_, source) in validSources do
    match QASM.parse source with
    | .error _ => summary := { summary with parseRejected := summary.parseRejected + 1 }
    | .ok parsed =>
        match QASM.check parsed with
        | .error _ => summary := { summary with checkRejected := summary.checkRejected + 1 }
        | .ok checked =>
            match QASM.analyzeTypes {} parsed with
            | .error _ => summary := { summary with nonportable := summary.nonportable + 1 }
            | .ok analysis =>
                match QASM.Lowering.program parsed analysis with
                | .ok _ =>
                    if checked.requiredCapabilities.isEmpty then
                      summary := { summary with lowered := summary.lowered + 1 }
                    else
                      summary := { summary with nonportable := summary.nonportable + 1 }
                | .error _ =>
                    if checked.requiredCapabilities.isEmpty then
                      summary := { summary with loweringRejected := summary.loweringRejected + 1 }
                    else
                      summary := { summary with nonportable := summary.nonportable + 1 }
  pure summary

private def verifyInvalid : Except String Nat := do
  let mut rejected := 0
  for (label, source) in invalidSources do
    match QASM.parse source with
    | .error _ => rejected := rejected + 1
    | .ok _ => throw s!"{label}: invalid fixture was accepted"
  pure rejected

```

## Executable summary

The final evaluation locks the current boundary classification and invalid-fixture count.
This keeps known frontend gaps visible without allowing them to grow or migrate silently;
intentional support changes must update the explicit baseline.

```lean
private def expectedValid : ValidSummary := {
  lowered := 3
  nonportable := 15
  parseRejected := 6
}

#eval match verifyInvalid with
  | .ok invalid =>
      let actual := classifyValid
      if actual == expectedValid && invalid == invalidSources.size then (actual, invalid)
      else panic! s!"regression classification changed: valid={repr actual}, invalid={invalid}"
  | .error message => panic! message
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
