    import LiterateLean
    import Mathlib.Analysis.SpecialFunctions.Log.Basic
    import QASM.IR.ExactRealExpr
    import QASMVerification.Quantum
    open scoped LiterateLean

# Domain-checked symbolic real evaluation

Evaluation is a relation so an undefined expression has no value. Typed integer
embeddings are supplied by the classical evaluator, not reinterpreted as unbounded
integer arithmetic. Division and square roots have explicit domain premises. Real
powers use the positive-base profile; zero and negative bases require separate rules.

```lean
noncomputable section
namespace QASMVerification
open QASM.IR
structure RealEnvironment where
  parameter : VarId → ℝ → Prop
  integer : Expr → Int → Prop

def constantValue : RealConstant → ℝ
  | .pi => Real.pi
  | .tau => 2 * Real.pi
  | .euler => Real.exp 1

def decimalValue (d : DecimalLiteral) : ℝ :=
  if d.exponent10 ≥ 0 then (d.significand : ℝ) * 10 ^ d.exponent10.toNat
  else (d.significand : ℝ) / 10 ^ (-d.exponent10).toNat

inductive RealEval (env : RealEnvironment) : ExactRealExpr → ℝ → Prop where
  | rational (h : d ≠ 0) : RealEval env (.rational a d) ((a : ℝ) / d)
  | decimal : RealEval env (.decimal d) (decimalValue d)
  | constant : RealEval env (.constant c) (constantValue c)
  | parameter (h : env.parameter v x) : RealEval env (.parameter v) x
  | integer (h : env.integer e i) : RealEval env (.intValue e) (i : ℝ)
  | neg (h : RealEval env e x) : RealEval env (.neg e) (-x)
  | add (ha : RealEval env a x) (hb : RealEval env b y) : RealEval env (.add a b) (x+y)
  | sub (ha : RealEval env a x) (hb : RealEval env b y) : RealEval env (.sub a b) (x-y)
  | mul (ha : RealEval env a x) (hb : RealEval env b y) : RealEval env (.mul a b) (x*y)
  | div (ha : RealEval env a x) (hb : RealEval env b y) (h : y ≠ 0) :
      RealEval env (.div a b) (x/y)
  | pow (ha : RealEval env a x) (hb : RealEval env b y) (h : 0 < x) :
      RealEval env (.pow a b) (Real.exp (y * Real.log x))
  | sin (h : RealEval env e x) : RealEval env (.sin e) (Real.sin x)
  | cos (h : RealEval env e x) : RealEval env (.cos e) (Real.cos x)
  | exp (h : RealEval env e x) : RealEval env (.exp e) (Real.exp x)
  | sqrt (he : RealEval env e x) (h : 0 ≤ x) : RealEval env (.sqrt e) (Real.sqrt x)

/-- Exact bit-angle value, with a separate range predicate. -/
def bitAngle (width bits : Nat) : ℝ := 2 * Real.pi * bits / (2 ^ width : ℝ)
def ValidBitAngle (width bits : Nat) : Prop := bits < 2 ^ width
end QASMVerification
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
