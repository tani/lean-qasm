    import LiterateLean
    import QASM.IR.Expr
    open scoped LiterateLean

# Symbolic gate arithmetic

Exact gate arithmetic is syntax, not a host floating-point value. Integer embeddings
retain their original typed expression: extracting a gate argument does not silently
replace fixed-width integer computations by unbounded arithmetic. Explicit casts and
effectful subroutine calls are not admitted by this extraction pass.

```lean
namespace QASM.IR

inductive ExactRealExpr (size : Type := Nat) (integer : Type := Int) where
  | rational (numerator : Int) (denominator : Nat)
  | decimal (literal : DecimalLiteral)
  | constant (value : RealConstant)
  | parameter (id : VarId)
  | intValue (value : Expr size integer)
  | neg (value : ExactRealExpr size integer)
  | add (left right : ExactRealExpr size integer)
  | sub (left right : ExactRealExpr size integer)
  | mul (left right : ExactRealExpr size integer)
  | div (left right : ExactRealExpr size integer)
  | pow (left right : ExactRealExpr size integer)
  | sin (value : ExactRealExpr size integer)
  | cos (value : ExactRealExpr size integer)
  | exp (value : ExactRealExpr size integer)
  | sqrt (value : ExactRealExpr size integer)
  deriving Repr, BEq, Inhabited

```

## Checked extraction

The caller selects the symbolic gate precision profile before using this interpretation.
An ordinary floating-point expression is still evaluated by the classical model.
The pass below recognizes only the explicit symbolic grammar and refuses an explicit
cast, a machine float literal, a classical float variable, or a call with side effects.
The real evaluator additionally checks division, powers, and square-root domains.

```lean
private def extract (fuel : Nat) (value : Expr size integer) : Option (ExactRealExpr size integer) :=
  match fuel with
  | 0 => none
  | fuel + 1 => match value.node with
    | .intLit _ => some (.intValue value)
    | .decimalLit literal => some (.decimal literal)
    | .realConstant literal => some (.constant literal)
    | .var id => match value.type with
      | .scalar .gateAngle => some (.parameter id)
      | .scalar (.sint _) | .scalar (.uint _) => some (.intValue value)
      | _ => none
    | .unary .neg operand => .neg <$> extract fuel operand
    | .binary op left right => do
      let left ← extract fuel left
      let right ← extract fuel right
      match op with
      | .add => some (.add left right)
      | .sub => some (.sub left right)
      | .mul => some (.mul left right)
      | .div => some (.div left right)
      | .pow => some (.pow left right)
      | _ => none
    | .builtin op args => do
      match args.toList with
      | [arg] =>
        let arg ← extract fuel arg
        match op with
        | .sin => some (.sin arg)
        | .cos => some (.cos arg)
        | .exp => some (.exp arg)
        | .sqrt => some (.sqrt arg)
        | _ => none
      | _ => none
    | _ => none

/-- Bounded, total extraction; insufficient fuel rejects the expression. -/
def ExactRealExpr.ofExpr? (value : Expr size integer) (fuel : Nat := 1024) : Option (ExactRealExpr size integer) :=
  extract fuel value

end QASM.IR
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
