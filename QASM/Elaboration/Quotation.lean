    import LiterateLean
    import Lean
    import QASM.IR.Program
    import QASM.Frontend.Parameters
    open scoped LiterateLean

# Quoting persistent IR values

These metaprogramming-only orphan instances quote ordinary IR data into generated declarations without coupling the IR modules themselves to Lean elaboration APIs.

Quotation crosses only the compile-time persistence boundary:

```mermaid
flowchart LR
    IR["in-memory IR.Program"] --> ToExpr
    ToExpr --> Syntax["Lean expression syntax"]
    Syntax --> Declaration["generated program declaration"]
    Declaration --> Runtime["runtime interpreter"]
```

For closed programs the instances preserve data constructor-for-constructor.
`quoteTemplate` uses local quotation instances to replace symbolic sizes and integers
with ordinary Lean terms. It never executes the program or chooses a parameter value.
`templateValidity` collects positivity obligations for every residual size.

```lean
namespace QASM.Elaboration

open Lean
instance : ToExpr Float where
  toExpr value := mkApp (mkConst ``Float.ofBits) (toExpr value.toBits)
  toTypeExpr := mkConst ``Float


deriving instance ToExpr for QASM.IR.SourceSpan

deriving instance ToExpr for QASM.IR.VarId
deriving instance ToExpr for QASM.IR.DeclId
deriving instance ToExpr for QASM.IR.CallableId
deriving instance ToExpr for QASM.IR.Capability
deriving instance ToExpr for QASM.IR.ControlPolarity

deriving instance ToExpr for QASM.IR.ScalarTy
deriving instance ToExpr for QASM.IR.Type

deriving instance ToExpr for QASM.IR.WireTy
deriving instance ToExpr for QASM.IR.WirePermutation

deriving instance ToExpr for QASM.IR.UnaryOp
deriving instance ToExpr for QASM.IR.BinaryOp
deriving instance ToExpr for QASM.IR.Builtin
deriving instance ToExpr for QASM.IR.Expr, QASM.IR.ExprNode
deriving instance ToExpr for QASM.IR.Var
deriving instance ToExpr for QASM.IR.LValue

deriving instance ToExpr for QASM.IR.PrimitiveKind
deriving instance ToExpr for QASM.IR.Primitive
deriving instance ToExpr for QASM.IR.ControlSpec
deriving instance ToExpr for QASM.IR.Circuit

deriving instance ToExpr for QASM.IR.QuantumOperand
deriving instance ToExpr for QASM.IR.ClassicalTarget
deriving instance ToExpr for QASM.IR.QuantumDecl
deriving instance ToExpr for QASM.IR.GateModifier
deriving instance ToExpr for QASM.IR.CircuitRef
deriving instance ToExpr for QASM.IR.Argument
deriving instance ToExpr for QASM.IR.ExternCall
deriving instance ToExpr for QASM.IR.Op
deriving instance ToExpr for QASM.IR.IterationDomain
deriving instance ToExpr for QASM.IR.Proc, QASM.IR.SwitchCase

deriving instance ToExpr for QASM.IR.Version
deriving instance ToExpr for QASM.IR.TargetConfig
deriving instance ToExpr for QASM.IR.Dialect
deriving instance ToExpr for QASM.IR.ProgramOrigin
deriving instance ToExpr for QASM.IR.IncludeInfo
deriving instance ToExpr for QASM.IR.Annotation
deriving instance ToExpr for QASM.IR.Pragma
deriving instance ToExpr for QASM.IR.IODecl
deriving instance ToExpr for QASM.IR.ConstantDecl
deriving instance ToExpr for QASM.IR.TypeDecl
deriving instance ToExpr for QASM.IR.ExternDecl
deriving instance ToExpr for QASM.IR.GateDecl
deriving instance ToExpr for QASM.IR.SubroutineDecl
deriving instance ToExpr for QASM.IR.Program

/-- Quote a template directly as concrete constructors containing open Lean terms. -/
private def quoteInteger (variables : Array (String × Lean.Expr)) :
    QASM.Parameters.Integer → Lean.Expr
  | .literal value => toExpr value
  | .parameter name =>
      mkApp (mkConst ``Int.ofNat) (variables.find? (·.1 == name) |>.get! |>.2)
  | .add left right => mkApp2 (mkConst ``Int.add) (quoteInteger variables left) (quoteInteger variables right)
  | .sub left right => mkApp2 (mkConst ``Int.sub) (quoteInteger variables left) (quoteInteger variables right)
  | .mul left right => mkApp2 (mkConst ``Int.mul) (quoteInteger variables left) (quoteInteger variables right)
  | .neg value => mkApp (mkConst ``Int.neg) (quoteInteger variables value)

def quoteTemplate (variables : Array (String × Lean.Expr))
    (program : QASM.IR.Program QASM.Parameters.Size QASM.Parameters.Integer) : Lean.Expr :=
  letI : ToExpr QASM.Parameters.Integer :=
    { toExpr := quoteInteger variables, toTypeExpr := mkConst ``Int }
  letI : ToExpr QASM.Parameters.Size :=
    { toExpr := fun size => match size.value.closed? with
        | some value => toExpr value.toNat
        | none => mkApp (mkConst ``Int.toNat) (quoteInteger variables size.value),
      toTypeExpr := mkConst ``Nat }
  toExpr program

private partial def symbolicSizes (expression : Lean.Expr) : Array Lean.Expr :=
  let own := if expression.isAppOfArity ``Int.toNat 1 then #[expression.appArg!] else #[]
  match expression with
  | .app fn argument => own ++ symbolicSizes fn ++ symbolicSizes argument
  | _ => own

/-- Positivity conditions for every residual width and extent in a quoted family. -/
def templateValidity (expression : Lean.Expr) : Lean.Expr :=
  let sizes := (symbolicSizes expression).foldl
    (fun values value => if values.contains value then values else values.push value) #[]
  sizes.foldr (fun size rest =>
    mkApp2 (mkConst ``And)
      (mkApp4 (mkConst ``LT.lt [.zero]) (mkConst ``Int) (mkConst ``Int.instLTInt) (toExpr (0 : Int)) size) rest) (mkConst ``True)

end QASM.Elaboration
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
