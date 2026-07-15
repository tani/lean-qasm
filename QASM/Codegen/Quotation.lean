    import LiterateLean
    import Lean
    import QASM.IR.Program
    open scoped LiterateLean

# Quoting persistent IR values

These metaprogramming-only orphan instances quote ordinary IR data into generated declarations without coupling the IR modules themselves to Lean elaboration APIs.

```lean
namespace QASM.Codegen

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

end QASM.Codegen
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
