    import LiterateLean
    import QASM.IR.Expr
    import QASM.IR.Circuit
    import QASM.IR.Name
    import QASM.IR.Type
    open scoped LiterateLean

# First-order process IR

Processes represent effects and structured control flow without higher-order syntax.
Expressions remain pure; measurement, mutation, allocation, calls, and backend interaction
occur only through `Op`, while `Proc` determines sequencing and non-local control.

```lean
namespace QASM.IR

```

## Operands, calls, and atomic effects

Quantum and classical operands are distinct variants, and mutable array arguments carry
their writeback contract explicitly. `CircuitRef` resolves a gate target while retaining
parameters and modifiers. Atomic operations are the only process nodes allowed to change
interpreter state or cross `QuantumBackend`.

```lean
inductive QuantumOperand
  | wire     (var : VarId) (indices : Array Expr := #[]) (approximate : Bool := false)
  | physical (index : Nat)
  deriving Repr, BEq, Inhabited

inductive ClassicalTarget
  | lvalue (target : LValue)
  | discard
  deriving Repr, BEq, Inhabited

structure QuantumDecl where
  var    : VarId
  name   : Name
  size   : Nat
  origin : SourceSpan := {}
  deriving Repr, BEq, Inhabited

inductive GateModifier
  | inverse
  | power   (exponent : Expr)
  | control (negate : Bool) (count : Nat)
  deriving Repr, BEq, Inhabited

structure CircuitRef where
  target     : PrimitiveKind
  name       : Name
  parameters : Array Expr := #[]
  modifiers  : Array GateModifier := #[]
  origin     : SourceSpan := {}
  deriving Repr, BEq, Inhabited

inductive Argument
  | expr     (value : Expr)
  | quantum  (operand : QuantumOperand)
  | arrayRef (target : LValue) (mutable : Bool)
  deriving Repr, BEq, Inhabited

structure ExternCall where
  callee    : DeclId
  arguments : Array Expr := #[]
  origin    : SourceSpan := {}
  deriving Repr, BEq, Inhabited

inductive Op
  | eval        (value : Expr)
  | declare     (var : Var) (init : Option Expr)
  | assign      (target : LValue) (value : Expr)
  | apply       (gate : CircuitRef) (operands : Array QuantumOperand)
  | measure     (source : QuantumOperand) (target : ClassicalTarget)
  | reset       (operand : QuantumOperand)
  | barrier     (operands : Array QuantumOperand)
  | allocate    (decl : QuantumDecl)
  | call        (callee : CallableId) (arguments : Array Argument)
  | emitExtern  (call : ExternCall)
  | unsupported (capability : Capability) (detail : String)
  deriving Repr, BEq, Inhabited

```

## Iteration and structured control

Iteration domains distinguish ranges, explicit sets, and array values after expression
typing. `Proc.scope` names every local binding that must be restored on exit, and explicit
flow nodes model `break`, `continue`, `return`, and `end` without exceptions or closures.

```lean
inductive IterationDomain
  | range (start step stop : Expr)
  | set   (values : Array Expr)
  | array (value : Expr)
  deriving Repr, BEq, Inhabited

mutual
inductive Proc
  | skip
  | operation   (op : Op)
  | sequence    (steps : Array Proc)
  | scope       (locals : Array Var) (body : Proc)
  | branch      (cond : Expr) (thenBranch : Proc) (elseBranch : Option Proc)
  | switch      (scrutinee : Expr) (cases : Array SwitchCase) (default : Option Proc)
  | forLoop     (iterator : Var) (domain : IterationDomain) (body : Proc)
  | whileLoop   (cond : Expr) (body : Proc)
  | breakLoop
  | continueLoop
  | returnValue (value : Option Expr)
  | endProgram
inductive SwitchCase
  | mk (labels : Array Expr) (body : Proc)
end

deriving instance Repr, BEq for Proc, SwitchCase

instance : Inhabited Proc := ⟨.skip⟩

instance : Inhabited SwitchCase := ⟨.mk #[] .skip⟩

end QASM.IR
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
