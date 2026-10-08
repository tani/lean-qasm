    import LiterateLean
    import QASM.IR.Expr
    import QASM.IR.Circuit
    import QASM.IR.Name
    import QASM.IR.Type
    open scoped LiterateLean

# First-order process IR

Processes represent effects and structured control flow without higher-order syntax.
Measurement, mutation, allocation, and backend interaction are explicit `Op` nodes.
Expressions can call effectful subroutines when a return value is required; those calls
share operand binding and writeback semantics with statement calls. `Proc` determines
sequencing and structured control.

The effect boundary is visible in the tree shape:

```mermaid
flowchart TD
    Proc --> Control["sequence / scope / branch / loop"]
    Proc --> Op
    Op --> Classical["mutation and calls"]
    Op --> Quantum["allocation and backend effects"]
    Expr["typed Expr / value calls"] --> Op
    Expr --> Control
```

`Op` and expression calls can change state; `Proc` controls when those effects occur.

```lean
namespace QASM.IR

```

## Operands, calls, and atomic effects

Quantum and classical operands are distinct variants, and mutable array arguments carry
their writeback contract explicitly. `CircuitRef` resolves a gate target while retaining
parameters and modifiers. Atomic operations express direct effects; a subroutine invoked
from an expression can also execute them through its process body.

```lean
inductive QuantumOperand (size : Type := Nat) (integer : Type := Int)
  | wire     (var : VarId) (indices : Array (Expr size integer) := #[]) (approximate : Bool := false)
  | physical (index : Nat)
  deriving Repr, BEq, Inhabited

inductive ClassicalTarget (size : Type := Nat) (integer : Type := Int)
  | lvalue (target : (LValue size integer))
  | discard
  deriving Repr, BEq, Inhabited

structure QuantumDecl (size : Type := Nat) where
  var    : VarId
  name   : Name
  size   : size
  origin : SourceSpan := {}
  deriving Repr, BEq, Inhabited

inductive GateModifier (size : Type := Nat) (integer : Type := Int)
  | inverse
  | power   (exponent : (Expr size integer))
  | control (negate : Bool) (count : Nat)
  deriving Repr, BEq, Inhabited

structure CircuitRef (size : Type := Nat) (integer : Type := Int) where
  target     : PrimitiveKind
  name       : Name
  parameters : Array (Expr size integer) := #[]
  modifiers  : Array (GateModifier size integer) := #[]
  origin     : SourceSpan := {}
  deriving Repr, BEq, Inhabited

inductive Argument (size : Type := Nat) (integer : Type := Int)
  | expr     (value : (Expr size integer))
  | quantum  (operand : (QuantumOperand size integer))
  | arrayRef (target : (LValue size integer)) (mutable : Bool)
  deriving Repr, BEq, Inhabited

structure ExternCall (size : Type := Nat) (integer : Type := Int) where
  callee    : DeclId
  arguments : Array (Expr size integer) := #[]
  origin    : SourceSpan := {}
  deriving Repr, BEq, Inhabited

inductive Op (size : Type := Nat) (integer : Type := Int)
  | eval        (value : (Expr size integer))
  | declare     (var : (Var size)) (init : Option (Expr size integer))
  | assign      (target : (LValue size integer)) (value : (Expr size integer))
  | apply       (gate : (CircuitRef size integer)) (operands : Array (QuantumOperand size integer))
  | measure     (source : (QuantumOperand size integer)) (target : (ClassicalTarget size integer))
  | reset       (operand : (QuantumOperand size integer))
  | barrier     (operands : Array (QuantumOperand size integer))
  | allocate    (decl : (QuantumDecl size))
  | call        (callee : CallableId) (arguments : Array (Argument size integer))
  | emitExtern  (call : (ExternCall size integer))
  | unsupported (capability : Capability) (detail : String)
  deriving Repr, BEq, Inhabited

```

## Iteration and structured control

Iteration domains distinguish ranges, explicit sets, and array values after expression
typing. `Proc.scope` names every local binding that must be restored on exit, and explicit
flow nodes represent `break`, `continue`, `return`, and whole-program `end` directly.
The interpreter propagates `end` through expression calls using an internal signal.

```lean
inductive IterationDomain (size : Type := Nat) (integer : Type := Int)
  | range (start step stop : (Expr size integer))
  | set   (values : Array (Expr size integer))
  | array (value : (Expr size integer))
  deriving Repr, BEq, Inhabited

mutual
inductive Proc (size : Type := Nat) (integer : Type := Int)
  | skip
  | operation   (op : (Op size integer))
  | sequence    (steps : Array (Proc size integer))
  | scope       (locals : Array (Var size)) (body : (Proc size integer))
  | branch      (cond : (Expr size integer)) (thenBranch : (Proc size integer)) (elseBranch : Option (Proc size integer))
  | switch      (scrutinee : (Expr size integer)) (cases : Array (SwitchCase size integer)) (default : Option (Proc size integer))
  | forLoop     (iterator : (Var size)) (domain : (IterationDomain size integer)) (body : (Proc size integer))
  | whileLoop   (cond : (Expr size integer)) (body : (Proc size integer))
  | breakLoop
  | continueLoop
  | returnValue (value : Option (Expr size integer))
  | endProgram
inductive SwitchCase (size : Type := Nat) (integer : Type := Int)
  | mk (labels : Array (Expr size integer)) (body : (Proc size integer))
end

deriving instance Repr, BEq for Proc, SwitchCase

instance {size integer : Type} : Inhabited (Proc size integer) := ⟨.skip⟩

instance {size integer : Type} : Inhabited (SwitchCase size integer) := ⟨.mk #[] .skip⟩

end QASM.IR
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
