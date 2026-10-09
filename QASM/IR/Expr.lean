    import LiterateLean
    import QASM.IR.Source
    import QASM.IR.Name
    import QASM.IR.Type
    import QASM.IR.NumericLiteral
    open scoped LiterateLean

# Resolved expressions and variables

Expressions contain only resolved identifiers, closed operators and builtins, explicit
types, and target capability markers. Each `Expr` repeats its resolved result type beside
the recursive node so the interpreter and emitters never rerun source inference.

Expression resolution removes every dependency on mutable frontend context:

```mermaid
flowchart LR
    Source["source expression"] --> Infer["type and name resolution"]
    Infer --> Expr["IR.Expr<br/>type + node + origin"]
    Expr --> Interpreter
    Expr --> Emitter
```

Both consumers therefore agree on the same operator, identifier, and result type.

```lean
namespace QASM.IR

inductive UnaryOp
  | not
  | neg
  | bitnot
  deriving Repr, BEq, DecidableEq, Hashable, Inhabited

inductive BinaryOp
  | add | sub | mul | div | mod | pow
  | shl | shr | band | bor | bxor
  | land | lor | eq | ne | lt | le | gt | ge | concat
  deriving Repr, BEq, DecidableEq, Hashable, Inhabited

inductive Builtin
  | popcount | sizeof | real | imag | sin | cos | tan
  | arcsin | arccos | arctan | sqrt | exp | log | floor | ceiling | mod | rotl | rotr
  deriving Repr, BEq, DecidableEq, Hashable, Inhabited

```

## Typed expression trees

Literal nodes retain exact decimal values and named real constants. Legacy binary
float literals remain distinguishable from those exact values. Size and integer
representation parameters default to `Nat` and `Int`; compilation templates temporarily
use symbolic values, then quotation emits the concrete constructors with open Lean terms. Variable, constant, and
subroutine references use their dedicated stable IDs; casts store the resolved target
type; unsupported nodes retain a capability and diagnostic detail instead of inventing a
fallback value.

```lean
mutual
structure Expr (size : Type := Nat) (integer : Type := Int) where
  type   : («Type» size)
  node   : (ExprNode size integer)
  origin : SourceSpan := {}
inductive ExprNode (size : Type := Nat) (integer : Type := Int) where
  | intLit         (value : integer)
  | floatLit       (value : Float)
  | decimalLit     (value : DecimalLiteral)
  | realConstant   (value : RealConstant)
  | imaginaryDecimalLit (value : DecimalLiteral)
  | imaginaryLit   (value : Float)
  | boolLit        (value : Bool)
  | bitstringLit   (bits : Array Bool)
  | durationLit    (seconds : Float)
  | var            (id : VarId)
  | const          (id : DeclId)
  | unary          (op : UnaryOp) (operand : (Expr size integer))
  | binary         (op : BinaryOp) (lhs rhs : (Expr size integer))
  | builtin        (fn : Builtin) (args : Array (Expr size integer))
  | callSubroutine (callee : CallableId) (args : Array (Expr size integer))
  | cast           (target : («Type» size)) (value : (Expr size integer))
  | index          (value : (Expr size integer)) (indices : Array (Expr size integer))
  | range          (start step stop : Option (Expr size integer))
  | set            (values : Array (Expr size integer))
  | array          (values : Array (Expr size integer))
  | unsupported    (capability : Capability) (detail : String)
end

deriving instance Repr, BEq for Expr, ExprNode

instance {size integer : Type} [Inhabited integer] : Inhabited (ExprNode size integer) := ⟨.intLit default⟩

instance {size integer : Type} [Inhabited integer] : Inhabited (Expr size integer) :=
  ⟨{ type := .scalar .void, node := .intLit default, origin := {} }⟩

```

## Variables and assignment paths

`Var` joins identity, display name, resolved type, and origin at declaration sites.
`LValue` references one root variable plus ordered selector groups, preserving chained
multidimensional indexing for checked read-modify-write reconstruction.

```lean
structure Var (size : Type := Nat) where
  id     : VarId
  name   : Name
  type   : («Type» size)
  origin : SourceSpan := {}
  deriving Repr, BEq, Inhabited

structure LValue (size : Type := Nat) (integer : Type := Int) where
  root    : VarId
  indices : Array (Array (Expr size integer)) := #[]
  type    : («Type» size)
  origin  : SourceSpan := {}
  deriving Repr, BEq, Inhabited

end QASM.IR
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
