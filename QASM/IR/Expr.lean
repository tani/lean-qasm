    import LiterateLean
    import QASM.IR.Source
    import QASM.IR.Name
    import QASM.IR.Type
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

Literal nodes carry semantic values rather than source spellings. Variable, constant, and
subroutine references use their dedicated stable IDs; casts store the resolved target
type; unsupported nodes retain a capability and diagnostic detail instead of inventing a
fallback value.

```lean
mutual
structure Expr where
  type   : «Type»
  node   : ExprNode
  origin : SourceSpan := {}
inductive ExprNode where
  | intLit         (value : Int)
  | floatLit       (value : Float)
  | imaginaryLit   (value : Float)
  | boolLit        (value : Bool)
  | bitstringLit   (bits : Array Bool)
  | durationLit    (seconds : Float)
  | var            (id : VarId)
  | const          (id : DeclId)
  | unary          (op : UnaryOp) (operand : Expr)
  | binary         (op : BinaryOp) (lhs rhs : Expr)
  | builtin        (fn : Builtin) (args : Array Expr)
  | callSubroutine (callee : CallableId) (args : Array Expr)
  | cast           (target : «Type») (value : Expr)
  | index          (value : Expr) (indices : Array Expr)
  | range          (start step stop : Option Expr)
  | set            (values : Array Expr)
  | array          (values : Array Expr)
  | unsupported    (capability : Capability) (detail : String)
end

deriving instance Repr, BEq for Expr, ExprNode

instance : Inhabited ExprNode := ⟨.intLit 0⟩

instance : Inhabited Expr :=
  ⟨{ type := .scalar .void, node := .intLit 0, origin := {} }⟩

```

## Variables and assignment paths

`Var` joins identity, display name, resolved type, and origin at declaration sites.
`LValue` references one root variable plus ordered selector groups, preserving chained
multidimensional indexing for checked read-modify-write reconstruction.

```lean
structure Var where
  id     : VarId
  name   : Name
  type   : «Type»
  origin : SourceSpan := {}
  deriving Repr, BEq, Inhabited

structure LValue where
  root    : VarId
  indices : Array (Array Expr) := #[]
  type    : «Type»
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
