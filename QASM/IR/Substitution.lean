    import LiterateLean
    import QASM.IR.Program
    open scoped LiterateLean

# Substituting IR sizes and integer literals

The same IR grammar describes concrete programs and compilation templates. Substitution
changes only size fields and integer literals, preserving resolved identities, control
flow, declarations, metadata, and every quantum operation. Concrete consumers continue to
use the default `Nat` and `Int` parameters.

All traversals below are total definitions. Consequently their equations are available
in proofs independently of the command elaborator or runtime interpreter.

```lean
namespace QASM.IR

variable {s t i j : Type}

def ScalarTy.map (f : s → t) : ScalarTy s → ScalarTy t
  | .bit width => .bit (width.map f)
  | .sint width => .sint (f width)
  | .uint width => .uint (f width)
  | .float width => .float (f width)
  | .angle width => .angle (f width)
  | .boolean => .boolean
  | .complex width => .complex (f width)
  | .duration => .duration
  | .stretch => .stretch
  | .qubit count => .qubit (f count)
  | .void => .void

def Type.map (f : s → t) : «Type» s → «Type» t
  | .scalar element => .scalar (element.map f)
  | .array element shape => .array (element.map f) (shape.map f)
  | .arrayRef mutable element shape rank =>
      .arrayRef mutable (element.map f) (shape.map (·.map f)) rank

mutual
  def Expr.map (f : s → t) (g : i → j) (value : Expr s i) : Expr t j :=
    match value with
    | ⟨type, node, origin⟩ => { type := type.map f, node := node.map f g, origin }
  termination_by sizeOf value
  def ExprNode.map (f : s → t) (g : i → j) : ExprNode s i → ExprNode t j
    | .intLit value => .intLit (g value)
    | .floatLit value => .floatLit value
    | .imaginaryLit value => .imaginaryLit value
    | .boolLit value => .boolLit value
    | .bitstringLit value => .bitstringLit value
    | .durationLit value => .durationLit value
    | .var id => .var id
    | .const id => .const id
    | .unary op value => .unary op (value.map f g)
    | .binary op left right => .binary op (left.map f g) (right.map f g)
    | .builtin fn args => .builtin fn (args.attach.map (fun value => value.val.map f g))
    | .callSubroutine callee args => .callSubroutine callee (args.attach.map (fun value => value.val.map f g))
    | .cast target value => .cast (target.map f) (value.map f g)
    | .index value indices => .index (value.map f g) (indices.attach.map (fun value => value.val.map f g))
    | .range start step stop =>
        .range (start.attach.map (fun value => value.val.map f g)) (step.attach.map (fun value => value.val.map f g)) (stop.attach.map (fun value => value.val.map f g))
    | .set values => .set (values.attach.map (fun value => value.val.map f g))
    | .array values => .array (values.attach.map (fun value => value.val.map f g))
    | .unsupported capability detail => .unsupported capability detail
  termination_by value => sizeOf value
  decreasing_by
    all_goals simp_wf
    all_goals first
      | omega
      | have h := Array.sizeOf_lt_of_mem value.property; omega
      | cases value; simp_all +arith
end

def Var.map (f : s → t) (value : Var s) : Var t :=
  { id := value.id, name := value.name, type := value.type.map f, origin := value.origin }

def LValue.map (f : s → t) (g : i → j) (value : LValue s i) : LValue t j :=
  { root := value.root, indices := value.indices.map (·.map (·.map f g)),
    type := value.type.map f, origin := value.origin }

def Primitive.map (f : s → t) (g : i → j) (value : Primitive s i) : Primitive t j :=
  { kind := value.kind, name := value.name, parameters := value.parameters.map (·.map f g),
    input := value.input, output := value.output, origin := value.origin }

def Circuit.map (f : s → t) (g : i → j) : Circuit s i → Circuit t j
  | .identity wires => .identity wires
  | .primitive value => .primitive (value.map f g)
  | .compose left right => .compose (left.map f g) (right.map f g)
  | .tensor left right => .tensor (left.map f g) (right.map f g)
  | .permute value => .permute value
  | .inverse value => .inverse (value.map f g)
  | .power exponent value => .power (exponent.map f g) (value.map f g)
  | .controlled spec value => .controlled spec (value.map f g)
  | .unsupported capability detail input output => .unsupported capability detail input output

def QuantumOperand.map (f : s → t) (g : i → j) : QuantumOperand s i → QuantumOperand t j
  | .wire var indices approximate => .wire var (indices.attach.map (fun value => value.val.map f g)) approximate
  | .physical index => .physical index

def ClassicalTarget.map (f : s → t) (g : i → j) : ClassicalTarget s i → ClassicalTarget t j
  | .lvalue target => .lvalue (target.map f g)
  | .discard => .discard

def QuantumDecl.map (f : s → t) (value : QuantumDecl s) : QuantumDecl t :=
  { var := value.var, name := value.name, size := f value.size, origin := value.origin }

def GateModifier.map (f : s → t) (g : i → j) : GateModifier s i → GateModifier t j
  | .inverse => .inverse
  | .power exponent => .power (exponent.map f g)
  | .control negative count => .control negative count

def CircuitRef.map (f : s → t) (g : i → j) (value : CircuitRef s i) : CircuitRef t j :=
  { target := value.target, name := value.name, parameters := value.parameters.map (·.map f g),
    modifiers := value.modifiers.map (·.map f g), origin := value.origin }

def Argument.map (f : s → t) (g : i → j) : Argument s i → Argument t j
  | .expr value => .expr (value.map f g)
  | .quantum value => .quantum (value.map f g)
  | .arrayRef target mutable => .arrayRef (target.map f g) mutable

def ExternCall.map (f : s → t) (g : i → j) (value : ExternCall s i) : ExternCall t j :=
  { callee := value.callee, arguments := value.arguments.map (·.map f g), origin := value.origin }

def Op.map (f : s → t) (g : i → j) : Op s i → Op t j
  | .eval value => .eval (value.map f g)
  | .declare var init => .declare (var.map f) (init.map (·.map f g))
  | .assign target value => .assign (target.map f g) (value.map f g)
  | .apply gate operands => .apply (gate.map f g) (operands.map (·.map f g))
  | .measure source target => .measure (source.map f g) (target.map f g)
  | .reset value => .reset (value.map f g)
  | .barrier values => .barrier (values.attach.map (fun value => value.val.map f g))
  | .allocate value => .allocate (value.map f)
  | .call callee args => .call callee (args.attach.map (fun value => value.val.map f g))
  | .emitExtern invocation => .emitExtern (invocation.map f g)
  | .unsupported capability detail => .unsupported capability detail

def IterationDomain.map (f : s → t) (g : i → j) : IterationDomain s i → IterationDomain t j
  | .range start step stop => .range (start.map f g) (step.map f g) (stop.map f g)
  | .set values => .set (values.attach.map (fun value => value.val.map f g))
  | .array value => .array (value.map f g)

mutual
  def Proc.map (f : s → t) (g : i → j) : Proc s i → Proc t j
    | .skip => .skip
    | .operation op => .operation (op.map f g)
    | .sequence steps => .sequence (steps.attach.map (fun value => value.val.map f g))
    | .scope locals body => .scope (locals.map (·.map f)) (body.map f g)
    | .branch cond yes no => .branch (cond.map f g) (yes.map f g) (no.attach.map (fun value => value.val.map f g))
    | .switch scrutinee cases other =>
        .switch (scrutinee.map f g) (cases.attach.map (fun value => value.val.map f g)) (other.attach.map (fun value => value.val.map f g))
    | .forLoop iterator domain body => .forLoop (iterator.map f) (domain.map f g) (body.map f g)
    | .whileLoop cond body => .whileLoop (cond.map f g) (body.map f g)
    | .breakLoop => .breakLoop
    | .continueLoop => .continueLoop
    | .returnValue value => .returnValue (value.map (·.map f g))
    | .endProgram => .endProgram
  termination_by value => sizeOf value
  decreasing_by
    all_goals simp_wf
    all_goals first
      | omega
      | have h := Array.sizeOf_lt_of_mem value.property; omega
      | cases value; simp_all +arith
  def SwitchCase.map (f : s → t) (g : i → j) : SwitchCase s i → SwitchCase t j
    | .mk labels body => .mk (labels.map (·.map f g)) (body.map f g)
  termination_by value => sizeOf value
  decreasing_by
    all_goals simp_wf
    all_goals first
      | omega
      | have h := Array.sizeOf_lt_of_mem value.property; omega
      | cases value; simp_all +arith
end

```

## Compilation-unit substitution

The outer pass maps each declaration and the process body. It copies target settings and
source metadata, whose values are independent of family parameters.

```lean
def IODecl.map (f : s → t) (value : IODecl s) : IODecl t :=
  { var := value.var.map f, origin := value.origin }

def ConstantDecl.map (f : s → t) (g : i → j) (value : ConstantDecl s i) : ConstantDecl t j :=
  { id := value.id, name := value.name, type := value.type.map f,
    value := value.value.map f g, origin := value.origin }

def TypeDecl.map (f : s → t) (value : TypeDecl s) : TypeDecl t :=
  { id := value.id, name := value.name, type := value.type.map f, origin := value.origin }

def ExternDecl.map (f : s → t) (value : ExternDecl s) : ExternDecl t :=
  { id := value.id, name := value.name, parameters := value.parameters.map (·.map f),
    returnType := value.returnType.map f, origin := value.origin }

def GateDecl.map (f : s → t) (g : i → j) (value : GateDecl s i) : GateDecl t j :=
  { id := value.id, name := value.name, parameters := value.parameters.map (·.map f),
    qubits := value.qubits.map (·.map f), body := value.body.map f g, origin := value.origin }

def SubroutineDecl.map (f : s → t) (g : i → j) (value : SubroutineDecl s i) : SubroutineDecl t j :=
  { id := value.id, name := value.name, parameters := value.parameters.map (·.map f),
    returnType := value.returnType.map f, body := value.body.map f g, origin := value.origin }

def Program.map (f : s → t) (g : i → j) (value : Program s i) : Program t j :=
  { version := value.version, target := value.target, dialect := value.dialect,
    origins := value.origins, annotations := value.annotations, pragmas := value.pragmas,
    includes := value.includes, inputs := value.inputs.map (·.map f), outputs := value.outputs.map (·.map f),
    constants := value.constants.map (·.map f g), types := value.types.map (·.map f),
    externs := value.externs.map (·.map f), gates := value.gates.map (·.map f g),
    subroutines := value.subroutines.map (·.map f g), body := value.body.map f g }

/-- Substitution preserves both categorical boundaries for every circuit. -/
theorem Circuit.interfaces_map (f : s → t) (g : i → j) (circuit : Circuit s i) :
    (circuit.map f g).dom = circuit.dom ∧ (circuit.map f g).cod = circuit.cod := by
  induction circuit <;> simp_all [Circuit.map, Circuit.dom, Circuit.cod, Primitive.map]

@[simp] theorem Circuit.dom_map (f : s → t) (g : i → j) (circuit : Circuit s i) :
    (circuit.map f g).dom = circuit.dom :=
  (Circuit.interfaces_map f g circuit).1

@[simp] theorem Circuit.cod_map (f : s → t) (g : i → j) (circuit : Circuit s i) :
    (circuit.map f g).cod = circuit.cod :=
  (Circuit.interfaces_map f g circuit).2

end QASM.IR
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
