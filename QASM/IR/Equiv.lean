    import LiterateLean
    import QASM.IR.Program
    open scoped LiterateLean

# IR equivalence relations

Exact equality retains every byte of metadata. Alpha equality canonicalizes resolved identifiers and removes source-location and source-file identity. Semantic-shape equality additionally removes display-only names and directives while retaining declarations, types, values, control flow, and capability failures.

The three relations form a deliberate implication chain:

$$
p = q
\;\Longrightarrow\;
p \equiv_{\alpha} q
\;\Longrightarrow\;
p \equiv_{\mathrm{shape}} q.
$$

Each step forgets more presentation information while preserving binding, types,
declarations, values, control flow, and explicit capability failures.

```lean
namespace QASM.IR

```

## Canonical identifier spaces

Alpha equality must ignore the concrete numbers assigned during lowering without merging
distinct namespaces. `CanonState` therefore maintains independent first-occurrence maps
for variables, declarations, and callables. Every definition and reference passes through
the same map, preserving binding structure while replacing incidental IDs deterministically.

```lean
private structure CanonState where
  vars : Std.HashMap VarId VarId := {}
  decls : Std.HashMap DeclId DeclId := {}
  callables : Std.HashMap CallableId CallableId := {}
  nextVar : Nat := 0
  nextDecl : Nat := 0
  nextCallable : Nat := 0

private abbrev CanonM := StateM CanonState

private def canonVarId (id : VarId) : CanonM VarId := do
  let state ← get
  match state.vars[id]? with
  | some canonical => pure canonical
  | none =>
      let canonical : VarId := ⟨state.nextVar⟩
      set { state with vars := state.vars.insert id canonical, nextVar := state.nextVar + 1 }
      pure canonical

private def canonDeclId (id : DeclId) : CanonM DeclId := do
  let state ← get
  match state.decls[id]? with
  | some canonical => pure canonical
  | none =>
      let canonical : DeclId := ⟨state.nextDecl⟩
      set { state with decls := state.decls.insert id canonical, nextDecl := state.nextDecl + 1 }
      pure canonical

private def canonCallableId (id : CallableId) : CanonM CallableId := do
  let state ← get
  match state.callables[id]? with
  | some canonical => pure canonical
  | none =>
      let canonical : CallableId := ⟨state.nextCallable⟩
      set { state with
        callables := state.callables.insert id canonical
        nextCallable := state.nextCallable + 1 }
      pure canonical

```

## Expressions and assignment paths

Expression canonicalization recursively rewrites every referenced ID while retaining
resolved types, operators, literal values, and capability tags. Lvalue roots and selector
expressions follow the same transformation, so mutation targets remain aligned with their
declarations after renaming.

```lean
private def canonVar (var : Var) : CanonM Var := do
  pure { var with id := ← canonVarId var.id, origin := {} }

mutual
  private partial def canonExpr (value : Expr) : CanonM Expr := do
    pure { value with node := ← canonExprNode value.node, origin := {} }

  private partial def canonExprNode (node : ExprNode) : CanonM ExprNode := do
    match node with
    | .intLit value => pure (.intLit value)
    | .floatLit value => pure (.floatLit value)
    | .imaginaryLit value => pure (.imaginaryLit value)
    | .boolLit value => pure (.boolLit value)
    | .bitstringLit value => pure (.bitstringLit value)
    | .durationLit seconds => pure (.durationLit seconds)
    | .array values => .array <$> values.mapM canonExpr
    | .const id => .const <$> canonDeclId id
    | .var id => .var <$> canonVarId id
    | .unary operator operand => pure (.unary operator (← canonExpr operand))
    | .binary operator left right =>
        pure (.binary operator (← canonExpr left) (← canonExpr right))
    | .builtin function arguments => .builtin function <$> arguments.mapM canonExpr
    | .callSubroutine callee arguments =>
        pure (.callSubroutine (← canonCallableId callee) (← arguments.mapM canonExpr))
    | .cast type value => pure (.cast type (← canonExpr value))
    | .index value indices =>
        pure (.index (← canonExpr value) (← indices.mapM canonExpr))
    | .range start step stop =>
        pure (.range (← start.mapM canonExpr) (← step.mapM canonExpr) (← stop.mapM canonExpr))
    | .set values => .set <$> values.mapM canonExpr
    | .unsupported capability detail => pure (.unsupported capability detail)
end

private def canonLValue (target : LValue) : CanonM LValue := do
  pure { target with
    root := ← canonVarId target.root
    indices := ← target.indices.mapM fun group => group.mapM canonExpr
    origin := {} }

private def canonQuantumOperand (operand : QuantumOperand) : CanonM QuantumOperand := do
  match operand with
  | .wire var indices approximate =>
      pure (.wire (← canonVarId var) (← indices.mapM canonExpr) approximate)
  | .physical index => pure (.physical index)

private def canonTarget (target : ClassicalTarget) : CanonM ClassicalTarget := do
  match target with
  | .lvalue value => .lvalue <$> canonLValue value
  | .discard => pure .discard

private def canonModifier (modifier : GateModifier) : CanonM GateModifier := do
  match modifier with
  | .inverse => pure .inverse
  | .power exponent => .power <$> canonExpr exponent
  | .control negate count => pure (.control negate count)

private def canonPrimitiveKind (kind : PrimitiveKind) : CanonM PrimitiveKind := do
  match kind with
  | .userDefined id => .userDefined <$> canonDeclId id
  | other => pure other

private def canonPrimitive (primitive : Primitive) : CanonM Primitive := do
  pure { primitive with
    kind := ← canonPrimitiveKind primitive.kind
    parameters := ← primitive.parameters.mapM canonExpr
    origin := {} }

```

## Categorical circuit normalization

Circuit normalization preserves tensor, permutation, inverse, power, and control nodes.
Sequential composition is the one associativity-insensitive case: nested composition is
flattened and rebuilt left-to-right over the original domain. This makes equivalent
parenthesizations alpha-equal without erasing wire order or unsupported capabilities.

```lean
private def canonPermutation (permutation : WirePermutation) : WirePermutation :=
  { permutation with origin := {} }

private partial def circuitSteps : Circuit → Array Circuit
  | .identity _ => #[]
  | .compose first second => circuitSteps first ++ circuitSteps second
  | value => #[value]

private def rebuildCircuit (wires : Interface) (steps : Array Circuit) : Circuit :=
  match steps.toList with
  | [] => .identity wires
  | first :: rest => rest.foldl Circuit.compose first

private partial def canonCircuit (circuit : Circuit) : CanonM Circuit := do
  match circuit with
  | .identity wires => pure (.identity wires)
  | .primitive primitive => .primitive <$> canonPrimitive primitive
  | .compose first second =>
      let first ← canonCircuit first
      let second ← canonCircuit second
      pure (rebuildCircuit (Circuit.dom circuit) (circuitSteps first ++ circuitSteps second))
  | .tensor first second =>
      let first ← canonCircuit first
      let second ← canonCircuit second
      match first, second with
      | .identity left, .identity right => pure (.identity (left ++ right))
      | _, _ => pure (.tensor first second)
  | .permute permutation =>
      let permutation := canonPermutation permutation
      if permutation.domain == permutation.codomain &&
          permutation.mapping == Array.range permutation.domain.length then
        pure (.identity permutation.domain)
      else pure (.permute permutation)
  | .inverse value =>
      let value ← canonCircuit value
      match value with
      | .identity wires => pure (.identity wires)
      | _ => pure (.inverse value)
  | .power exponent value => pure (.power (← canonExpr exponent) (← canonCircuit value))
  | .controlled spec value =>
      pure (.controlled { spec with origin := {} } (← canonCircuit value))
  | .unsupported capability detail input output =>
      pure (.unsupported capability detail input output)

```

## Operations and structured processes

Gate references, arguments, effects, iteration domains, and process control are rewritten
structurally. The mutual process traversal handles recursive switch cases and scopes;
local declarations are canonicalized before their bodies, preserving lexical identity and
non-local control-flow shape.

```lean
private def canonCircuitRef (gate : CircuitRef) : CanonM CircuitRef := do
  pure { gate with
    target := ← canonPrimitiveKind gate.target
    parameters := ← gate.parameters.mapM canonExpr
    modifiers := ← gate.modifiers.mapM canonModifier
    origin := {} }

private def canonArgument (argument : Argument) : CanonM Argument := do
  match argument with
  | .expr value => .expr <$> canonExpr value
  | .quantum operand => .quantum <$> canonQuantumOperand operand
  | .arrayRef target mutable => pure (.arrayRef (← canonLValue target) mutable)

private def canonExternCall (call : ExternCall) : CanonM ExternCall := do
  pure { call with
    callee := ← canonDeclId call.callee
    arguments := ← call.arguments.mapM canonExpr
    origin := {} }

private def canonOp (op : Op) : CanonM Op := do
  match op with
  | .eval value => .eval <$> canonExpr value
  | .declare var init => pure (.declare (← canonVar var) (← init.mapM canonExpr))
  | .assign target value => pure (.assign (← canonLValue target) (← canonExpr value))
  | .apply gate operands =>
      pure (.apply (← canonCircuitRef gate) (← operands.mapM canonQuantumOperand))
  | .measure source target =>
      pure (.measure (← canonQuantumOperand source) (← canonTarget target))
  | .reset operand => .reset <$> canonQuantumOperand operand
  | .barrier operands => .barrier <$> operands.mapM canonQuantumOperand
  | .allocate decl =>
      pure (.allocate { decl with var := ← canonVarId decl.var, origin := {} })
  | .call callee arguments =>
      pure (.call (← canonCallableId callee) (← arguments.mapM canonArgument))
  | .emitExtern call => .emitExtern <$> canonExternCall call
  | .unsupported capability detail => pure (.unsupported capability detail)

private def canonDomain (domain : IterationDomain) : CanonM IterationDomain := do
  match domain with
  | .range start step stop =>
      pure (.range (← canonExpr start) (← canonExpr step) (← canonExpr stop))
  | .set values => .set <$> values.mapM canonExpr
  | .array value => .array <$> canonExpr value

mutual
  private partial def canonProc (proc : Proc) : CanonM Proc := do
    match proc with
    | .skip => pure .skip
    | .operation op => .operation <$> canonOp op
    | .sequence steps =>
        let steps ← steps.mapM canonProc
        let steps := steps.flatMap fun
          | .skip => #[]
          | .sequence nested => nested
          | step => #[step]
        if steps.isEmpty then pure .skip
        else if steps.size == 1 then pure steps[0]!
        else pure (.sequence steps)
    | .scope locals body =>
        let locals ← locals.mapM canonVar
        let body ← canonProc body
        if locals.isEmpty then pure body else pure (.scope locals body)
    | .branch cond thenBranch elseBranch =>
        pure (.branch (← canonExpr cond) (← canonProc thenBranch) (← elseBranch.mapM canonProc))
    | .switch scrutinee cases default =>
        pure (.switch (← canonExpr scrutinee) (← cases.mapM canonSwitchCase)
          (← default.mapM canonProc))
    | .forLoop iterator domain body =>
        pure (.forLoop (← canonVar iterator) (← canonDomain domain) (← canonProc body))
    | .whileLoop cond body => pure (.whileLoop (← canonExpr cond) (← canonProc body))
    | .breakLoop => pure .breakLoop
    | .continueLoop => pure .continueLoop
    | .returnValue value => .returnValue <$> value.mapM canonExpr
    | .endProgram => pure .endProgram

  private partial def canonSwitchCase (switchCase : SwitchCase) : CanonM SwitchCase := do
    match switchCase with
    | .mk labels body => pure (.mk (← labels.mapM canonExpr) (← canonProc body))
end

```

## Whole-program alpha normalization

Compilation-unit declarations are visited in dependency order before the executable body.
Names, directives, source origins, and target settings remain present in alpha-normalized
programs; only stable numeric identities and source-location identity are normalized.

```lean
private def canonIODecl (declaration : IODecl) : CanonM IODecl := do
  pure { declaration with var := ← canonVar declaration.var, origin := {} }

private def canonConstantDecl (declaration : ConstantDecl) : CanonM ConstantDecl := do
  pure { declaration with
    id := ← canonDeclId declaration.id
    value := ← canonExpr declaration.value
    origin := {} }

private def canonTypeDecl (declaration : TypeDecl) : CanonM TypeDecl := do
  pure { declaration with id := ← canonDeclId declaration.id, origin := {} }

private def canonExternDecl (declaration : ExternDecl) : CanonM ExternDecl := do
  pure { declaration with id := ← canonDeclId declaration.id, origin := {} }

private def canonGateDecl (declaration : GateDecl) : CanonM GateDecl := do
  pure { declaration with
    id := ← canonDeclId declaration.id
    parameters := ← declaration.parameters.mapM canonVar
    qubits := ← declaration.qubits.mapM canonVar
    body := ← canonCircuit declaration.body
    origin := {} }

private def canonSubroutineDecl (declaration : SubroutineDecl) : CanonM SubroutineDecl := do
  pure { declaration with
    id := ← canonCallableId declaration.id
    parameters := ← declaration.parameters.mapM canonVar
    body := ← canonProc declaration.body
    origin := {} }

private def alphaNormalizeM (program : Program) : CanonM Program := do
  pure { program with
    origins := #[]
    annotations := program.annotations.map fun value => { value with origin := {} }
    pragmas := program.pragmas.map fun value => { value with origin := {} }
    includes := #[]
    inputs := ← program.inputs.mapM canonIODecl
    outputs := ← program.outputs.mapM canonIODecl
    constants := ← program.constants.mapM canonConstantDecl
    types := ← program.types.mapM canonTypeDecl
    externs := ← program.externs.mapM canonExternDecl
    gates := ← program.gates.mapM canonGateDecl
    subroutines := ← program.subroutines.mapM canonSubroutineDecl
    body := ← canonProc program.body }

```

## Alpha equality

`alphaEq` compares the complete normalized values. It remains strict about display names,
directives, target configuration, literal values, types, and capability details, making it
suitable when only lowering-assigned IDs and source identity should be ignored.

```lean
private def Program.alphaNormalize (program : Program) : Program :=
  (alphaNormalizeM program).run' {}

/-- Equality modulo resolved identifier allocation and source-file metadata. -/
def Program.alphaEq (left right : Program) : Bool :=
  left.alphaNormalize == right.alphaNormalize

```

## Semantic-shape equality

Round-trip emission may legitimately change display-only names, directives, include
boundaries, origins, and diagnostic detail. The semantic-shape projection removes exactly
those fields after alpha normalization while retaining declarations, resolved types,
values, wire structure, control flow, and capability categories. It is intentionally not
an optimizer equivalence or a claim about arbitrary program behavior.

```lean
private def eraseVarName (var : Var) : Var := { var with name := "" }

private partial def eraseExprDetails (value : Expr) : Expr :=
  { value with node := match value.node with
    | .array values => .array (values.map eraseExprDetails)
    | .unary operator operand => .unary operator (eraseExprDetails operand)
    | .binary operator left right =>
        .binary operator (eraseExprDetails left) (eraseExprDetails right)
    | .builtin function arguments => .builtin function (arguments.map eraseExprDetails)
    | .callSubroutine callee arguments => .callSubroutine callee (arguments.map eraseExprDetails)
    | .cast type operand => .cast type (eraseExprDetails operand)
    | .index operand indices =>
        .index (eraseExprDetails operand) (indices.map eraseExprDetails)
    | .range start step stop =>
        .range (start.map eraseExprDetails) (step.map eraseExprDetails) (stop.map eraseExprDetails)
    | .set values => .set (values.map eraseExprDetails)
    | .unsupported capability _ => .unsupported capability ""
    | node => node }

private def eraseLValueDetails (value : LValue) : LValue :=
  { value with indices := value.indices.map fun group => group.map eraseExprDetails }

private def eraseQuantumDetails : QuantumOperand → QuantumOperand
  | .wire var indices approximate => .wire var (indices.map eraseExprDetails) approximate
  | value => value

private partial def eraseCircuitDetails : Circuit → Circuit
  | .identity wires => .identity wires
  | .primitive primitive => .primitive { primitive with
      name := "", parameters := primitive.parameters.map eraseExprDetails }
  | .compose first second => .compose (eraseCircuitDetails first) (eraseCircuitDetails second)
  | .tensor first second => .tensor (eraseCircuitDetails first) (eraseCircuitDetails second)
  | .permute permutation => .permute permutation
  | .inverse value => .inverse (eraseCircuitDetails value)
  | .power exponent value => .power (eraseExprDetails exponent) (eraseCircuitDetails value)
  | .controlled spec value => .controlled spec (eraseCircuitDetails value)
  | .unsupported capability _ input output => .unsupported capability "" input output

private def eraseModifierDetails : GateModifier → GateModifier
  | .power exponent => .power (eraseExprDetails exponent)
  | value => value

private def eraseArgumentDetails : Argument → Argument
  | .expr value => .expr (eraseExprDetails value)
  | .quantum value => .quantum (eraseQuantumDetails value)
  | .arrayRef target mutable => .arrayRef (eraseLValueDetails target) mutable

private def eraseOpDetails : Op → Op
  | .eval value => .eval (eraseExprDetails value)
  | .declare var init => .declare (eraseVarName var) (init.map eraseExprDetails)
  | .assign target value => .assign (eraseLValueDetails target) (eraseExprDetails value)
  | .apply gate operands =>
      let gate := { gate with name := "" }
      let gate := { gate with parameters := gate.parameters.map eraseExprDetails }
      let gate := { gate with modifiers := gate.modifiers.map eraseModifierDetails }
      .apply gate (operands.map eraseQuantumDetails)
  | .measure source (.lvalue target) =>
      .measure (eraseQuantumDetails source) (.lvalue (eraseLValueDetails target))
  | .measure source .discard => .measure (eraseQuantumDetails source) .discard
  | .reset operand => .reset (eraseQuantumDetails operand)
  | .barrier operands => .barrier (operands.map eraseQuantumDetails)
  | .allocate declaration => .allocate { declaration with name := "" }
  | .call callee arguments => .call callee (arguments.map eraseArgumentDetails)
  | .emitExtern call => .emitExtern { call with arguments := call.arguments.map eraseExprDetails }
  | .unsupported capability _ => .unsupported capability ""

private def eraseDomainDetails : IterationDomain → IterationDomain
  | .range start step stop =>
      .range (eraseExprDetails start) (eraseExprDetails step) (eraseExprDetails stop)
  | .set values => .set (values.map eraseExprDetails)
  | .array value => .array (eraseExprDetails value)

mutual
  private partial def eraseProcDetails : Proc → Proc
    | .skip => .skip
    | .operation op => .operation (eraseOpDetails op)
    | .sequence steps => .sequence (steps.map eraseProcDetails)
    | .scope locals body => .scope (locals.map eraseVarName) (eraseProcDetails body)
    | .branch cond thenBranch elseBranch =>
        .branch (eraseExprDetails cond) (eraseProcDetails thenBranch)
          (elseBranch.map eraseProcDetails)
    | .switch scrutinee cases default =>
        .switch (eraseExprDetails scrutinee) (cases.map eraseSwitchDetails)
          (default.map eraseProcDetails)
    | .forLoop iterator domain body =>
        .forLoop (eraseVarName iterator) (eraseDomainDetails domain) (eraseProcDetails body)
    | .whileLoop cond body => .whileLoop (eraseExprDetails cond) (eraseProcDetails body)
    | .breakLoop => .breakLoop
    | .continueLoop => .continueLoop
    | .returnValue value => .returnValue (value.map eraseExprDetails)
    | .endProgram => .endProgram

  private partial def eraseSwitchDetails : SwitchCase → SwitchCase
    | .mk labels body => .mk (labels.map eraseExprDetails) (eraseProcDetails body)
end

private def eraseConstantDetails (value : ConstantDecl) : ConstantDecl :=
  { { value with name := "" } with value := eraseExprDetails value.value }

private def eraseGateDetails (value : GateDecl) : GateDecl :=
  let value := { value with name := "" }
  let value := { value with parameters := value.parameters.map eraseVarName }
  let value := { value with qubits := value.qubits.map eraseVarName }
  { value with body := eraseCircuitDetails value.body }

private def eraseSubroutineDetails (value : SubroutineDecl) : SubroutineDecl :=
  let value := { value with name := "" }
  let value := { value with parameters := value.parameters.map eraseVarName }
  { value with body := eraseProcDetails value.body }

private def Program.semanticShape (program : Program) : Program :=
  let program := program.alphaNormalize
  { program with
    annotations := #[]
    pragmas := #[]
    includes := #[]
    inputs := program.inputs.map fun value => { value with var := eraseVarName value.var }
    outputs := program.outputs.map fun value => { value with var := eraseVarName value.var }
    constants := program.constants.map eraseConstantDetails
    types := program.types.map fun value => { value with name := "" }
    externs := program.externs.map fun value => { value with name := "" }
    gates := program.gates.map eraseGateDetails
    subroutines := program.subroutines.map eraseSubroutineDetails
    body := eraseProcDetails program.body }

/-- Equality of typed operational structure, excluding presentation and diagnostic metadata. -/
def Program.semanticShapeEq (left right : Program) : Bool :=
  left.semanticShape == right.semanticShape

end QASM.IR
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
