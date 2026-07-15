    import LiterateLean
    import QASM.Lowering.Circuit
    open scoped LiterateLean

# Process lowering

Statements lower to explicit first-order process nodes. Effectful measurements nested in expressions are hoisted into preceding operations so measurement never survives as an expression node.

Measurement hoisting converts an effectful expression into an ordered process prefix:

```mermaid
flowchart LR
    Nested["expression containing measure"] --> Fresh["fresh temporary"]
    Fresh --> Measure["Op.measure into temporary"]
    Measure --> Pure["pure expression referencing temporary"]
```

If an expression yields prelude operations $p_1,\ldots,p_n$ and pure remainder $e$, the
lowered order is $p_1;\cdots;p_n;e$. Left-to-right traversal therefore remains observable
through backend effects.

```lean
namespace QASM.Lowering

open QASM

```

## Sequencing and effect hoisting

Process sequences discard structural `skip` nodes and avoid singleton wrappers. The
hoisting pass then rewrites every nested measurement into a fresh declaration followed by
`Op.measure`, replacing the source occurrence with a pure identifier. Traversal is
left-to-right, so emitted preludes preserve source evaluation order across calls, indices,
ranges, sets, arrays, and operand selectors.

```lean
private def sequence (steps : Array QASM.IR.Proc) : QASM.IR.Proc :=
  let steps := steps.filter (· != .skip)
  if steps.isEmpty then .skip else if steps.size == 1 then steps[0]! else .sequence steps

private def prepend (prelude : Array QASM.IR.Proc) (body : QASM.IR.Proc) : QASM.IR.Proc :=
  sequence (prelude.push body)

mutual
private partial def hoistExpression (source : QASM.Frontend.Expression) :
    LowerM (Array QASM.IR.Proc × QASM.Frontend.Expression) := do
  match source with
  | .measure operand =>
      let (prelude, operand) ← hoistOperand operand
      let type ← inferType (.measure operand)
      let context ← get
      let name := s!"__qasm_measure_{context.nextVarId}"
      let binding ← freshBinding name type true
      let target : QASM.IR.LValue :=
        { root := binding.var.id, type := resolvedType type,
          origin := sourceOrigin context.options }
      let operations := prelude ++ #[
        .operation (.declare binding.var none),
        .operation (.measure (← quantumOperand operand) (.lvalue target))
      ]
      pure (operations, .identifier name)
  | .unary operator operand =>
      let (prelude, operand) ← hoistExpression operand
      pure (prelude, .unary operator operand)
  | .binary operator lhs rhs =>
      let (leftPrelude, lhs) ← hoistExpression lhs
      let (rightPrelude, rhs) ← hoistExpression rhs
      pure (leftPrelude ++ rightPrelude, .binary operator lhs rhs)
  | .call name arguments =>
      let (prelude, arguments) ← hoistExpressions arguments
      pure (prelude, .call name arguments)
  | .cast name width value =>
      let (widthPrelude, width) ← hoistOptionalExpression width
      let (valuePrelude, value) ← hoistExpression value
      pure (widthPrelude ++ valuePrelude, .cast name width value)
  | .arrayCast name width dimensions value =>
      let (widthPrelude, width) ← hoistOptionalExpression width
      let (dimensionPrelude, dimensions) ← hoistExpressions dimensions
      let (valuePrelude, value) ← hoistExpression value
      pure (widthPrelude ++ dimensionPrelude ++ valuePrelude,
        .arrayCast name width dimensions value)
  | .index value indices =>
      let (valuePrelude, value) ← hoistExpression value
      let (indexPrelude, indices) ← hoistExpressions indices
      pure (valuePrelude ++ indexPrelude, .index value indices)
  | .range start step stop =>
      let (startPrelude, start) ← hoistOptionalExpression start
      let (stepPrelude, step) ← hoistOptionalExpression step
      let (stopPrelude, stop) ← hoistOptionalExpression stop
      pure (startPrelude ++ stepPrelude ++ stopPrelude, .range start step stop)
  | .set values =>
      let (prelude, values) ← hoistExpressions values
      pure (prelude, .set values)
  | .array values =>
      let (prelude, values) ← hoistExpressions values
      pure (prelude, .array values)
  | value => pure (#[], value)

private partial def hoistOptionalExpression (source : Option QASM.Frontend.Expression) :
    LowerM (Array QASM.IR.Proc × Option QASM.Frontend.Expression) := do
  match source with
  | none => pure (#[], none)
  | some value =>
      let (prelude, value) ← hoistExpression value
      pure (prelude, some value)

private partial def hoistExpressions (sources : Array QASM.Frontend.Expression) :
    LowerM (Array QASM.IR.Proc × Array QASM.Frontend.Expression) := do
  let mut prelude := #[]
  let mut values := #[]
  for source in sources do
    let (nextPrelude, value) ← hoistExpression source
    prelude := prelude ++ nextPrelude
    values := values.push value
  pure (prelude, values)

private partial def hoistOperand (source : QASM.Frontend.Operand) :
    LowerM (Array QASM.IR.Proc × QASM.Frontend.Operand) := do
  match source with
  | .hardware index => pure (#[], .hardware index)
  | .identifier name groups =>
      let mut prelude := #[]
      let mut loweredGroups := #[]
      for group in groups do
        let (groupPrelude, lowered) ← hoistExpressions group
        prelude := prelude ++ groupPrelude
        loweredGroups := loweredGroups.push lowered
      pure (prelude, .identifier name loweredGroups)
end

```

## Typed expressions and iteration domains

After hoisting, pure expression lowering can enforce the invariant that `IR.Expr` contains
no measurement effect. Iteration domains retain their source category—range, set, or
array—while omitted range bounds receive target-width integer literals. Type resolution is
reused from the completed frontend analysis.

```lean
private def lowerExpression (source : QASM.Frontend.Expression) :
    LowerM (Array QASM.IR.Proc × QASM.IR.Expr) := do
  let (prelude, source) ← hoistExpression source
  pure (prelude, ← expression source)


private def resolveSourceType (type : QASM.Frontend.TypeSpec) :
    LowerM QASM.Frontend.ResolvedType := do
  let context ← get
  match QASM.Frontend.resolveType context.options.target context.analysis.constants type with
  | .ok type => pure type
  | .error error => throw error

private def directLValue (binding : Binding) (type : QASM.IR.Type)
    (origin : QASM.IR.SourceSpan) : QASM.IR.LValue :=
  { root := binding.var.id, type, origin }

private def iterationDomain (source : QASM.Frontend.Expression) :
    LowerM (Array QASM.IR.Proc × QASM.IR.IterationDomain) := do
  match source with
  | .range start step stop =>
      let target ← get
      let defaultExpr (value : Int) : QASM.IR.Expr :=
        { type := .scalar (.sint target.options.target.intWidth), node := .intLit value,
          origin := sourceOrigin target.options }
      let (startPrelude, start) ← match start with
        | some value => lowerExpression value
        | none => pure (#[], defaultExpr 0)
      let (stepPrelude, step) ← match step with
        | some value => lowerExpression value
        | none => pure (#[], defaultExpr 1)
      let (stopPrelude, stop) ← match stop with
        | some value => lowerExpression value
        | none => pure (#[], start)
      pure (startPrelude ++ stepPrelude ++ stopPrelude, .range start step stop)
  | .set values =>
      let (prelude, values) ← hoistExpressions values
      pure (prelude, .set (← values.mapM expression))
  | .array _ =>
      let (prelude, value) ← lowerExpression source
      pure (prelude, .array value)
  | value =>
      let (prelude, value) ← lowerExpression value
      pure (prelude, .array value)

```

## Calls, compound assignment, and gate operations

Checked signatures determine whether a call becomes `Op.call`, `Op.emitExtern`, a builtin
expression, or an ordinary evaluated expression. Compound assignments are normalized to
one read and one typed binary or unary expression. Gate statements hoist parameter and
operand effects before emitting a resolved `Op.apply`.

```lean
private def callOperation (name : String) (sources : Array QASM.Frontend.Expression) :
    LowerM (Array QASM.IR.Proc × QASM.IR.Op) := do
  let context ← get
  let (prelude, sources) ← hoistExpressions sources
  match lookupCallable? context name, lookupCallableSignature? context name with
  | some callable, some signature =>
      let arguments ← (signature.arguments.zip sources).mapM fun pair => argument pair.1 pair.2
      pure (prelude, .call callable.id arguments)
  | none, some _ =>
      let external ← match lookupExtern? context name with
        | some external => pure external
        | none => fail s!"callable '{name}' has no resolved declaration"
      pure (prelude, .emitExtern
        { callee := external.id, arguments := ← sources.mapM expression,
          origin := sourceOrigin context.options })
  | _, none => fail s!"callable '{name}' has no checked signature"

private def compoundValue (target source : QASM.Frontend.Expression) (operator : String) :
    LowerM (Array QASM.IR.Proc × QASM.IR.Expr) := do
  let (prelude, rhs) ← lowerExpression source
  if operator == "=" then pure (prelude, rhs)
  else if operator == "~=" then
    pure (prelude, { rhs with node := .unary .bitnot rhs })
  else
    let lhs ← expression target
    let base := operator.dropEnd 1 |>.toString
    pure (prelude, { type := lhs.type, node := .binary (← match binaryOp base with
      | .ok value => pure value
      | .error error => throw error) lhs rhs, origin := lhs.origin })

private def statementGateCall (modifiers : Array QASM.Frontend.GateModifier) (name : String)
    (parameters : Array QASM.Frontend.Expression) (designator : Option QASM.Frontend.Expression)
    (operands : Array QASM.Frontend.Operand) : LowerM QASM.IR.Proc := do
  if designator.isSome then
    pure (.operation (.unsupported .timing s!"timed gate call '{name}'"))
  else
    let (parameterPrelude, parameters) ← hoistExpressions parameters
    let mut operandPrelude := #[]
    let mut loweredOperands := #[]
    for operand in operands do
      let (prelude, operand) ← hoistOperand operand
      operandPrelude := operandPrelude ++ prelude
      loweredOperands := loweredOperands.push (← quantumOperand operand)
    let gate ← gateReference modifiers name parameters
    pure (prepend (parameterPrelude ++ operandPrelude)
      (.operation (.apply gate loweredOperands)))

```

## Statement and scope translation

`statement` is the source-to-process correspondence table. Declarations allocate stable
bindings, assignments emit explicit lvalues, and structured source control becomes
`Proc.branch`, `Proc.switch`, `Proc.forLoop`, or `Proc.whileLoop`. `break`, `continue`,
`return`, and `end` remain first-order process signals for the runtime interpreter.

The mutually recursive `statements`, `statement`, and `scopedStatements` definitions must
remain in one Lean block. Scope lowering records every local variable in `Proc.scope` so
the interpreter can restore shadowed bindings on both normal and non-local exits.
Backend-dependent constructs survive only as capability-tagged unsupported operations.

```lean
mutual
partial def statements (source : Array QASM.Frontend.Statement) : LowerM QASM.IR.Proc := do
  let mut result := #[]
  for current in source do result := result.push (← statement current)
  pure (sequence result)

partial def statement (source : QASM.Frontend.Statement) : LowerM QASM.IR.Proc := do
  let context ← get
  let origin := sourceOrigin context.options
  match source with
  | .includeFile _ | .constDeclaration .. |
      .defStatement .. | .externStatement .. | .gateDefinition .. |
      .pragma _ => pure .skip
  | .qubit name size | .qreg name size =>
      let type ← resolveSourceType (.scalar "qubit" size)
      let binding ← freshBinding name type false
      let count := match type with | .scalar (.qubit count) => count | _ => 1
      pure (.operation (.allocate { var := binding.var.id, name, size := count, origin }))
  | .bit name size | .creg name size =>
      let type ← resolveSourceType (.scalar "bit" size)
      let binding ← freshBinding name type true
      pure (.operation (.declare binding.var none))
  | .classicalDeclaration type name initializer =>
      let type ← resolveSourceType type
      let binding ← freshBinding name type true
      match initializer with
      | none => pure (.operation (.declare binding.var none))
      | some value =>
          let (prelude, value) ← lowerExpression value
          pure (prepend prelude (.operation (.declare binding.var (some value))))
  | .ioDeclaration input type name =>
      let type ← resolveSourceType type
      let _ ← freshBinding name type (!input)
      pure .skip
  | .aliasDeclaration name value =>
      let type ← inferType value
      let binding ← freshBinding name type false
      let (prelude, value) ← lowerExpression value
      pure (prepend prelude (.operation (.declare binding.var (some value))))
  | .assignment target operator value =>
      let targetValue ← lvalue target
      let (prelude, value) ← compoundValue target value operator
      pure (prepend prelude (.operation (.assign targetValue value)))
  | .expression (.measure operand) =>
      let (prelude, operand) ← hoistOperand operand
      pure (prepend prelude (.operation (.measure (← quantumOperand operand) .discard)))
  | .expression (.call name arguments) =>
      if (lookupCallableSignature? context name).isSome then
        let (prelude, operation) ← callOperation name arguments
        pure (prepend prelude (.operation operation))
      else
        let (prelude, value) ← lowerExpression (.call name arguments)
        pure (prepend prelude (.operation (.eval value)))
  | .expression value =>
      let (prelude, value) ← lowerExpression value
      pure (prepend prelude (.operation (.eval value)))
  | .scope body => scopedStatements body
  | .ifStatement condition thenBody elseBody =>
      let (prelude, condition) ← lowerExpression condition
      let thenBranch ← scopedStatements thenBody
      let elseBranch ← elseBody.mapM scopedStatements
      pure (prepend prelude (.branch condition thenBranch elseBranch))
  | .whileStatement condition body =>
      let (prelude, condition) ← lowerExpression condition
      pure (prepend prelude (.whileLoop condition (← scopedStatements body)))
  | .switchStatement value cases defaultBody =>
      let (prelude, value) ← lowerExpression value
      let cases ← cases.mapM fun entry => do
        let labels ← entry.1.mapM fun label => (lowerExpression label).map (·.2)
        pure (QASM.IR.SwitchCase.mk labels (← scopedStatements entry.2))
      let defaultBody ← defaultBody.mapM scopedStatements
      pure (prepend prelude (.switch value cases defaultBody))
  | .forStatement type iterator iterable body =>
      let iteratorType ← resolveSourceType type
      let (prelude, domain) ← iterationDomain iterable
      pushScope
      let iteratorBinding ← freshBinding iterator iteratorType true
      let loweredBody ← statements body
      let after ← get
      let bindings : List Binding := after.scopes.headD []
      let locals := (bindings.reverse.filter fun binding =>
        binding.var.id != iteratorBinding.var.id).map (·.var) |>.toArray
      popScope
      let loweredBody := if locals.isEmpty then loweredBody else .scope locals loweredBody
      pure (prepend prelude (.forLoop iteratorBinding.var domain loweredBody))
  | .breakStatement => pure .breakLoop
  | .continueStatement => pure .continueLoop
  | .endStatement => pure .endProgram
  | .returnStatement none => pure (.returnValue none)
  | .returnStatement (some value) =>
      let (prelude, value) ← lowerExpression value
      pure (prepend prelude (.returnValue (some value)))
  | .gateCall modifiers name parameters designator operands =>
      statementGateCall modifiers name parameters designator operands
  | .measure source target =>
      let (sourcePrelude, source) ← hoistOperand source
      let target ← match target with
        | none => pure QASM.IR.ClassicalTarget.discard
        | some target => pure (.lvalue (← operandLValue target))
      pure (prepend sourcePrelude (.operation (.measure (← quantumOperand source) target)))
  | .reset operand =>
      let (prelude, operand) ← hoistOperand operand
      pure (prepend prelude (.operation (.reset (← quantumOperand operand))))
  | .barrier operands =>
      let mut prelude := #[]
      let mut lowered := #[]
      for operand in operands do
        let (next, operand) ← hoistOperand operand
        prelude := prelude ++ next
        lowered := lowered.push (← quantumOperand operand)
      pure (prepend prelude (.operation (.barrier lowered)))
  | .boxStatement _ _ => pure (.operation (.unsupported .timing source.toQasm))
  | .delayStatement _ _ => pure (.operation (.unsupported .timing source.toQasm))
  | .nopStatement _ => pure (.operation (.unsupported .calibration source.toQasm))
  | .annotated _ nested => statement nested
  | .calibrationGrammar _ | .calStatement _ | .defcalStatement _ _ =>
      pure (.operation (.unsupported .calibration source.toQasm))
private partial def scopedStatements
    (body : Array QASM.Frontend.Statement) : LowerM QASM.IR.Proc := do
  pushScope
  let lowered ← statements body
  let context ← get
  let bindings : List Binding := context.scopes.headD []
  let locals := bindings.reverse.map (·.var) |>.toArray
  popScope
  pure (.scope locals lowered)

end

end QASM.Lowering
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
