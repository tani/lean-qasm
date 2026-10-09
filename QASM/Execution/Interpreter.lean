    import LiterateLean
    import QASM.Runtime
    import QASM.IR.Program
    open scoped LiterateLean

# Interpreting canonical IR

This module is the typed runtime interpreter for `QASM.IR.Program`. It evaluates resolved
expressions, operations, callables, circuits, and structured control flow; parsing and
frontend ASTs are not part of the execution path.

Execution keeps interpreter state beneath an internal exception layer. This preserves the
final classical state when `end` exits through a nested expression or subroutine call;
public failures still cross the boundary as `RunError`.

The runtime path stays entirely on canonical data:

```mermaid
flowchart LR
    Program["IR.Program"] --> Proc
    Proc --> ExprEval["expression evaluation"]
    Proc --> Effects["operation evaluation"]
    Effects --> Backend["QuantumBackend"]
    Proc --> Flow["next / break / continue / return / end"]
```

```lean
namespace QASM.Execution

open QASM.IR

```

## State, effects, and non-local control

Classical values and allocated qubits occupy separate maps because a resolved `VarId`
cannot change category during execution. `ExecM` keeps state beneath the internal signal
layer and the caller's backend effects; backend failures are wrapped exactly once and
unwrapped into portable `RunError` values at the public boundary.

`Flow` carries structured loop and return transfers. `end` uses an internal signal so
it also escapes calls embedded in expressions. Scopes and calls restore their bindings
before forwarding either form of transfer.

```lean
structure ExecutionState (qubit : Type) where
  values : Std.HashMap VarId QASM.Value := {}
  qubits : Std.HashMap VarId (Array qubit) := {}

inductive Signal (error : Type) where
  | failure (error : QASM.RunError error)
  | ended

abbrev ExecM (m : Type → Type) (qubit error : Type) :=
  ExceptT (Signal error) (StateT (ExecutionState qubit) m)

inductive Flow where
  | next
  | breakLoop
  | continueLoop
  | returned (value : Option QASM.Value)
  | ended
  deriving Inhabited

private structure SavedBinding (qubit : Type) where
  id : VarId
  value : Option QASM.Value
  qubits : Option (Array qubit)

private def saveBinding (state : ExecutionState qubit) (id : VarId) : SavedBinding qubit :=
  { id, value := state.values[id]?, qubits := state.qubits[id]? }

private def restoreBinding (state : ExecutionState qubit) (saved : SavedBinding qubit) :
    ExecutionState qubit :=
  let values := match saved.value with
    | some value => state.values.insert saved.id value
    | none => state.values.erase saved.id
  let qubits := match saved.qubits with
    | some value => state.qubits.insert saved.id value
    | none => state.qubits.erase saved.id
  { values, qubits }

private def fail [Monad m] (error : QASM.RunError backendError) :
    ExecM m qubit backendError α :=
  throw (.failure error)

private def backend [Monad m] (action : m (Except backendError α)) :
    ExecM m qubit backendError α := do
  match ← (liftM action : ExecM m qubit backendError (Except backendError α)) with
  | .ok value => pure value
  | .error error => fail (.backend error)

```

## Resolved operators and runtime values

IR operators are closed inductive types, while `QASM.Value` implements the shared scalar
semantics using the source spellings of those operators. These total name maps are the
only conversion between the two vocabularies. Type-directed casts and defaults then
reconstruct the widths and shapes fixed by static analysis; unsupported IR types map to
`.unit` only as an internal invariant failure, never as source-level dynamic typing.

```lean
private def unaryName : UnaryOp → String
  | .not => "!"
  | .neg => "-"
  | .bitnot => "~"

private def binaryName : BinaryOp → String
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .div => "/"
  | .mod => "%"
  | .pow => "**"
  | .shl => "<<"
  | .shr => ">>"
  | .band => "&"
  | .bor => "|"
  | .bxor => "^"
  | .land => "&&"
  | .lor => "||"
  | .eq => "=="
  | .ne => "!="
  | .lt => "<"
  | .le => "<="
  | .gt => ">"
  | .ge => ">="
  | .concat => "++"

private def builtinName : Builtin → String
  | .popcount => "popcount"
  | .sizeof => "sizeof"
  | .real => "real"
  | .imag => "imag"
  | .sin => "sin"
  | .cos => "cos"
  | .tan => "tan"
  | .arcsin => "arcsin"
  | .arccos => "arccos"
  | .arctan => "arctan"
  | .sqrt => "sqrt"
  | .exp => "exp"
  | .log => "log"
  | .floor => "floor"
  | .ceiling => "ceiling"
  | .mod => "mod"
  | .rotl => "rotl"
  | .rotr => "rotr"

private def scalarNameWidth : ScalarTy → String × Nat
  | .bit width => ("bit", width.getD 1)
  | .sint width => ("int", width)
  | .uint width => ("uint", width)
  | .float width => ("float", width)
  | .angle width => ("angle", width)
  | .gateAngle => ("float", 64)
  | .boolean => ("bool", 1)
  | .complex width => ("complex", width)
  | .duration => ("duration", 64)
  | .stretch | .qubit _ | .void => ("void", 0)

private def castScalar (type : ScalarTy) (value : QASM.Value) : QASM.Value :=
  match type with
  | .bit none => .bit value.truthy
  | _ =>
      let (name, width) := scalarNameWidth type
      QASM.Value.cast name width value

private def castValue (type : QASM.IR.Type) (value : QASM.Value) : QASM.Value :=
  match type with
  | .scalar scalar => castScalar scalar value
  | .array element shape =>
      let (name, width) := scalarNameWidth element
      QASM.Value.castArray name width shape.toList value
  | .arrayRef _ element (some shape) _ =>
      let (name, width) := scalarNameWidth element
      QASM.Value.castArray name width shape.toList value
  | _ => value

private def defaultScalar : ScalarTy → QASM.Value
  | .bit none => .bit false
  | .bit (some width) => .bits (Array.replicate width false)
  | .sint width => .sint width 0
  | .uint width => .uint width 0
  | .float 32 => .float32 0
  | .float _ => .float 0
  | .angle width => .angle width 0
  | .gateAngle => .float 0.0
  | .boolean => .boolean false
  | .complex 32 => .complex32 0 0
  | .complex _ => .complex 0 0
  | .duration => .duration 0
  | .stretch | .qubit _ | .void => .unit

private def defaultValue : QASM.IR.Type → QASM.Value
  | .scalar type => defaultScalar type
  | .array element shape =>
      QASM.Value.replicateShape shape (defaultScalar element)
  | .arrayRef _ element (some shape) _ =>
      QASM.Value.replicateShape shape (defaultScalar element)
  | _ => .unit

private def isQuantumType : QASM.IR.Type → Bool
  | .scalar (.qubit _) => true
  | _ => false

```

## Declarations, unitary grouping, and qubit selection

Circuit interpretation may produce several backend operations for one source gate.
`unitarySequence` preserves that grouping so inverse, power, and control modifiers apply
to the complete gate. Callable and gate references use stable numeric identifiers; names
remain diagnostic metadata and are never used for lookup.

Qubit selection is the checked counterpart of classical `Value.index`: every resolved
index must address an allocated wire, otherwise execution reports `indexOutOfBounds`
before invoking the backend.

```lean
private def unitarySequence (operations : Array (QASM.Unitary qubit)) : QASM.Unitary qubit :=
  match operations with
  | #[operation] => operation
  | _ => .sequence operations

private def findSubroutine (program : Program) (id : CallableId) : Option SubroutineDecl :=
  program.subroutines.find? (·.id == id)

private def findGate (program : Program) (id : DeclId) : Option GateDecl :=
  program.gates.find? (·.id == id)

private def selectQubits (name : String) (values : Array qubit) (selector : QASM.Value) :
    Except (QASM.RunError backendError) (Array qubit) := do
  match selector with
  | .array selectors =>
      let mut selected := #[]
      for selector in selectors do
        let index := QASM.Value.resolveIndex values.size selector
        match values[index]? with
        | some value => selected := selected.push value
        | none => throw (.indexOutOfBounds name index values.size)
      pure selected
  | selector =>
      let index := QASM.Value.resolveIndex values.size selector
      match values[index]? with
      | some value => pure #[value]
      | none => throw (.indexOutOfBounds name index values.size)

```

## Captured call arguments

Expression calls recover operand kinds from the resolved callable signature. Both call
forms then use the same invocation path. Selectors and actual values are captured before
any parameter binding is installed, so recursive calls evaluate in the caller's environment.

```lean
private partial def expressionTarget (value : Expr) : Except (QASM.RunError error) LValue := do
  match value.node with
  | .var id => pure { root := id, type := value.type, origin := value.origin }
  | .index base indices =>
      let target ← expressionTarget base
      pure { target with indices := target.indices.push indices, type := value.type }
  | _ => throw (.internal "a reference argument must have a variable root")

private def expressionArgument (parameter : Var) (value : Expr) :
    Except (QASM.RunError error) Argument := do
  match parameter.type with
  | .scalar (.qubit _) =>
      let target ← expressionTarget value
      pure (.quantum (.wire target.root (target.indices.flatten)))
  | .arrayRef mutable _ _ _ => pure (.arrayRef (← expressionTarget value) mutable)
  | _ => pure (.expr value)

private structure CapturedTarget where
  root : VarId
  selectors : Array (Array QASM.Value)
  type : QASM.IR.Type
  deriving Inhabited

private partial def updateTarget (value : QASM.Value) (groups : Array (Array QASM.Value))
    (replacement : QASM.Value) : QASM.Value :=
  match groups.toList with
  | [] => replacement
  | selectors :: rest =>
      let selected := QASM.Value.index value selectors
      QASM.Value.setIndex value selectors (updateTarget selected rest.toArray replacement)

private inductive CapturedArgument (qubit : Type) where
  | value (value : QASM.Value) (writeback : Option CapturedTarget := none)
  | quantum (wires : Array qubit)

/-- Only representable rational multiples of pi bypass floating-point conversion.
    Other expressions retain the existing finite classical evaluation. -/
private def piCoefficient (fuel : Nat) (value : Expr) : Option Rat :=
  match fuel with
  | 0 => none
  | fuel + 1 => match value.node with
    | .realConstant .pi => some 1
    | .realConstant .tau => some 2
    | .intLit 0 => some 0
    | .unary .neg a => (- ·) <$> piCoefficient fuel a
    | .binary .add a b => do return (← piCoefficient fuel a) + (← piCoefficient fuel b)
    | .binary .sub a b => do return (← piCoefficient fuel a) - (← piCoefficient fuel b)
    | .binary .div a b => do
        let coefficient ← piCoefficient fuel a
        match b.node with
        | .intLit i =>
          let i := (castValue b.type (.integer i)).asInt
          if i = 0 then none else some (coefficient / (i : Rat))
        | _ => none
    | .binary .mul a b =>
        match a.node, b.node with
        | .intLit i, _ => (((castValue a.type (.integer i)).asInt : Rat) * ·) <$> piCoefficient fuel b
        | _, .intLit i => (· * ((castValue b.type (.integer i)).asInt : Rat)) <$> piCoefficient fuel a
        | _, _ => none
    | _ => none

private def exactAngle? (target : QASM.IR.Type) (value : Expr) : Option QASM.Value := do
  let .scalar (.angle width) := target | none
  let coefficient ← piCoefficient 1024 value
  let scaled : Rat := coefficient * ((2 ^ width : Nat) : Rat) / 2
  if scaled.den ≠ 1 then none
  else some (.angle width (scaled.num % (Int.ofNat (2 ^ width))).toNat)

private def decimalApproximation (literal : DecimalLiteral) : Except String Float := do
  let json ← Lean.Json.parse literal.toQasm
  Float.fromJson? json

private def constantApproximation : RealConstant → Float
  | .pi => 3.141592653589793
  | .tau => 6.283185307179586
  | .euler => 2.718281828459045
```

## The recursive interpreter

Expressions, lvalues, quantum operands, circuits, callables, operations, and processes
form one recursive execution graph, so Lean requires them in a single `mutual` block. The
definitions follow the dependency order encountered during execution:

1. `evalExpr` evaluates typed scalar and aggregate expressions and dispatches subroutine
   calls;
2. `captureTarget`, `readTarget`, and `assignLValue` traverse classical storage without changing resolved
   roots;
3. `evalQuantumOperand`, `buildCircuit`, and `applyCircuitRef` resolve wires and turn
   categorical circuit IR into backend-facing `Unitary` trees;
4. subroutine invocation saves parameter bindings, executes a process, writes mutable
   array references back, and restores the caller environment;
5. `evalDomain`, `evalOp`, and `evalProc` implement iteration, effects, scopes, and
   structured control flow.

Source `if`, `for`, and `while` therefore remain `Proc.branch`, `Proc.forLoop`, and
`Proc.whileLoop` in each generated program. Lean control constructs occur here in the
shared interpreter, not in the generated `execute` wrapper.

```lean
mutual
  private partial def evalExpr [Monad m] [QASM.QuantumBackend m qubit backendError]
      (program : Program) (value : Expr) : ExecM m qubit backendError QASM.Value := do
    match value.node with
    | .intLit literal => pure (castValue value.type (.integer literal))
    | .floatLit literal => pure (castValue value.type (.float literal))
    | .decimalLit literal =>
        match decimalApproximation literal with
        | .ok literal => pure (castValue value.type (.float literal))
        | .error message => fail (.internal message)
    | .realConstant literal =>
        pure (castValue value.type (.float (constantApproximation literal)))
    | .imaginaryDecimalLit literal =>
        match decimalApproximation literal with
        | .ok literal => pure (castValue value.type (.complex 0 literal))
        | .error message => fail (.internal message)
    | .imaginaryLit literal => pure (castValue value.type (.complex 0 literal))
    | .boolLit literal => pure (castValue value.type (.boolean literal))
    | .bitstringLit bits => pure (castValue value.type (.bits bits))
    | .durationLit seconds => pure (castValue value.type (.duration seconds))
    | .var id =>
        match (← get).values[id]? with
        | some .uninitialized => fail (.uninitializedRead s!"var{id.value}")
        | some value => pure value
        | none => fail (.internal s!"unknown variable {id.value}")
    | .const id =>
        match program.constants.find? (·.id == id) with
        | some declaration => evalTypedExpr program declaration.type declaration.value
        | none => fail (.internal s!"unknown constant {id.value}")
    | .unary operator operand =>
        pure (QASM.Value.unary (unaryName operator) (← evalExpr program operand))
    | .binary operator leftExpr rightExpr =>
        let left ← evalExpr program leftExpr
        let right ← evalExpr program rightExpr
        if (operator == .div || operator == .mod) && right.isZero then
          fail .divisionByZero
        let right := if operator == .eq || operator == .ne then
          castValue leftExpr.type right else right
        pure (QASM.Value.binary (binaryName operator) left right)
    | .builtin builtin arguments =>
        pure (QASM.Value.builtin (builtinName builtin) (← arguments.mapM (evalExpr program)))
    | .callSubroutine callee arguments =>
        let declaration ← match findSubroutine program callee with
          | some declaration => pure declaration
          | none => fail (.internal s!"unknown subroutine {callee.value}")
        if arguments.size != declaration.parameters.size then
          fail (.internal "subroutine argument count mismatch")
        let arguments ← (declaration.parameters.zip arguments).mapM fun (parameter, value) =>
          match expressionArgument parameter value with
          | .ok argument => pure argument
          | .error error => fail error
        invokeSubroutine program callee arguments
    | .cast target value => evalTypedExpr program target value
    | .index value indices =>
        pure (QASM.Value.index (← evalExpr program value) (← indices.mapM (evalExpr program)))
    | .range start step stop =>
        let start ← start.mapM (evalExpr program)
        let step ← step.mapM (evalExpr program)
        let stop ← stop.mapM (evalExpr program)
        pure (.array (QASM.Value.range (start.getD (.integer 0))
          (step.getD (.integer 1)) (stop.getD (.integer 0))))
    | .set values | .array values => .array <$> values.mapM (evalExpr program)
    | .unsupported _ detail => fail (.internal detail)

  private partial def evalTypedExpr [Monad m] [QASM.QuantumBackend m qubit backendError]
      (program : Program) (target : QASM.IR.Type) (expression : Expr) : ExecM m qubit backendError QASM.Value := do
    let value ← evalExpr program expression
    pure ((exactAngle? target expression).getD (castValue target value))

  private partial def captureTarget [Monad m] [QASM.QuantumBackend m qubit backendError]
      (program : Program) (target : LValue) : ExecM m qubit backendError CapturedTarget := do
    let mut selectors := #[]
    for group in target.indices do
      selectors := selectors.push (← group.mapM (evalExpr program))
    pure { root := target.root, selectors, type := target.type }

  private partial def readTarget [Monad m] (target : CapturedTarget) :
      ExecM m qubit backendError QASM.Value := do
    let root ← match (← get).values[target.root]? with
      | some value => pure value
      | none => fail (.internal s!"unknown variable {target.root.value}")
    pure (target.selectors.foldl QASM.Value.index root)

  private partial def writeTarget [Monad m] (target : CapturedTarget) (newValue : QASM.Value) :
      ExecM m qubit backendError Unit := do
    let state ← get
    let root ← match state.values[target.root]? with
      | some value => pure value
      | none => fail (.internal s!"unknown variable {target.root.value}")
    let newValue := castValue target.type newValue
    let updated := if target.selectors.isEmpty then newValue
      else updateTarget root target.selectors newValue
    set { state with values := state.values.insert target.root updated }

  private partial def assignLValue [Monad m] [QASM.QuantumBackend m qubit backendError]
      (program : Program) (target : LValue) (newValue : QASM.Value) :
      ExecM m qubit backendError Unit := do
    writeTarget (← captureTarget program target) newValue

  private partial def evalQuantumExpr [Monad m] [QASM.QuantumBackend m qubit backendError]
      (program : Program) (value : Expr) : ExecM m qubit backendError (Array qubit) := do
    match value.node with
    | .var id =>
        match (← get).qubits[id]? with
        | some values => pure values
        | none => fail (.internal s!"unknown qubit variable {id.value}")
    | .index root indices =>
        let mut values ← evalQuantumExpr program root
        for index in indices do
          let selector ← evalExpr program index
          match selectQubits "qubit" values selector with
          | .ok selected => values := selected
          | .error error => fail error
        pure values
    | _ => fail (.internal "invalid quantum alias expression")

  private partial def evalQuantumOperand [Monad m]
      [QASM.QuantumBackend m qubit backendError] (program : Program)
      (operand : QuantumOperand) : ExecM m qubit backendError (Array qubit) := do
    match operand with
    | .physical index => fail (.internal s!"physical qubit ${index} is unavailable")
    | .wire id indices _ =>
        let state ← get
        let mut values ← match state.qubits[id]? with
          | some values => pure values
          | none => fail (.internal s!"unknown qubit variable {id.value}")
        for index in indices do
          let selector ← evalExpr program index
          match selectQubits s!"var{id.value}" values selector with
          | .ok selected => values := selected
          | .error error => fail error
        pure values

  private partial def buildCircuit [Monad m] [QASM.QuantumBackend m qubit backendError]
      (program : Program) (circuit : Circuit) (lanes : Array qubit) :
      ExecM m qubit backendError (Array (QASM.Unitary qubit) × Array qubit) := do
    match circuit with
    | .identity _ => pure (#[], lanes)
    | .primitive primitive =>
        let parameters ← primitive.parameters.mapM fun value =>
          return (← evalExpr program value).asFloat
        let operation ← match primitive.kind with
          | .userDefined id =>
              match findGate program id with
              | some declaration => invokeGate program declaration parameters lanes
              | none => fail (.internal s!"unknown gate {id.value}")
          | _ => pure (QASM.Unitary.standard primitive.name parameters lanes)
        pure (#[operation], lanes)
    | .compose first second =>
        let (firstOperations, lanes) ← buildCircuit program first lanes
        let (secondOperations, lanes) ← buildCircuit program second lanes
        pure (firstOperations ++ secondOperations, lanes)
    | .tensor first second =>
        let boundary := first.dom.length
        let (firstOperations, firstLanes) ← buildCircuit program first (lanes.extract 0 boundary)
        let (secondOperations, secondLanes) ← buildCircuit program second
          (lanes.extract boundary lanes.size)
        pure (firstOperations ++ secondOperations, firstLanes ++ secondLanes)
    | .permute permutation =>
        let mut reordered := #[]
        for index in permutation.mapping do
          match lanes[index]? with
          | some lane => reordered := reordered.push lane
          | none => fail (.internal "invalid circuit permutation")
        pure (#[], reordered)
    | .inverse value =>
        let (operations, lanes) ← buildCircuit program value lanes
        pure (#[.inverse (unitarySequence operations)], lanes)
    | .power exponent value =>
        let exponent := (← evalExpr program exponent).asFloat
        let (operations, lanes) ← buildCircuit program value lanes
        pure (#[.power exponent (unitarySequence operations)], lanes)
    | .controlled spec value =>
        let controls := lanes.extract 0 spec.controls.length
        let (operations, targetLanes) ← buildCircuit program value
          (lanes.extract spec.controls.length lanes.size)
        let mut operation := unitarySequence operations
        for reverseIndex in [:controls.size] do
          let index := controls.size - reverseIndex - 1
          let polarity := match spec.polarities[index]? with
            | some .negative => QASM.ControlPolarity.negative
            | _ => QASM.ControlPolarity.positive
          match controls[index]? with
          | some control => operation := .controlled polarity #[control] operation
          | none => fail (.internal "invalid controlled circuit")
        pure (#[operation], controls ++ targetLanes)
    | .unsupported _ detail _ _ => fail (.internal detail)

  private partial def invokeGate [Monad m] [QASM.QuantumBackend m qubit backendError]
      (program : Program) (declaration : GateDecl) (parameters : Array Float)
      (targets : Array qubit) : ExecM m qubit backendError (QASM.Unitary qubit) := do
    let state ← get
    let saved := declaration.parameters.map (fun parameter => saveBinding state parameter.id)
    let mut state := state
    for index in [:declaration.parameters.size] do
      let parameter := declaration.parameters[index]!
      let value := QASM.Value.float (parameters[index]?.getD 0)
      state := { state with values := state.values.insert parameter.id (castValue parameter.type value) }
    set state
    let (operations, _) ← buildCircuit program declaration.body targets
    let mut restored ← get
    for binding in saved do restored := restoreBinding restored binding
    set restored
    pure (unitarySequence operations)

  private partial def applyCircuitRef [Monad m] [QASM.QuantumBackend m qubit backendError]
      (program : Program) (gate : CircuitRef) (operands : Array QuantumOperand) :
      ExecM m qubit backendError Unit := do
    let operandArrays ← operands.mapM (evalQuantumOperand program)
    let width ← match QASM.broadcastWidth operandArrays with
      | .ok width => pure width
      | .error message => fail (.internal message)
    let parameters ← gate.parameters.mapM fun value => return (← evalExpr program value).asFloat
    for lane in [:width] do
      let targets := QASM.broadcastLane operandArrays lane
      let controlCount := gate.modifiers.foldl (fun count modifier => match modifier with
        | .control _ value => count + value
        | _ => count) 0
      let gateTargets := targets.extract controlCount targets.size
      let mut operation ← match gate.target with
        | .userDefined id =>
            match findGate program id with
            | some declaration => invokeGate program declaration parameters gateTargets
            | none => fail (.internal s!"unknown gate {id.value}")
        | _ => pure (QASM.Unitary.standard gate.name parameters gateTargets)
      for reverseIndex in [:gate.modifiers.size] do
        let index := gate.modifiers.size - reverseIndex - 1
        match gate.modifiers[index]! with
        | .inverse => operation := .inverse operation
        | .power exponent => operation := .power (← evalExpr program exponent).asFloat operation
        | .control negative count =>
            let offset := (gate.modifiers.extract 0 index).foldl (fun offset modifier =>
              match modifier with | .control _ count => offset + count | _ => offset) 0
            let polarity := if negative then QASM.ControlPolarity.negative
              else QASM.ControlPolarity.positive
            operation := .controlled polarity (targets.extract offset (offset + count)) operation
      backend (QASM.QuantumBackend.apply (m := m) (Qubit := qubit)
        (Error := backendError) operation)

  private partial def invokeSubroutine [Monad m] [QASM.QuantumBackend m qubit backendError]
      (program : Program) (callee : CallableId) (arguments : Array Argument) :
      ExecM m qubit backendError QASM.Value := do
    let declaration ← match findSubroutine program callee with
      | some declaration => pure declaration
      | none => fail (.internal s!"unknown subroutine {callee.value}")
    if arguments.size != declaration.parameters.size then
      fail (.internal "subroutine argument count mismatch")
    let captured ← arguments.mapM fun argument => do
      match argument with
      | .expr value => return CapturedArgument.value (← evalExpr program value)
      | .arrayRef target mutable =>
          let target ← captureTarget program target
          return CapturedArgument.value (← readTarget target) (if mutable then some target else none)
      | .quantum operand => return CapturedArgument.quantum (← evalQuantumOperand program operand)
    let state ← get
    let saved := declaration.parameters.map (fun parameter => saveBinding state parameter.id)
    for (parameter, argument) in declaration.parameters.zip captured do
      match argument with
      | .value value _ => modify fun state => { state with
          values := state.values.insert parameter.id (castValue parameter.type value) }
      | .quantum wires => modify fun state => { state with
          qubits := state.qubits.insert parameter.id wires }
    let outcome : Except (Signal backendError) Flow ← try pure (.ok (← evalProc program declaration.body))
      catch signal => pure (.error signal)
    let current ← get
    let writebacks := (declaration.parameters.zip captured).filterMap fun (parameter, argument) =>
      match argument with
      | .value _ (some target) => some (target, current.values[parameter.id]?.getD .unit)
      | _ => none
    let mut restored := current
    for binding in saved do restored := restoreBinding restored binding
    set restored
    for (target, value) in writebacks do writeTarget target value
    match outcome with
    | .error signal => throw signal
    | .ok (.returned value) => pure (castValue declaration.returnType (value.getD .unit))
    | .ok .ended => throw .ended
    | .ok _ => pure .unit

  private partial def evalDomain [Monad m] [QASM.QuantumBackend m qubit backendError]
      (program : Program) (domain : IterationDomain) :
      ExecM m qubit backendError (Array QASM.Value) := do
    match domain with
    | .range start step stop =>
        let start ← evalExpr program start
        let step ← evalExpr program step
        let stop ← evalExpr program stop
        if step.asInt == 0 then fail .rangeStepZero
        pure (QASM.Value.range start step stop)
    | .set values => values.mapM (evalExpr program)
    | .array value =>
        match ← evalExpr program value with
        | .bits bits => pure (bits.map QASM.Value.bit)
        | value => pure value.asArray

  private partial def evalOp [Monad m] [QASM.QuantumBackend m qubit backendError]
      (program : Program) (operation : Op) : ExecM m qubit backendError Flow := do
    match operation with
    | .eval value => evalExpr program value *> pure .next
    | .declare var initializer =>
        if isQuantumType var.type then
          match initializer with
          | some value =>
              let qubits ← evalQuantumExpr program value
              modify fun state => { state with qubits := state.qubits.insert var.id qubits }
          | none => fail (.internal s!"qubit variable '{var.name}' requires allocation or an alias")
        else
          let value ← match initializer with
            | some value => evalTypedExpr program var.type value
            | none => pure (defaultValue var.type)
          modify fun state => { state with values := state.values.insert var.id value }
        pure .next
    | .assign target value => assignLValue program target (← evalTypedExpr program target.type value) *> pure .next
    | .apply gate operands => applyCircuitRef program gate operands *> pure .next
    | .measure source target =>
        let qubits ← evalQuantumOperand program source
        let mut bits := #[]
        for wire in qubits do
          bits := bits.push (← backend (QASM.QuantumBackend.measure (m := m)
            (Qubit := qubit) (Error := backendError) wire))
        match target with
        | .discard => pure ()
        | .lvalue target =>
            let value := if bits.size == 1 then QASM.Value.bit bits[0]! else .bits bits
            assignLValue program target value
        pure .next
    | .reset operand =>
        for wire in (← evalQuantumOperand program operand) do
          backend (QASM.QuantumBackend.reset (m := m) (Qubit := qubit)
            (Error := backendError) wire)
        pure .next
    | .barrier operands =>
        let qubits ← operands.flatMapM (evalQuantumOperand program)
        backend (QASM.QuantumBackend.barrier (m := m) (Qubit := qubit)
          (Error := backendError) (.targets qubits))
        pure .next
    | .allocate declaration =>
        let qubits ← backend (QASM.QuantumBackend.allocate (m := m) (Qubit := qubit)
          (Error := backendError) declaration.size)
        modify fun state => { state with qubits := state.qubits.insert declaration.var qubits }
        pure .next
    | .call callee arguments => invokeSubroutine program callee arguments *> pure .next
    | .emitExtern _ => fail (.internal "extern execution is not portable")
    | .unsupported _ detail => fail (.internal detail)

  private partial def evalProc [Monad m] [QASM.QuantumBackend m qubit backendError]
      (program : Program) (proc : Proc) : ExecM m qubit backendError Flow := do
    match proc with
    | .skip => pure .next
    | .operation operation => evalOp program operation
    | .sequence steps =>
        for step in steps do
          match ← evalProc program step with
          | .next => pure ()
          | flow => return flow
        pure .next
    | .scope locals body =>
        let state ← get
        let saved := locals.map (fun entry => saveBinding state entry.id)
        let outcome : Except (Signal backendError) Flow ← try pure (.ok (← evalProc program body))
          catch signal => pure (.error signal)
        let mut restored ← get
        for binding in saved do restored := restoreBinding restored binding
        set restored
        match outcome with
        | .ok flow => pure flow
        | .error signal => throw signal
    | .branch condition thenBranch elseBranch =>
        if (← evalExpr program condition).truthy then evalProc program thenBranch
        else match elseBranch with | some branch => evalProc program branch | none => pure .next
    | .switch scrutineeExpr cases default =>
        let scrutinee ← evalExpr program scrutineeExpr
        for entry in cases do
          match entry with
          | .mk labels body =>
              let mut selected := false
              for label in labels do
                let labelValue := castValue scrutineeExpr.type (← evalExpr program label)
                selected := selected || (QASM.Value.binary "==" scrutinee labelValue).truthy
              if selected then return ← evalProc program body
        match default with | some body => evalProc program body | none => pure .next
    | .forLoop iterator domain body =>
        let state ← get
        let saved := saveBinding state iterator.id
        let outcome : Except (Signal backendError) Flow ← try
          let mut flow := Flow.next
          for value in (← evalDomain program domain) do
            modify fun state => { state with
              values := (state.values.insert iterator.id (castValue iterator.type value)) }
            match ← evalProc program body with
            | .breakLoop => break
            | .continueLoop | .next => pure ()
            | transfer => flow := transfer; break
          pure (.ok flow)
        catch signal => pure (.error signal)
        modify fun state => restoreBinding state saved
        match outcome with
        | .ok flow => pure flow
        | .error signal => throw signal
    | .whileLoop condition body =>
        while (← evalExpr program condition).truthy do
          match ← evalProc program body with
          | .breakLoop => break
          | .continueLoop | .next => pure ()
          | flow => return flow
        pure .next
    | .breakLoop => pure .breakLoop
    | .continueLoop => pure .continueLoop
    | .returnValue value => .returned <$> value.mapM (evalExpr program)
    | .endProgram => throw .ended
end

```

## Public execution boundary

`run` initializes inputs and typed output defaults, evaluates the program body once, and
returns only the final classical environment. Qubit storage is intentionally internal:
observable quantum effects cross `QuantumBackend`, while generated output codecs consume
the returned `VarId` map.

```lean
/-- Executes a resolved canonical program and returns its final classical environment. -/
def run [Monad m] [QASM.QuantumBackend m qubit backendError]
    (program : Program) (inputs : Array (VarId × QASM.Value)) :
    m (Except (QASM.RunError backendError) (Std.HashMap VarId QASM.Value)) := do
  let mut initial : ExecutionState qubit := {}
  for (id, value) in inputs do
    initial := { initial with values := initial.values.insert id value }
  for declaration in program.outputs do
    initial := { initial with
      values := initial.values.insert declaration.var.id (defaultValue declaration.var.type) }
  let action : ExecM m qubit backendError Unit := do
    discard <| evalProc program program.body
  let (outcome, state) ← action.run.run initial
  match outcome with
  | .error (.failure error) => pure (.error error)
  | .error .ended | .ok _ => pure (.ok state.values)

end QASM.Execution
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
