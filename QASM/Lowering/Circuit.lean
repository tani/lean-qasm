    import LiterateLean
    import QASM.Lowering.Expr
    open scoped LiterateLean

# Circuit lowering

Gate bodies lower to explicit categorical composition. Applications on selected wires are represented by permutations around a primitive tensor identity, preserving sequential and parallel structure.

Applying a gate $`g`$ to selected lanes is represented structurally as

```math
P^{-1} \circ (g \otimes \mathrm{id}) \circ P,
```

where $`P`$ moves the selected wires into the primitive interface. This makes both the
selection and the untouched wires explicit:

```mermaid
flowchart LR
    Input --> P["permute P"]
    P --> Parallel["gate tensor identity"]
    Parallel --> Pinv["permute inverse P"]
    Pinv --> Output
```

```lean
namespace QASM.Lowering

open QASM

```

## Gate references and modifiers

Gate lookup resolves source names to either a standard primitive kind or a preassigned
user declaration. Modifier parameters are lowered once and stored outside the circuit
body; positive control counts are compile-time constants so the circuit interface remains
fully known.

```lean
private def controlCount (count : Option QASM.Frontend.Expression) : LowerM Nat := do
  match count with
  | none => pure 1
  | some value =>
      let count ← evalConstInt value
      if count <= 0 then fail "gate control count must be positive" else pure count.toNat

def gateModifier : QASM.Frontend.GateModifier → LowerM QASM.IR.GateModifier
  | .inverse => pure .inverse
  | .power exponent => .power <$> expression exponent
  | .control negative count => do pure (.control negative (← controlCount count))

def gateReference (modifiers : Array QASM.Frontend.GateModifier) (name : String)
    (parameters : Array QASM.Frontend.Expression) : LowerM QASM.IR.CircuitRef := do
  let context ← get
  let gate ← match lookupGate? context name with
    | some gate => pure gate
    | none => fail s!"gate '{name}' was not resolved"
  let parameters ← parameters.mapM expression
  let modifiers ← modifiers.mapM gateModifier
  let result : QASM.IR.CircuitRef :=
    { target := gate.kind, name, parameters, modifiers,
      origin := sourceOrigin context.options }
  pure result

```

## Static wire selections

Pure gate bodies have a fixed ordered wire interface. Aliases, concatenations, sets, and
ranges are therefore evaluated to concrete wire positions while lowering. Selection
rejects duplicate, out-of-range, physical, or dynamically indexed wires before a circuit
can violate its interface.

```lean
private def selectorValues (selector : QASM.Frontend.Expression) : LowerM (Array Int) := do
  match selector with
  | .range start step stop =>
      let first ← match start with | some value => evalConstInt value | none => pure 0
      let increment ← match step with | some value => evalConstInt value | none => pure 1
      let last ← match stop with | some value => evalConstInt value | none => pure first
      if increment == 0 then fail "range step cannot be zero" else
        pure (QASM.Value.range (.integer first) (.integer increment) (.integer last) |>.map (·.asInt))
  | .set values | .array values => values.mapM evalConstInt
  | value => pure #[← evalConstInt value]

private def selectPositions (positions : Array Nat)
    (selector : QASM.Frontend.Expression) : LowerM (Array Nat) := do
  let selectors ← selectorValues selector
  selectors.mapM fun selector =>
    match QASM.Value.resolveIndex? positions.size (.integer selector) with
    | .ok index => pure positions[index]!
    | .error message => fail message

partial def wirePositionsExpression
    (source : QASM.Frontend.Expression) : LowerM (Array Nat) := do
  match source with
  | .identifier name =>
      let context ← get
      match (lookupBinding? context name).bind (·.wirePositions) with
      | some positions => pure positions
      | none => fail s!"quantum alias source '{name}' has no circuit wire mapping"
  | .index value indices =>
      let mut positions ← wirePositionsExpression value
      for selector in indices do positions ← selectPositions positions selector
      pure positions
  | .binary "++" left right =>
      pure ((← wirePositionsExpression left) ++ (← wirePositionsExpression right))
  | .set values | .array values =>
      let mut positions := #[]
      for value in values do positions := positions ++ (← wirePositionsExpression value)
      pure positions
  | value => fail s!"'{value.toQasm}' is not a quantum alias expression"

private def operandPositions (source : QASM.Frontend.Operand) : LowerM (Array Nat) := do
  match source with
  | .hardware index => fail s!"physical qubit ${index} cannot occur in a portable gate body"
  | .identifier name groups =>
      let context ← get
      let base ← match (lookupBinding? context name).bind (·.wirePositions) with
        | some positions => pure positions
        | none => fail s!"gate operand '{name}' has no circuit wire mapping"
      if groups.isEmpty then pure base else
        let mut positions := #[]
        for selector in groups.flatMap id do
          positions := positions ++ (← selectPositions base selector)
        pure positions

```

## Placing an action in the full interface

A gate action on selected wires is represented categorically: permute selected wires to
the front, tensor the action with identity on untouched wires, then apply the inverse
permutation. `placeAction` checks arity and distinctness before constructing this
`pre ≫ (action ⊗ id) ≫ post` shape.

```lean
private def fullInterface (wireCount : Nat) : QASM.IR.Interface :=
  List.replicate wireCount .qubit

private def allDistinct (values : Array Nat) : Bool :=
  values.toList.Pairwise (· != ·)

private def placeAction (wireCount : Nat) (positions : Array Nat)
    (action : QASM.IR.Circuit) (origin : QASM.IR.SourceSpan) : LowerM QASM.IR.Circuit := do
  let arity := QASM.IR.Circuit.dom action |>.length
  unless positions.size == arity do
    fail s!"circuit action expects {arity} wires, got {positions.size}"
  unless positions.all (· < wireCount) && allDistinct positions do
    fail "circuit action contains duplicate or out-of-range wires"
  let remaining := (Array.range wireCount).filter (!positions.contains ·)
  let order := positions ++ remaining
  let interface := fullInterface wireCount
  let pre : QASM.IR.Circuit := .permute
    { domain := interface, codomain := interface, mapping := order, origin }
  let parallel := if remaining.isEmpty then action else
    QASM.IR.Circuit.tensor action (.identity (fullInterface remaining.size))
  let inverse := (Array.range wireCount).map fun position => order.toList.idxOf position
  let post : QASM.IR.Circuit := .permute
    { domain := interface, codomain := interface, mapping := inverse, origin }
  pure (.compose pre (.compose parallel post))

private def applyModifiers (modifiers : Array QASM.IR.GateModifier)
    (origin : QASM.IR.SourceSpan) (action : QASM.IR.Circuit) : QASM.IR.Circuit :=
  modifiers.foldr (fun modifier action => match modifier with
    | .inverse => .inverse action
    | .power exponent => .power exponent action
    | .control negative count =>
        .controlled
          { controls := List.replicate count .qubit,
            polarities := Array.replicate count
              (if negative then .negative else .positive), origin }
          action) action

private def composeCircuits (interface : QASM.IR.Interface)
    (circuits : Array QASM.IR.Circuit) : QASM.IR.Circuit :=
  circuits.foldl QASM.IR.Circuit.compose (.identity interface)

```

## Broadcasting and composing applications

OpenQASM operands broadcast when each width is either one or the common maximum. Each
broadcast lane becomes one placed primitive circuit, modifiers wrap the primitive before
placement, and the applications compose left to right over the unchanged full interface.
Timed calls remain explicit unsupported circuit nodes.

```lean
private def broadcastPositions (operands : Array (Array Nat)) : LowerM (Array (Array Nat)) := do
  let width := operands.foldl (fun width operand => max width operand.size) 1
  unless operands.all (fun operand => operand.size == 1 || operand.size == width) do
    fail "gate operands have incompatible broadcast widths"
  pure <| (Array.range width).map fun lane =>
    operands.map fun operand => if operand.size == 1 then operand[0]! else operand[lane]!

private def gateCallCircuit (wireCount : Nat)
    (modifiers : Array QASM.Frontend.GateModifier) (name : String)
    (parameters : Array QASM.Frontend.Expression) (designator : Option QASM.Frontend.Expression)
    (operands : Array QASM.Frontend.Operand) : LowerM QASM.IR.Circuit := do
  let context ← get
  let interface := fullInterface wireCount
  if designator.isSome then
    pure (.unsupported .timing s!"timed gate call '{name}'" interface interface)
  else
    let gate ← match lookupGate? context name with
      | some gate => pure gate
      | none => fail s!"gate '{name}' was not resolved"
    let parameters ← parameters.mapM expression
    let modifiers ← modifiers.mapM gateModifier
    let operandGroups ← operands.mapM operandPositions
    let lanes ← broadcastPositions operandGroups
    let mut applications := #[]
    for positions in lanes do
      let primitive : QASM.IR.Primitive :=
        { kind := gate.kind, name, parameters,
          input := fullInterface gate.qubitCount, output := fullInterface gate.qubitCount,
          origin := sourceOrigin context.options }
      let action := applyModifiers modifiers (sourceOrigin context.options) (.primitive primitive)
      applications := applications.push
        (← placeAction wireCount positions action (sourceOrigin context.options))
    pure (composeCircuits interface applications)

```

## Statically expanding gate-body control flow

Gate declarations are pure circuits, so their loops must be evaluable during lowering.
The recursive walk expands constant iteration domains, tracks aliases in lexical scopes,
and propagates `break` or `continue` as lowering signals. Runtime-dependent statements
are rejected rather than smuggled into a supposedly pure `Circuit`.

```lean
private inductive CircuitSignal
  | next
  | breakLoop
  | continueLoop
  deriving Inhabited, BEq

private structure CircuitResult where
  circuit : QASM.IR.Circuit
  signal  : CircuitSignal := .next
  deriving Inhabited

private def iterationValues (source : QASM.Frontend.Expression) : LowerM (Array Int) :=
  selectorValues source

mutual
private partial def circuitStatements (wireCount : Nat)
    (statements : Array QASM.Frontend.Statement) : LowerM CircuitResult := do
  let interface := fullInterface wireCount
  let mut circuits := #[]
  for statement in statements do
    let result ← circuitStatement wireCount statement
    circuits := circuits.push result.circuit
    if result.signal != .next then
      return { circuit := composeCircuits interface circuits, signal := result.signal }
  pure { circuit := composeCircuits interface circuits }

private partial def circuitStatement (wireCount : Nat)
    (statement : QASM.Frontend.Statement) : LowerM CircuitResult := do
  let context ← get
  let interface := fullInterface wireCount
  match statement with
  | .gateCall modifiers name parameters designator operands =>
      pure { circuit := ← gateCallCircuit wireCount modifiers name parameters designator operands }
  | .aliasDeclaration name value =>
      let type ← inferType value
      let positions ← wirePositionsExpression value
      let _ ← freshBinding name type false (some positions)
      pure { circuit := .identity interface }
  | .scope body =>
      pushScope
      let result ← circuitStatements wireCount body
      popScope
      pure result
  | .forStatement type iterator iterable body =>
      let iteratorType ← match QASM.Frontend.resolveType
          context.options.target context.analysis.constants type with
        | .ok value => pure value
        | .error error => throw error
      let values ← iterationValues iterable
      let savedConstants := context.localConstants
      let mut circuits := #[]
      for value in values do
        pushScope
        let _ ← freshBinding iterator iteratorType true
        modify fun context => { context with localConstants := (iterator, value) :: savedConstants }
        let result ← circuitStatements wireCount body
        popScope
        modify fun context => { context with localConstants := savedConstants }
        circuits := circuits.push result.circuit
        if result.signal == .breakLoop then break
        else if result.signal == .continueLoop then continue
      pure { circuit := composeCircuits interface circuits }
  | .breakStatement => pure { circuit := .identity interface, signal := .breakLoop }
  | .continueStatement => pure { circuit := .identity interface, signal := .continueLoop }
  | .annotated _ statement => circuitStatement wireCount statement
  | .pragma _ => pure { circuit := .identity interface }
  | other => fail s!"statement cannot occur in a pure gate circuit: {other.toQasm}"
end

```

## Public gate-body boundary

The final boundary requires loop-control signals to be consumed inside their loop. A
signal escaping the gate body is a lowering error; otherwise the accumulated circuit has
the same domain and codomain as the declared qubit parameter list.

```lean
def gateBody (wireCount : Nat) (statements : Array QASM.Frontend.Statement) :
    LowerM QASM.IR.Circuit := do
  let result ← circuitStatements wireCount statements
  unless result.signal == .next do fail "break/continue escaped a gate loop"
  pure result.circuit

end QASM.Lowering
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
