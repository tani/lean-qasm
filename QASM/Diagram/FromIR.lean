    import LiterateLean
    import QASM.Diagram.Model
    import QASM.IR.Program
    open scoped LiterateLean

# Circuit diagrams from canonical IR

Diagram extraction walks only the canonical process IR. It assigns stable lanes to allocated and physical qubits, preserves structured control flow as regions, and marks dynamic wire selections as approximate.

Extraction visits structure rather than choosing an execution path:

```mermaid
flowchart TD
    Program["IR.Program"] --> Discover["discover wire lanes"]
    Program --> Walk["walk Proc tree"]
    Discover --> Diagram["CircuitDiagram"]
    Walk --> Operations
    Walk --> Regions["branch and loop regions"]
    Operations --> Diagram
    Regions --> Diagram
```

Consequently both sides of a branch appear once, and a loop body appears once regardless
of its runtime iteration count.

```lean
namespace QASM.Diagram

open QASM.IR

```

## Discovering wires and display names

Diagram lanes are assigned in first-occurrence order. Allocations reserve contiguous
labels, physical qubits receive their own stable lanes, and recursive process traversal
visits every branch and loop body because the diagram is a static source view rather than
one execution trace. A separate name pass records classical locals used in labels without
turning them into quantum wires.

```lean
private structure WireBinding where
  first : Nat
  count : Nat
  deriving Inhabited

private structure WireState where
  labels : Array String := #[]
  vars : Std.HashMap VarId WireBinding := {}
  physical : Std.HashMap Nat Nat := {}

private def registerVar (state : WireState) (id : VarId) (name : String) (count : Nat) : WireState :=
  if state.vars.contains id then state else
    let first := state.labels.size
    let labels := if count == 1 then state.labels.push name else
      state.labels ++ (Array.range count).map fun index => s!"{name}[{index}]"
    { state with labels, vars := state.vars.insert id { first, count } }

private def registerPhysical (state : WireState) (index : Nat) : WireState :=
  if state.physical.contains index then state else
    let lane := state.labels.size
    let state := { state with labels := state.labels.push s!"${index}" }
    { state with physical := state.physical.insert index lane }

private def collectOperand (state : WireState) : QuantumOperand → WireState
  | .physical index => registerPhysical state index
  | .wire _ _ _ => state

private def collectArgument (state : WireState) : Argument → WireState
  | .quantum operand => collectOperand state operand
  | _ => state

private def collectOp (state : WireState) : Op → WireState
  | .allocate declaration => registerVar state declaration.var declaration.name declaration.size
  | .apply _ operands | .barrier operands => operands.foldl collectOperand state
  | .measure source _ | .reset source => collectOperand state source
  | .call _ arguments => arguments.foldl collectArgument state
  | _ => state

private partial def collectProc (state : WireState) : Proc → WireState
  | .skip | .breakLoop | .continueLoop | .returnValue _ | .endProgram => state
  | .operation op => collectOp state op
  | .sequence steps => steps.foldl collectProc state
  | .scope _ body => collectProc state body
  | .branch _ thenBranch elseBranch =>
      let state := collectProc state thenBranch
      elseBranch.map (collectProc state) |>.getD state
  | .switch _ cases default =>
      let state := cases.foldl (fun state entry => match entry with
        | .mk _ body => collectProc state body) state
      default.map (collectProc state) |>.getD state
  | .forLoop _ _ body | .whileLoop _ body => collectProc state body

private partial def collectNames (names : Std.HashMap VarId String) : Proc → Std.HashMap VarId String
  | .skip | .breakLoop | .continueLoop | .returnValue _ | .endProgram => names
  | .operation (.declare var _) => names.insert var.id var.name
  | .operation (.allocate declaration) => names.insert declaration.var declaration.name
  | .operation _ => names
  | .sequence steps => steps.foldl collectNames names
  | .scope locals body => collectNames (locals.foldl (fun names var => names.insert var.id var.name) names) body
  | .branch _ thenBranch elseBranch =>
      let names := collectNames names thenBranch
      elseBranch.map (collectNames names) |>.getD names
  | .switch _ cases default =>
      let names := cases.foldl (fun names entry => match entry with
        | .mk _ body => collectNames names body) names
      default.map (collectNames names) |>.getD names
  | .forLoop iterator _ body => collectNames (names.insert iterator.id iterator.name) body
  | .whileLoop _ body => collectNames names body

```

## Exact and approximate operand selection

Literal positive and negative indices can be mapped to exact lanes statically. A dynamic,
missing, or out-of-range selector falls back to the complete allocated register and marks
the operand approximate. Rendering therefore never invents a precise runtime wire while
still showing the operation on every lane it may address.

```lean
private def literalIndex (count : Nat) (value : Expr) : Option Nat :=
  match value.node with
  | .intLit index =>
      if index >= 0 then
        let index := index.toNat
        if index < count then some index else none
      else
        let distance := index.natAbs
        if distance <= count then some (count - distance) else none
  | _ => none

private def operandDiagram (wires : WireState) : QuantumOperand → QASM.DiagramOperand
  | .physical index =>
      { wires := wires.physical[index]?.map (#[·]) |>.getD #[], approximate := false }
  | .wire var indices approximate =>
      match wires.vars[var]? with
      | none => { wires := #[], approximate := true }
      | some binding =>
          if indices.isEmpty then
            { wires := (Array.range binding.count).map (binding.first + ·), approximate }
          else
            let selected := indices.map (literalIndex binding.count)
            if selected.all Option.isSome then
              { wires := selected.filterMap id |>.map (binding.first + ·), approximate }
            else
              { wires := (Array.range binding.count).map (binding.first + ·), approximate := true }

```

## Choosing conventional gate glyphs

Built-in controls and explicit modifiers contribute one ordered polarity list. Exact,
untransformed X-family and swap operations receive conventional glyphs; inverse or power
modifiers force a labeled box because a simple target symbol would hide semantics.
Controlled nonstandard gates retain their controls but use an explicit target label.

```lean
private def runtimePolarity (negative : Bool) : QASM.ControlPolarity :=
  if negative then .negative else .positive

private def builtinControls (name : String) : Array QASM.ControlPolarity :=
  match name with
  | "cx" | "CX" | "cy" | "cz" | "ch" | "cp" | "crx" | "cry" | "crz" | "cswap" | "cu" =>
      #[.positive]
  | "ccx" => #[.positive, .positive]
  | _ => #[]

private def explicitControls (modifiers : Array GateModifier) : Array QASM.ControlPolarity :=
  modifiers.foldl (fun controls modifier => match modifier with
    | .control negative count => controls ++ Array.replicate count (runtimePolarity negative)
    | _ => controls) #[]

private def gateGlyph (gate : CircuitRef) : QASM.DiagramGateGlyph :=
  let controls := explicitControls gate.modifiers ++ builtinControls gate.name
  let transformed := gate.modifiers.any fun
    | .inverse | .power _ => true
    | .control .. => false
  if gate.name == "swap" || gate.name == "cswap" then
    if transformed then
      if controls.isEmpty then .box else .controlledBox controls gate.name
    else .swap controls
  else if (gate.name == "x" || gate.name == "cx" || gate.name == "CX" || gate.name == "ccx") &&
      !transformed then
    .controlledX controls
  else if controls.isEmpty then .box else .controlledBox controls gate.name

```

## Compact semantic labels

Diagram labels are intentionally summaries, not a second OpenQASM emitter. Literal and
variable expressions remain readable, complex expressions collapse to an ellipsis, and
modifier details preserve only information needed to distinguish the displayed operation.
Classical targets show their root name while nested selectors remain visibly approximate.

```lean
private partial def expressionLabel (names : Std.HashMap VarId String) (value : Expr) : String :=
  match value.node with
  | .intLit value => toString value
  | .floatLit value => toString value
  | .boolLit true => "true"
  | .boolLit false => "false"
  | .var id => names[id]?.getD s!"var{id.value}"
  | .unary _ operand => expressionLabel names operand
  | .binary _ left right => s!"{expressionLabel names left}, {expressionLabel names right}"
  | _ => "…"

private def modifierDetail (names : Std.HashMap VarId String) : GateModifier → String
  | .inverse => "inv"
  | .power exponent => s!"pow({expressionLabel names exponent})"
  | .control false 1 => "ctrl"
  | .control true 1 => "negctrl"
  | .control false count => s!"ctrl({count})"
  | .control true count => s!"negctrl({count})"

private def gateLabel (names : Std.HashMap VarId String) (gate : CircuitRef) : String :=
  let modifiers := gate.modifiers.toList.map (modifierDetail names)
  String.intercalate " @ " (modifiers ++ [gate.name])

private def targetName (names : Std.HashMap VarId String) (target : LValue) : String :=
  let name := names[target.root]?.getD s!"var{target.root.value}"
  if target.indices.isEmpty then name else
    name ++ String.join (target.indices.toList.map fun _ => "[…]")

```

## Operations at the presentation boundary

Only quantum effects and calls become diagram operations. Assignment and declaration
nodes affect names but consume no circuit column. Every visible operation records semantic
kind, accessible label, optional detail, operands, glyph policy, and measurement target;
the SVG renderer does not need to inspect canonical IR.

```lean
private def operationItem (wires : WireState) (names : Std.HashMap VarId String)
    (callables : Std.HashMap CallableId String) (decls : Std.HashMap DeclId String) :
    Op → Option QASM.DiagramItem
  | .apply gate operands =>
      let detail := String.intercalate " @ " (gate.modifiers.toList.map (modifierDetail names))
      some (.operation {
        kind := .gate
        label := gateLabel names gate
        detail
        operands := operands.map (operandDiagram wires)
        glyph := gateGlyph gate })
  | .measure source target =>
      let classicalTarget := match target with
        | .discard => none
        | .lvalue target => some (targetName names target)
      some (.operation {
        kind := .measurement
        label := "M"
        detail := ""
        operands := #[operandDiagram wires source]
        classicalTarget })
  | .reset operand => some (.operation {
      kind := .reset
      label := "reset"
      detail := ""
      operands := #[operandDiagram wires operand] })
  | .barrier operands => some (.operation {
      kind := .barrier
      label := "barrier"
      detail := ""
      operands := operands.map (operandDiagram wires) })
  | .call callee arguments =>
      let operands := arguments.filterMap fun
        | .quantum operand => some (operandDiagram wires operand)
        | _ => none
      some (.operation {
        kind := .call
        label := callables[callee]?.getD s!"call {callee.value}"
        detail := "subroutine"
        operands })
  | .emitExtern call => some (.operation {
      kind := .call
      label := decls[call.callee]?.getD s!"extern {call.callee.value}"
      detail := "external function" })
  | .unsupported capability detail => some (.operation {
      kind := .call
      label := "unsupported"
      detail := s!"{repr capability}: {detail}" })
  | _ => none

```

## Preserving structured control as regions

Process traversal flattens sequential effects while wrapping branches, switch cases, and
loops in labeled regions. Every path appears once and no condition is evaluated. This
static policy makes the diagram deterministic for programs whose runtime path depends on
inputs or measurements.

```lean
private def domainLabel (names : Std.HashMap VarId String) : IterationDomain → String
  | .range start step stop =>
      let middle := match step.node with
        | .intLit 1 => ""
        | _ => ":" ++ expressionLabel names step
      s!"[{expressionLabel names start}{middle}:{expressionLabel names stop}]"
  | .set values =>
      "{" ++ String.intercalate ", " (values.toList.map (expressionLabel names)) ++ "}"
  | .array value => expressionLabel names value

private partial def procItems (wires : WireState) (names : Std.HashMap VarId String)
    (callables : Std.HashMap CallableId String) (decls : Std.HashMap DeclId String) :
    Proc → Array QASM.DiagramItem
  | .skip | .breakLoop | .continueLoop | .returnValue _ | .endProgram => #[]
  | .operation op => (operationItem wires names callables decls op).map (#[·]) |>.getD #[]
  | .sequence steps => steps.flatMap (procItems wires names callables decls)
  | .scope _ body => procItems wires names callables decls body
  | .branch condition thenBranch elseBranch =>
      let items := #[.region s!"if {expressionLabel names condition}"
        (procItems wires names callables decls thenBranch)]
      match elseBranch with
      | none => items
      | some body => items.push (.region "else" (procItems wires names callables decls body))
  | .switch scrutinee cases default =>
      let items := cases.map fun entry => match entry with
        | .mk labels body =>
            let label := String.intercalate ", " (labels.toList.map (expressionLabel names))
            .region s!"case {label}" (procItems wires names callables decls body)
      let items := #[.region s!"switch {expressionLabel names scrutinee}" items]
      match default with
      | none => items
      | some body => items.push
          (.region "default" (procItems wires names callables decls body))
  | .forLoop iterator domain body =>
      #[.region s!"for {iterator.name} in {domainLabel names domain}"
        (procItems wires names callables decls body)]
  | .whileLoop condition body =>
      #[.region s!"while {expressionLabel names condition}"
        (procItems wires names callables decls body)]

```

## Public extraction

`ofProgram` joins the independent name, wire, and item passes. It reads immutable IR only,
does not invoke `QASM.Codegen.run`, and returns the renderer's small `CircuitDiagram`
model so HTML integration remains a separate instance module.

```lean
/-- Extracts immutable renderer input directly from a canonical IR program. -/
def ofProgram (program : Program) : QASM.CircuitDiagram :=
  let names := program.inputs.foldl
    (fun names declaration => names.insert declaration.var.id declaration.var.name) {}
  let names := program.outputs.foldl
    (fun names declaration => names.insert declaration.var.id declaration.var.name) names
  let names := collectNames names program.body
  let callables := program.subroutines.foldl
    (fun names declaration => names.insert declaration.id declaration.name) {}
  let decls := program.externs.foldl
    (fun names declaration => names.insert declaration.id declaration.name) {}
  let wires := program.inputs.foldl (fun state declaration => match declaration.var.type with
    | .scalar (.qubit count) => registerVar state declaration.var.id declaration.var.name count
    | _ => state) {}
  let wires := collectProc wires program.body
  { wires := wires.labels, items := procItems wires names callables decls program.body }

end QASM.Diagram
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
