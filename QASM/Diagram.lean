    import LiterateLean
    import QASM.Runtime
    import ProofWidgets.Component.HtmlDisplay

    open scoped LiterateLean ProofWidgets.Jsx

# Static circuit diagrams

The generated program metadata remains backend-independent. This module is the sole
presentation boundary: it turns that immutable data into an SVG for `#html`.

```lean
namespace QASM

open Lean ProofWidgets

meta section

private def svgNode (tag : String) (attributes : Array (String × Json))
    (children : Array Html := #[]) : Html :=
  .element tag attributes children

private def textAttribute (name value : String) : String × Json := (name, .str value)

private def numberAttribute (name : String) (value : Nat) : String × Json := (name, toJson value)

private def deduplicateWires (wires : Array Nat) : Array Nat :=
  wires.foldl (fun result wire =>
    if result.contains wire then result else result.push wire) #[]

private def truncateLabel (limit : Nat) (value : String) : String :=
  if value.length <= limit then value else (value.take (limit - 1)).toString ++ "…"

private structure DiagramLeaf where
  operation : DiagramOperation
  depth : Nat
  deriving Inhabited

private structure DiagramRegion where
  label : String
  firstColumn : Nat
  lastColumn : Nat
  depth : Nat
  deriving Inhabited

private structure DiagramLayout where
  leaves : Array DiagramLeaf := #[]
  regions : Array DiagramRegion := #[]
  nextColumn : Nat := 0
  deriving Inhabited

private partial def collectDiagramItems
    (items : Array DiagramItem) (depth column : Nat) : DiagramLayout :=
  Id.run do
    let mut leaves := #[]
    let mut regions := #[]
    let mut column := column
    for item in items do
      match item with
      | .operation operation =>
          leaves := leaves.push { operation, depth }
          column := column + 1
      | .region label children =>
          let nested := collectDiagramItems children (depth + 1) column
          leaves := leaves ++ nested.leaves
          if nested.nextColumn > column then
            regions := regions.push
              { label, firstColumn := column, lastColumn := nested.nextColumn - 1, depth } ++
              nested.regions
          column := nested.nextColumn
    return { leaves, regions, nextColumn := column }

private def operationWires (operation : DiagramOperation) : Array Nat :=
  deduplicateWires (operation.operands.foldl (fun wires operand =>
    wires ++ operand.wires) #[])

private def operationHasApproximation (operation : DiagramOperation) : Bool :=
  operation.operands.any (·.approximate)

private def laneRange (lanes : Array Nat) : Nat × Nat :=
  let first := lanes[0]?.getD 0
  lanes.foldl (fun (first, last) lane => (min first lane, max last lane)) (first, first)

private def operationCandidateLanes (operation : DiagramOperation)
    (sourceWireCount globalOffset : Nat) : Array Nat :=
  let wires := (operationWires operation).filter (· < sourceWireCount)
  if wires.isEmpty then
    if globalOffset == 1 then #[0] else #[]
  else wires.map (globalOffset + ·)

private def exactOperandLanes? (operation : DiagramOperation)
    (sourceWireCount globalOffset : Nat) : Option (Array Nat) :=
  if operation.operands.all (fun operand =>
      !operand.approximate && operand.wires.size == 1 && operand.wires[0]! < sourceWireCount) then
    some (operation.operands.map fun operand => globalOffset + operand.wires[0]!)
  else none

private def lineNode (x1 y1 x2 y2 : Nat) (strokeWidth : String := "1")
    (dash : Option String := none) : Html :=
  let dash := dash.map (fun value => #[textAttribute "strokeDasharray" value]) |>.getD #[]
  svgNode "line" (#[
    numberAttribute "x1" x1, numberAttribute "y1" y1,
    numberAttribute "x2" x2, numberAttribute "y2" y2,
    textAttribute "stroke" "currentColor", textAttribute "strokeWidth" strokeWidth
  ] ++ dash)

private def textNode (x y : Nat) (value : String) (size : String := "12")
    (anchor : String := "middle") : Html :=
  svgNode "text" #[
    numberAttribute "x" x, numberAttribute "y" y,
    textAttribute "fill" "currentColor", textAttribute "fontSize" size,
    textAttribute "textAnchor" anchor
  ] #[.text value]

private def controlNode (x y : Nat) (polarity : ControlPolarity) : Html :=
  match polarity with
  | .positive => svgNode "circle" #[
      numberAttribute "cx" x, numberAttribute "cy" y, numberAttribute "r" 5,
      textAttribute "fill" "currentColor", textAttribute "stroke" "currentColor"
    ]
  | .negative => svgNode "circle" #[
      numberAttribute "cx" x, numberAttribute "cy" y, numberAttribute "r" 6,
      textAttribute "fill" "var(--vscode-editor-background)",
      textAttribute "stroke" "currentColor", textAttribute "strokeWidth" "1.5"
    ]

private def targetXNode (x y : Nat) : Array Html := #[
  svgNode "circle" #[
    numberAttribute "cx" x, numberAttribute "cy" y, numberAttribute "r" 10,
    textAttribute "fill" "var(--vscode-editor-background)",
    textAttribute "stroke" "currentColor", textAttribute "strokeWidth" "1.5"
  ],
  lineNode (x - 6) y (x + 6) y "1.5",
  lineNode x (y - 6) x (y + 6) "1.5"
]

private def targetBoxNodes (x : Nat) (lanes : Array Nat) (laneY : Nat → Nat)
    (label : String) : Array Html :=
  let (firstLane, lastLane) := laneRange lanes
  let firstY := laneY firstLane
  let lastY := laneY lastLane
  let midpoint := (firstY + lastY) / 2
  #[
    svgNode "rect" #[
      numberAttribute "x" (x - 24), numberAttribute "y" (firstY - 15),
      numberAttribute "width" 48, numberAttribute "height" (lastY - firstY + 30),
      numberAttribute "rx" 4, textAttribute "fill" "var(--vscode-editor-background)",
      textAttribute "stroke" "currentColor", textAttribute "strokeWidth" "1.5"
    ],
    textNode x (midpoint + 4) (truncateLabel 10 label)
  ]

private def swapNodes (x : Nat) (lanes : Array Nat) (laneY : Nat → Nat) : Array Html :=
  lanes.foldl (fun nodes lane =>
    let y := laneY lane
    nodes ++ #[lineNode (x - 6) (y - 6) (x + 6) (y + 6) "1.5",
      lineNode (x - 6) (y + 6) (x + 6) (y - 6) "1.5"]) #[]

private def operationGroup (operation : DiagramOperation) (children : Array Html) : Html :=
  svgNode "g" #[textAttribute "aria-label" operation.detail] (
    #[svgNode "title" #[] #[.text operation.detail]] ++ children)

private def fallbackOperationNodes (operation : DiagramOperation) (centerX : Nat)
    (lanes : Array Nat) (laneY : Nat → Nat) : Array Html :=
  let (firstLane, lastLane) := laneRange lanes
  let firstY := laneY firstLane
  let lastY := laneY lastLane
  let midpoint := (firstY + lastY) / 2
  let dashed := if operationHasApproximation operation then
    #[textAttribute "strokeDasharray" "4 3"] else #[]
  let measurementTarget := match operation.classicalTarget with
    | none => #[]
    | some target => #[textNode (centerX + 30) (midpoint + 4)
      ("→ " ++ truncateLabel 10 target) "11" "start"]
  #[
    svgNode "rect" (#[
      numberAttribute "x" (centerX - 24), numberAttribute "y" (firstY - 15),
      numberAttribute "width" 48, numberAttribute "height" (lastY - firstY + 30),
      numberAttribute "rx" 4, textAttribute "fill" "var(--vscode-editor-background)",
      textAttribute "stroke" "currentColor", textAttribute "strokeWidth" "1.5"
    ] ++ dashed),
    textNode centerX (midpoint + 4) (truncateLabel 10 operation.label)
  ] ++ measurementTarget

private def conventionalOperationNodes (operation : DiagramOperation)
    (centerX sourceWireCount globalOffset : Nat) (laneY : Nat → Nat) :
    Option (Array Html) :=
  match operation.glyph, exactOperandLanes? operation sourceWireCount globalOffset with
  | .controlledX controls, some operands =>
      if operands.size != controls.size + 1 then none else
        let (firstLane, lastLane) := laneRange operands
        let controlLanes := operands.extract 0 controls.size
        let targetLane := operands[controls.size]!
        some <| #[lineNode centerX (laneY firstLane) centerX (laneY lastLane) "1.5"] ++
          (controls.zip controlLanes).map (fun pair => controlNode centerX (laneY pair.2) pair.1) ++
          targetXNode centerX (laneY targetLane)
  | .controlledBox controls _, some operands =>
      if operands.size < controls.size + 1 then none else
        let (firstLane, lastLane) := laneRange operands
        let controlLanes := operands.extract 0 controls.size
        let targetLanes := operands.extract controls.size operands.size
        match operation.glyph with
        | .controlledBox _ target =>
            some <| #[lineNode centerX (laneY firstLane) centerX (laneY lastLane) "1.5"] ++
              (controls.zip controlLanes).map (fun pair => controlNode centerX (laneY pair.2) pair.1) ++
              targetBoxNodes centerX targetLanes laneY target
        | _ => none
  | .swap controls, some operands =>
      if operands.size != controls.size + 2 then none else
        let (firstLane, lastLane) := laneRange operands
        let controlLanes := operands.extract 0 controls.size
        let targetLanes := operands.extract controls.size operands.size
        some <| #[lineNode centerX (laneY firstLane) centerX (laneY lastLane) "1.5"] ++
          (controls.zip controlLanes).map (fun pair => controlNode centerX (laneY pair.2) pair.1) ++
          swapNodes centerX targetLanes laneY
  | _, _ => none

private def operationNode (operation : DiagramOperation) (column : Nat)
    (sourceWireCount globalOffset topMargin : Nat) : Html :=
  let centerX := 120 + 36 + column * 72
  let laneY := fun lane => topMargin + lane * 48
  let candidates := operationCandidateLanes operation sourceWireCount globalOffset
  let children := match operation.kind with
  | .barrier =>
      let (firstLane, lastLane) := laneRange candidates
      #[lineNode centerX (laneY firstLane - 18) centerX (laneY lastLane + 18) "2" (some "4 4")]
  | _ =>
      match conventionalOperationNodes operation centerX sourceWireCount globalOffset laneY with
      | some children => children
      | none => fallbackOperationNodes operation centerX candidates laneY
  operationGroup operation children

private def regionOutlineNode (region : DiagramRegion) (svgHeight : Nat) : Html :=
  let firstCenter := 120 + 36 + region.firstColumn * 72
  let lastCenter := 120 + 36 + region.lastColumn * 72
  let x := firstCenter - 36 + 4
  let y := 8 + region.depth * 20
  let bottom := svgHeight - 8 - region.depth * 4
  svgNode "g" #[textAttribute "aria-label" region.label] #[
    svgNode "title" #[] #[.text region.label],
    svgNode "rect" #[
      numberAttribute "x" x, numberAttribute "y" y,
      numberAttribute "width" (lastCenter + 36 - 4 - x), numberAttribute "height" (bottom - y),
      numberAttribute "rx" 4, textAttribute "fill" "none",
      textAttribute "stroke" "currentColor", textAttribute "strokeWidth" "1",
      textAttribute "strokeDasharray" "6 4"
    ]
  ]

private def regionLabelNode (region : DiagramRegion) : Html :=
  let firstCenter := 120 + 36 + region.firstColumn * 72
  textNode (firstCenter - 36 + 12) (8 + region.depth * 20 + 14)
    (truncateLabel 32 region.label) "11" "start"

meta def CircuitDiagram.toHtml (diagram : CircuitDiagram) : ProofWidgets.Html :=
  if diagram.wires.isEmpty && diagram.items.isEmpty then
    .text "No quantum operations."
  else
    let layout := collectDiagramItems diagram.items 0 0
    let needsGlobal := layout.leaves.any fun leaf =>
      (operationWires leaf.operation).filter (· < diagram.wires.size) |>.isEmpty
    let globalOffset := if needsGlobal || (diagram.wires.isEmpty && !diagram.items.isEmpty) then 1 else 0
    let laneCount := diagram.wires.size + globalOffset
    let maxDepth := layout.regions.foldl (fun depth region => max depth region.depth) 0
    let topMargin := 40 + maxDepth * 20
    let svgWidth := max 240 (120 + layout.leaves.size * 72 + 96)
    let svgHeight := topMargin + (laneCount - 1) * 48 + 40
    let laneLabels :=
      (if globalOffset == 1 then #["global"] else #[]) ++ diagram.wires
    let wireNodes := laneLabels.mapIdx fun index label =>
      let y := topMargin + index * 48
      #[lineNode 120 y (svgWidth - 96) y,
        textNode (120 - 12) (y + 4) label "12" "end"]
    let operationNodes := layout.leaves.mapIdx fun column leaf =>
      operationNode leaf.operation column diagram.wires.size globalOffset topMargin
    let svg := svgNode "svg" #[
      textAttribute "xmlns" "http://www.w3.org/2000/svg",
      numberAttribute "width" svgWidth, numberAttribute "height" svgHeight,
      textAttribute "viewBox" s!"0 0 {svgWidth} {svgHeight}",
      textAttribute "role" "img", textAttribute "aria-label" "Quantum circuit"
    ] ((layout.regions.map (regionOutlineNode · svgHeight)) ++ wireNodes.flatten ++
      operationNodes ++ layout.regions.map regionLabelNode)
    svgNode "div" #[("style", json% { overflowX: "auto", padding: "4px 0" })] #[svg]

meta instance : ProofWidgets.HtmlEval CheckedProgramInfo where
  eval info := pure info.diagram.toHtml

end
end QASM
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
