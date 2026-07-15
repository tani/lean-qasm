    import LiterateLean
    import QASM.Diagram.Model
    import ProofWidgets.Component.HtmlDisplay

    open scoped LiterateLean ProofWidgets.Jsx

# Static circuit diagrams

Canonical program IR remains backend-independent. This module is the presentation
boundary that turns a derived `CircuitDiagram` into SVG for `#html`.

Rendering is a pure presentation pipeline after IR projection:

```mermaid
flowchart LR
    Model["CircuitDiagram"] --> Layout["lane and column layout"]
    Layout --> SVG["typed SVG tree"]
    SVG --> Html["ProofWidgets.Html"]
    Html --> Infoview
```

For wire lane $i$ and operation column $j$, layout uses affine coordinates of the form

$$
y_i = y_0 + i\,\Delta_y,
\qquad
x_j = x_0 + j\,\Delta_x,
$$

so nested rendering changes grouping without changing wire identity.

```lean
namespace QASM

open Lean ProofWidgets

meta section

```

## Building SVG without string concatenation

ProofWidgets represents HTML and SVG as a typed tree. The helpers below construct that
tree directly, so escaping and child structure remain the responsibility of the widget
renderer rather than ad-hoc string interpolation. Attributes are encoded as JSON because
that is the representation expected by `Html.element`.

The small wire and label utilities establish two presentation policies used throughout
the renderer: duplicate wire references collapse to one lane, and long source labels are
truncated before they can dominate a circuit column.

```lean
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

```

## Flattening nested diagram regions

The source diagram may contain nested regions for loops, branches, and callable bodies,
but an SVG circuit needs concrete horizontal columns. `DiagramLeaf` pairs each executable
operation with its nesting depth. `DiagramRegion` remembers the inclusive column span
occupied by one source region. `DiagramLayout` accumulates both views while assigning the
next free column.

These are private rendering records rather than additions to the public diagram model:
the compiler continues to own semantic metadata, while this module owns only its layout.

```lean
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

```

The recursive collection pass is a preorder traversal. Operations consume exactly one
column. Regions consume however many columns their children require and receive no
separate operation column of their own. Empty regions therefore produce no outline,
which avoids zero-width SVG rectangles.

Nested regions are appended after their parent span. Rendering outlines before operations
later ensures that region decoration stays behind gate glyphs.

```lean
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

```

## Mapping source operands to display lanes

OpenQASM operands can mention the same qubit more than once, and some compiler metadata
is deliberately approximate when a target depends on runtime control flow. The following
helpers normalize exact wire lists, detect approximation, and map source wire indices into
SVG lanes.

An extra global lane may be inserted at the top for operations such as global phase that
have no concrete qubit operand. Exact conventional glyphs are permitted only when every
operand resolves to one in-range source wire; all other cases use the explicit fallback
box below.

```lean
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

```

## Primitive SVG glyphs

Circuit notation is assembled from a deliberately small vocabulary: lines, text,
positive and negative control circles, controlled-X targets, labeled boxes, and swap
crosses. Every primitive uses `currentColor` and the editor background variable, allowing
the infoview theme to control contrast without a separate light/dark palette.

Coordinates are natural numbers because the layout uses a fixed grid. Each operation
column is 72 units wide and each wire lane is 48 units high; later functions translate
semantic columns and lanes into those coordinates.

```lean
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

```

## Accessible operation groups and fallback boxes

Each rendered operation is wrapped in an SVG group with both an `aria-label` and a
`title`. The visible label can stay compact while hover text and assistive technology
retain the compiler's complete operation detail.

The fallback glyph is the correctness path, not an error case. It handles ordinary named
gates, measurements, approximate operands, and any conventional glyph whose exact lane
shape cannot be established. Dashed borders signal approximation, and measurement
targets are printed beside the box when present.

```lean
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

```

## Conventional controlled and swap notation

The renderer chooses conventional glyphs only after `exactOperandLanes?` proves that the
operand mapping is exact. It then checks the arity encoded by each glyph:

* controlled X requires one target after all controls;
* a controlled box requires at least one target;
* swap requires exactly two targets after all controls.

Any mismatch returns `none`, allowing the caller to fall back to a labeled box instead
of drawing a plausible but semantically incorrect circuit symbol.

```lean
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

```

## Placing operations and source regions

`operationNode` converts one semantic column into an SVG x-coordinate and one lane into
a y-coordinate. Barriers use a dashed vertical line across candidate lanes. Every other
operation first attempts conventional notation and then takes the fallback path.

Region outlines use their previously collected column spans. Increasing nesting depth
moves the top edge downward slightly and the bottom edge upward, so nested outlines remain
visually distinguishable without changing operation coordinates.

```lean
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

```

## Assembling the complete widget

The public renderer handles an empty diagram as text rather than manufacturing an empty
SVG. For a nonempty diagram it performs four steps:

1. flatten source items into leaves and regions;
2. decide whether a synthetic global lane is required;
3. derive canvas dimensions from lane count, column count, and nesting depth;
4. compose region outlines, wires, operations, and labels in paint order.

The outer scrolling `div` keeps large circuits usable inside a narrow infoview. The SVG
itself receives an image role and accessible name, while individual operation groups
provide finer detail.

```lean
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

end
end QASM
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
