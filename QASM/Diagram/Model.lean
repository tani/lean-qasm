    import LiterateLean
    import QASM.Runtime

    open scoped LiterateLean

# Backend-independent circuit diagram model

The diagram layer owns the immutable presentation model shared by IR projection and HTML
rendering. Keeping these records outside the execution runtime prevents visualization-only
types from becoming part of the interpreter's value and backend boundary.

Operations retain semantic categories, wire selections, and optional classical targets.
Structured regions preserve source control flow without choosing a branch or executing a
loop. Gate glyphs refer to runtime control polarity because controlled-unitary semantics
and their diagram notation must agree on positive and negative controls.

```lean
namespace QASM

inductive DiagramOperationKind where
  | gate
  | measurement
  | reset
  | barrier
  | call
  deriving Repr, Inhabited, BEq

inductive DiagramGateGlyph where
  | box
  | controlledX (controls : Array ControlPolarity)
  | controlledBox (controls : Array ControlPolarity) (targetLabel : String)
  | swap (controls : Array ControlPolarity)
  deriving Repr, Inhabited, BEq

structure DiagramOperand where
  wires : Array Nat
  approximate : Bool := false
  deriving Repr, Inhabited, BEq

structure DiagramOperation where
  kind : DiagramOperationKind
  label : String
  detail : String
  operands : Array DiagramOperand := #[]
  glyph : DiagramGateGlyph := .box
  classicalTarget : Option String := none
  deriving Repr, Inhabited, BEq

inductive DiagramItem where
  | operation (value : DiagramOperation)
  | region (label : String) (items : Array DiagramItem)
  deriving Repr, Inhabited, BEq

structure CircuitDiagram where
  wires : Array String := #[]
  items : Array DiagramItem := #[]
  deriving Repr, Inhabited, BEq

end QASM
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
