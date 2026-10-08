    import LiterateLean
    import QASM.IR.Decl
    open scoped LiterateLean

# Canonical IR program

`Program` is the complete persistent result of lowering. Its size and integer type
parameters default to `Nat` and `Int`. Compilation templates reuse this grammar with
symbolic values, but generated definitions return the ordinary concrete `Program`. The runtime interpreter,
canonical emitter, diagram extractor, equivalence relations, and generated boundary API
all consume this value directly; no downstream pass needs the frontend AST or elaborator
state.

`Program` is the architectural join point and the only persistent value shared by all
downstream views:

```mermaid
flowchart LR
    Frontend --> Lowering
    Lowering --> Program["QASM.IR.Program"]
    Program --> Interpreter
    Program --> Emitter
    Program --> Diagram
    Program --> Equivalence
```

No arrow returns to the source AST, which keeps execution and rendering independent of
elaboration state.

```lean
namespace QASM.IR

structure Program (size : Type := Nat) (integer : Type := Int) where
  version     : Version := {}
  target      : TargetConfig := {}
  dialect     : Dialect := .v3_0
  origins     : Array ProgramOrigin := #[]
  annotations : Array Annotation := #[]
  pragmas     : Array Pragma := #[]
  includes    : Array IncludeInfo := #[]
  inputs      : Array (IODecl size) := #[]
  outputs     : Array (IODecl size) := #[]
  constants   : Array (ConstantDecl size integer) := #[]
  types       : Array (TypeDecl size) := #[]
  externs     : Array (ExternDecl size) := #[]
  gates       : Array (GateDecl size integer) := #[]
  subroutines : Array (SubroutineDecl size integer) := #[]
  body        : (Proc size integer) := .skip
  deriving Repr, BEq, Inhabited


end QASM.IR
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
