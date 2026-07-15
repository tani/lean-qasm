    import LiterateLean
    import QASM.IR.Decl
    open scoped LiterateLean

# Canonical IR program

`Program` is the complete persistent result of lowering. The runtime interpreter,
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

structure Program where
  version     : Version := {}
  target      : TargetConfig := {}
  dialect     : Dialect := .v3_0
  origins     : Array ProgramOrigin := #[]
  annotations : Array Annotation := #[]
  pragmas     : Array Pragma := #[]
  includes    : Array IncludeInfo := #[]
  inputs      : Array IODecl := #[]
  outputs     : Array IODecl := #[]
  constants   : Array ConstantDecl := #[]
  types       : Array TypeDecl := #[]
  externs     : Array ExternDecl := #[]
  gates       : Array GateDecl := #[]
  subroutines : Array SubroutineDecl := #[]
  body        : Proc := .skip
  deriving Repr, BEq, Inhabited


end QASM.IR
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
