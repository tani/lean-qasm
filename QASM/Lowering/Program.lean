    import LiterateLean
    import QASM.Lowering.Decl
    open scoped LiterateLean

# Complete program lowering

The public lowering entry point consumes the checked frontend program and its type analysis, producing the single canonical IR compilation unit.

```lean
namespace QASM.Lowering

open QASM

```

## Accumulating compilation-unit components

`Components` separates declarations from executable body steps while preserving source
order within each category. Annotations and pragmas are collected recursively as immutable
metadata: they affect reproducibility and emission, not process execution. Wrapper
annotations are stripped only for statement classification; the metadata pass retains
them independently.

```lean
private structure Components where
  includes    : Array QASM.IR.IncludeInfo := #[]
  inputs      : Array QASM.IR.IODecl := #[]
  outputs     : Array QASM.IR.IODecl := #[]
  constants   : Array QASM.IR.ConstantDecl := #[]
  externs     : Array QASM.IR.ExternDecl := #[]
  gates       : Array QASM.IR.GateDecl := #[]
  subroutines : Array QASM.IR.SubroutineDecl := #[]
  body        : Array QASM.IR.Proc := #[]
  deriving Inhabited

private partial def stripAnnotations : QASM.Frontend.Statement → QASM.Frontend.Statement
  | .annotated _ statement => stripAnnotations statement
  | statement => statement

private partial def collectMetadataStatement (origin : QASM.IR.SourceSpan)
    (metadata : Array QASM.IR.Annotation × Array QASM.IR.Pragma)
    (statement : QASM.Frontend.Statement) :
    Array QASM.IR.Annotation × Array QASM.IR.Pragma :=
  let (annotations, pragmas) := metadata
  match statement with
  | .pragma content => (annotations, pragmas.push { content, origin })
  | .annotated values statement =>
      let annotations := values.foldl (fun result annotation => result.push
        { keyword := annotation.keyword, content := annotation.content, origin }) annotations
      collectMetadataStatement origin (annotations, pragmas) statement
  | .scope body | .whileStatement _ body | .forStatement _ _ _ body |
      .gateDefinition _ _ _ body | .boxStatement _ body | .defStatement _ _ _ body =>
      body.foldl (collectMetadataStatement origin) (annotations, pragmas)
  | .ifStatement _ thenBody elseBody =>
      let metadata := thenBody.foldl (collectMetadataStatement origin) (annotations, pragmas)
      elseBody.map (·.foldl (collectMetadataStatement origin) metadata) |>.getD metadata
  | .switchStatement _ cases defaultBody =>
      let metadata := cases.foldl (fun metadata entry =>
        entry.2.foldl (collectMetadataStatement origin) metadata) (annotations, pragmas)
      defaultBody.map (·.foldl (collectMetadataStatement origin) metadata) |>.getD metadata
  | _ => (annotations, pragmas)

private def programBody (steps : Array QASM.IR.Proc) : QASM.IR.Proc :=
  let steps := steps.filter (· != .skip)
  if steps.isEmpty then .skip else if steps.size == 1 then steps[0]! else .sequence steps

```

## Classifying top-level statements

Each source statement has one canonical destination. Includes and declarations enter
their dedicated arrays; executable statements lower through `statement` and append to the
program body. This single dispatch prevents a declaration from being represented both as
metadata and as a runtime no-op.

```lean
private def lowerComponents (source : QASM.Frontend.Program) : LowerM Components := do
  let mut components : Components := {}
  for original in source.statements do
    let current := stripAnnotations original
    match current with
    | .includeFile filename =>
        let context ← get
        let digest := context.options.origins.find? (·.1.endsWith filename) |>.map (·.2) |>.getD 0
        let includeInfo : QASM.IR.IncludeInfo :=
          { filename := filename, digest := digest, origin := sourceOrigin context.options }
        components := { components with includes := components.includes.push includeInfo }
    | .constDeclaration type name value =>
        let declaration ← constantDeclaration type name value
        components := { components with constants := components.constants.push declaration }
    | .ioDeclaration input type name =>
        let declaration ← ioDeclaration name type input
        if input then components := { components with inputs := components.inputs.push declaration }
        else components := { components with outputs := components.outputs.push declaration }
    | .externStatement name arguments returnType =>
        let declaration ← externDeclaration name arguments returnType
        components := { components with externs := components.externs.push declaration }
    | .gateDefinition name parameters qubits body =>
        let declaration ← gateDeclaration name parameters qubits body
        components := { components with gates := components.gates.push declaration }
    | .defStatement name arguments returnType body =>
        let declaration ← subroutineDeclaration name arguments returnType body
        components := { components with subroutines := components.subroutines.push declaration }
    | .pragma _ => pure ()
    | _ =>
        let lowered ← statement original
        components := { components with body := components.body.push lowered }
  pure components

```

## Assembling canonical program IR

Assembly combines source version, target settings, dialect, origin digests, directives,
declarations, and the normalized process body. Empty and singleton process sequences are
collapsed without changing order, yielding the one persistent value consumed by emitters,
diagram extraction, equivalence checks, and execution.

```lean
private def lowerProgram (source : QASM.Frontend.Program) : LowerM QASM.IR.Program := do
  let context ← get
  let components ← lowerComponents source
  let (annotations, pragmas) := source.statements.foldl
    (collectMetadataStatement (sourceOrigin context.options)) (#[], #[])
  let version : QASM.IR.Version := match source.version with
    | some version => { major := version.major, minor := version.minor }
    | none => {}
  let origins : Array QASM.IR.ProgramOrigin :=
    context.options.origins.map fun origin => { name := origin.1, digest := origin.2 }
  pure {
    version,
    target := targetConfig context.options.target,
    dialect := dialect context.options.dialect,
    origins,
    annotations,
    pragmas,
    includes := components.includes,
    inputs := components.inputs,
    outputs := components.outputs,
    constants := components.constants,
    externs := components.externs,
    gates := components.gates,
    subroutines := components.subroutines,
    body := programBody components.body
  }

```

## Public lowering transaction

The public entry point initializes every stable declaration ID before running the stateful
body pass. It exposes only `Except Diagnostic Program`; the final lowering context is an
implementation detail and cannot leak into downstream consumers.

```lean
/-- Lowers a type-checked frontend compilation unit into canonical categorical–monadic IR. -/
def program (source : QASM.Frontend.Program) (analysis : QASM.Frontend.TypeAnalysis)
    (options : LoweringOptions := {}) : Except QASM.Diagnostic QASM.IR.Program := do
  let context ← Context.initialize options analysis source
  let (program, _) ← lowerProgram source |>.run context
  pure program

end QASM.Lowering
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
