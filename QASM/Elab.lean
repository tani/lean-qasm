    import LiterateLean

    import QASM.Runtime
    import QASM.Diagram
    import QASM.Source
    import QASM.Frontend
    import QASM.Semantics
    import QASM.Typing
    import QASM.Lowering.Program
    import QASM.Codegen.IRValue
    import QASM.Codegen.Runtime
    import Lean.Elab.Eval

    open scoped LiterateLean

# OpenQASM elaboration pipeline

`qasm!` is a compile-time frontend embedded in Lean's command elaborator. This module
coordinates the complete path from captured OpenQASM text through include expansion,
parsing, semantic checks, type analysis, and lowering to a canonical `QASM.IR.Program`.
It then declares that IR value together with native input/output structures and a typed
`execute` wrapper.

The wrapper encodes boundary values, calls `QASM.Codegen.run`, and decodes the resulting
classical environment. Expressions, operations, callables, and structured control flow
are interpreted from IR at runtime; allocation, unitaries, measurement, reset, and
barriers cross `QuantumBackend`.

Input/output structures and the wrapper are emitted as Lean source strings and reparsed
as commands. The canonical IR value is quoted directly as a Lean expression. This keeps
the generated API native and typed without presenting the interpreted program body as
per-program Lean control flow.

```lean
namespace QASM
namespace Compiler

open Lean
open Lean Elab Command
open Frontend

private def leanString (value : String) : String := reprStr value

private def leanIdentifier (name : String) : String :=
  "«" ++ name ++ "»"

private def arrayCode (values : Array String) : String :=
  "#[" ++ String.intercalate ", " values.toList ++ "]"

private def indent (source : String) (amount : Nat := 2) : String :=
  let indentation := String.ofList (List.replicate amount ' ')
  String.intercalate "\n" (source.splitOn "\n" |>.map fun line => indentation ++ line)


```

## Dialects and boundary structures

Before lowering, the compiler detects extended-only statements. After lowering, it
constructs native input and output structures from the resolved IR declarations; target,
origin, annotation, and pragma metadata remain in the canonical program value.

```lean

private partial def hasExtendedStatement : Statement → Bool
  | .switchStatement .. | .nopStatement _ => true
  | .scope body | .whileStatement _ body | .forStatement _ _ _ body |
      .gateDefinition _ _ _ body | .boxStatement _ body => body.any hasExtendedStatement
  | .ifStatement _ thenBody elseBody =>
      thenBody.any hasExtendedStatement || elseBody.any (·.any hasExtendedStatement)
  | .defStatement _ _ _ body => body.any hasExtendedStatement
  | .annotated _ statement => hasExtendedStatement statement
  | _ => false

private def irScalarLeanType : QASM.IR.ScalarTy → Except String String
  | .bit none => pure "QASM.Bit"
  | .bit (some width) => pure s!"BitVec {width}"
  | .sint width => pure s!"QASM.SInt {width}"
  | .uint width => pure s!"QASM.UInt {width}"
  | .float 32 => pure "Float32"
  | .float 64 => pure "Float"
  | .float width => throw s!"cannot emit float[{width}]"
  | .angle width => pure s!"QASM.Angle {width}"
  | .boolean => pure "Bool"
  | .complex width => pure s!"QASM.ComplexN {width}"
  | .duration => pure "QASM.Duration"
  | .stretch => throw "stretch requires a timing backend"
  | .qubit _ => throw "qubits cannot appear in classical I/O structures"
  | .void => throw "void cannot appear in a value structure"

private def irLeanType : QASM.IR.Type → Except String String
  | .scalar value => irScalarLeanType value
  | .array element shape => do
      let element ← irScalarLeanType element
      pure s!"QASM.FixedArray ({element}) [{String.intercalate ", " (shape.toList.map toString)}]"
  | .arrayRef .. => throw "array-reference types cannot appear in program I/O"

private def structureCommand (name suffix : String) (fields : Array QASM.IR.IODecl) :
    Except String String := do
  let header := s!"structure {name}.{suffix} where"
  if fields.isEmpty then pure header
  else
    let mut declarations := #[]
    for field in fields do
      declarations := declarations.push
        s!"  {leanIdentifier field.var.name} : {← irLeanType field.var.type}"
    pure (header ++ "\n" ++ String.intercalate "\n" declarations.toList)


private def elaborateProgram (name : String) (program : QASM.IR.Program) :
    CommandElabM Unit := do
  let declarationName := (← getCurrNamespace) ++ name.toName ++ `program
  liftTermElabM do
    addAndCompile <| .defnDecl {
      name := declarationName
      levelParams := []
      type := mkConst ``QASM.IR.Program
      value := Lean.toExpr program
      safety := .safe
      hints := .abbrev
    }

private def backendBinders : String :=
  "{qasmM : Type → Type} {qasmQubit qasmError : Type} [Monad qasmM] " ++
  "[QASM.QuantumBackend qasmM qasmQubit qasmError]"

private def executeCommand (name : String) (program : QASM.IR.Program) : String :=
  let inputs := program.inputs.map fun declaration =>
    s!"((⟨{declaration.var.id.value}⟩ : QASM.IR.VarId), " ++
      s!"QASM.ValueCodec.toValue inputs.{leanIdentifier declaration.var.name})"
  let outputFields := program.outputs.map fun declaration =>
    let key := s!"((⟨{declaration.var.id.value}⟩ : QASM.IR.VarId))"
    let value := s!"qasm_values[{key}]?.getD QASM.Value.uninitialized"
    s!"{leanIdentifier declaration.var.name} := (← match QASM.ValueCodec.fromValue ({value}) with\n" ++
      s!"| .ok qasm_decoded_value => pure qasm_decoded_value\n" ++
      s!"| .error message => return .error (.invalidCast (" ++
        leanString ("output '" ++ declaration.var.name ++ "': ") ++ " ++ message)))"
  let success := if outputFields.isEmpty then "return .ok {}" else
    "return .ok {\n" ++ indent (String.intercalate ",\n" outputFields.toList) ++ "\n}"
  let body :=
    s!"let qasm_result ← QASM.Codegen.run {name}.program {arrayCode inputs}\n" ++
    "match qasm_result with\n" ++
    "| .error error => return .error error\n" ++
    "| .ok qasm_values =>\n" ++ indent success
  s!"def {name}.execute " ++ backendBinders ++ s!" (inputs : {name}.Inputs) : " ++
    s!"qasmM (Except (QASM.RunError qasmError) {name}.Outputs) := do\n" ++ indent body

```

## Includes and generated boundary commands

Generated input/output structures and the `execute` wrapper are reparsed as Lean commands
and elaborated in the current environment. With LiterateLean open, command parsing also
offers a Markdown fallback; generated declarations explicitly select the non-Markdown
alternative so they cannot disappear as prose. Semantic capability checks run before this
step, and include expansion resolves nested files with cycle detection and origin hashes.

```lean

private def elaborateGenerated (source : String) : CommandElabM Unit := do
  let parsed ← match Parser.runParserCategory (← getEnv) `command source "<generated by qasm!>" with
    | .ok stx => pure stx
    | .error message => throwError m!"generated Lean code is invalid:\n{message}\n\n{source}"
  let stx :=
    if parsed.getKind == `choice then
      parsed.getArgs.find? (·.getKind != `LiterateLean.Internal.markdownBlock) |>.getD parsed
    else parsed
  Command.elabCommand stx

private def rejectBackendRequirements (program : Frontend.Program) : CommandElabM Unit := do
  match QASM.check program with
  | .error diagnostics =>
      throwError m!"OpenQASM semantic checking failed: {repr diagnostics}"
  | .ok checked =>
      unless checked.requiredCapabilities.isEmpty do
        throwError m!"portable elaboration does not support backend capabilities: {repr checked.requiredCapabilities}"

private def findIncludePath
    (baseDirectory : System.FilePath) (options : ElabOptions) (filename : String) :
    CommandElabM System.FilePath := do
  let relative := System.FilePath.mk filename
  let candidates := #[baseDirectory / relative] ++ options.includePaths.map (· / relative)
  for candidate in candidates do
    if ← candidate.pathExists then return candidate
  throwError m!"cannot resolve OpenQASM include {leanString filename}; searched {repr candidates}"

private partial def expandIncludes
    (program : Frontend.Program) (baseDirectory : System.FilePath) (options : ElabOptions)
    (includeStack : Array String := #[]) :
    CommandElabM (Frontend.Program × Array (String × UInt64)) := do
  let mut statements : Array Statement := #[]
  let mut origins : Array (String × UInt64) := #[]
  for statement in program.statements do
    match statement with
    | statement@(.includeFile "stdgates.inc") =>
        statements := statements.push statement
    | .includeFile filename =>
        let path ← findIncludePath baseDirectory options filename
        let pathName := toString path
        if includeStack.contains pathName then
          throwError m!"cyclic OpenQASM include detected: {repr (includeStack.push pathName)}"
        let includedText ← try IO.FS.readFile path catch error =>
          throwError m!"cannot read OpenQASM include '{path}': {error.toMessageData}"
        let included ← match QASM.parse includedText with
          | .ok included => pure included
          | .error error => throwError m!"{path}:{error}"
        let (included, nestedOrigins) ← expandIncludes included (path.parent.getD ".") options
          (includeStack.push pathName)
        statements := statements ++ included.statements
        origins := origins.push (pathName, hash includedText) ++ nestedOrigins
    | other => statements := statements.push other
  pure ({ program with statements }, origins)

```

## The compilation transaction

Compilation validates target widths, parses and expands the source, enforces dialect and
type rules, lowers the result to canonical IR, and then elaborates the boundary structures,
IR constant, and interpreter wrapper in dependency order. Lean checks each generated
declaration before compilation advances.

```lean

private def compileProgram
    (name origin source : String) (options : ElabOptions) : CommandElabM Unit := do
  match options.target.validate with
  | .error message => throwError message
  | .ok () => pure ()
  let program ← match QASM.parse source with
    | .ok program => pure program
    | .error error => throwError m!"{origin}:{error}"
  let leanFile ← getFileName
  let baseDirectory :=
    if origin.startsWith "<" then
      (System.FilePath.mk leanFile).parent.getD "."
    else (System.FilePath.mk origin).parent.getD "."
  let (program, includeOrigins) ← expandIncludes program baseDirectory options
  let origins := #[(origin, hash source)] ++ includeOrigins
  if options.dialect == .v3_0 && program.statements.any hasExtendedStatement then
    throwError "`switch` and `nop` require `Dialect.extended`; strict OpenQASM 3.0 is the default"
  rejectBackendRequirements program
  let analysis ← match QASM.analyzeTypes options.target program with
    | .ok analysis => pure analysis
    | .error diagnostics =>
        throwError m!"OpenQASM type checking failed: {repr diagnostics}"
  let irProgram ← match QASM.Lowering.program program analysis
      { target := options.target, dialect := options.dialect, origins } with
    | .ok program => pure program
    | .error error => throwError m!"OpenQASM IR lowering failed: {error.message}"
  let inputs ← match structureCommand name "Inputs" irProgram.inputs with
    | .ok source => pure source
    | .error error => throwError m!"cannot emit input type: {error}"
  let outputs ← match structureCommand name "Outputs" irProgram.outputs with
    | .ok source => pure source
    | .error error => throwError m!"cannot emit output type: {error}"
  elaborateGenerated inputs
  elaborateGenerated outputs
  elaborateProgram name irProgram
  elaborateGenerated (executeCommand name irProgram)

private unsafe def evalOptions (usingClause : Syntax) : CommandElabM ElabOptions :=
  if usingClause.isNone then pure {} else
    liftTermElabM <| Term.evalTerm ElabOptions (mkConst ``ElabOptions) usingClause[1]!

private def resolveSourcePath (path : String) : CommandElabM System.FilePath := do
  let leanPath := System.FilePath.mk (← getFileName)
  pure (leanPath.parent.getD "." / path)

private def programNameFromPath (path : System.FilePath) : CommandElabM String := do
  let some stem := path.fileStem
    | throwError m!"cannot derive a program name from OpenQASM path '{path}'"
  let characters := stem.toList.map fun char =>
    if char == '_' || char.isAlpha || char.isDigit || char.toNat ≥ 0x80 then char else '_'
  let characters := match characters with
    | first :: _ => if first.isDigit then '_' :: characters else characters
    | [] => []
  if characters.isEmpty then
    throwError m!"cannot derive a program name from OpenQASM path '{path}'"
  pure (leanIdentifier (String.ofList characters))

```

## The `qasm!` command
The inline and file forms share one command name. An optional ordinary Lean
`ElabOptions` term follows `using`; omission selects the portable defaults.

```lean

syntax (name := qasmInlineCommand)
  "qasm!" ident "{" qasmBlock "}" ("using" term)? : command

syntax (name := qasmFileCommand)
  "qasm!" str ("using" term)? : command
```

The command syntax is registered before its elaborators. Inline commands take their
generated namespace explicitly; file commands derive it from the sanitized file stem.

```lean
@[command_elab qasmInlineCommand]
meta unsafe def elaborateQasmInline : CommandElab
  | stx => do
      let options ← evalOptions stx[5]!
      compileProgram stx[1]!.getId.toString "<qasm!>" stx[3]!.getAtomVal options

@[command_elab qasmFileCommand]
meta unsafe def elaborateQasmFile : CommandElab
  | stx => do
      let resolved ← resolveSourcePath stx[1]!.isStrLit?.get!
      let source ← try IO.FS.readFile resolved catch error =>
        throwError m!"cannot read OpenQASM source '{resolved}': {error.toMessageData}"
      let options ← evalOptions stx[2]!
      compileProgram (← programNameFromPath resolved) (toString resolved) source options
end Compiler
end QASM
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
