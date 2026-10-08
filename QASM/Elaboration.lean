    import LiterateLean

    import QASM.Runtime
    import QASM.Elaboration.BlockParser
    import QASM.Frontend
    import QASM.Frontend.Semantics
    import QASM.Frontend.Typing
    import QASM.Lowering.Program
    import QASM.Elaboration.Quotation
    import QASM.Execution.Interpreter
    import Lean.Elab.Eval

    open scoped LiterateLean

# OpenQASM elaboration pipeline

`qasm!` is a compile-time frontend embedded in Lean's command elaborator. This module
coordinates the complete path from captured OpenQASM text through include expansion,
parsing, semantic checks, type analysis, and lowering to a canonical `QASM.IR.Program`.
It then declares that IR value together with native input/output structures and a typed
`execute` wrapper.

The wrapper encodes boundary values, calls `QASM.Execution.run`, and decodes the resulting
classical environment. Expressions, operations, callables, and structured control flow
are interpreted from IR at runtime; allocation, unitaries, measurement, reset, and
barriers cross `QuantumBackend`.

Input/output structures and the wrapper are emitted as Lean source strings and reparsed
as commands. The canonical IR value or parameterized template is quoted directly as a
Lean expression. This keeps the generated API native and typed without presenting the
interpreted program body as
per-program Lean control flow.

The command elaborator coordinates two distinct times:

```mermaid
flowchart LR
    subgraph CompileTime["Lean elaboration time"]
        Source --> Includes --> Parse --> Semantics --> Typing --> Lowering
        Lowering --> Program["quoted IR.Program"]
        Program --> API["generated Inputs / Outputs / execute"]
    end
    subgraph RunTime["program execution time"]
        API --> Interpreter["QASM.Execution.run"]
        Interpreter --> Backend["QuantumBackend"]
    end
```

Closed declarations store immutable IR; family declarations store kernel-reducible
functions returning ordinary IR and dependent boundary structures. `Family.Valid` records
positive residual widths and extents, and `execute` requires its proof.
Only these generated definitions cross from elaboration into runtime;
frontend state, source cursors, and diagnostics do not.

```lean
namespace QASM
namespace Compiler

open Lean
open Lean Meta Elab Command
open Frontend
open QASM.Parameters

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

private def irScalarLeanType : QASM.IR.ScalarTy Size → Except String String
  | .bit none => pure "QASM.Bit"
  | .bit (some width) => pure s!"BitVec ({width.leanCode})"
  | .sint width => pure s!"QASM.SInt ({width.leanCode})"
  | .uint width => pure s!"QASM.UInt ({width.leanCode})"
  | .float ⟨.literal 32⟩ => pure "Float32"
  | .float ⟨.literal 64⟩ => pure "Float"
  | .float width => throw s!"cannot emit float[{width}]"
  | .angle width => pure s!"QASM.Angle ({width.leanCode})"
  | .boolean => pure "Bool"
  | .complex width => pure s!"QASM.ComplexN ({width.leanCode})"
  | .duration => pure "QASM.Duration"
  | .stretch => throw "stretch requires a timing backend"
  | .qubit _ => throw "qubits cannot appear in classical I/O structures"
  | .void => throw "void cannot appear in a value structure"

private def irLeanType : QASM.IR.Type Size → Except String String
  | .scalar value => irScalarLeanType value
  | .array element shape => do
      let element ← irScalarLeanType element
      pure s!"QASM.FixedArray ({element}) [{String.intercalate ", " (shape.toList.map Size.leanCode)}]"
  | .arrayRef .. => throw "array-reference types cannot appear in program I/O"

private def familyBinders (parameters : Array String) : String :=
  String.join (parameters.toList.map fun name => s!" ({leanIdentifier name} : Nat)")

private def familyArguments (parameters : Array String) : String :=
  String.join (parameters.toList.map fun name => s!" {leanIdentifier name}")

private def structureCommand (name suffix : String) (fields : Array (QASM.IR.IODecl Size))
    (parameters : Array String) :
    Except String String := do
  let header := s!"structure {name}.{suffix}{familyBinders parameters} where"
  if fields.isEmpty then pure header
  else
    let mut declarations := #[]
    for field in fields do
      declarations := declarations.push
        s!"  {leanIdentifier field.var.name} : {← irLeanType field.var.type}"
    pure (header ++ "\n" ++ String.intercalate "\n" declarations.toList)


private def elaborateProgram (name : String)
    (program : QASM.IR.Program Size Integer) (parameters : Array String) : CommandElabM Unit := do
  let namespaceName := (← getCurrNamespace) ++ name.toName
  liftTermElabM do
    let rec bind (remaining : List String) (variables : Array (String × Lean.Expr)) : TermElabM Unit :=
      match remaining with
      | [] => do
          let value := QASM.Elaboration.quoteTemplate variables program
          let arguments := variables.map (·.2)
          let type ← mkForallFVars arguments (mkApp2 (mkConst ``QASM.IR.Program) (mkConst ``Nat) (mkConst ``Int))
          let body ← mkLambdaFVars arguments value
          addAndCompile <| .defnDecl {
            name := namespaceName ++ `program, levelParams := [], type, value := body,
            safety := .safe, hints := .abbrev }
          saveEqnAffectingOptions (namespaceName ++ `program)
          enableRealizationsForConst (namespaceName ++ `program)
          setReducibilityStatus (namespaceName ++ `program) .reducible
          unless parameters.isEmpty do
            let valid ← mkLambdaFVars arguments (QASM.Elaboration.templateValidity value)
            let validType ← mkForallFVars arguments (mkSort .zero)
            addAndCompile <| .defnDecl {
              name := namespaceName ++ `Valid, levelParams := [], type := validType, value := valid,
              safety := .safe, hints := .abbrev }
            saveEqnAffectingOptions (namespaceName ++ `Valid)
            enableRealizationsForConst (namespaceName ++ `Valid)
            setReducibilityStatus (namespaceName ++ `Valid) .reducible
      | parameter :: rest =>
          withLocalDeclD parameter.toName (mkConst ``Nat) fun parameterTerm =>
            bind rest (variables.push (parameter, parameterTerm))
    bind parameters.toList #[]

private partial def freshGeneratedName (parameters : Array String) (candidate : String) : String :=
  if parameters.contains candidate then freshGeneratedName parameters (candidate ++ "_") else candidate

private def backendBinders (monad qubit error : String) : String :=
  "{" ++ monad ++ " : Type → Type} {" ++ qubit ++ " " ++ error ++ " : Type} " ++
  s!"[Monad {monad}] [QASM.QuantumBackend {monad} {qubit} {error}]"

private def executeCommand (name : String) (program : QASM.IR.Program Size Integer)
    (parameters : Array String) : String :=
  let monad := freshGeneratedName parameters "qasmM"
  let qubit := freshGeneratedName parameters "qasmQubit"
  let error := freshGeneratedName parameters "qasmError"
  let inputName := freshGeneratedName parameters "inputs"
  let resultName := freshGeneratedName parameters "qasm_result"
  let valuesName := if program.outputs.isEmpty then "_" else freshGeneratedName parameters "qasm_values"
  let decodedName := freshGeneratedName parameters "qasm_decoded_value"
  let validName := freshGeneratedName parameters "_valid"
  let arguments := familyArguments parameters
  let inputs := program.inputs.map fun declaration =>
    s!"((⟨{declaration.var.id.value}⟩ : QASM.IR.VarId), " ++
      s!"QASM.ValueCodec.toValue {inputName}.{leanIdentifier declaration.var.name})"
  let outputFields := program.outputs.map fun declaration =>
    let key := s!"((⟨{declaration.var.id.value}⟩ : QASM.IR.VarId))"
    let value := s!"{valuesName}[{key}]?.getD QASM.Value.uninitialized"
    s!"{leanIdentifier declaration.var.name} := (← match QASM.ValueCodec.fromValue ({value}) with\n" ++
      s!"| .ok {decodedName} => pure {decodedName}\n" ++
      s!"| .error message => return .error (.invalidCast (" ++
        leanString ("output '" ++ declaration.var.name ++ "': ") ++ " ++ message)))"
  let success := if outputFields.isEmpty then "return .ok {}" else
    "return .ok {\n" ++ indent (String.intercalate ",\n" outputFields.toList) ++ "\n}"
  let body :=
    s!"let {resultName} ← QASM.Execution.run ({name}.program{arguments}) {arrayCode inputs}\n" ++
    s!"match {resultName} with\n" ++
    "| .error error => return .error error\n" ++
    s!"| .ok {valuesName} =>\n" ++ indent success
  let validity := if parameters.isEmpty then "" else s!" ({validName} : {name}.Valid{arguments})"
  s!"def {name}.execute " ++ backendBinders monad qubit error ++ familyBinders parameters ++ validity ++
    s!" ({inputName} : {name}.Inputs{arguments}) : " ++
    s!"{monad} (Except (QASM.RunError {error}) ({name}.Outputs{arguments})) := do\n" ++ indent body

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
    (name origin source : String) (options : ElabOptions)
    (parameters : Array String := #[]) : CommandElabM Unit := do
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
  let analysis ← match QASM.Frontend.analyzeTypes options.target program parameters with
    | .ok analysis => pure analysis
    | .error diagnostics =>
        throwError m!"OpenQASM type checking failed: {repr diagnostics}"
  let irProgram ← match QASM.Lowering.template program analysis
      { target := options.target, dialect := options.dialect, origins } with
    | .ok program => pure program
    | .error error => throwError m!"OpenQASM IR lowering failed: {error.message}"
  let inputs ← match structureCommand name "Inputs" irProgram.inputs parameters with
    | .ok source => pure source
    | .error error => throwError m!"cannot emit input type: {error}"
  let outputs ← match structureCommand name "Outputs" irProgram.outputs parameters with
    | .ok source => pure source
    | .error error => throwError m!"cannot emit output type: {error}"
  elaborateGenerated inputs
  elaborateGenerated outputs
  elaborateProgram name irProgram parameters
  elaborateGenerated (executeCommand name irProgram parameters)

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
The inline, family, and file forms share one command name. Family binders each name a
Lean `Nat` parameter; they are validated without evaluating the parameter. Multiple
parameters use separate binders, for example `(n : Nat) (m : Nat)`. An optional ordinary Lean
`ElabOptions` term follows `using`; omission selects the portable defaults.

```lean

syntax (name := qasmInlineCommand)
  "qasm!" ident "{" qasmBlock "}" ("using" term)? : command

syntax qasmFamilyParameter := "(" ident ":" term ")"
syntax (name := qasmFamilyCommand)
  "qasm!" ident qasmFamilyParameter+ "{" qasmBlock "}" ("using" term)? : command

syntax (name := qasmFileCommand)
  "qasm!" str ("using" term)? : command
```

The command syntax is registered before its elaborators. Binder types use the ordinary
Lean term parser so registering family syntax does not reserve `Nat` as a new keyword. Inline commands take their
generated namespace explicitly; file commands derive it from the sanitized file stem.

```lean
@[command_elab qasmInlineCommand]
meta unsafe def elaborateQasmInline : CommandElab
  | stx => do
      let options ← evalOptions stx[5]!
      compileProgram stx[1]!.getId.toString "<qasm!>" stx[3]!.getAtomVal options

@[command_elab qasmFamilyCommand]
meta unsafe def elaborateQasmFamily : CommandElab
  | stx => do
      for binder in stx[2].getArgs do
        liftTermElabM do
          let parameterType ← Term.elabType binder[3]
          unless ← isDefEq parameterType (mkConst ``Nat) do
            throwErrorAt binder[3] "QASM family parameters must have type Nat"
      let parameters := stx[2].getArgs.map (fun binder => binder[1].getId.toString)
      let options ← evalOptions stx[6]!
      compileProgram stx[1]!.getId.toString "<qasm!>" stx[4]!.getAtomVal options parameters

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
