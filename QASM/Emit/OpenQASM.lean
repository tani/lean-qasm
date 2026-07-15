    import LiterateLean
    import QASM.IR.Program
    open scoped LiterateLean

# Canonical OpenQASM emission

The emitter reconstructs stable OpenQASM 3.0 from resolved IR. It deliberately ignores source whitespace and locations. Unsupported target capabilities become explicit `pragma qasm_ir_unsupported` statements; unsupported expression positions become conspicuous unresolved calls rather than being silently erased.

```lean
namespace QASM.Emit.OpenQASM

open QASM.IR

```

## Emission modes and resolved names

Canonical IR uses numeric identities internally, but OpenQASM output must use display
names consistently across declarations and nested bodies. `Context` collects every
variable, declaration, and callable name before rendering, including locals hidden inside
process scopes. Missing identities receive conspicuous synthetic names rather than
silently colliding.

`EmitMode.selfContained` normalizes modules for reproducible output;
`preserveModules` retains recorded include boundaries when a caller needs them.

```lean
inductive EmitMode
  | selfContained
  | preserveModules
  deriving Repr, BEq, DecidableEq, Inhabited

private structure Context where
  vars : Std.HashMap VarId String := {}
  decls : Std.HashMap DeclId String := {}
  callables : Std.HashMap CallableId String := {}

private def insertVar (context : Context) (var : Var) : Context :=
  { context with vars := context.vars.insert var.id var.name }

private partial def collectProcVars (context : Context) : Proc → Context
  | .skip | .breakLoop | .continueLoop | .endProgram => context
  | .operation (.declare var _) => insertVar context var
  | .operation (.allocate declaration) =>
      { context with vars := context.vars.insert declaration.var declaration.name }
  | .operation _ => context
  | .sequence steps => steps.foldl collectProcVars context
  | .scope locals body => collectProcVars (locals.foldl insertVar context) body
  | .branch _ thenBranch elseBranch =>
      let context := collectProcVars context thenBranch
      elseBranch.map (collectProcVars context) |>.getD context
  | .switch _ cases default =>
      let context := cases.foldl (fun current entry => match entry with
        | .mk _ body => collectProcVars current body) context
      default.map (collectProcVars context) |>.getD context
  | .forLoop iterator _ body => collectProcVars (insertVar context iterator) body
  | .whileLoop _ body => collectProcVars context body
  | .returnValue _ => context

private def buildContext (program : Program) : Context :=
  let context := program.inputs.foldl (fun context declaration => insertVar context declaration.var) {}
  let context := program.outputs.foldl (fun context declaration => insertVar context declaration.var) context
  let context := program.constants.foldl (fun context declaration =>
    { context with decls := context.decls.insert declaration.id declaration.name }) context
  let context := program.types.foldl (fun context declaration =>
    { context with decls := context.decls.insert declaration.id declaration.name }) context
  let context := program.externs.foldl (fun context declaration =>
    { context with decls := context.decls.insert declaration.id declaration.name }) context
  let context := program.gates.foldl (fun context declaration =>
    let context := { context with decls := context.decls.insert declaration.id declaration.name }
    let context := declaration.parameters.foldl insertVar context
    declaration.qubits.foldl insertVar context) context
  let context := program.subroutines.foldl (fun context declaration =>
    let context := { context with
      callables := context.callables.insert declaration.id declaration.name }
    declaration.parameters.foldl insertVar context) context
  let context := program.subroutines.foldl
    (fun context declaration => collectProcVars context declaration.body) context
  collectProcVars context program.body

private def varName (context : Context) (id : VarId) : String :=
  context.vars[id]?.getD s!"__qasm_unknown_var_{id.value}"

private def declName (context : Context) (id : DeclId) : String :=
  context.decls[id]?.getD s!"__qasm_unknown_decl_{id.value}"

private def callableName (context : Context) (id : CallableId) : String :=
  context.callables[id]?.getD s!"__qasm_unknown_callable_{id.value}"

```

## Types and closed source spellings

Resolved IR types render without consulting target defaults. Operator, builtin, and
capability maps are total over their inductive inputs, establishing one canonical source
spelling for each semantic constructor. Array-reference mutability and either concrete
shape or rank are preserved explicitly.

```lean
private def scalarType : ScalarTy → String
  | .bit none => "bit"
  | .bit (some width) => s!"bit[{width}]"
  | .sint width => s!"int[{width}]"
  | .uint width => s!"uint[{width}]"
  | .float width => s!"float[{width}]"
  | .angle width => s!"angle[{width}]"
  | .boolean => "bool"
  | .complex width => s!"complex[float[{width}]]"
  | .duration => "duration"
  | .stretch => "stretch"
  | .qubit 1 => "qubit"
  | .qubit count => s!"qubit[{count}]"
  | .void => "void"

private def type : QASM.IR.Type → String
  | .scalar value => scalarType value
  | .array element shape =>
      s!"array[{scalarType element}, {String.intercalate ", " (shape.toList.map toString)}]"
  | .arrayRef mutable element (some shape) _ =>
      let qualifier := if mutable then "mutable" else "readonly"
      s!"{qualifier} array[{scalarType element}, {String.intercalate ", " (shape.toList.map toString)}]"
  | .arrayRef mutable element none rank =>
      let qualifier := if mutable then "mutable" else "readonly"
      s!"{qualifier} array[{scalarType element}, #dim={rank}]"

private def unaryOperator : UnaryOp → String
  | .not => "!"
  | .neg => "-"
  | .bitnot => "~"

private def binaryOperator : BinaryOp → String
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .div => "/"
  | .mod => "%"
  | .pow => "**"
  | .shl => "<<"
  | .shr => ">>"
  | .band => "&"
  | .bor => "|"
  | .bxor => "^"
  | .land => "&&"
  | .lor => "||"
  | .eq => "=="
  | .ne => "!="
  | .lt => "<"
  | .le => "<="
  | .gt => ">"
  | .ge => ">="
  | .concat => "++"

private def builtinName : Builtin → String
  | .popcount => "popcount"
  | .sizeof => "sizeof"
  | .real => "real"
  | .imag => "imag"
  | .sin => "sin"
  | .cos => "cos"
  | .tan => "tan"
  | .arcsin => "arcsin"
  | .arccos => "arccos"
  | .arctan => "arctan"
  | .sqrt => "sqrt"
  | .exp => "exp"
  | .log => "log"
  | .floor => "floor"
  | .ceiling => "ceiling"
  | .mod => "mod"
  | .rotl => "rotl"
  | .rotr => "rotr"

private def capabilityName : Capability → String
  | .externalFunction => "external_function"
  | .calibration => "calibration"
  | .timing => "timing"
  | .physicalQubit => "physical_qubit"

```

## Literals, expressions, and operands

Finite floating-point values are rendered from their IEEE bits so output is deterministic
and reparses to the same value; non-finite values become explicit unsupported calls.
Expression rendering adds parentheses around operators instead of attempting to recover
minimal precedence. Stable IDs are translated through `Context`, and unsupported
expressions remain visible capability markers.

Lvalues preserve selector groups, quantum operands preserve wire selections, and argument
rendering follows the resolved IR variant rather than re-inferring a source type.

```lean
private def float (value : Float) : String :=
  let bits := value.toBits
  let negative := ((bits >>> 63) &&& 1) == 1
  let exponentBits := (((bits >>> 52) &&& 0x7ff).toNat)
  let fraction := (bits &&& 0x000fffffffffffff).toNat
  if exponentBits == 0x7ff then
    "__qasm_unsupported_nonfinite_float()"
  else
    let mantissa := if exponentBits == 0 then fraction else 2 ^ 52 + fraction
    let exponent : Int := if exponentBits == 0 then -1074 else
      Int.ofNat exponentBits - 1023 - 52
    let sign := if negative then "-" else ""
    if exponent >= 0 then
      s!"{sign}{mantissa * 2 ^ exponent.toNat}.0"
    else
      let scale := exponent.natAbs
      s!"{sign}{mantissa * 5 ^ scale}e-{scale}"

private def bitstring (bits : Array Bool) : String :=
  "\"" ++ String.ofList (bits.toList.map fun bit => if bit then '1' else '0') ++ "\""

private partial def expr (context : Context) (value : Expr) : String :=
  match value.node with
  | .intLit literal => toString literal
  | .floatLit literal => float literal
  | .imaginaryLit literal => float literal ++ "im"
  | .boolLit true => "true"
  | .boolLit false => "false"
  | .bitstringLit bits => bitstring bits
  | .durationLit seconds => float seconds ++ "s"
  | .var id => varName context id
  | .const id => declName context id
  | .unary operator operand => s!"({unaryOperator operator}{expr context operand})"
  | .binary operator left right =>
      s!"({expr context left} {binaryOperator operator} {expr context right})"
  | .builtin function arguments =>
      s!"{builtinName function}({String.intercalate ", " (arguments.toList.map (expr context))})"
  | .callSubroutine callee arguments =>
      s!"{callableName context callee}({String.intercalate ", " (arguments.toList.map (expr context))})"
  | .cast target value => s!"{type target}({expr context value})"
  | .index value indices =>
      s!"{expr context value}[{String.intercalate ", " (indices.toList.map (expr context))}]"
  | .range start step stop =>
      let start := start.map (expr context) |>.getD ""
      let stop := stop.map (expr context) |>.getD ""
      match step with
      | none => s!"{start}:{stop}"
      | some step => s!"{start}:{expr context step}:{stop}"
  | .set values | .array values =>
      "{" ++ String.intercalate ", " (values.toList.map (expr context)) ++ "}"
  | .unsupported capability _ => s!"__qasm_unsupported_{capabilityName capability}()"

private def lvalue (context : Context) (value : LValue) : String :=
  let indices := value.indices.toList.map fun group =>
    s!"[{String.intercalate ", " (group.toList.map (expr context))}]"
  varName context value.root ++ String.join indices

private def quantumOperand (context : Context) : QuantumOperand → String
  | .physical index => s!"${index}"
  | .wire var indices _ =>
      let suffix := if indices.isEmpty then "" else
        s!"[{String.intercalate ", " (indices.toList.map (expr context))}]"
      varName context var ++ suffix

private def argument (context : Context) : Argument → String
  | .expr value => expr context value
  | .quantum operand => quantumOperand context operand
  | .arrayRef target _ => lvalue context target

private def modifier (context : Context) : GateModifier → String
  | .inverse => "inv @ "
  | .power exponent => s!"pow({expr context exponent}) @ "
  | .control false 1 => "ctrl @ "
  | .control true 1 => "negctrl @ "
  | .control false count => s!"ctrl({count}) @ "
  | .control true count => s!"negctrl({count}) @ "

private def gateCall (context : Context) (gate : CircuitRef)
    (operands : Array QuantumOperand) : String :=
  let modifiers := String.join (gate.modifiers.toList.map (modifier context))
  let parameters := if gate.parameters.isEmpty then "" else
    s!"({String.intercalate ", " (gate.parameters.toList.map (expr context))})"
  let operands := if operands.isEmpty then "" else
    " " ++ String.intercalate ", " (operands.toList.map (quantumOperand context))
  s!"{modifiers}{gate.name}{parameters}{operands};"

```

## Circuit rendering and wire order

Categorical circuits carry wire order as data, while OpenQASM expresses order through
operand lists. The renderer threads a lane array through composition, tensor, and
permutation nodes. Inversion reverses sequential composition and inverts permutations;
controls and powers become source modifiers around the rendered primitive. Unsupported
circuits become explicit pragmas with their capability and diagnostic detail.

```lean
private def indentLine (depth : Nat) (line : String) : String :=
  String.join (List.replicate depth "  ") ++ line

private def unsupportedLine (capability : Capability) (detail : String) : String :=
  let detail := detail.replace "\n" " "
  s!"pragma qasm_ir_unsupported {capabilityName capability}: {detail}"

private def permutationLanes (lanes : Array String) (mapping : Array Nat) : Array String :=
  mapping.map fun index => lanes[index]?.getD s!"__qasm_unknown_wire_{index}"

private def inverseMapping (mapping : Array Nat) : Array Nat :=
  (Array.range mapping.size).map fun index => mapping.toList.idxOf index

mutual
private partial def circuitLines (context : Context) (depth : Nat)
    (prefixes : Array String) (controls lanes : Array String) (circuit : Circuit) :
    Array String × Array String :=
  match circuit with
  | .identity _ => (#[], lanes)
  | .primitive primitive =>
      let prefixes := String.join prefixes.toList
      let parameters := if primitive.parameters.isEmpty then "" else
        s!"({String.intercalate ", " (primitive.parameters.toList.map (expr context))})"
      let operands := controls ++ lanes
      let operands := if operands.isEmpty then "" else " " ++ String.intercalate ", " operands.toList
      (#[indentLine depth s!"{prefixes}{primitive.name}{parameters}{operands};"], lanes)
  | .compose first second =>
      let (firstLines, lanes) := circuitLines context depth prefixes controls lanes first
      let (secondLines, lanes) := circuitLines context depth prefixes controls lanes second
      (firstLines ++ secondLines, lanes)
  | .tensor first second =>
      let firstCount := Circuit.dom first |>.length
      let firstLanes := lanes.extract 0 firstCount
      let secondLanes := lanes.extract firstCount lanes.size
      let (firstLines, firstLanes) := circuitLines context depth prefixes controls firstLanes first
      let (secondLines, secondLanes) := circuitLines context depth prefixes controls secondLanes second
      (firstLines ++ secondLines, firstLanes ++ secondLanes)
  | .permute permutation => (#[], permutationLanes lanes permutation.mapping)
  | .inverse value => inverseCircuitLines context depth prefixes controls lanes value
  | .power exponent value =>
      circuitLines context depth (prefixes.push s!"pow({expr context exponent}) @ ") controls lanes value
  | .controlled spec value =>
      let count := spec.controls.length
      let nextControls := lanes.extract 0 count
      let targetLanes := lanes.extract count lanes.size
      let negative := spec.polarities.any (· == .negative)
      let modifierText := if negative then
        if count == 1 then "negctrl @ " else s!"negctrl({count}) @ "
      else if count == 1 then "ctrl @ " else s!"ctrl({count}) @ "
      let (lines, targetLanes) :=
        circuitLines context depth (prefixes.push modifierText) (controls ++ nextControls) targetLanes value
      (lines, nextControls ++ targetLanes)
  | .unsupported capability detail _ _ =>
      (#[indentLine depth (unsupportedLine capability detail)], lanes)

private partial def inverseCircuitLines (context : Context) (depth : Nat)
    (prefixes : Array String) (controls lanes : Array String) (circuit : Circuit) :
    Array String × Array String :=
  match circuit with
  | .compose first second =>
      let (secondLines, lanes) :=
        inverseCircuitLines context depth prefixes controls lanes second
      let (firstLines, lanes) :=
        inverseCircuitLines context depth prefixes controls lanes first
      (secondLines ++ firstLines, lanes)
  | .tensor first second =>
      let firstCount := Circuit.cod first |>.length
      let firstLanes := lanes.extract 0 firstCount
      let secondLanes := lanes.extract firstCount lanes.size
      let (firstLines, firstLanes) :=
        inverseCircuitLines context depth prefixes controls firstLanes first
      let (secondLines, secondLanes) :=
        inverseCircuitLines context depth prefixes controls secondLanes second
      (firstLines ++ secondLines, firstLanes ++ secondLanes)
  | .permute permutation =>
      (#[], permutationLanes lanes (inverseMapping permutation.mapping))
  | .inverse value => circuitLines context depth prefixes controls lanes value
  | value => circuitLines context depth (prefixes.push "inv @ ") controls lanes value
end

```

## Gates and structured processes

Gate declarations render their categorical body against the declared qubit names.
Processes retain their first-order structure: scopes become blocks, branches and loops
become normalized OpenQASM control flow, and operations render through one local
`opLine` correspondence. This is serialization of IR, not decompilation from the runtime
interpreter.

```lean
private def gateDeclaration (context : Context) (declaration : GateDecl) : Array String :=
  let parameters := if declaration.parameters.isEmpty then "" else
    "(" ++ String.intercalate ", " (declaration.parameters.toList.map (·.name)) ++ ")"
  let qubits := declaration.qubits.map (·.name)
  let header := s!"gate {declaration.name}{parameters} {String.intercalate ", " qubits.toList} \{"
  let (body, _) := circuitLines context 1 #[] #[] qubits declaration.body
  #[header] ++ body ++ #["}"]

private def block (lines : Array String) (depth : Nat) : Array String :=
  #[indentLine depth "{"] ++ lines.map (indentLine (depth + 1)) ++ #[indentLine depth "}"]

private partial def procLines (context : Context) (depth : Nat) : Proc → Array String
  | .skip => #[]
  | .operation op => #[indentLine depth (opLine context op)]
  | .sequence steps => steps.flatMap (procLines context depth)
  | .scope _ body => block (procLines context 0 body) depth
  | .branch condition thenBranch none =>
      #[indentLine depth s!"if ({expr context condition}) \{"] ++
      procLines context (depth + 1) thenBranch ++ #[indentLine depth "}"]
  | .branch condition thenBranch (some elseBranch) =>
      #[indentLine depth s!"if ({expr context condition}) \{"] ++
      procLines context (depth + 1) thenBranch ++ #[indentLine depth "} else {"] ++
      procLines context (depth + 1) elseBranch ++ #[indentLine depth "}"]
  | .switch scrutinee cases default =>
      let caseLines := cases.flatMap fun entry => match entry with
        | .mk labels body =>
            #[indentLine (depth + 1)
              s!"case {String.intercalate ", " (labels.toList.map (expr context))} \{"] ++
            procLines context (depth + 2) body ++ #[indentLine (depth + 1) "}"]
      let defaultLines := default.map (fun body =>
        #[indentLine (depth + 1) "default {"] ++ procLines context (depth + 2) body ++
          #[indentLine (depth + 1) "}"]) |>.getD #[]
      #[indentLine depth s!"switch ({expr context scrutinee}) \{"] ++ caseLines ++ defaultLines ++
        #[indentLine depth "}"]
  | .forLoop iterator domain body =>
      #[indentLine depth s!"for {type iterator.type} {iterator.name} in {domainText context domain} \{"] ++
      procLines context (depth + 1) body ++ #[indentLine depth "}"]
  | .whileLoop condition body =>
      #[indentLine depth s!"while ({expr context condition}) \{"] ++
      procLines context (depth + 1) body ++ #[indentLine depth "}"]
  | .breakLoop => #[indentLine depth "break;"]
  | .continueLoop => #[indentLine depth "continue;"]
  | .returnValue none => #[indentLine depth "return;"]
  | .returnValue (some value) => #[indentLine depth s!"return {expr context value};"]
  | .endProgram => #[indentLine depth "end;"]
where
  opLine (context : Context) : Op → String
    | .eval value => expr context value ++ ";"
    | .declare var none => s!"{type var.type} {var.name};"
    | .declare var (some value) => match var.type with
        | .scalar (.qubit _) => s!"let {var.name} = {expr context value};"
        | _ => s!"{type var.type} {var.name} = {expr context value};"
    | .assign target value => s!"{lvalue context target} = {expr context value};"
    | .apply gate operands => gateCall context gate operands
    | .measure source .discard => s!"measure {quantumOperand context source};"
    | .measure source (.lvalue target) =>
        s!"measure {quantumOperand context source} -> {lvalue context target};"
    | .reset operand => s!"reset {quantumOperand context operand};"
    | .barrier operands => if operands.isEmpty then "barrier;" else
        s!"barrier {String.intercalate ", " (operands.toList.map (quantumOperand context))};"
    | .allocate declaration => if declaration.size == 1 then s!"qubit {declaration.name};"
        else s!"qubit[{declaration.size}] {declaration.name};"
    | .call callee arguments =>
        s!"{callableName context callee}({String.intercalate ", " (arguments.toList.map (argument context))});"
    | .emitExtern call =>
        s!"{declName context call.callee}({String.intercalate ", " (call.arguments.toList.map (expr context))});"
    | .unsupported capability detail => unsupportedLine capability detail

  domainText (context : Context) : IterationDomain → String
    | .range start step stop =>
        s!"[{expr context start}:{expr context step}:{expr context stop}]"
    | .set values => "{" ++ String.intercalate ", " (values.toList.map (expr context)) ++ "}"
    | .array value => expr context value

```

## Compilation-unit declarations

I/O, constants, externs, gates, and subroutines render from their resolved declarations.
Sections remain separate arrays until final assembly, which makes ordering explicit and
allows empty categories to disappear without creating unstable blank lines.

```lean
private def ioDeclaration (input : Bool) (declaration : IODecl) : String :=
  s!"{if input then "input" else "output"} {type declaration.var.type} {declaration.var.name};"

private def constantDeclaration (context : Context) (declaration : ConstantDecl) : String :=
  s!"const {type declaration.type} {declaration.name} = {expr context declaration.value};"

private def externDeclaration (declaration : ExternDecl) : String :=
  let parameters := String.intercalate ", " (declaration.parameters.toList.map type)
  let result := match declaration.returnType with
    | .scalar .void => ""
    | value => " -> " ++ type value
  s!"extern {declaration.name}({parameters}){result};"

private def subroutineDeclaration (context : Context) (declaration : SubroutineDecl) : Array String :=
  let parameters := declaration.parameters.toList.map fun parameter =>
    s!"{type parameter.type} {parameter.name}"
  let result := match declaration.returnType with
    | .scalar .void => ""
    | value => " -> " ++ type value
  #[s!"def {declaration.name}({String.intercalate ", " parameters}){result} \{"] ++
    procLines context 1 declaration.body ++ #["}"]

```

## Directives and module boundaries

Annotations and pragmas preserve their recorded order. Self-contained output always
selects the intrinsic standard-gate module; module-preserving output reproduces recorded
includes while ensuring that standard gates remain available.

```lean
private def annotationLines (program : Program) : Array String :=
  program.annotations.map fun annotation => match annotation.content with
    | none => "@" ++ annotation.keyword
    | some content => s!"@{annotation.keyword} {content}"

private def pragmaLines (program : Program) : Array String :=
  program.pragmas.map fun pragma => if pragma.content.isEmpty then "pragma" else "pragma " ++ pragma.content

private def includeLines (mode : EmitMode) (program : Program) : Array String :=
  match mode with
  | .selfContained => #["include \"stdgates.inc\";"]
  | .preserveModules =>
      if program.includes.any (·.filename == "stdgates.inc") then
        program.includes.map fun moduleInfo => s!"include \"{moduleInfo.filename}\";"
      else
        #["include \"stdgates.inc\";"] ++
          program.includes.map fun moduleInfo => s!"include \"{moduleInfo.filename}\";"

```

## Public deterministic emitter

`emitWithMode` assembles the compilation unit in canonical dependency order: header,
includes, directives, boundary declarations, constants and types, externs, gates,
subroutines, then the executable body. Exactly one blank line separates nonempty sections
and one newline terminates the result, making textual output stable for inspection and
round-trip tests.

```lean
/-- Emits deterministic canonical OpenQASM. Standard gates use one normalized module include. -/
def emitWithMode (mode : EmitMode) (program : Program) : String :=
  let context := buildContext program
  let header := #[s!"OPENQASM {program.version.major}.{program.version.minor};"]
  let includes := includeLines mode program
  let annotations := annotationLines program
  let pragmas := pragmaLines program
  let inputs := program.inputs.map (ioDeclaration true)
  let outputs := program.outputs.map (ioDeclaration false)
  let constants := program.constants.map (constantDeclaration context)
  let typeWarnings := program.types.map fun declaration =>
    unsupportedLine .externalFunction s!"named type {declaration.name}: {type declaration.type}"
  let externs := program.externs.flatMap fun declaration => #[externDeclaration declaration]
  let gates := program.gates.flatMap (gateDeclaration context)
  let subroutines := program.subroutines.flatMap (subroutineDeclaration context)
  let body := procLines context 0 program.body
  let sections := #[header, includes, annotations, pragmas, inputs, outputs, constants,
    typeWarnings, externs, gates, subroutines, body]
  let nonempty := sections.filter (!·.isEmpty) |>.map fun lines => String.intercalate "\n" lines.toList
  String.intercalate "\n\n" nonempty.toList ++ "\n"

def emit (program : Program) : String := emitWithMode .selfContained program

end QASM.Emit.OpenQASM
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
