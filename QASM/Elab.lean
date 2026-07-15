    import LiterateLean

    import QASM.Runtime
    import QASM.Diagram
    import QASM.Source
    import QASM.Frontend
    import QASM.Semantics
    import QASM.Typing
    import Lean.Elab.Eval

    open scoped LiterateLean

# OpenQASM elaboration pipeline

`qasm!` is a compile-time compiler embedded in Lean's command elaborator. This module
coordinates the complete path from captured OpenQASM text to native Lean declarations:
include expansion, frontend parsing, semantic checks, type analysis, portable code
generation, static diagram construction, and command elaboration.

Generated code executes classical behavior as ordinary Lean control flow. Only allocation,
unitaries, measurement, reset, and barriers cross `QuantumBackend`. This division keeps
programs portable while allowing a caller to choose a trace backend, simulator, or device
integration at the generated `run` boundary.

Most helpers below produce Lean source strings rather than constructing syntax trees
incrementally. That choice makes the emitted program readable in diagnostics and keeps
large recursive OpenQASM lowering routines independent of Lean macro quotations. The
final command boundary reparses and elaborates the assembled declarations in the caller's
environment.

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

private def sanitizeFloat (raw : String) : String :=
  let raw := raw.replace "_" ""
  let raw := if raw.startsWith "." then "0" ++ raw else raw
  if raw.endsWith "." then raw ++ "0" else raw

private def timingLiteralCode (raw : String) : String :=
  let units : List (String × String) := [
    ("dt", "0.0"), ("ns", "0.000000001"), ("us", "0.000001"),
    ("µs", "0.000001"), ("ms", "0.001"), ("s", "1.0")
  ]
  match units.find? (fun entry => raw.endsWith entry.1) with
  | some (unit, scale) =>
      let number := sanitizeFloat (raw.dropEnd unit.length |>.toString)
      s!"QASM.Value.duration (({number} : Float) * ({scale} : Float))"
  | none => "QASM.Value.unit"

```

## Emitting expression fragments

The first lowering layer renders literals and expression trees as Lean source. Numeric
normalization, target-sized casts, operand slicing, and assignment updates are expressed
only through the portable runtime API.

```lean

private partial def expressionCode : Expression → String
  | .literal (.integer raw) =>
      s!"QASM.Value.integerLiteral {leanString raw}"
  | .literal (.float raw) =>
      s!"QASM.Value.float ({sanitizeFloat raw} : Float)"
  | .literal (.imaginary raw) =>
      let coefficient := sanitizeFloat (raw.dropEnd 2 |>.trimAscii |>.toString)
      s!"QASM.Value.complex 0.0 ({coefficient} : Float)"
  | .literal (.boolean value) =>
      if value then "QASM.Value.boolean true" else "QASM.Value.boolean false"
  | .literal (.bitstring value) =>
      s!"QASM.Value.bitstringLiteral {leanString value}"
  | .literal (.timing raw) => timingLiteralCode raw
  | .identifier "pi" | .identifier "π" =>
      "QASM.Value.float 3.141592653589793"
  | .identifier "tau" | .identifier "τ" =>
      "QASM.Value.float 6.283185307179586"
  | .identifier "euler" | .identifier "ℇ" =>
      "QASM.Value.float 2.718281828459045"
  | .identifier name =>
      leanIdentifier name
  | .hardwareQubit _ =>
      "QASM.Value.unit"
  | .unary operator operand =>
      s!"QASM.Value.unary {leanString operator} ({expressionCode operand})"
  | .binary operator left right =>
      s!"QASM.Value.binary {leanString operator} ({expressionCode left}) ({expressionCode right})"
  | .call name arguments =>
      s!"QASM.Value.builtin {leanString name} {arrayCode (arguments.map expressionCode)}"
  | .cast typeName width value =>
      let defaultWidth := match typeName with
        | "int" => "__qasm_target.intWidth"
        | "uint" => "__qasm_target.uintWidth"
        | "float" | "complex" => "__qasm_target.floatWidth"
        | "angle" => "__qasm_target.angleWidth"
        | _ => "1"
      let width := width.map (fun width =>
        s!"QASM.Value.asNat ({expressionCode width})") |>.getD defaultWidth
      s!"QASM.Value.cast {leanString typeName} ({width}) ({expressionCode value})"
  | .arrayCast elementName elementWidth dimensions value =>
      let defaultWidth := match elementName with
        | "int" => "__qasm_target.intWidth"
        | "uint" => "__qasm_target.uintWidth"
        | "float" | "complex" => "__qasm_target.floatWidth"
        | "angle" => "__qasm_target.angleWidth"
        | _ => "1"
      let width := elementWidth.map (fun width =>
        s!"QASM.Value.asNat ({expressionCode width})") |>.getD defaultWidth
      let shape := "[" ++ String.intercalate ", " (dimensions.toList.map fun dimension =>
        s!"QASM.Value.asNat ({expressionCode dimension})") ++ "]"
      s!"QASM.Value.castArray {leanString elementName} ({width}) {shape} ({expressionCode value})"
  | .index value indices =>
      s!"QASM.Value.index ({expressionCode value}) {arrayCode (indices.map expressionCode)}"
  | .range start step stop =>
      let start := start.map expressionCode |>.getD "QASM.Value.integer 0"
      let step := step.map expressionCode |>.getD "QASM.Value.integer 1"
      let stop := stop.map expressionCode |>.getD start
      s!"QASM.Value.array (QASM.Value.range ({start}) ({step}) ({stop}))"
  | .set values | .array values =>
      s!"QASM.Value.array {arrayCode (values.map expressionCode)}"
  | .measure _ =>
      "QASM.Value.unit"
  | .durationOf _ =>
      "QASM.Value.unit"

```

### Defaults and scalar coercions

Expression lowering assumes an initialized runtime `Value`. Declarations without an
initializer therefore need a type-directed default: zero for numeric scalars, false bits,
and recursively replicated defaults for shaped arrays.

`scalarCoercionCode` applies the resolved source declaration at assignment boundaries.
Target-sized types read their width from the generated target configuration when the
source omitted a designator, ensuring that defaults, casts, and arithmetic agree.

```lean
private partial def typeDefaultCode : TypeSpec → String
  | .scalar "bool" _ => "QASM.Value.boolean false"
  | .scalar "bit" width =>
      let width := width.map expressionCode |>.getD "QASM.Value.integer 1"
      s!"QASM.Value.bits (Array.replicate (QASM.Value.asNat ({width})) false)"
  | .scalar "float" _ | .scalar "angle" _ => "QASM.Value.float 0.0"
  | .scalar "complex" _ => "QASM.Value.complex 0.0 0.0"
  | .scalar _ _ => "QASM.Value.integer 0"
  | .array element dimensions =>
      let shape := arrayCode (dimensions.map fun dimension =>
        s!"QASM.Value.asNat ({expressionCode dimension})")
      s!"QASM.Value.replicateShape {shape} ({typeDefaultCode element})"
  | .arrayRef _ _ _ _ => "QASM.Value.unit"

private def scalarCoercionCode (type : TypeSpec) (value : String) : String :=
  match type with
  | .scalar "bit" none => s!"QASM.Value.scalarBit ({value})"
  | .scalar name width =>
      let defaultWidth := match name with
        | "int" => "__qasm_target.intWidth"
        | "uint" => "__qasm_target.uintWidth"
        | "float" | "complex" => "__qasm_target.floatWidth"
        | "angle" => "__qasm_target.angleWidth"
        | _ => "1"
      let width := width.map (fun width =>
        s!"QASM.Value.asNat ({expressionCode width})") |>.getD defaultWidth
      s!"QASM.Value.cast {leanString name} ({width}) ({value})"
  | _ => value

private def operandSelectionCode (register : String) (index : Expression) : String :=
  match index with
  | .range .. | .set .. | .array .. =>
      s!"(QASM.Value.asArray ({expressionCode index})).filterMap " ++
        s!"(fun qasm_index => {register}[QASM.Value.resolveIndex {register}.size qasm_index]?)"
  | _ =>
      let position := s!"QASM.Value.resolveIndex {register}.size ({expressionCode index})"
      s!"({register}.extract ({position}) (({position}) + 1))"

private def concatenateArrays (values : List String) : String :=
  match values with
  | [] => "#[]"
  | first :: rest => rest.foldl (fun acc value => s!"({acc} ++ {value})") first

```

### Quantum operands and assignment targets

Classical expressions lower to one `Value`, but a quantum operand lowers to an array of
backend qubit handles. Index ranges and sets filter-map the selected register positions,
while scalar indices extract one-element arrays. Concatenating those arrays implements
OpenQASM operand-list flattening before broadcast validation.

`operandTarget?` converts a writable logical operand back into an expression-shaped target.
The assignment helper uses the same recursive runtime indexing functions for ordinary
assignment and compound assignment, so reads and writes share index semantics.

```lean
private def operandCode : Operand → String
  | .hardware index => s!"#[qasm_physical_{index}]"
  | .identifier name indices =>
      let register := leanIdentifier name
      match indices.toList with
      | [] => register
      | groups =>
          groups.flatMap (fun group => group.toList) |>.map (operandSelectionCode register) |>
            concatenateArrays

private def operandTarget? : Operand → Option Expression
  | .hardware _ => none
  | .identifier name groups =>
      some (groups.foldl (fun target indices => .index target indices) (.identifier name))

private def assignmentCode (target : Expression) (operator : String) (value : Expression) : String :=
  match target with
  | .identifier name =>
      let identifier := leanIdentifier name
      s!"{identifier} := QASM.Value.compound {leanString operator} {identifier} ({expressionCode value})"
  | .index (.identifier name) indices =>
      let identifier := leanIdentifier name
      let indexValues := arrayCode (indices.map expressionCode)
      let current := s!"QASM.Value.index {identifier} {indexValues}"
      let updated := s!"QASM.Value.compound {leanString operator} ({current}) ({expressionCode value})"
      s!"{identifier} := QASM.Value.setIndex {identifier} {indexValues} ({updated})"
  | _ =>
      "pure ()"

```

## Generated text and lowering state

Indentation and output conversion assemble readable command fragments. A small state
monad supplies collision-free temporary names, and `GenerateContext` records which source
bindings are quantum, mutable, or returned by the current generated function.

```lean

private def indent (source : String) (amount : Nat := 2) : String :=
  let indentation := String.ofList (List.replicate amount ' ')
  String.intercalate "\n" (source.splitOn "\n" |>.map fun line => indentation ++ line)

private def outputReturnCode (outputs : Array IOField) : String :=
  if outputs.isEmpty then "return .ok {}"
  else
    let conversions := outputs.toList.map fun field =>
      let converted := leanIdentifier ("qasm_output_" ++ field.name)
      s!"let {converted} ← match QASM.ValueCodec.fromValue {leanIdentifier field.name} with\n" ++
      s!"| .ok qasm_decoded_value => pure qasm_decoded_value\n" ++
      s!"| .error message => return .error (.invalidCast (" ++
        leanString ("output '" ++ field.name ++ "': ") ++ " ++ message))"
    let fields := outputs.toList.map fun field =>
      s!"{leanIdentifier field.name} := {leanIdentifier ("qasm_output_" ++ field.name)}"
    String.intercalate "\n" conversions ++ "\nreturn .ok { " ++
      String.intercalate ", " fields ++ " }"

private abbrev GenerateM := StateM Nat

private def fresh (label : String) : GenerateM String := do
  let index ← get
  set (index + 1)
  pure s!"qasm_{label}_{index}"

private inductive ReturnMode where
  | program
  | subroutine
  | gate

private structure GenerateContext where
  namespaceName : String
  declarations : Array Statement
  outputs : Array IOField := #[]
  quantumNames : Array String := #[]
  mutableArguments : Array String := #[]
  returnMode : ReturnMode := .program

```

## Callable arguments and result propagation

These helpers classify source expressions, prepare classical and quantum arguments, and
write mutable array references back after a call. They also centralize the `Except`
propagation protocol shared by generated subroutines.

```lean

private def expressionRoot? : Expression → Option String
  | .identifier name => some name
  | .index value _ => expressionRoot? value
  | _ => none

private def isQuantumExpression (context : GenerateContext) (expression : Expression) : Bool :=
  match expressionRoot? expression with
  | some name => context.quantumNames.contains name
  | none => false

private def findSubroutine? (context : GenerateContext) (name : String) :
    Option (Array ArgumentDefinition × Option TypeSpec × Array Statement) :=
  context.declarations.toList.findSome? fun statement => match statement with
    | .defStatement candidate arguments returnType body =>
        if candidate == name then some (arguments, returnType, body) else none
    | _ => none

private def findGate? (context : GenerateContext) (name : String) :
    Option (Array String × Array String × Array Statement) :=
  context.declarations.toList.findSome? fun statement => match statement with
    | .gateDefinition candidate parameters qubits body =>
        if candidate == name then some (parameters, qubits, body) else none
    | _ => none

private def isQuantumType : TypeSpec → Bool
  | .scalar name _ => name == "qubit" || name == "qreg"
  | _ => false

private def isMutableArrayReference : TypeSpec → Bool
  | .arrayRef true _ _ _ => true
  | _ => false

private def expressionOperandCode : Expression → String
  | .identifier name => leanIdentifier name
  | .index (.identifier name) indices =>
      operandCode (.identifier name #[indices])
  | _ => "#[]"

```

### Matching source arguments to callable parameters

Callable definitions decide how each argument is represented. Quantum parameters receive
qubit arrays directly; classical parameters receive parenthesized runtime values.
Mutable array references are identified separately because they require copy-out after
the generated call returns.

```lean
private def callableArgumentsCode
    (definitions : Array ArgumentDefinition) (arguments : Array Expression) : Array String :=
  (definitions.toList.zip arguments.toList).map (fun (definition, argument) =>
    if isQuantumType definition.type then expressionOperandCode argument
    else "(" ++ expressionCode argument ++ ")") |>.toArray

private def assignmentValueCode
    (target : Expression) (operator valueCode : String) : String :=
  match target with
  | .identifier name =>
      let identifier := leanIdentifier name
      s!"{identifier} := QASM.Value.compound {leanString operator} {identifier} ({valueCode})"
  | .index (.identifier name) indices =>
      let identifier := leanIdentifier name
      let indexValues := arrayCode (indices.map expressionCode)
      let current := s!"QASM.Value.index {identifier} {indexValues}"
      let updated := s!"QASM.Value.compound {leanString operator} ({current}) ({valueCode})"
      s!"{identifier} := QASM.Value.setIndex {identifier} {indexValues} ({updated})"
  | _ => "pure ()"

```

### Propagating subroutine results and mutable references

Generated subroutines return an `Except` payload containing the ordinary return value and
an array of mutable-reference values. Invocation lowering evaluates arguments first,
propagates a `RunError` unchanged, then writes each mutable result back to its original
source target in declaration order.

Fresh local names prevent collisions with OpenQASM identifiers. Returning a prelude plus
the final value lets callers preserve evaluation order without duplicating this protocol.

```lean
private def subroutineInvocationFromCodes
    (context : GenerateContext) (name : String) (arguments : Array Expression)
    (argumentValues : Array String) :
    GenerateM (Option (String × String)) := do
  let some (definitions, _, _) := findSubroutine? context name | return none
  let result ← fresh "call_result"
  let payload ← fresh "call_payload"
  let value ← fresh "call_value"
  let actualArguments := arguments
  let argumentCode := (definitions.toList.zip
      (actualArguments.toList.zip argumentValues.toList)).map
    (fun (definition, argument, value) =>
      if isQuantumType definition.type then expressionOperandCode argument
      else "(" ++ value ++ ")") |>.toArray
  let invocation := s!"{context.namespaceName}.{leanIdentifier name} " ++
    String.intercalate " " argumentCode.toList
  let mut writebacks : Array String := #[]
  let mut mutableIndex := 0
  for (definition, argument) in definitions.toList.zip actualArguments.toList do
    if isMutableArrayReference definition.type then
      let returned := s!"{payload}.2[{mutableIndex}]?.getD QASM.Value.unit"
      writebacks := writebacks.push (assignmentValueCode argument "=" returned)
      mutableIndex := mutableIndex + 1
  let code := s!"let {result} ← {invocation}\n" ++
    s!"let {payload} ← match {result} with\n" ++
    s!"| .ok payload => pure payload\n" ++
    s!"| .error error => return .error error\n" ++
    s!"let {value} := {payload}.1" ++
    (if writebacks.isEmpty then "" else "\n" ++ String.intercalate "\n" writebacks.toList)
  pure (some (code, value))

private def subroutineInvocationCode
    (context : GenerateContext) (name : String) (arguments : Array Expression) :
    GenerateM (Option (String × String)) :=
  subroutineInvocationFromCodes context name arguments (arguments.map expressionCode)

private def combinePrelude (parts : Array String) : String :=
  String.intercalate "\n" (parts.toList.filter (fun part => !part.isEmpty))

private def prependPrelude (prelude code : String) : String :=
  if prelude.isEmpty then code else prelude ++ "\n" ++ code

```

## Effectful expression lowering

Most expressions lower directly, but measurements and subroutine calls need monadic
preludes. `lowerExpression` returns both that prelude and the resulting value expression so
statement generation can preserve source evaluation order.

```lean

private partial def lowerExpression (context : GenerateContext) : Expression →
    GenerateM (String × String)
  | expression@(.literal _) | expression@(.identifier _) |
      expression@(.hardwareQubit _) | expression@(.measure _) |
      expression@(.durationOf _) => pure ("", expressionCode expression)
  | .unary operator operand => do
      let (prelude, operand) ← lowerExpression context operand
      pure (prelude, s!"QASM.Value.unary {leanString operator} ({operand})")
  | .binary operator left right => do
      let (leftPrelude, left) ← lowerExpression context left
      let (rightPrelude, right) ← lowerExpression context right
      pure (combinePrelude #[leftPrelude, rightPrelude],
        s!"QASM.Value.binary {leanString operator} ({left}) ({right})")
  | .call name arguments => do
      let mut preludes := #[]
      let mut values := #[]
      for argument in arguments do
        let (prelude, value) ← lowerExpression context argument
        preludes := preludes.push prelude
        values := values.push value
      match ← subroutineInvocationFromCodes context name arguments values with
      | some (invocation, value) =>
          pure (combinePrelude (preludes.push invocation), value)
      | none => pure (combinePrelude preludes,
          s!"QASM.Value.builtin {leanString name} {arrayCode values}")
  | .cast typeName width value => do
      let (widthPrelude, widthCode) ← match width with
        | some width => lowerExpression context width
        | none => pure ("", match typeName with
          | "int" => "QASM.Value.integer __qasm_target.intWidth"
          | "uint" => "QASM.Value.integer __qasm_target.uintWidth"
          | "float" | "complex" => "QASM.Value.integer __qasm_target.floatWidth"
          | "angle" => "QASM.Value.integer __qasm_target.angleWidth"
          | _ => "QASM.Value.integer 1")
      let (valuePrelude, value) ← lowerExpression context value
      pure (combinePrelude #[widthPrelude, valuePrelude],
        s!"QASM.Value.cast {leanString typeName} (QASM.Value.asNat ({widthCode})) ({value})")
  | .arrayCast elementName elementWidth dimensions value => do
      let (widthPrelude, widthCode) ← match elementWidth with
        | some width => lowerExpression context width
        | none => pure ("", match elementName with
          | "int" => "QASM.Value.integer __qasm_target.intWidth"
          | "uint" => "QASM.Value.integer __qasm_target.uintWidth"
          | "float" | "complex" => "QASM.Value.integer __qasm_target.floatWidth"
          | "angle" => "QASM.Value.integer __qasm_target.angleWidth"
          | _ => "QASM.Value.integer 1")
      let mut preludes := #[widthPrelude]
      let mut shape := #[]
      for dimension in dimensions do
        let (prelude, dimension) ← lowerExpression context dimension
        preludes := preludes.push prelude
        shape := shape.push s!"QASM.Value.asNat ({dimension})"
      let (valuePrelude, value) ← lowerExpression context value
      preludes := preludes.push valuePrelude
      let shapeCode := "[" ++ String.intercalate ", " shape.toList ++ "]"
      pure (combinePrelude preludes,
        s!"QASM.Value.castArray {leanString elementName} (QASM.Value.asNat ({widthCode})) {shapeCode} ({value})")
  | .index value indices => do
      let (valuePrelude, value) ← lowerExpression context value
      let mut preludes := #[valuePrelude]
      let mut loweredIndices := #[]
      for index in indices do
        let (prelude, value) ← lowerExpression context index
        preludes := preludes.push prelude
        loweredIndices := loweredIndices.push value
      pure (combinePrelude preludes,
        s!"QASM.Value.index ({value}) {arrayCode loweredIndices}")
  | .range start step stop => do
      let lowerOptional (value : Option Expression) (fallback : String) := do
        match value with
        | some value => lowerExpression context value
        | none => pure ("", fallback)
      let (startPrelude, start) ← lowerOptional start "QASM.Value.integer 0"
      let (stepPrelude, step) ← lowerOptional step "QASM.Value.integer 1"
      let (stopPrelude, stop) ← lowerOptional stop start
      pure (combinePrelude #[startPrelude, stepPrelude, stopPrelude],
        s!"QASM.Value.array (QASM.Value.range ({start}) ({step}) ({stop}))")
  | .set values | .array values => do
      let mut preludes := #[]
      let mut lowered := #[]
      for value in values do
        let (prelude, value) ← lowerExpression context value
        preludes := preludes.push prelude
        lowered := lowered.push value
      pure (combinePrelude preludes, s!"QASM.Value.array {arrayCode lowered}")

```

### Returning from generated bodies

After effectful expressions have produced their preludes, return generation depends on
the current body kind. A program encodes all declared outputs, a subroutine packages its
value with mutable-reference write-backs, and a gate returns only success.

Centralizing this choice prevents explicit `return` statements and implicit fall-through
returns from drifting into different wire formats.

```lean
private def subroutinePayloadCode (context : GenerateContext) (value : String) : String :=
  let arguments := arrayCode (context.mutableArguments.map leanIdentifier)
  s!"({value}, {arguments})"

private def returnValueCode (context : GenerateContext) (value : Option String := none) : String :=
  match context.returnMode with
  | .program => outputReturnCode context.outputs
  | .subroutine =>
      let value := value.getD "QASM.Value.unit"
      s!"return .ok {subroutinePayloadCode context value}"
  | .gate => "return .ok ()"

private def returnCode (context : GenerateContext) (value : Option Expression := none) : String :=
  returnValueCode context (value.map expressionCode)

```

## Native statement generation

Statements become Lean `do` code. Source `if`, `while`, `for`, and `switch` constructs map
to native Lean control flow; quantum effects alone cross `QuantumBackend`, and every
backend error is lifted into `RunError`.

```lean

mutual
private partial def statementsCode
    (context : GenerateContext) (statements : Array Statement) : GenerateM String := do
  let mut parts := #[]
  let mut currentContext := context
  for statement in statements do
    let code ← statementCode currentContext statement
    unless code.isEmpty do parts := parts.push code
    match statement with
    | .qubit name _ | .qreg name _ =>
        currentContext := { currentContext with
          quantumNames := currentContext.quantumNames.push name }
    | .aliasDeclaration name value =>
        if isQuantumExpression currentContext value then
          currentContext := { currentContext with
            quantumNames := currentContext.quantumNames.push name }
    | _ => pure ()
  pure (String.intercalate "\n" parts.toList)

private partial def statementCode (context : GenerateContext) : Statement → GenerateM String
  | .includeFile _ => pure ""
  | .qubit name size | .qreg name size => do
      let temporary ← fresh "allocation"
      let count := size.map expressionCode |>.getD "QASM.Value.integer 1"
      pure <| s!"let {temporary} ← QASM.QuantumBackend.allocate (m := qasmM) (Qubit := qasmQubit) (Error := qasmError) (QASM.Value.asNat ({count}))\n" ++
        s!"let {leanIdentifier name} ← match {temporary} with\n" ++
        s!"| .ok value => pure value\n" ++
        s!"| .error error => return .error (.backend error)"
  | .bit name size | .creg name size =>
      let count := size.map expressionCode |>.getD "QASM.Value.integer 1"
      pure s!"let mut {leanIdentifier name} : QASM.Value := QASM.Value.bits (Array.replicate (QASM.Value.asNat ({count})) false)"
  | .classicalDeclaration _ name (some (.measure source)) => do
      let measured ← fresh "measured"
      let bit ← fresh "bit"
      let result ← fresh "measure_result"
      pure <| s!"let mut {measured} : Array Bool := #[]\n" ++
        s!"for {bit} in {operandCode source} do\n" ++
        indent (s!"let {result} ← QASM.QuantumBackend.measure (m := qasmM) (Qubit := qasmQubit) (Error := qasmError) {bit}\n" ++
          s!"match {result} with\n" ++
          s!"| .error error => return .error (.backend error)\n" ++
          s!"| .ok value => {measured} := {measured}.push value") ++ "\n" ++
        s!"let mut {leanIdentifier name} : QASM.Value := QASM.Value.bits {measured}"
  | .classicalDeclaration _ name (some (.call callee arguments)) => do
      let (prelude, value) ← lowerExpression context (.call callee arguments)
      pure (prependPrelude prelude
        s!"let mut {leanIdentifier name} : QASM.Value := {value}")
  | .classicalDeclaration _type name (some initializer) => do
      let (prelude, value) ← lowerExpression context initializer
      pure (prependPrelude prelude
        s!"let mut {leanIdentifier name} : QASM.Value := {value}")
  | .classicalDeclaration type name none =>
      pure s!"let mut {leanIdentifier name} : QASM.Value := {typeDefaultCode type}"
  | .constDeclaration _ name value =>
      pure s!"let {leanIdentifier name} : QASM.Value := {expressionCode value}"
  | .ioDeclaration true _ name =>
      pure s!"let {leanIdentifier name} : QASM.Value := QASM.ValueCodec.toValue inputs.{leanIdentifier name}"
  | .ioDeclaration false _type name =>
      pure s!"let mut {leanIdentifier name} : QASM.Value := QASM.Value.uninitialized"
  | .aliasDeclaration name value =>
      if isQuantumExpression context value then
        pure s!"let {leanIdentifier name} : Array qasmQubit := {expressionOperandCode value}"
      else do
        let (prelude, value) ← lowerExpression context value
        pure (prependPrelude prelude
          s!"let {leanIdentifier name} : QASM.Value := {value}")
  | .assignment target _operator (.measure source) => do
      let measured ← fresh "measured"
      let bit ← fresh "bit"
      let result ← fresh "measure_result"
      pure <| s!"let mut {measured} : Array Bool := #[]\n" ++
        s!"for {bit} in {operandCode source} do\n" ++
        indent (s!"let {result} ← QASM.QuantumBackend.measure (m := qasmM) (Qubit := qasmQubit) (Error := qasmError) {bit}\n" ++
          s!"match {result} with\n" ++
          s!"| .error error => return .error (.backend error)\n" ++
          s!"| .ok value => {measured} := {measured}.push value") ++ "\n" ++
        assignmentValueCode target "=" (s!"QASM.Value.bits {measured}")
  | .assignment target operator (.call callee arguments) => do
      let (prelude, value) ← lowerExpression context (.call callee arguments)
      pure (prependPrelude prelude (assignmentValueCode target operator value))
  | .assignment target operator value => do
      let (prelude, value) ← lowerExpression context value
      pure (prependPrelude prelude (assignmentValueCode target operator value))
  | .expression (.call callee arguments) => do
      let (prelude, value) ← lowerExpression context (.call callee arguments)
      pure (prependPrelude prelude s!"let _ := {value}")
  | .expression value => do
      let (prelude, value) ← lowerExpression context value
      pure (prependPrelude prelude s!"let _ := {value}")
  | .scope body => do
      let body ← statementsCode context body
      pure ("do\n" ++ indent (if body.isEmpty then "pure ()" else body))
  | .ifStatement condition thenBody elseBody => do
      let (conditionPrelude, condition) ← lowerExpression context condition
      let thenCode ← statementsCode context thenBody
      let thenCode := if thenCode.isEmpty then "pure ()" else thenCode
      match elseBody with
      | none => pure (prependPrelude conditionPrelude
          s!"if QASM.Value.truthy ({condition}) then\n{indent thenCode}")
      | some elseBody =>
          let elseCode ← statementsCode context elseBody
          let elseCode := if elseCode.isEmpty then "pure ()" else elseCode
          pure (prependPrelude conditionPrelude
            s!"if QASM.Value.truthy ({condition}) then\n{indent thenCode}\nelse\n{indent elseCode}")
  | .whileStatement condition body => do
      let (conditionPrelude, condition) ← lowerExpression context condition
      let body ← statementsCode context body
      let body := if body.isEmpty then "pure ()" else body
      if conditionPrelude.isEmpty then
        pure s!"while QASM.Value.truthy ({condition}) do\n{indent body}"
      else
        pure <| "while true do\n" ++ indent (
          conditionPrelude ++ "\n" ++
          s!"if !QASM.Value.truthy ({condition}) then break\n" ++ body)
  | .forStatement type iterator iterable body => do
      let item ← fresh "item"
      let (iterablePrelude, iterable) ← lowerExpression context iterable
      let sequence := s!"QASM.Value.asArray ({iterable})"
      let body ← statementsCode context body
      let binding := s!"let mut {leanIdentifier iterator} : QASM.Value := {scalarCoercionCode type item}"
      let body := if body.isEmpty then binding else binding ++ "\n" ++ body
      pure (prependPrelude iterablePrelude s!"for {item} in {sequence} do\n{indent body}")
  | .switchStatement value cases defaultBody => do
      let controlling ← fresh "switch"
      let (valuePrelude, value) ← lowerExpression context value
      let mut code := prependPrelude valuePrelude s!"let {controlling} := {value}\n"
      for index in [:cases.size] do
        let entry := cases[index]!
        let condition := entry.1.toList.map (fun candidate =>
          s!"QASM.Value.truthy (QASM.Value.binary \"==\" {controlling} ({expressionCode candidate}))")
        let body ← statementsCode context entry.2
        code := code ++ (if index == 0 then "if " else "else if ") ++
          String.intercalate " || " condition ++ " then\n" ++ indent (if body.isEmpty then "pure ()" else body) ++ "\n"
      match defaultBody with
      | some body =>
          let body ← statementsCode context body
          code := code ++ "else\n" ++ indent (if body.isEmpty then "pure ()" else body)
      | none => code := code ++ "else\n  pure ()"
      pure code
  | .breakStatement => pure "break"
  | .continueStatement => pure "continue"
  | .endStatement => pure (returnCode context)
  | .returnStatement (some (.measure source)) => do
      let measured ← fresh "measured"
      let bit ← fresh "bit"
      let result ← fresh "measure_result"
      let returned := match context.returnMode with
        | .subroutine =>
            "return .ok " ++
              subroutinePayloadCode context (s!"QASM.Value.bits {measured}")
        | .program => returnCode context
        | .gate => "return .ok ()"
      pure <| s!"let mut {measured} : Array Bool := #[]\n" ++
        s!"for {bit} in {operandCode source} do\n" ++
        indent (s!"let {result} ← QASM.QuantumBackend.measure (m := qasmM) (Qubit := qasmQubit) (Error := qasmError) {bit}\n" ++
          s!"match {result} with\n" ++
          s!"| .error error => return .error (.backend error)\n" ++
          s!"| .ok value => {measured} := {measured}.push value") ++ "\n" ++ returned
  | .returnStatement (some (.call callee arguments)) => do
      let (prelude, value) ← lowerExpression context (.call callee arguments)
      pure (prependPrelude prelude (returnValueCode context (some value)))
  | .returnStatement (some value) => do
      let (prelude, value) ← lowerExpression context value
      pure (prependPrelude prelude (returnValueCode context (some value)))
  | .returnStatement none => pure (returnValueCode context)
  | .defStatement .. => pure ""
  | .externStatement .. => pure ""
  | .gateDefinition .. => pure ""
  | .gateCall modifiers name parameters _ operands => do
      let mut gatePreludes := #[]
      let mut parameterValues := #[]
      for parameter in parameters do
        let (prelude, value) ← lowerExpression context parameter
        gatePreludes := gatePreludes.push prelude
        parameterValues := parameterValues.push value
      if modifiers.isEmpty then
        match findGate? context name with
        | some _ =>
            let result ← fresh "gate_call_result"
            let arguments := parameterValues.map (fun value => "(" ++ value ++ ")") ++
              operands.map operandCode
            let invocation := s!"{context.namespaceName}.{leanIdentifier ("gate_" ++ name)} " ++
              String.intercalate " " arguments.toList
            return prependPrelude (combinePrelude gatePreludes) <|
              s!"let {result} ← {invocation}\n" ++
              s!"match {result} with\n" ++
              s!"| .ok () => pure ()\n" ++
              s!"| .error error => return .error error"
        | none => pure ()
      let operandArrays ← fresh "gate_operands"
      let widthResult ← fresh "broadcast_result"
      let width ← fresh "broadcast_width"
      let lane ← fresh "broadcast_lane"
      let targets ← fresh "gate_targets"
      let result ← fresh "gate_result"
      let operandArraysCode := arrayCode (operands.map operandCode)
      let parameters := arrayCode (parameterValues.map fun parameter =>
        s!"QASM.Value.asFloat ({parameter})")
      let mut controlSlices : Array (Option (String × String)) :=
        Array.replicate modifiers.size none
      let mut modifierExponents : Array (Option String) :=
        Array.replicate modifiers.size none
      let mut consumedControls := "0"
      for index in [:modifiers.size] do
        match modifiers[index]! with
        | .control _ count =>
            let count := count.map (fun value =>
              s!"QASM.Value.asNat ({expressionCode value})") |>.getD "1"
            controlSlices := controlSlices.set! index (some (consumedControls, count))
            consumedControls := s!"(({consumedControls}) + ({count}))"
        | .power exponent =>
            let (prelude, value) ← lowerExpression context exponent
            gatePreludes := gatePreludes.push prelude
            modifierExponents := modifierExponents.set! index (some value)
        | .inverse => pure ()
      let gateTargets :=
        if consumedControls == "0" then targets
        else s!"({targets}.extract ({consumedControls}) {targets}.size)"
      let mut unitaryPrelude := ""
      let mut unitary :=
        s!"QASM.Unitary.standard {leanString name} {parameters} {gateTargets}"
      match findGate? context name with
      | some (_gateParameters, gateQubits, _) =>
          let recording ← fresh "gate_recording"
          let recordedUnitary ← fresh "recorded_unitary"
          let gateArguments := parameterValues.map (fun value => "(" ++ value ++ ")") ++
            gateQubits.mapIdx (fun index _ =>
              s!"({gateTargets}.extract {index} {index + 1})")
          let invocation := s!"{context.namespaceName}.{leanIdentifier ("gate_" ++ name)} " ++
            String.intercalate " " gateArguments.toList
          unitaryPrelude :=
            s!"let {recording} := Id.run (({invocation} (qasmM := QASM.UnitaryBuilder qasmQubit)).run #[])\n" ++
            s!"let {recordedUnitary} ← match {recording}.1 with\n" ++
            s!"| .ok () => pure (QASM.Unitary.sequence {recording}.2)\n" ++
            s!"| .error _ => return .error (.internal {leanString ("cannot construct modified user gate '" ++ name ++ "'")})"
          unitary := recordedUnitary
      | none => pure ()
      for reverseIndex in [:modifiers.size] do
        let index := modifiers.size - reverseIndex - 1
        unitary := match modifiers[index]! with
          | .inverse => s!"QASM.Unitary.inverse ({unitary})"
          | .power _ =>
              let exponent := modifierExponents[index]!.getD "QASM.Value.float 1.0"
              s!"QASM.Unitary.power (QASM.Value.asFloat ({exponent})) ({unitary})"
          | .control negative _ =>
              let polarity := if negative then "QASM.ControlPolarity.negative" else "QASM.ControlPolarity.positive"
              match controlSlices[index]! with
              | some (offset, count) =>
                  let controls := s!"({targets}.extract ({offset}) (({offset}) + ({count})))"
                  s!"QASM.Unitary.controlled {polarity} {controls} ({unitary})"
              | none => unitary
      pure <| prependPrelude (combinePrelude gatePreludes) <|
        s!"let {operandArrays} : Array (Array qasmQubit) := {operandArraysCode}\n" ++
        s!"let {widthResult} := QASM.broadcastWidth {operandArrays}\n" ++
        s!"let {width} ← match {widthResult} with\n" ++
        s!"| .ok value => pure value\n" ++
        s!"| .error message => return .error (.internal message)\n" ++
        s!"for {lane} in [:{width}] do\n" ++ indent (
          s!"let {targets} := QASM.broadcastLane {operandArrays} {lane}\n" ++
          (if unitaryPrelude.isEmpty then "" else unitaryPrelude ++ "\n") ++
          s!"let {result} ← QASM.QuantumBackend.apply (m := qasmM) (Qubit := qasmQubit) (Error := qasmError) ({unitary})\n" ++
          s!"match {result} with\n| .ok () => pure ()\n| .error error => return .error (.backend error)")
  | .measure source target => do
      let measured ← fresh "measured"
      let bit ← fresh "bit"
      let result ← fresh "measure_result"
      let assignment := match target.bind operandTarget? with
        | some target => assignmentValueCode target "=" (s!"QASM.Value.bits {measured}")
        | none => "pure ()"
      pure <| s!"let mut {measured} : Array Bool := #[]\n" ++
        s!"for {bit} in {operandCode source} do\n" ++
        indent (s!"let {result} ← QASM.QuantumBackend.measure (m := qasmM) (Qubit := qasmQubit) (Error := qasmError) {bit}\n" ++
          s!"match {result} with\n| .error error => return .error (.backend error)\n" ++
          s!"| .ok value => {measured} := {measured}.push value") ++ "\n" ++ assignment
  | .reset operand => do
      let bit ← fresh "reset_qubit"
      let result ← fresh "reset_result"
      pure <| s!"for {bit} in {operandCode operand} do\n" ++ indent (
        s!"let {result} ← QASM.QuantumBackend.reset (m := qasmM) (Qubit := qasmQubit) (Error := qasmError) {bit}\n" ++
        s!"match {result} with\n| .ok () => pure ()\n| .error error => return .error (.backend error)")
  | .barrier operands => do
      let result ← fresh "barrier_result"
      let barrier := if operands.isEmpty then "QASM.Barrier.all" else
        let targets := operands.map operandCode |>.toList
        let targets := match targets with
          | [] => "#[]"
          | first :: rest => rest.foldl (fun acc value => s!"({acc} ++ {value})") first
        s!"QASM.Barrier.targets {targets}"
      pure <| s!"let {result} ← QASM.QuantumBackend.barrier (m := qasmM) (Qubit := qasmQubit) (Error := qasmError) ({barrier})\n" ++
        s!"match {result} with\n| .ok () => pure ()\n| .error error => return .error (.backend error)"
  | .boxStatement _ body => statementsCode context body
  | .delayStatement .. => pure ""
  | .nopStatement _ => pure "pure ()"
  | .pragma _ => pure ""
  | .annotated _ statement => statementCode context statement
  | .calibrationGrammar _ | .calStatement _ | .defcalStatement _ _ => pure ""
end

```

## Dialects, structures, and metadata

Before emitting functions, the compiler detects extended-only statements, constructs the
native input and output structures, and collects annotations and pragmas for reproducible
program metadata.

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

private def structureCommand (name suffix : String) (fields : Array IOField) :
    Except Diagnostic String := do
  let header := s!"structure {name}.{suffix} where"
  if fields.isEmpty then pure header
  else
    let mut declarations := #[]
    for field in fields do
      declarations := declarations.push
        s!"  {leanIdentifier field.name} : {← field.type.toLean}"
    pure (header ++ "\n" ++ String.intercalate "\n" declarations.toList)

private partial def collectMetadataFromStatement
    (metadata : Array String × Array String) (statement : Statement) :
    Array String × Array String :=
  let (annotations, pragmas) := metadata
  match statement with
  | .pragma content => (annotations, pragmas.push content)
  | .annotated values statement =>
      let annotations := values.foldl (fun annotations annotation =>
        annotations.push ("@" ++ annotation.keyword ++
          (annotation.content.map (" " ++ ·) |>.getD ""))) annotations
      collectMetadataFromStatement (annotations, pragmas) statement
  | .scope body | .whileStatement _ body | .forStatement _ _ _ body |
      .gateDefinition _ _ _ body | .boxStatement _ body | .defStatement _ _ _ body =>
      body.foldl collectMetadataFromStatement (annotations, pragmas)
  | .ifStatement _ thenBody elseBody =>
      let metadata := thenBody.foldl collectMetadataFromStatement (annotations, pragmas)
      match elseBody with
      | some body => body.foldl collectMetadataFromStatement metadata
      | none => metadata
  | .switchStatement _ cases defaultBody =>
      let metadata := cases.foldl (fun metadata entry =>
        entry.2.foldl collectMetadataFromStatement metadata) (annotations, pragmas)
      match defaultBody with
      | some body => body.foldl collectMetadataFromStatement metadata
      | none => metadata
  | _ => (annotations, pragmas)

private def collectMetadata (program : Frontend.Program) : Array String × Array String :=
  program.statements.foldl collectMetadataFromStatement (#[], #[])

private abbrev DiagramEnvironment := List (String × Option DiagramOperand)

```

## Building static circuit metadata

Diagram generation is a compile-time interpretation of the checked source, separate from
runtime execution. `DiagramEnvironment` maps source names to known wire sets when possible.
`DiagramState` owns stable display labels and declaration order, while `DiagramM` combines
that state with explicit failure.

Unknown dynamic selections are represented as approximate operands instead of guessed
exact wires. This preserves a useful source diagram without claiming that a runtime branch
or index has already been chosen.

```lean
private structure DiagramState where
  wires : Array String := #[]
  declaredNames : Array String := #[]

private abbrev DiagramM := StateT DiagramState (Except String)

private def diagramDeduplicate (wires : Array Nat) : Array Nat :=
  wires.foldl (fun result wire =>
    if result.contains wire then result else result.push wire) #[]

private def diagramOperandFrom (operands : Array DiagramOperand) : DiagramOperand :=
  { wires := diagramDeduplicate (operands.foldl (fun wires operand =>
      wires ++ operand.wires) #[])
    approximate := operands.any (·.approximate) }

private def diagramBinding? (environment : DiagramEnvironment) (name : String) :
    Option (Option DiagramOperand) :=
  (environment.find? fun binding => binding.1 == name).map fun binding => binding.2

private def diagramOptionalConst (constants : ConstantEnvironment)
    (value : Option Expression) (fallback : Int) : Option Int :=
  match value with
  | none => some fallback
  | some value => (Frontend.evalConstInt constants value).toOption

private def diagramSelectorValues? (constants : ConstantEnvironment) :
    Expression → Option (Array Value)
  | .range start step stop => do
      let start ← diagramOptionalConst constants start 0
      let step ← diagramOptionalConst constants step 1
      let stop ← diagramOptionalConst constants stop start
      pure (Value.range (.integer start) (.integer step) (.integer stop))
  | .set values | .array values =>
      values.mapM fun value =>
        (Frontend.evalConstInt constants value).toOption.map fun value => Value.integer value
  | value =>
      (Frontend.evalConstInt constants value).toOption.map fun value => #[Value.integer value]

private def diagramSelect (constants : ConstantEnvironment)
    (binding : DiagramOperand) (selector : Expression) : DiagramOperand :=
  if binding.approximate then
    { binding with approximate := true }
  else
    match diagramSelectorValues? constants selector with
    | none => { wires := binding.wires, approximate := true }
    | some selectors =>
        let selected := selectors.foldl (fun result selector =>
          match Value.resolveIndex? binding.wires.size selector with
          | .ok index => match binding.wires[index]? with
            | some wire => result.push wire
            | none => result
          | .error _ => result) #[]
        if selected.size == selectors.size then
          { wires := diagramDeduplicate selected }
        else
          { wires := binding.wires, approximate := true }

private partial def diagramQuantumExpression?
    (analysis : Frontend.TypeAnalysis) (environment : DiagramEnvironment) :
    Expression → Except String (Option DiagramOperand)
  | .identifier name => pure (diagramBinding? environment name |>.join)
  | .hardwareQubit index =>
      throw s!"hardware qubit ${index} reached portable diagram generation"
  | .index value indices => do
      let some binding ← diagramQuantumExpression? analysis environment value
        | pure none
      let binding := indices.foldl
        (fun binding selector => diagramSelect analysis.constants binding selector) binding
      pure (some binding)
  | .binary "++" left right => do
      let left ← diagramQuantumExpression? analysis environment left
      let right ← diagramQuantumExpression? analysis environment right
      match left, right with
      | none, none => pure none
      | some left, some right => pure (some (diagramOperandFrom #[left, right]))
      | _, _ => throw "quantum concatenation mixes quantum and classical values"
  | .set values | .array values => do
      let mut operands := #[]
      for value in values do
        match ← diagramQuantumExpression? analysis environment value with
        | some operand => operands := operands.push operand
        | none => return none
      pure (some (diagramOperandFrom operands))
  | _ => pure none

private def diagramOperand
    (analysis : Frontend.TypeAnalysis) (environment : DiagramEnvironment) :
    Operand → Except String DiagramOperand
  | .hardware index =>
      throw s!"hardware qubit ${index} reached portable diagram generation"
  | .identifier name groups => do
      let binding ← match diagramBinding? environment name with
      | some (some binding) => pure binding
      | _ => throw s!"unknown quantum binding '{name}'"
      if groups.isEmpty then pure binding else
        let mut selections := #[]
        for group in groups do
          for selector in group do
            selections := selections.push (diagramSelect analysis.constants binding selector)
        pure (diagramOperandFrom selections)

private def diagramVisibleWires (environment : DiagramEnvironment) : Array Nat :=
  Id.run do
    let mut names := #[]
    let mut wires := #[]
    for (name, binding) in environment do
      unless names.contains name do
        names := names.push name
        match binding with
        | some binding => wires := wires ++ binding.wires
        | none => pure ()
    return diagramDeduplicate wires

private def diagramWidth (analysis : Frontend.TypeAnalysis)
    (name : String) (size : Option Expression) : Except String Nat := do
  let count ← match size with
    | none => pure 1
    | some size => match Frontend.evalConstInt analysis.constants size with
      | .ok count => pure count
      | .error error => throw error.message
  unless count > 0 do
    throw s!"declaration '{name}' has non-positive quantum width {count}"
  pure count.toNat

private def diagramAllocate
    (analysis : Frontend.TypeAnalysis) (name : String) (size : Option Expression) :
    DiagramM DiagramOperand := do
  let count ← match diagramWidth analysis name size with
    | .ok count => pure count
    | .error error => throw error
  let state ← get
  let ordinal := state.declaredNames.foldl
    (fun total declared => if declared == name then total + 1 else total) 1
  let base := if ordinal == 1 then name else name ++ "#" ++ toString ordinal
  let start := state.wires.size
  let labels := Array.range count |>.map fun index =>
    if size.isNone then base else s!"{base}[{index}]"
  modify fun state =>
    { wires := state.wires ++ labels,
      declaredNames := state.declaredNames.push name }
  pure { wires := Array.range count |>.map (start + ·) }

```

### Gate labels, controls, and conventional glyphs

Allocation assigns diagram-only wire indices and disambiguates repeated source names.
Gate helpers then separate two representations: a complete textual label for arbitrary
operations and a conservative conventional glyph for controls, X targets, and swaps.

Control counts must be compile-time constants before exact control circles can be drawn.
Inverse or power modifiers may force a labeled target box even for a familiar gate, which
avoids erasing semantically relevant modifiers from the static view.

```lean
private def diagramModifierLabel : GateModifier → String
  | .inverse => "inv"
  | .power exponent => s!"pow({exponent.toQasm})"
  | .control false none => "ctrl"
  | .control true none => "negctrl"
  | .control false (some count) => s!"ctrl({count.toQasm})"
  | .control true (some count) => s!"negctrl({count.toQasm})"

private def diagramGateLabel (modifiers : Array GateModifier) (name : String)
    (parameters : Array Expression) (designator : Option Expression) : String :=
  let parameters := if parameters.isEmpty then ""
    else s!"({String.intercalate ", " (parameters.toList.map Expression.toQasm)})"
  let designator := designator.map (fun value => s!"[{value.toQasm}]") |>.getD ""
  String.intercalate " @ " ((modifiers.map diagramModifierLabel).toList ++ [name ++ parameters ++ designator])

private def diagramExplicitControls? (constants : ConstantEnvironment)
    (modifiers : Array GateModifier) : Option (Array ControlPolarity) :=
  modifiers.foldl (fun controls modifier => do
    let controls ← controls
    match modifier with
    | .inverse | .power _ => pure controls
    | .control negative none =>
        pure (controls.push (if negative then .negative else .positive))
    | .control negative (some count) => do
        let count ← (Frontend.evalConstInt constants count).toOption
        if count <= 0 then none else
          pure (controls ++ Array.replicate count.toNat
            (if negative then .negative else .positive))) (some #[])

private def diagramBuiltinControls (name : String) : Array ControlPolarity :=
  match name with
  | "cx" | "CX" | "cy" | "cz" | "cp" | "crx" | "cry" | "crz" |
      "ch" | "cu" | "cphase" | "cswap" => #[.positive]
  | "ccx" => #[.positive, .positive]
  | _ => #[]

private def diagramGateTargetLabel (name : String)
    (parameters : Array Expression) (designator : Option Expression) : String :=
  let parameters := if parameters.isEmpty then ""
    else s!"({String.intercalate ", " (parameters.toList.map Expression.toQasm)})"
  let designator := designator.map (fun value => s!"[{value.toQasm}]") |>.getD ""
  match name with
  | "x" | "cx" | "CX" | "ccx" => "X"
  | "y" | "cy" => "Y"
  | "z" | "cz" => "Z"
  | "h" | "ch" => "H"
  | "p" | "cp" => "P" ++ parameters
  | "rx" | "crx" => "Rx" ++ parameters
  | "ry" | "cry" => "Ry" ++ parameters
  | "rz" | "crz" => "Rz" ++ parameters
  | "u" | "cu" => "U" ++ parameters
  | "phase" | "cphase" => "phase" ++ parameters
  | _ => name ++ parameters ++ designator

private def diagramGateGlyph (analysis : Frontend.TypeAnalysis)
    (modifiers : Array GateModifier) (name : String)
    (parameters : Array Expression) (designator : Option Expression) : DiagramGateGlyph :=
  match diagramExplicitControls? analysis.constants modifiers with
  | none => .box
  | some explicitControls =>
      let controls := explicitControls ++ diagramBuiltinControls name
      let hasInverseOrPower := modifiers.any fun modifier => match modifier with
        | .inverse | .power _ => true
        | .control .. => false
      let targetModifiers := modifiers.filterMap fun modifier => match modifier with
        | .inverse | .power _ => some (diagramModifierLabel modifier)
        | .control .. => none
      let target := String.intercalate " @ "
        (targetModifiers.toList ++ [diagramGateTargetLabel name parameters designator])
      if name == "swap" || name == "cswap" then
        if hasInverseOrPower then
          if controls.isEmpty then .box else .controlledBox controls target
        else .swap controls
      else if (name == "x" || name == "cx" || name == "CX" || name == "ccx") &&
          !hasInverseOrPower then
        .controlledX controls
      else if controls.isEmpty then .box else .controlledBox controls target

```

### Emitting diagram metadata as Lean source

The diagram exists first as compiler-side structures. The following encoders serialize
operation kinds, control polarities, glyphs, operands, nested items, and the complete
circuit into Lean expressions embedded in `CheckedProgramInfo`.

This is structural serialization rather than SVG generation. `QASM.Diagram` remains the
sole presentation layer and can change rendering without recompiling the OpenQASM parser
or duplicating compiler logic.

```lean
private def diagramOperationKindCode : DiagramOperationKind → String
  | .gate => "QASM.DiagramOperationKind.gate"
  | .measurement => "QASM.DiagramOperationKind.measurement"
  | .reset => "QASM.DiagramOperationKind.reset"
  | .barrier => "QASM.DiagramOperationKind.barrier"
  | .call => "QASM.DiagramOperationKind.call"

private def diagramControlPolarityCode : ControlPolarity → String
  | .positive => "QASM.ControlPolarity.positive"
  | .negative => "QASM.ControlPolarity.negative"

private def diagramGlyphCode : DiagramGateGlyph → String
  | .box => "QASM.DiagramGateGlyph.box"
  | .controlledX controls =>
      "QASM.DiagramGateGlyph.controlledX " ++ arrayCode (controls.map diagramControlPolarityCode)
  | .controlledBox controls target =>
      "QASM.DiagramGateGlyph.controlledBox " ++
        arrayCode (controls.map diagramControlPolarityCode) ++ " " ++ leanString target
  | .swap controls =>
      "QASM.DiagramGateGlyph.swap " ++ arrayCode (controls.map diagramControlPolarityCode)

private def diagramOperandCode (operand : DiagramOperand) : String :=
  "{ wires := " ++ arrayCode (operand.wires.map toString) ++
    ", approximate := " ++ toString operand.approximate ++ " }"

private def diagramOperationCode (operation : DiagramOperation) : String :=
  "{ kind := " ++ diagramOperationKindCode operation.kind ++
    ", label := " ++ leanString operation.label ++
    ", detail := " ++ leanString operation.detail ++
    ", operands := " ++ arrayCode (operation.operands.map diagramOperandCode) ++
    ", glyph := " ++ diagramGlyphCode operation.glyph ++
    ", classicalTarget := " ++ (match operation.classicalTarget with
      | none => "none"
      | some target => "some " ++ leanString target) ++ " }"

private partial def diagramItemCode : DiagramItem → String
  | .operation operation =>
      "QASM.DiagramItem.operation " ++ diagramOperationCode operation
  | .region label items =>
      "QASM.DiagramItem.region " ++ leanString label ++ " " ++
        arrayCode (items.map diagramItemCode)

private def circuitDiagramCode (diagram : CircuitDiagram) : String :=
  "{ wires := " ++ arrayCode (diagram.wires.map leanString) ++
    ", items := " ++ arrayCode (diagram.items.map diagramItemCode) ++ " }"

private def diagramSubroutine? (program : Frontend.Program) (name : String) :
    Option (Array ArgumentDefinition) :=
  program.statements.toList.findSome? fun statement => match statement with
    | .defStatement candidate arguments _ _ =>
        if candidate == name then some arguments else none
    | _ => none

```

### Discovering quantum effects inside expressions

Subroutine calls can occur inside larger classical expressions yet still perform quantum
operations. `diagramExpressionItems` recursively visits every evaluation position and
inlines the static items contributed by known subroutine bodies.

Arguments are bound to diagram operands when their quantum target is statically known.
Literal and purely classical leaves contribute no circuit item, while nested calls,
indices, ranges, sets, and arrays preserve source evaluation order.

```lean
private partial def diagramExpressionItems
    (program : Frontend.Program) (analysis : Frontend.TypeAnalysis)
    (environment : DiagramEnvironment) (detail : String) :
    Expression → Except String (Array DiagramItem)
  | .literal _ | .identifier _ | .hardwareQubit _ | .measure _ | .durationOf _ => pure #[]
  | .unary _ operand => diagramExpressionItems program analysis environment detail operand
  | .binary _ left right => do
      let left ← diagramExpressionItems program analysis environment detail left
      let right ← diagramExpressionItems program analysis environment detail right
      pure (left ++ right)
  | .call name arguments => do
      let mut items := #[]
      for argument in arguments do
        items := items ++ (← diagramExpressionItems program analysis environment detail argument)
      match diagramSubroutine? program name with
      | none => pure items
      | some definitions =>
          let mut operands := #[]
          for (definition, argument) in definitions.zip arguments do
            if isQuantumType definition.type then
              let some operand ← diagramQuantumExpression? analysis environment argument
                | throw s!"unknown quantum binding in argument to subroutine '{name}'"
              operands := operands.push operand
          if operands.isEmpty then pure items else
            pure (items.push (.operation
              { kind := .call, label := name, detail := detail, operands := operands }))
  | .cast _ width value => do
      let widthItems ← match width with
        | none => pure #[]
        | some width => diagramExpressionItems program analysis environment detail width
      pure (widthItems ++ (← diagramExpressionItems program analysis environment detail value))
  | .arrayCast _ width dimensions value => do
      let mut items ← match width with
        | none => pure #[]
        | some width => diagramExpressionItems program analysis environment detail width
      for dimension in dimensions do
        items := items ++ (← diagramExpressionItems program analysis environment detail dimension)
      pure (items ++ (← diagramExpressionItems program analysis environment detail value))
  | .index value indices => do
      let mut items ← diagramExpressionItems program analysis environment detail value
      for index in indices do
        items := items ++ (← diagramExpressionItems program analysis environment detail index)
      pure items
  | .range start step stop => do
      let mut items := #[]
      for value in #[start, step, stop].filterMap id do
        items := items ++ (← diagramExpressionItems program analysis environment detail value)
      pure items
  | .set values | .array values => do
      let mut items := #[]
      for value in values do
        items := items ++ (← diagramExpressionItems program analysis environment detail value)
      pure items

```

### Diagram regions and measurements

Small adapters lift ordinary `Except` computations into the diagram state monad and omit
empty source regions. Measurement construction records the resolved quantum operand and
an optional classical destination but never chooses a result.

That distinction is essential: diagrams describe possible static effects, whereas
measurement outcomes belong to the runtime backend.

```lean
private def diagramLift (value : Except String α) : DiagramM α :=
  match value with
  | .ok value => pure value
  | .error error => throw error

private def diagramRegion (label : String) (items : Array DiagramItem) : Array DiagramItem :=
  if items.isEmpty then #[] else #[.region label items]

private def diagramMeasurement
    (analysis : Frontend.TypeAnalysis) (environment : DiagramEnvironment)
    (source : Operand) (detail : String) (target : Option String := none) :
    Except String (Array DiagramItem) := do
  let operand ← diagramOperand analysis environment source
  let operation : DiagramOperation :=
    { kind := .measurement, label := "M", «detail» := detail,
      operands := #[operand], classicalTarget := target }
  pure #[.operation operation]

```

### Walking statements into diagram items

The mutually recursive statement walk threads diagram bindings in source order.
Declarations extend the environment, gate calls create operation items, and nested
control-flow bodies become labeled regions. Definitions themselves are skipped at the
top level and expanded only when a source call makes their effects relevant.

Loops and branches are represented once as static regions; the walker does not execute
conditions or unroll runtime iteration counts. Approximation flags expose every place
where exact target wires depend on values unavailable during elaboration.

```lean
mutual
private partial def diagramStatements
    (program : Frontend.Program) (analysis : Frontend.TypeAnalysis)
    (environment : DiagramEnvironment) (statements : Array Statement) :
    DiagramM (DiagramEnvironment × Array DiagramItem) := do
  let mut environment := environment
  let mut items := #[]
  for statement in statements do
    let (nextEnvironment, statementItems) ←
      diagramStatement program analysis environment statement
    environment := nextEnvironment
    items := items ++ statementItems
  pure (environment, items)

private partial def diagramStatement
    (program : Frontend.Program) (analysis : Frontend.TypeAnalysis)
    (environment : DiagramEnvironment) : Statement →
    DiagramM (DiagramEnvironment × Array DiagramItem)
  | .includeFile _ | .pragma _ | .calibrationGrammar _ | .calStatement _ |
      .defcalStatement _ _ | .externStatement _ _ _ | .gateDefinition _ _ _ _ |
      .defStatement _ _ _ _ =>
      pure (environment, #[])
  | .qubit name size | .qreg name size => do
      let binding ← diagramAllocate analysis name size
      pure ((name, some binding) :: environment, #[])
  | .bit name _ | .creg name _ =>
      pure ((name, none) :: environment, #[])
  | .classicalDeclaration type name initializer => do
      let detail := (Statement.classicalDeclaration type name initializer).toQasm
      let items ← match initializer with
      | some (.measure source) => diagramLift (diagramMeasurement analysis environment source detail (some name))
      | some value => diagramLift (diagramExpressionItems program analysis environment detail value)
      | none => pure #[]
      pure ((name, none) :: environment, items)
  | .constDeclaration _ name _ =>
      pure ((name, none) :: environment, #[])
  | .ioDeclaration _ _ name =>
      pure ((name, none) :: environment, #[])
  | .aliasDeclaration name value => do
      match ← diagramLift (diagramQuantumExpression? analysis environment value) with
      | some binding => pure ((name, some binding) :: environment, #[])
      | none =>
          let items ← diagramLift
            (diagramExpressionItems program analysis environment
              (Statement.aliasDeclaration name value).toQasm value)
          pure ((name, none) :: environment, items)
  | .assignment target operator value => do
      let detail := (Statement.assignment target operator value).toQasm
      let items ← match value with
      | .measure source =>
          diagramLift (diagramMeasurement analysis environment source detail (some target.toQasm))
      | value => diagramLift (diagramExpressionItems program analysis environment detail value)
      pure (environment, items)
  | .expression value => do
      let detail := (Statement.expression value).toQasm
      pure (environment, ← diagramLift (diagramExpressionItems program analysis environment detail value))
  | .scope body => do
      let (_, items) ← diagramStatements program analysis environment body
      pure (environment, items)
  | .ifStatement condition thenBody elseBody => do
      let calls ← diagramLift
        (diagramExpressionItems program analysis environment condition.toQasm condition)
      let (_, thenItems) ← diagramStatements program analysis environment thenBody
      let mut items := calls ++ diagramRegion ("if " ++ condition.toQasm) thenItems
      match elseBody with
      | none => pure ()
      | some elseBody =>
          let (_, elseItems) ← diagramStatements program analysis environment elseBody
          items := items ++ diagramRegion "else" elseItems
      pure (environment, items)
  | .whileStatement condition body => do
      let calls ← diagramLift
        (diagramExpressionItems program analysis environment condition.toQasm condition)
      let (_, bodyItems) ← diagramStatements program analysis environment body
      pure (environment, calls ++ diagramRegion ("while " ++ condition.toQasm) bodyItems)
  | .switchStatement value cases defaultBody => do
      let mut items ← diagramLift
        (diagramExpressionItems program analysis environment value.toQasm value)
      for (values, body) in cases do
        let (_, bodyItems) ← diagramStatements program analysis environment body
        let label := "case " ++ String.intercalate ", " (values.toList.map Expression.toQasm)
        items := items ++ diagramRegion label bodyItems
      match defaultBody with
      | none => pure ()
      | some body =>
          let (_, bodyItems) ← diagramStatements program analysis environment body
          items := items ++ diagramRegion "default" bodyItems
      pure (environment, items)
  | .forStatement type iterator iterable body => do
      let detail := (Statement.forStatement type iterator iterable body).toQasm
      let calls ← diagramLift (diagramExpressionItems program analysis environment detail iterable)
      let (_, bodyItems) ← diagramStatements program analysis ((iterator, none) :: environment) body
      let iterableLabel := match iterable with
        | .range _ _ _ => "[" ++ iterable.toQasm ++ "]"
        | _ => iterable.toQasm
      pure (environment, calls ++ diagramRegion ("for " ++ iterator ++ " in " ++ iterableLabel) bodyItems)
  | .breakStatement | .continueStatement | .endStatement =>
      pure (environment, #[])
  | .returnStatement none => pure (environment, #[])
  | .returnStatement (some value) => do
      let detail := (Statement.returnStatement (some value)).toQasm
      let items ← match value with
      | .measure source => diagramLift (diagramMeasurement analysis environment source detail)
      | value => diagramLift (diagramExpressionItems program analysis environment detail value)
      pure (environment, items)
  | .gateCall modifiers name parameters designator operands => do
      let statement : Statement := .gateCall modifiers name parameters designator operands
      let detail := statement.toQasm
      let mut items := #[]
      for parameter in parameters do
        items := items ++ (← diagramLift
          (diagramExpressionItems program analysis environment detail parameter))
      for modifier in modifiers do
        match modifier with
        | .power exponent =>
            items := items ++ (← diagramLift
              (diagramExpressionItems program analysis environment detail exponent))
        | .inverse | .control .. => pure ()
      let resolved ← diagramLift (operands.mapM (diagramOperand analysis environment))
      items := items.push (.operation
        { kind := .gate, label := diagramGateLabel modifiers name parameters designator,
          detail := detail, operands := resolved,
          glyph := diagramGateGlyph analysis modifiers name parameters designator })
      pure (environment, items)
  | .measure source target => do
      let statement : Statement := .measure source target
      let target := target.map Operand.toQasm
      pure (environment, ← diagramLift
        (diagramMeasurement analysis environment source statement.toQasm target))
  | .reset operand => do
      let statement : Statement := .reset operand
      let operand ← diagramLift (diagramOperand analysis environment operand)
      pure (environment, #[.operation
        { kind := .reset, label := "reset", detail := statement.toQasm, operands := #[operand] }])
  | .barrier operands => do
      let statement : Statement := .barrier operands
      let resolved ← if operands.isEmpty then
        pure #[{ wires := diagramVisibleWires environment }]
      else diagramLift (operands.mapM (diagramOperand analysis environment))
      pure (environment, #[.operation
        { kind := .barrier, label := "barrier", detail := statement.toQasm, operands := resolved }])
  | .boxStatement designator body => do
      let (_, items) ← diagramStatements program analysis environment body
      let label := designator.map (fun value => "box [" ++ value.toQasm ++ "]") |>.getD "box"
      pure (environment, diagramRegion label items)
  | .delayStatement _ _ | .nopStatement _ =>
      pure (environment, #[])
  | .annotated _ statement =>
      diagramStatement program analysis environment statement
end

```

### Final program metadata and backend binders

After the recursive walk finishes, `circuitDiagram` combines collected wire labels and
items. `programCommand` embeds that diagram beside target widths, source digests,
annotations, and pragmas in the generated `CheckedProgramInfo`.

`backendBinders` is the portable execution contract shared by generated programs,
subroutines, and gates. It quantifies over the monad, qubit handle, and backend error type
rather than selecting an implementation during elaboration.

```lean
private def circuitDiagram
    (program : Frontend.Program) (analysis : Frontend.TypeAnalysis) : Except String CircuitDiagram :=
  match (diagramStatements program analysis [] program.statements).run {} with
  | .ok ((_, items), state) => .ok { wires := state.wires, items }
  | .error message => .error s!"cannot build circuit diagram: {message}"

private def programCommand
    (name : String) (origins : Array (String × UInt64))
    (options : ElabOptions) (program : Frontend.Program)
    (analysis : Frontend.TypeAnalysis) : Except String String := do
  let diagram ← circuitDiagram program analysis
  let (annotations, pragmas) := collectMetadata program
  let originCode := origins.map fun origin =>
    "{ name := " ++ leanString origin.1 ++ ", digest := " ++ toString origin.2 ++ " }"
  pure <| s!"def {name}.program : QASM.CheckedProgramInfo where\n" ++
    "  target := { intWidth := " ++ toString options.target.intWidth ++
    ", uintWidth := " ++ toString options.target.uintWidth ++
    ", floatWidth := " ++ toString options.target.floatWidth ++
    ", angleWidth := " ++ toString options.target.angleWidth ++ " }\n" ++
    "  origins := " ++ arrayCode originCode ++ "\n" ++
    "  annotations := " ++ arrayCode (annotations.map leanString) ++ "\n" ++
    "  pragmas := " ++ arrayCode (pragmas.map leanString) ++ "\n" ++
    "  diagram := " ++ circuitDiagramCode diagram

private def backendBinders (inhabitedQubit : Bool := false) : String :=
  "{qasmM : Type → Type} {qasmQubit qasmError : Type} [Monad qasmM] " ++
  "[QASM.QuantumBackend qasmM qasmQubit qasmError]" ++
  (if inhabitedQubit then " [Inhabited qasmQubit]" else "")

private def globalConstantBindings (declarations : Array Statement) : Array String :=
  declarations.filterMap fun statement => match statement with
    | .constDeclaration _ name value =>
        some s!"let {leanIdentifier name} : QASM.Value := {expressionCode value}"
    | _ => none

```

## Returns and the source call graph

Generated callable bodies need a fallback return only when control may fall through. The
recursive call-graph walkers inspect every expression and nested statement so directly
recursive subroutines receive an appropriate Lean definition form and backend constraint.

```lean

private partial def definitelyReturns : Statement → Bool
  | .returnStatement _ | .endStatement => true
  | .scope body => body.back?.any definitelyReturns
  | .ifStatement _ thenBody (some elseBody) =>
      thenBody.back?.any definitelyReturns && elseBody.back?.any definitelyReturns
  | .switchStatement _ cases (some defaultBody) =>
      cases.all (fun entry => entry.2.back?.any definitelyReturns) &&
        defaultBody.back?.any definitelyReturns
  | .annotated _ statement => definitelyReturns statement
  | _ => false

mutual
private partial def operandCalls (callee : String) : Operand → Bool
  | .hardware _ => false
  | .identifier _ groups => groups.any fun group => group.any (expressionCalls callee)

private partial def expressionCalls (callee : String) : Expression → Bool
  | .unary _ operand => expressionCalls callee operand
  | .binary _ left right => expressionCalls callee left || expressionCalls callee right
  | .call name arguments => name == callee || arguments.any (expressionCalls callee)
  | .cast _ width value => width.any (expressionCalls callee) || expressionCalls callee value
  | .arrayCast _ width dimensions value =>
      width.any (expressionCalls callee) || dimensions.any (expressionCalls callee) ||
        expressionCalls callee value
  | .index value indices =>
      expressionCalls callee value || indices.any (expressionCalls callee)
  | .range start step stop =>
      start.any (expressionCalls callee) || step.any (expressionCalls callee) ||
        stop.any (expressionCalls callee)
  | .set values | .array values => values.any (expressionCalls callee)
  | .measure operand => operandCalls callee operand
  | _ => false

private partial def statementCalls (callee : String) : Statement → Bool
  | .qubit _ size | .bit _ size | .qreg _ size | .creg _ size =>
      size.any (expressionCalls callee)
  | .gateCall modifiers _ parameters designator operands =>
      parameters.any (expressionCalls callee) || designator.any (expressionCalls callee) ||
        modifiers.any (fun modifier => match modifier with
          | .inverse => false
          | .power exponent => expressionCalls callee exponent
          | .control _ count => count.any (expressionCalls callee)) ||
        operands.any (operandCalls callee)
  | .measure source target =>
      operandCalls callee source || target.any (operandCalls callee)
  | .reset operand => operandCalls callee operand
  | .barrier operands | .nopStatement operands => operands.any (operandCalls callee)
  | .classicalDeclaration _ _ initializer => initializer.any (expressionCalls callee)
  | .constDeclaration _ _ value | .aliasDeclaration _ value | .expression value =>
      expressionCalls callee value
  | .assignment target _ value =>
      expressionCalls callee target || expressionCalls callee value
  | .scope body => body.any (statementCalls callee)
  | .ifStatement condition thenBody elseBody =>
      expressionCalls callee condition || thenBody.any (statementCalls callee) ||
        elseBody.any (fun body => body.any (statementCalls callee))
  | .whileStatement condition body =>
      expressionCalls callee condition || body.any (statementCalls callee)
  | .switchStatement value cases defaultBody =>
      expressionCalls callee value ||
        cases.any (fun entry => entry.1.any (expressionCalls callee) ||
          entry.2.any (statementCalls callee)) ||
        defaultBody.any (fun body => body.any (statementCalls callee))
  | .forStatement _ _ iterable body =>
      expressionCalls callee iterable || body.any (statementCalls callee)
  | .returnStatement value => value.any (expressionCalls callee)
  | .defStatement _ _ _ body | .gateDefinition _ _ _ body =>
      body.any (statementCalls callee)
  | .boxStatement designator body =>
      designator.any (expressionCalls callee) || body.any (statementCalls callee)
  | .delayStatement designator operands =>
      expressionCalls callee designator || operands.any (operandCalls callee)
  | .annotated _ statement => statementCalls callee statement
  | _ => false
end

private def hasDirectRecursion (program : Frontend.Program) : Bool :=
  program.statements.any fun statement => match statement with
    | .defStatement name _ _ body => body.any (statementCalls name)
    | _ => false

```

## Emitting callables, gates, and the runner

Each source subroutine and gate receives a native Lean function. The program runner then
allocates its boundary structures, executes the lowered top-level statements, and decodes
all declared outputs.

```lean

private def subroutineCommand
    (namespaceName : String) (declarations : Array Statement)
    (name : String) (arguments : Array ArgumentDefinition) (body : Array Statement)
    (recursiveProgram : Bool) : String :=
  let parameters := arguments.mapIdx fun index definition =>
    let type := if isQuantumType definition.type then "Array qasmQubit" else "QASM.Value"
    s!"(qasm_argument_{index} : {type})"
  let bindings := arguments.mapIdx fun index definition =>
    if isQuantumType definition.type then
      s!"let {leanIdentifier definition.name} : Array qasmQubit := qasm_argument_{index}"
    else
      s!"let mut {leanIdentifier definition.name} : QASM.Value := qasm_argument_{index}"
  let context : GenerateContext :=
    { namespaceName, declarations,
      quantumNames := arguments.filterMap fun definition =>
        if isQuantumType definition.type then some definition.name else none
      mutableArguments := arguments.filterMap fun definition =>
        if isMutableArrayReference definition.type then some definition.name else none
      returnMode := .subroutine }
  let generated := Id.run ((statementsCode context body).run' 0)
  let fallback := if body.back?.any definitelyReturns then []
    else ["return .ok " ++ subroutinePayloadCode context "QASM.Value.unit"]
  let generated := String.intercalate "\n" ([s!"let __qasm_target := {namespaceName}.program.target"] ++
    (globalConstantBindings declarations).toList ++ bindings.toList ++
    (if generated.isEmpty then [] else [generated]) ++ fallback)
  let keyword := if body.any (statementCalls name) then "partial def" else "def"
  s!"{keyword} {namespaceName}.{leanIdentifier name} " ++ backendBinders recursiveProgram ++ " " ++
    String.intercalate " " parameters.toList ++
    " : qasmM (Except (QASM.RunError qasmError) (QASM.Value × Array QASM.Value)) := do\n" ++
      indent generated

private def gateCommand
    (namespaceName : String) (declarations : Array Statement)
    (name : String) (parameters qubits : Array String) (body : Array Statement) : String :=
  let parameterBinders := parameters.mapIdx fun index _ =>
    s!"(qasm_parameter_{index} : QASM.Value)"
  let qubitBinders := qubits.mapIdx fun index _ =>
    s!"(qasm_gate_qubit_{index} : Array qasmQubit)"
  let parameterBindings := parameters.mapIdx fun index parameter =>
    s!"let {leanIdentifier parameter} : QASM.Value := qasm_parameter_{index}"
  let qubitBindings := qubits.mapIdx fun index qubit =>
    s!"let {leanIdentifier qubit} : Array qasmQubit := qasm_gate_qubit_{index}"
  let context : GenerateContext :=
    { namespaceName, declarations, quantumNames := qubits, returnMode := .gate }
  let generated := Id.run ((statementsCode context body).run' 0)
  let fallback := if body.back?.any definitelyReturns then [] else ["return .ok ()"]
  let generated := String.intercalate "\n" ([s!"let __qasm_target := {namespaceName}.program.target"] ++
    (globalConstantBindings declarations).toList ++ parameterBindings.toList ++
      qubitBindings.toList ++
    (if generated.isEmpty then [] else [generated]) ++ fallback)
  s!"def {namespaceName}.{leanIdentifier ("gate_" ++ name)} " ++ backendBinders ++ " " ++
    String.intercalate " " (parameterBinders.toList ++ qubitBinders.toList) ++
    " : qasmM (Except (QASM.RunError qasmError) Unit) := do\n" ++ indent generated

private def runCommand (name : String) (program : Frontend.Program)
    (analysis : TypeAnalysis) (recursiveProgram : Bool) : String :=
  let outputs := analysis.outputs
  let context : GenerateContext :=
    { namespaceName := name, declarations := program.statements, outputs }
  let body := Id.run ((statementsCode context program.statements).run' 0)
  let body := s!"let __qasm_target := {name}.program.target\n" ++
    (if body.isEmpty then outputReturnCode outputs else
      body ++ "\n" ++ outputReturnCode outputs)
  s!"def {name}.run " ++ backendBinders recursiveProgram ++ s!" (inputs : {name}.Inputs) : " ++
  s!"qasmM (Except (QASM.RunError qasmError) {name}.Outputs) := do\n" ++ indent body

```

## Includes and generated Lean commands

Generated source is reparsed as Lean commands and elaborated in the current environment.
Before that point, semantic capability checks reject backend-dependent programs and include
expansion resolves nested files with cycle detection and origin hashes.

```lean

private def elaborateGenerated (source : String) : CommandElabM Unit := do
  let stx ← match Parser.runParserCategory (← getEnv) `command source "<generated by qasm!>" with
    | .ok stx => pure stx
    | .error message => throwError m!"generated Lean code is invalid:\n{message}\n\n{source}"
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
type rules, then elaborates structures, metadata, declarations, gates, and the runner in
dependency order. Each generated command is checked by Lean before compilation advances.

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
  let recursiveProgram := hasDirectRecursion program
  let inputs ← match structureCommand name "Inputs" analysis.inputs with
    | .ok source => pure source
    | .error error => throwError m!"cannot emit input type: {error}"
  let outputs ← match structureCommand name "Outputs" analysis.outputs with
    | .ok source => pure source
    | .error error => throwError m!"cannot emit output type: {error}"
  elaborateGenerated inputs
  elaborateGenerated outputs
  let metadata ← match programCommand name origins options program analysis with
    | .ok source => pure source
    | .error message => throwError message
  elaborateGenerated metadata
  for statement in program.statements do
    match statement with
    | .defStatement subroutine arguments _ body =>
        elaborateGenerated
          (subroutineCommand name program.statements subroutine arguments body recursiveProgram)
    | .gateDefinition gate parameters qubits body =>
        elaborateGenerated
          (gateCommand name program.statements gate parameters qubits body)
    | _ => pure ()
  elaborateGenerated (runCommand name program analysis recursiveProgram)

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
