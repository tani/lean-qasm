    import LiterateLean

    import QASM.Runtime
    import QASM.Source
    import QASM.Frontend
    import QASM.Semantics
    import QASM.Typing
    import Lean.Elab.Eval

    open scoped LiterateLean

# OpenQASM elaboration pipeline

The core of `elab_qasm`; it runs parsing, include expansion, type checking,
and native Lean function generation in a single command.

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

private def programCommand
    (name : String) (origins : Array (String × UInt64))
    (options : ElabOptions) (program : Frontend.Program) : String :=
  let (annotations, pragmas) := collectMetadata program
  let originCode := origins.map fun origin =>
    "{ name := " ++ leanString origin.1 ++ ", digest := " ++ toString origin.2 ++ " }"
  s!"def {name}.program : QASM.CheckedProgramInfo where\n" ++
  "  target := { intWidth := " ++ toString options.target.intWidth ++
  ", uintWidth := " ++ toString options.target.uintWidth ++
  ", floatWidth := " ++ toString options.target.floatWidth ++
  ", angleWidth := " ++ toString options.target.angleWidth ++ " }\n" ++
  "  origins := " ++ arrayCode originCode ++ "\n" ++
  "  annotations := " ++ arrayCode (annotations.map leanString) ++ "\n" ++
  "  pragmas := " ++ arrayCode (pragmas.map leanString)

private def backendBinders (inhabitedQubit : Bool := false) : String :=
  "{qasmM : Type → Type} {qasmQubit qasmError : Type} [Monad qasmM] " ++
  "[QASM.QuantumBackend qasmM qasmQubit qasmError]" ++
  (if inhabitedQubit then " [Inhabited qasmQubit]" else "")

private def globalConstantBindings (declarations : Array Statement) : Array String :=
  declarations.filterMap fun statement => match statement with
    | .constDeclaration _ name value =>
        some s!"let {leanIdentifier name} : QASM.Value := {expressionCode value}"
    | _ => none

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

private def elaborateGenerated (source : String) : CommandElabM Unit := do
  let stx ← match Parser.runParserCategory (← getEnv) `command source "<generated by elab_qasm>" with
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
  elaborateGenerated (programCommand name origins options program)
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

private unsafe def evalOptions (syntax? : Option Syntax) : CommandElabM ElabOptions :=
  match syntax? with
  | none => pure {}
  | some stx => liftTermElabM <|
      Term.evalTerm ElabOptions (mkConst ``ElabOptions) stx

private unsafe def evalSource (stx : Syntax) : CommandElabM String :=
  liftTermElabM <| Term.evalTerm String (mkConst ``String) stx

private def resolveSourcePath (path : String) : CommandElabM System.FilePath := do
  let leanPath := System.FilePath.mk (← getFileName)
  pure (leanPath.parent.getD "." / path)

syntax (name := elabQasmSource)
  "elab_qasm" ident "(" term ")" ("using" term)? : command

syntax (name := elabQasmFile)
  "elab_qasm" ident "from" str ("using" term)? : command

```

The command syntax is registered before its elaborators are defined so that the
following quoted patterns can use it.

```lean

@[command_elab elabQasmSource]
meta unsafe def elaborateQasmSource : CommandElab
  | `(command| elab_qasm $name:ident ($qasm:term) $[using $options?]?) => do
      let sourceValue ← evalSource qasm
      let optionsValue ← evalOptions options?
      compileProgram name.getId.toString "<embedded>" sourceValue optionsValue
  | _ => throwUnsupportedSyntax

@[command_elab elabQasmFile]
meta unsafe def elaborateQasmFile : CommandElab
  | `(command| elab_qasm $name:ident from $path:str $[using $options?]?) => do
      let resolved ← resolveSourcePath path.getString
      let qasmText ← try IO.FS.readFile resolved catch error =>
        throwError m!"cannot read OpenQASM source '{resolved}': {error.toMessageData}"
      let optionsValue ← evalOptions options?
      compileProgram name.getId.toString (toString resolved) qasmText optionsValue
  | _ => throwUnsupportedSyntax

end Compiler
end QASM
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
