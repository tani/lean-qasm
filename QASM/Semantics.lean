    import LiterateLean
    import QASM.Frontend

    open scoped LiterateLean

# Static semantics for OpenQASM source programs

```lean
namespace QASM
namespace Frontend

inductive Value where
  | integer (value : Int)
  | float (value : Float)
  | boolean (value : Bool)
  | bitstring (value : Array Bool)
  | array (values : Array Value)
  deriving Repr, Inhabited

structure Diagnostic where
  message : String
  deriving Repr, Inhabited, BEq

instance : ToString Diagnostic where
  toString diagnostic := diagnostic.message

abbrev ValueEnvironment := List (String × Value)

private def lookupValue (environment : ValueEnvironment) (name : String) :
    Except Diagnostic Value :=
  match environment.find? (fun entry => entry.1 == name) with
  | some entry => pure entry.2
  | none => throw ⟨s!"unknown constant '{name}'"⟩

private def parseInteger (raw : String) : Except Diagnostic Int :=
  match (raw.replace "_" "").toInt? with
  | some value => pure value
  | none => throw ⟨s!"integer literal '{raw}' is not supported by constant evaluation"⟩

private def bitsOfString (value : String) : Except Diagnostic (Array Bool) := do
  let mut bits := #[]
  for char in value.toList do
    if char == '0' then bits := bits.push false
    else if char == '1' then bits := bits.push true
    else if char != '_' then throw ⟨s!"invalid bitstring digit '{char}'"⟩
  pure bits

private def integerBinary (operator : String) (left right : Int) :
    Except Diagnostic Value :=
  match operator with
  | "+" => pure (.integer (left + right))
  | "-" => pure (.integer (left - right))
  | "*" => pure (.integer (left * right))
  | "/" => if right == 0 then throw ⟨"division by zero"⟩ else pure (.integer (left / right))
  | "%" => if right == 0 then throw ⟨"remainder by zero"⟩ else pure (.integer (left % right))
  | "==" => pure (.boolean (left == right))
  | "!=" => pure (.boolean (left != right))
  | "<" => pure (.boolean (left < right))
  | "<=" => pure (.boolean (left <= right))
  | ">" => pure (.boolean (left > right))
  | ">=" => pure (.boolean (left >= right))
  | _ => throw ⟨s!"operator '{operator}' is not supported for integers"⟩

private partial def evalExpression (environment : ValueEnvironment) :
    Expression → Except Diagnostic Value
  | .literal (.integer raw) => .integer <$> parseInteger raw
  | .literal (.float raw) =>
      throw ⟨s!"floating-point literal '{raw}' is deferred to runtime evaluation"⟩
  | .literal (.boolean value) => pure (.boolean value)
  | .literal (.bitstring value) => .bitstring <$> bitsOfString value
  | .literal (.imaginary _) => throw ⟨"imaginary constant evaluation requires a complex context"⟩
  | .literal (.timing _) => throw ⟨"timing constants are evaluated by the timing layer"⟩
  | .identifier name => lookupValue environment name
  | .unary "-" operand => do
      match ← evalExpression environment operand with
      | .integer value => pure (.integer (-value))
      | _ => throw ⟨"unary '-' requires an integer"⟩
  | .unary "!" operand => do
      match ← evalExpression environment operand with
      | .boolean value => pure (.boolean (!value))
      | _ => throw ⟨"unary '!' requires a boolean"⟩
  | .unary operator _ => throw ⟨s!"unary operator '{operator}' is not yet evaluable"⟩
  | .binary operator left right => do
      let left ← evalExpression environment left
      let right ← evalExpression environment right
      match left, right with
      | .integer left, .integer right => integerBinary operator left right
      | .boolean left, .boolean right =>
          match operator with
          | "&&" => pure (.boolean (left && right))
          | "||" => pure (.boolean (left || right))
          | "==" => pure (.boolean (left == right))
          | "!=" => pure (.boolean (left != right))
          | _ => throw ⟨s!"operator '{operator}' is not supported for booleans"⟩
      | _, _ => throw ⟨s!"incompatible operands for '{operator}'"⟩
  | .cast _ _ value => evalExpression environment value
  | .array values => .array <$> values.mapM (evalExpression environment)
  | .index value indices => do
      let value ← evalExpression environment value
      match value, indices.toList with
      | .array values, [index] =>
          match ← evalExpression environment index with
          | .integer index =>
              match values[index.toNat]? with
              | some value => pure value
              | none => throw ⟨"constant array index out of bounds"⟩
          | _ => throw ⟨"array index must be an integer"⟩
      | _, _ => throw ⟨"constant indexing requires one array index"⟩
  | expression => throw ⟨s!"expression is not constant-evaluable: {expression.toQasm}"⟩

```

## Scope-sensitive checks

Control-flow legality depends on context rather than token shape. The checker
therefore walks every nested scope while carrying loop depth and whether a
subroutine return is permitted.

```lean
private partial def controlFlowDiagnostics
    (loopDepth : Nat) (returnAllowed : Bool) (statements : Array Statement) :
    Array Diagnostic := Id.run do
  let mut diagnostics := #[]
  for statement in statements do
    match statement with
    | .breakStatement =>
        if loopDepth == 0 then
          diagnostics := diagnostics.push ⟨"'break' is only valid inside a loop"⟩
    | .continueStatement =>
        if loopDepth == 0 then
          diagnostics := diagnostics.push ⟨"'continue' is only valid inside a loop"⟩
    | .returnStatement _ =>
        unless returnAllowed do
          diagnostics := diagnostics.push ⟨"'return' is only valid inside a subroutine"⟩
    | .scope body =>
        diagnostics := diagnostics ++ controlFlowDiagnostics loopDepth returnAllowed body
    | .ifStatement _ thenBody elseBody =>
        diagnostics := diagnostics ++ controlFlowDiagnostics loopDepth returnAllowed thenBody
        match elseBody with
        | some body =>
            diagnostics := diagnostics ++ controlFlowDiagnostics loopDepth returnAllowed body
        | none => pure ()
    | .whileStatement _ body | .forStatement _ _ _ body =>
        diagnostics := diagnostics ++ controlFlowDiagnostics (loopDepth + 1) returnAllowed body
    | .switchStatement _ cases defaultBody =>
        for entry in cases do
          diagnostics := diagnostics ++
            controlFlowDiagnostics loopDepth returnAllowed entry.2
        match defaultBody with
        | some body =>
            diagnostics := diagnostics ++ controlFlowDiagnostics loopDepth returnAllowed body
        | none => pure ()
    | .defStatement _ _ _ body =>
        diagnostics := diagnostics ++ controlFlowDiagnostics 0 true body
    | .gateDefinition _ _ _ body =>
        diagnostics := diagnostics ++ controlFlowDiagnostics 0 false body
    | _ => pure ()
  return diagnostics

```

## Backend capability boundary

Valid OpenQASM may still require behavior that the core specification delegates
to a backend. Capability collection records these requirements structurally
instead of rejecting calibration, timing, extern, or physical-qubit syntax
during parsing.

```lean
inductive Capability where
  | externalFunction
  | calibration
  | timing
  | physicalQubit
  deriving Repr, Inhabited, BEq

private def pushCapability (capabilities : Array Capability) (capability : Capability) :
    Array Capability :=
  if capabilities.contains capability then capabilities else capabilities.push capability

private def operandCapabilities (capabilities : Array Capability) (operand : Operand) :
    Array Capability :=
  match operand with
  | .hardware _ => pushCapability capabilities .physicalQubit
  | _ => capabilities

private partial def collectCapabilities (statements : Array Statement)
    (initial : Array Capability := #[]) : Array Capability := Id.run do
  let mut capabilities := initial
  for statement in statements do
    match statement with
    | .externStatement .. =>
        capabilities := pushCapability capabilities .externalFunction
    | .calibrationGrammar .. | .calStatement .. | .defcalStatement .. =>
        capabilities := pushCapability capabilities .calibration
    | .delayStatement _ operands =>
        capabilities := pushCapability capabilities .timing
        for operand in operands do
          capabilities := operandCapabilities capabilities operand
    | .boxStatement designator body =>
        if designator.isSome then capabilities := pushCapability capabilities .timing
        capabilities := collectCapabilities body capabilities
    | .gateCall _ _ _ designator operands =>
        if designator.isSome then capabilities := pushCapability capabilities .timing
        for operand in operands do
          capabilities := operandCapabilities capabilities operand
    | .measure source target =>
        capabilities := operandCapabilities capabilities source
        match target with
        | some operand => capabilities := operandCapabilities capabilities operand
        | none => pure ()
    | .reset operand =>
        capabilities := operandCapabilities capabilities operand
    | .barrier operands | .nopStatement operands =>
        for operand in operands do
          capabilities := operandCapabilities capabilities operand
    | .scope body | .whileStatement _ body | .forStatement _ _ _ body |
        .gateDefinition _ _ _ body =>
        capabilities := collectCapabilities body capabilities
    | .switchStatement _ cases defaultBody =>
        for entry in cases do
          capabilities := collectCapabilities entry.2 capabilities
        match defaultBody with
        | some body => capabilities := collectCapabilities body capabilities
        | none => pure ()
    | .ifStatement _ thenBody elseBody =>
        capabilities := collectCapabilities thenBody capabilities
        match elseBody with
        | some body => capabilities := collectCapabilities body capabilities
        | none => pure ()
    | .defStatement _ _ _ body =>
        capabilities := collectCapabilities body capabilities
    | .annotated _ statement =>
        capabilities := collectCapabilities #[statement] capabilities
    | _ => pure ()
  return capabilities

```

## Checked programs

A checked program retains the source AST, evaluated constants, and the complete
set of backend capabilities discovered by the recursive walk.

```lean
structure CheckedProgram where
  program : Program
  constants : ValueEnvironment
  requiredCapabilities : Array Capability
  deriving Inhabited

def check (program : Program) : Except (Array Diagnostic) CheckedProgram := do
  let mut environment : ValueEnvironment := []
  let mut diagnostics : Array Diagnostic := #[]
  for statement in program.statements do
    match statement with
    | .constDeclaration _ name expression =>
        if environment.any (fun entry => entry.1 == name) then
          diagnostics := diagnostics.push ⟨s!"duplicate constant '{name}'"⟩
        else
          match evalExpression environment expression with
          | .ok value => environment := (name, value) :: environment
          | .error diagnostic => diagnostics := diagnostics.push diagnostic
    | _ => pure ()
  diagnostics := diagnostics ++ controlFlowDiagnostics 0 false program.statements
  if diagnostics.isEmpty then
    pure ⟨program, environment, collectCapabilities program.statements⟩
  else throw diagnostics

end Frontend

abbrev Diagnostic := Frontend.Diagnostic
abbrev Capability := Frontend.Capability
abbrev CheckedSourceProgram := Frontend.CheckedProgram

def check (program : SourceProgram) : Except (Array Diagnostic) CheckedSourceProgram :=
  Frontend.check program

end QASM
```
