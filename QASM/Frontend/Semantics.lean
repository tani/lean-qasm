    import LiterateLean
    import QASM.Frontend

    open scoped LiterateLean

# Static semantics for OpenQASM source programs

Parsing answers whether tokens have a valid grammatical shape; this pass answers
source-wide questions that require context. It deliberately separates three concerns:

1. evaluate the restricted constant expressions needed by declarations and designators;
2. validate placement of `break`, `continue`, and `return` across nested scopes;
3. collect features whose meaning must be supplied by a concrete backend.

The pass accumulates diagnostics instead of stopping at the first misplaced control-flow
statement. Capability discovery is descriptive rather than rejecting: portable
elaboration can later compare the collected requirements with the backend-independent
subset it supports.

This module has its own small semantic `Value` domain. It is not the execution-time
`QASM.Value`: constants are evaluated before canonical IR exists, and unsupported
floating, complex, or timing cases remain explicit instead of silently adopting runtime
semantics.

One traversal produces independent facts rather than partially lowering the program:

```mermaid
flowchart LR
    AST["parsed AST"] --> Walk["semantic traversal"]
    Walk --> Constants["constant environment"]
    Walk --> Diagnostics["accumulated diagnostics"]
    Walk --> Capabilities["required capabilities"]
    Capabilities --> Elaboration["portable-boundary check"]
```

This fan-out explains why discovering a target-only feature does not suppress unrelated
diagnostics.

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

```

## Primitive constant operations

The environment is a lexical list because constant declarations are processed in source
order and lookup should prefer the most recent binding. Literal helpers remove permitted
separators while preserving explicit failures for unsupported spellings.

`integerBinary` is the closed arithmetic vocabulary available during this semantic pass.
Division and remainder detect zero locally, comparisons return semantic booleans, and
unknown operators produce diagnostics. More general numeric behavior is deferred until
typing has resolved the operand family and the IR interpreter can preserve widths.

```lean
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

```

## Constant expression evaluation

The semantic value domain is intentionally smaller than the runtime carrier. It evaluates
only source constants needed during checking and reports when floating-point, complex, or
timing behavior must be deferred to later phases.

```lean

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
  | .arrayCast _ _ _ value => evalExpression environment value
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

private def foldOption (value : Option α) (operation : β → α → β) (initial : β) : β :=
  match value with
  | some value => operation initial value
  | none => initial

mutual
private partial def operandCapabilities
    (capabilities : Array Capability) (operand : Operand) : Array Capability :=
  match operand with
  | .hardware _ => pushCapability capabilities .physicalQubit
  | .identifier _ indices =>
      indices.foldl (fun capabilities group =>
        group.foldl expressionCapabilities capabilities) capabilities

private partial def expressionCapabilities
    (capabilities : Array Capability) (expression : Expression) : Array Capability :=
  match expression with
  | .literal (.timing raw) =>
      if raw.endsWith "dt" then pushCapability capabilities .timing else capabilities
  | .durationOf _ => pushCapability capabilities .timing
  | .hardwareQubit _ => pushCapability capabilities .physicalQubit
  | .unary _ operand => expressionCapabilities capabilities operand
  | .binary _ left right =>
      expressionCapabilities (expressionCapabilities capabilities left) right
  | .call _ arguments | .set arguments | .array arguments =>
      arguments.foldl expressionCapabilities capabilities
  | .cast _ width value =>
      let capabilities := foldOption width expressionCapabilities capabilities
      expressionCapabilities capabilities value
  | .arrayCast _ width dimensions value =>
      let capabilities := foldOption width expressionCapabilities capabilities
      let capabilities := dimensions.foldl expressionCapabilities capabilities
      expressionCapabilities capabilities value
  | .index value indices =>
      indices.foldl expressionCapabilities (expressionCapabilities capabilities value)
  | .range start step stop =>
      let capabilities := foldOption start expressionCapabilities capabilities
      let capabilities := foldOption step expressionCapabilities capabilities
      foldOption stop expressionCapabilities capabilities
  | .measure operand => operandCapabilities capabilities operand
  | _ => capabilities
end

```

### Type and statement requirements

Types contribute timing requirements through `stretch` and designators, while statements
combine those requirements with their expressions and operands. This direct layer remains
non-recursive over statement bodies so traversal policy stays explicit below.

```lean

private partial def typeCapabilities
    (capabilities : Array Capability) (type : TypeSpec) : Array Capability :=
  match type with
  | .scalar name width =>
      let capabilities :=
        if name == "stretch" then
          pushCapability capabilities .timing
        else capabilities
      foldOption width expressionCapabilities capabilities
  | .array element dimensions =>
      dimensions.foldl expressionCapabilities (typeCapabilities capabilities element)
  | .arrayRef _ element dimensions dimensionCount =>
      let capabilities := typeCapabilities capabilities element
      let capabilities := dimensions.foldl expressionCapabilities capabilities
      foldOption dimensionCount expressionCapabilities capabilities

private def directStatementCapabilities
    (capabilities : Array Capability) (statement : Statement) : Array Capability :=
  match statement with
  | .qubit _ size | .bit _ size | .qreg _ size | .creg _ size =>
      foldOption size expressionCapabilities capabilities
  | .gateCall _ _ parameters designator operands =>
      let capabilities := parameters.foldl expressionCapabilities capabilities
      let capabilities := foldOption designator expressionCapabilities capabilities
      operands.foldl operandCapabilities capabilities
  | .measure source target =>
      let capabilities := operandCapabilities capabilities source
      foldOption target operandCapabilities capabilities
  | .reset operand => operandCapabilities capabilities operand
  | .barrier operands | .nopStatement operands =>
      operands.foldl operandCapabilities capabilities
  | .classicalDeclaration type _ initializer =>
      foldOption initializer expressionCapabilities (typeCapabilities capabilities type)
  | .constDeclaration type _ value =>
      expressionCapabilities (typeCapabilities capabilities type) value
  | .ioDeclaration _ type _ => typeCapabilities capabilities type
  | .aliasDeclaration _ value | .expression value =>
      expressionCapabilities capabilities value
  | .assignment target _ value =>
      expressionCapabilities (expressionCapabilities capabilities target) value
  | .ifStatement condition _ _ | .whileStatement condition _ =>
      expressionCapabilities capabilities condition
  | .switchStatement value cases _ =>
      cases.foldl (fun capabilities entry =>
        entry.1.foldl expressionCapabilities capabilities)
        (expressionCapabilities capabilities value)
  | .forStatement type _ iterable _ =>
      expressionCapabilities (typeCapabilities capabilities type) iterable
  | .returnStatement value => foldOption value expressionCapabilities capabilities
  | .defStatement _ arguments returnType _ =>
      let capabilities := arguments.foldl
        (fun capabilities argument => typeCapabilities capabilities argument.type)
        capabilities
      foldOption returnType typeCapabilities capabilities
  | .externStatement _ arguments returnType =>
      let capabilities := arguments.foldl typeCapabilities capabilities
      foldOption returnType typeCapabilities capabilities
  | .boxStatement designator _ =>
      foldOption designator expressionCapabilities capabilities
  | .delayStatement designator operands =>
      operands.foldl operandCapabilities (expressionCapabilities capabilities designator)
  | .annotated _ statement => directStatementCapabilities capabilities statement
  | _ => capabilities

```

### Recursive capability collection

Direct requirements are only half the story: nested scopes, callables, branches, and loops
may introduce further backend needs. This walk accumulates each capability once across the
complete statement tree.

```lean

private partial def collectCapabilities (statements : Array Statement)
    (initial : Array Capability := #[]) : Array Capability := Id.run do
  let mut capabilities := initial
  for statement in statements do
    capabilities := directStatementCapabilities capabilities statement
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
          | .error _ => pure ()
    | _ => pure ()
  diagnostics := diagnostics ++ controlFlowDiagnostics 0 false program.statements
  if diagnostics.isEmpty then
    pure ⟨program, environment, collectCapabilities program.statements⟩
  else throw diagnostics

```

## Public semantic facade

The outer namespace exposes the diagnostic, capability, and checked-program vocabulary
without leaking the recursive implementation helpers.

```lean

end Frontend

abbrev Diagnostic := Frontend.Diagnostic
abbrev Capability := Frontend.Capability
abbrev CheckedSourceProgram := Frontend.CheckedProgram

def check (program : SourceProgram) : Except (Array Diagnostic) CheckedSourceProgram :=
  Frontend.check program

end QASM
```
<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
