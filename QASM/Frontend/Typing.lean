    import LiterateLean

    import QASM.Runtime
    import QASM.Frontend
    import QASM.Frontend.Semantics

    open scoped LiterateLean

# OpenQASM type analysis and checking

This module turns the source-oriented AST into facts strong enough for canonical IR
lowering. It resolves target-dependent widths and array shapes, evaluates integer
designators, collects callable signatures, infers expression types, and checks every
statement under its lexical context.

The checker is intentionally distinct from the earlier semantic pass. Semantics handles
source-wide rules and backend capability discovery; typing answers the representation and
compatibility questions required by resolved IR. Successful analysis leaves no unresolved
default width, array extent, callable arity, or operand category at the portable boundary.

Checking proceeds in dependency order: global constants first, signatures second, then
statement bodies. This allows a body to call a declaration that appears later in source
while still requiring widths and shapes to be compile-time values.

```lean
namespace QASM
namespace Frontend

/-- A scalar type after target widths and compile-time designators are resolved. -/
inductive ResolvedScalar where
  | bit (width : Option Nat)
  | sint (width : Nat)
  | uint (width : Nat)
  | float (width : Nat)
  | angle (width : Nat)
  | boolean
  | complex (width : Nat)
  | duration
  | stretch
  | qubit (count : Nat)
  | void
  deriving Repr, Inhabited, BEq

/-- A source type after all shape expressions have been evaluated. -/
inductive ResolvedType where
  | scalar (value : ResolvedScalar)
  | array (element : ResolvedScalar) (shape : Array Nat)
  | arrayRef (mutable : Bool) (element : ResolvedScalar)
      (shape : Option (Array Nat)) (rank : Nat)
  deriving Repr, Inhabited, BEq

```

## Compile-time integer designators

`ResolvedScalar` and `ResolvedType` are the normalized vocabulary consumed by later
checking and elaboration. Source `TypeSpec` nodes may still contain expressions for widths
and dimensions; resolved types contain only concrete natural numbers and explicit array
rank information.

The constant environment stores integers because widths, ranks, and extents require the
integer-evaluable subset. `evalConstInt` supports arithmetic, bitwise operations,
comparisons, logical operators, and casts while rejecting expressions that depend on
runtime state.

```lean
abbrev ConstantEnvironment := List (String × Int)

private def diagnostic (message : String) : Diagnostic := ⟨message⟩

private def lookupConstant (environment : ConstantEnvironment) (name : String) :
    Except Diagnostic Int :=
  match environment.find? (fun entry => entry.1 == name) with
  | some entry => pure entry.2
  | none => throw (diagnostic s!"'{name}' is not a compile-time integer constant")

private def integerLiteral (raw : String) : Int :=
  QASM.Value.integerLiteral raw |>.asInt

/-- Evaluates the integer constant-expression subset required by widths and shapes. -/
partial def evalConstInt (environment : ConstantEnvironment) :
    Expression → Except Diagnostic Int
  | .literal (.integer raw) => pure (integerLiteral raw)
  | .literal (.boolean true) => pure 1
  | .literal (.boolean false) => pure 0
  | .identifier name => lookupConstant environment name
  | .unary "-" operand => (-·) <$> evalConstInt environment operand
  | .unary "~" operand => (~~~·) <$> evalConstInt environment operand
  | .unary "!" operand => do
      pure (if (← evalConstInt environment operand) == 0 then 1 else 0)
  | .binary operator left right => do
      let left ← evalConstInt environment left
      let right ← evalConstInt environment right
      match operator with
      | "+" => pure (left + right)
      | "-" => pure (left - right)
      | "*" => pure (left * right)
      | "/" =>
          if right == 0 then throw (diagnostic "division by zero in constant expression")
          else pure (left / right)
      | "%" =>
          if right == 0 then throw (diagnostic "remainder by zero in constant expression")
          else pure (left % right)
      | "**" =>
          if right < 0 then throw (diagnostic "negative integer exponent in constant expression")
          else pure (left ^ right.toNat)
      | "<<" => pure (left <<< right.toNat)
      | ">>" => pure (left >>> right.toNat)
      | "&" => pure (Int.ofNat (left.natAbs &&& right.natAbs))
      | "|" => pure (Int.ofNat (left.natAbs ||| right.natAbs))
      | "^" => pure (Int.ofNat (left.natAbs ^^^ right.natAbs))
      | "==" => pure (if left == right then 1 else 0)
      | "!=" => pure (if left != right then 1 else 0)
      | "<" => pure (if left < right then 1 else 0)
      | "<=" => pure (if left <= right then 1 else 0)
      | ">" => pure (if left > right then 1 else 0)
      | ">=" => pure (if left >= right then 1 else 0)
      | "&&" => pure (if left != 0 && right != 0 then 1 else 0)
      | "||" => pure (if left != 0 || right != 0 then 1 else 0)
      | _ => throw (diagnostic s!"operator '{operator}' is not constant-evaluable")
  | .cast _ _ value => evalConstInt environment value
  | expression =>
      throw (diagnostic s!"expression is not an integer constant: {expression.toQasm}")

```

## Resolving widths and shapes

Every designator used as a width or extent passes through `positiveNat`, so zero and
negative sizes fail at the point where their purpose is known. Missing scalar widths are
filled from `TargetConfig`; explicit float and complex widths are restricted to the
representations supported by the runtime.

`resolveScalar` handles scalar families, while `resolveType` recursively handles concrete
arrays and array references. Nested source array syntax is normalized to one element type
plus a multidimensional shape, preventing two competing internal representations of the
same layout.

```lean
private def positiveNat (environment : ConstantEnvironment) (label : String)
    (expression : Expression) : Except Diagnostic Nat := do
  let value ← evalConstInt environment expression
  unless value > 0 do throw (diagnostic s!"{label} must be a positive integer, got {value}")
  pure value.toNat

private def resolveWidth (environment : ConstantEnvironment) (label : String)
    (fallback : Nat) (width : Option Expression) : Except Diagnostic Nat := do
  match width with
  | some expression => positiveNat environment s!"{label} width" expression
  | none => pure fallback

private def resolveScalar (target : TargetConfig) (environment : ConstantEnvironment)
    (name : String) (width : Option Expression) : Except Diagnostic ResolvedScalar := do
  match name with
  | "bit" =>
      match width with
      | none => pure (.bit none)
      | some expression => pure (.bit (some (← positiveNat environment "bit width" expression)))
  | "creg" =>
      let count ← resolveWidth environment "creg" 1 width
      pure (.bit (some count))
  | "int" => pure (.sint (← resolveWidth environment "int" target.intWidth width))
  | "uint" => pure (.uint (← resolveWidth environment "uint" target.uintWidth width))
  | "float" =>
      let width ← resolveWidth environment "float" target.floatWidth width
      unless width == 32 || width == 64 do
        throw (diagnostic s!"float width must be 32 or 64, got {width}")
      pure (.float width)
  | "angle" => pure (.angle (← resolveWidth environment "angle" target.angleWidth width))
  | "bool" =>
      if width.isSome then throw (diagnostic "bool does not accept a designator")
      pure .boolean
  | "complex" =>
      let width ← resolveWidth environment "complex component" target.floatWidth width
      unless width == 32 || width == 64 do
        throw (diagnostic s!"complex component width must be 32 or 64, got {width}")
      pure (.complex width)
  | "duration" =>
      if width.isSome then throw (diagnostic "duration does not accept a designator")
      pure .duration
  | "stretch" =>
      if width.isSome then throw (diagnostic "stretch does not accept a designator")
      pure .stretch
  | "qubit" | "qreg" =>
      pure (.qubit (← resolveWidth environment name 1 width))
  | "void" =>
      if width.isSome then throw (diagnostic "void does not accept a designator")
      pure .void
  | _ => throw (diagnostic s!"unknown OpenQASM type '{name}'")

```

### Classical array restrictions

Arrays contain classical scalar values only. Qubits, `void`, and `stretch` cannot become
elements, and an already-resolved array cannot be nested as another element because its
dimensions belong in the single shape vector.

Concrete arrays carry every extent. Array references may instead carry only a rank, which
models callable parameters that accept any extents of a fixed dimensionality. Both forms
enforce OpenQASM's maximum rank before IR lowering.

```lean
private def classicalArrayElement (element : ResolvedType) : Except Diagnostic ResolvedScalar :=
  match element with
  | .scalar scalar =>
      match scalar with
      | .qubit _ | .void | .stretch =>
          throw (diagnostic "array elements must be classical scalar values")
      | _ => pure scalar
  | _ => throw (diagnostic "nested array types are represented by one multidimensional shape")

/-- Resolves target-sized types and compile-time array shapes. -/
partial def resolveType (target : TargetConfig) (environment : ConstantEnvironment) :
    TypeSpec → Except Diagnostic ResolvedType
  | .scalar name width => .scalar <$> resolveScalar target environment name width
  | .array element dimensions => do
      let element ← classicalArrayElement (← resolveType target environment element)
      unless !dimensions.isEmpty && dimensions.size <= 7 do
        throw (diagnostic "OpenQASM arrays must have between 1 and 7 dimensions")
      let shape ← dimensions.mapM (positiveNat environment "array dimension")
      pure (.array element shape)
  | .arrayRef mutable element dimensions dimensionCount => do
      let element ← classicalArrayElement (← resolveType target environment element)
      match dimensionCount with
      | some count =>
          let rank ← positiveNat environment "array-reference rank" count
          unless rank <= 7 do throw (diagnostic "array-reference rank cannot exceed 7")
          pure (.arrayRef mutable element none rank)
      | none =>
          unless !dimensions.isEmpty && dimensions.size <= 7 do
            throw (diagnostic "array references must have between 1 and 7 dimensions")
          let shape ← dimensions.mapM (positiveNat environment "array-reference dimension")
          pure (.arrayRef mutable element (some shape) shape.size)

```


## Analysis products

The checker returns explicit descriptions of I/O fields and callable signatures. Keeping
this summary independent of parser state lets IR lowering resolve declarations and lets
elaboration construct typed boundary structures without repeating type inference.

```lean

structure IOField where
  name : String
  type : ResolvedType
  deriving Repr, Inhabited

structure CallableSignature where
  name : String
  arguments : Array ResolvedType
  returnType : Option ResolvedType
  deriving Repr, Inhabited

structure GateSignature where
  name : String
  parameterCount : Nat
  qubitCount : Nat
  deriving Repr, Inhabited

structure TypeAnalysis where
  constants : ConstantEnvironment
  inputs : Array IOField
  outputs : Array IOField
  callables : Array CallableSignature
  gates : Array GateSignature
  deriving Inhabited

```

## Built-in signatures and lexical scopes

The standard library signatures seed gate checking, while bindings and scope stacks track
mutability and shadowing. Reserved identifiers are rejected at insertion time so every
later lookup can assume a legal source name.

```lean

private def standardGates : Array GateSignature := #[
  ⟨"U", 3, 1⟩, ⟨"gphase", 1, 0⟩,
  ⟨"p", 1, 1⟩, ⟨"x", 0, 1⟩, ⟨"y", 0, 1⟩, ⟨"z", 0, 1⟩,
  ⟨"h", 0, 1⟩, ⟨"s", 0, 1⟩, ⟨"sdg", 0, 1⟩, ⟨"t", 0, 1⟩,
  ⟨"tdg", 0, 1⟩, ⟨"sx", 0, 1⟩, ⟨"rx", 1, 1⟩, ⟨"ry", 1, 1⟩,
  ⟨"rz", 1, 1⟩,
  ⟨"cx", 0, 2⟩, ⟨"cy", 0, 2⟩, ⟨"cz", 0, 2⟩, ⟨"ch", 0, 2⟩,
  ⟨"swap", 0, 2⟩, ⟨"cp", 1, 2⟩, ⟨"crx", 1, 2⟩, ⟨"cry", 1, 2⟩,
  ⟨"crz", 1, 2⟩, ⟨"ccx", 0, 3⟩, ⟨"cswap", 0, 3⟩, ⟨"cu", 4, 2⟩,
  ⟨"CX", 0, 2⟩, ⟨"phase", 1, 1⟩, ⟨"cphase", 1, 2⟩,
  ⟨"id", 0, 1⟩, ⟨"u1", 1, 1⟩, ⟨"u2", 2, 1⟩, ⟨"u3", 3, 1⟩
]

private def builtinGates : Array GateSignature := #[⟨"U", 3, 1⟩, ⟨"gphase", 1, 0⟩]

private structure Binding where
  name : String
  type : ResolvedType
  writable : Bool
  deriving Inhabited

private abbrev Scope := List Binding
private abbrev Scopes := List Scope

private def reservedIdentifiers : List String := [
  "OPENQASM", "include", "defcalgrammar", "def", "cal", "defcal", "gate",
  "extern", "box", "let", "break", "continue", "if", "else", "end",
  "return", "for", "while", "in", "switch", "case", "default", "nop",
  "pragma", "input", "output", "const", "readonly", "mutable", "qreg",
  "qubit", "creg", "bool", "bit", "int", "uint", "float", "angle",
  "complex", "array", "void", "duration", "stretch", "gphase", "inv",
  "pow", "ctrl", "negctrl", "durationof", "delay", "reset", "measure",
  "barrier", "true", "false", "im", "pi", "π", "tau", "τ", "euler", "ℇ",
  "arccos", "arcsin", "arctan", "ceiling", "cos", "exp", "floor", "log",
  "mod", "popcount", "rotl", "rotr", "sin", "sqrt", "tan", "sizeof",
  "real", "imag"
]

private def validateUserIdentifier (name : String) : Except Diagnostic Unit := do
  if reservedIdentifiers.contains name then
    throw (diagnostic s!"'{name}' is a reserved OpenQASM identifier")

private def lookupBinding (scopes : Scopes) (name : String) : Option Binding :=
  scopes.findSome? fun scope => scope.find? (fun binding => binding.name == name)

private def addBinding (scopes : Scopes) (binding : Binding) : Except Diagnostic Scopes := do
  validateUserIdentifier binding.name
  match scopes with
  | [] => pure [[binding]]
  | scope :: rest =>
      if scope.any (fun existing => existing.name == binding.name) then
        throw (diagnostic s!"duplicate declaration '{binding.name}' in the same scope")
      else pure ((binding :: scope) :: rest)

```

## Compatibility and checking context

OpenQASM permits controlled promotion among numeric types but keeps quantum, array, and
condition types distinct. The context gathers those rules with callable signatures and
the current control-flow position.

```lean

private def scalarOf : ResolvedType → Option ResolvedScalar
  | .scalar scalar => some scalar
  | _ => none

private def isNumeric : ResolvedScalar → Bool
  | .bit _ | .sint _ | .uint _ | .float _ | .angle _ | .complex _ | .duration => true
  | _ => false

private def promotedNumeric (left right : ResolvedScalar) : ResolvedScalar :=
  match left, right with
  | .duration, _ | _, .duration => .duration
  | .complex width, _ | _, .complex width => .complex width
  | .float width, _ | _, .float width => .float width
  | .angle width, _ | _, .angle width => .angle width
  | .sint width, _ | _, .sint width => .sint width
  | .uint width, _ | _, .uint width => .uint width
  | .bit width, _ | _, .bit width => .bit width
  | _, _ => .sint 64

private partial def compatible (expected actual : ResolvedType) : Bool :=
  if expected == actual then true else
  match expected, actual with
  | .scalar expected, .scalar actual =>
      (isNumeric expected && isNumeric actual) ||
      (match expected, actual with
       | .boolean, .bit none | .bit none, .boolean => true
       | _, _ => false)
  | .array expectedElement expectedShape, .array actualElement actualShape =>
      expectedShape == actualShape &&
        compatible (.scalar expectedElement) (.scalar actualElement)
  | .arrayRef _ expectedElement (some expectedShape) _, .array actualElement actualShape =>
      expectedShape == actualShape &&
        compatible (.scalar expectedElement) (.scalar actualElement)
  | .arrayRef _ expectedElement none expectedRank, .array actualElement actualShape =>
      expectedRank == actualShape.size &&
        compatible (.scalar expectedElement) (.scalar actualElement)
  | _, _ => false

private def isConditionType : ResolvedType → Bool
  | .scalar .boolean | .scalar (.bit _) => true
  | _ => false

private def isLoopIteratorType : ResolvedType → Bool
  | .scalar (.qubit _) | .scalar .void | .scalar .stretch => false
  | .scalar _ => true
  | _ => false

private structure CheckContext where
  target : TargetConfig
  constants : ConstantEnvironment
  callables : Array CallableSignature
  gates : Array GateSignature
  returnType : Option (Option ResolvedType) := none
  loopDepth : Nat := 0
  topLevel : Bool := true
  inSubroutine : Bool := false
  inGate : Bool := false

private def findCallable? (context : CheckContext) (name : String) : Option CallableSignature :=
  context.callables.find? (fun signature => signature.name == name)

private def findGate? (context : CheckContext) (name : String) : Option GateSignature :=
  context.gates.find? (fun signature => signature.name == name)

private def evalOptionalConst (constants : ConstantEnvironment)
    (expression : Option Expression) (fallback : Int) : Option Int :=
  match expression with
  | none => some fallback
  | some expression => (evalConstInt constants expression).toOption

private def selectionSize? (constants : ConstantEnvironment) : Expression → Option Nat
  | .set values | .array values => some values.size
  | .range start step stop => do
      let first : Int ← evalOptionalConst constants start 0
      let increment : Int ← evalOptionalConst constants step 1
      let last : Int ← evalOptionalConst constants stop first
      if increment == 0 then none
      else if increment > 0 then
        if first > last then some 0 else some ((last - first).toNat / increment.toNat + 1)
      else if first < last then some 0
      else some ((first - last).toNat / increment.natAbs + 1)
  | _ => none

```

## Expression inference

Expression inference follows the source tree recursively and computes one resolved type
for every literal, operator, selection, call, cast, and measurement. The result is not
stored by mutating the AST; callers request it under a `CheckContext` and lexical scope,
which keeps shadowing and callable environments explicit.

Operator cases enforce category compatibility before choosing a result type. Selection
reduces bit widths or array shapes, concatenation combines compatible widths, calls use
collected signatures, and measurement converts quantum operands into classical bits.
Shared helpers apply the same operand-width rules to built-in and user-defined gates.

```lean

private partial def inferExpression (context : CheckContext) (scopes : Scopes) :
    Expression → Except Diagnostic ResolvedType
  | .literal (.integer _) => pure (.scalar (.sint context.target.intWidth))
  | .literal (.float _) => pure (.scalar (.float context.target.floatWidth))
  | .literal (.imaginary _) => pure (.scalar (.complex context.target.floatWidth))
  | .literal (.boolean _) => pure (.scalar .boolean)
  | .literal (.bitstring raw) =>
      pure (.scalar (.bit (some (raw.replace "_" "").length)))
  | .literal (.timing _) => pure (.scalar .duration)
  | .identifier name =>
      match lookupBinding scopes name with
      | some binding => pure binding.type
      | none =>
          if ["pi", "π", "tau", "τ", "euler", "ℇ"].contains name then
            pure (.scalar (.float context.target.floatWidth))
          else throw (diagnostic s!"use of undeclared identifier '{name}'")
  | .hardwareQubit _ => pure (.scalar (.qubit 1))
  | .unary operator operand => do
      let operand ← inferExpression context scopes operand
      if operator == "!" then pure (.scalar .boolean)
      else match scalarOf operand with
        | some scalar =>
            unless isNumeric scalar do
              throw (diagnostic s!"unary '{operator}' requires a numeric operand")
            pure operand
        | none => throw (diagnostic s!"unary '{operator}' cannot be applied to an array")
  | .binary operator left right => do
      let left ← inferExpression context scopes left
      let right ← inferExpression context scopes right
      if ["==", "!=", "<", "<=", ">", ">=", "&&", "||"].contains operator then
        pure (.scalar .boolean)
      else if operator == "++" then
        match left, right with
        | .scalar (.bit (some leftWidth)), .scalar (.bit (some rightWidth)) =>
            pure (.scalar (.bit (some (leftWidth + rightWidth))))
        | .array element leftShape, .array rightElement rightShape =>
            if element == rightElement && leftShape.size == 1 && rightShape.size == 1 then
              pure (.array element #[leftShape[0]! + rightShape[0]!])
            else throw (diagnostic "array concatenation requires matching rank-one element types")
        | _, _ => throw (diagnostic "concatenation requires bit strings or rank-one arrays")
      else
        match scalarOf left, scalarOf right with
        | some left, some right =>
            unless isNumeric left && isNumeric right do
              throw (diagnostic s!"operator '{operator}' requires numeric operands")
            match left, right, operator with
            | .duration, .duration, "/" => pure (.scalar (.float context.target.floatWidth))
            | .duration, .duration, "+" | .duration, .duration, "-" =>
                pure (.scalar .duration)
            | .duration, _, "*" | .duration, _, "/" | _, .duration, "*" =>
                pure (.scalar .duration)
            | .duration, _, _ | _, .duration, _ =>
                throw (diagnostic s!"operator '{operator}' is not defined for duration")
            | _, _, _ => pure (.scalar (promotedNumeric left right))
        | _, _ => throw (diagnostic s!"operator '{operator}' cannot be applied to arrays")
  | .call name arguments => do
      match findCallable? context name with
      | some signature =>
          unless arguments.size == signature.arguments.size do
            throw (diagnostic s!"subroutine '{name}' expects {signature.arguments.size} arguments, got {arguments.size}")
          for pair in signature.arguments.zip arguments do
            let actual ← inferExpression context scopes pair.2
            unless compatible pair.1 actual do
              throw (diagnostic s!"argument of '{name}' has type {repr actual}; expected {repr pair.1}")
          match signature.returnType with
          | some type => pure type
          | none => pure (.scalar .void)
      | none => inferBuiltin context scopes name arguments
  | .cast typeName width value => do
      let _ ← inferExpression context scopes value
      resolveType context.target context.constants (.scalar typeName width)
  | .arrayCast elementName elementWidth dimensions value => do
      let actual ← inferExpression context scopes value
      let expected ← resolveType context.target context.constants
        (.array (.scalar elementName elementWidth) dimensions)
      match expected, actual with
      | .array _ expectedShape, .array _ actualShape =>
          unless expectedShape == actualShape do
            throw (diagnostic s!"array cast cannot change shape from {actualShape} to {expectedShape}")
          pure expected
      | _, _ => throw (diagnostic "array cast requires an array value")
  | .index value indices => do
      let type ← inferExpression context scopes value
      for index in indices do let _ ← inferExpression context scopes index
      let selectedSize := indices[0]?.bind (selectionSize? context.constants)
      match type with
      | .scalar (.qubit _) => pure (.scalar (.qubit (selectedSize.getD 1)))
      | .scalar (.bit (some _)) => pure (.scalar (.bit none))
      | .scalar (.sint _) => pure (.scalar (.bit none))
      | .scalar (.uint _) => pure (.scalar (.bit none))
      | .scalar (.angle _) => pure (.scalar (.bit none))
      | .array element shape =>
          match selectedSize with
          | some count =>
              let remaining := shape.extract 1 shape.size
              pure (.array element (#[count] ++ remaining))
          | none =>
              if indices.size >= shape.size then pure (.scalar element)
              else pure (.array element (shape.extract indices.size shape.size))
      | .arrayRef _ element shape rank =>
          let shape := shape.getD (Array.replicate rank 1)
          match selectedSize with
          | some count => pure (.array element (#[count] ++ shape.extract 1 shape.size))
          | none =>
              if indices.size >= rank then pure (.scalar element)
              else pure (.array element (shape.extract indices.size shape.size))
      | _ => throw (diagnostic "value is not indexable")
  | .range start step stop => do
      let values := #[start, step, stop].filterMap id
      for value in values do
        match scalarOf (← inferExpression context scopes value) with
        | some (.sint _) | some (.uint _) => pure ()
        | _ => throw (diagnostic "range bounds and step must have int or uint type")
      match step with
      | some value =>
          match evalConstInt context.constants value with
          | .ok 0 => throw (diagnostic "range step cannot be zero")
          | _ => pure ()
      | none => pure ()
      pure (.array (.sint context.target.intWidth) #[1])
  | .set values | .array values => do
      if values.isEmpty then throw (diagnostic "empty array/set literals are not valid")
      let first ← inferExpression context scopes values[0]!
      for value in values.extract 1 values.size do
        let actual ← inferExpression context scopes value
        unless compatible first actual do
          throw (diagnostic "array/set literal elements have incompatible types")
      match first with
      | .scalar element => pure (.array element #[values.size])
      | .array element shape => pure (.array element (#[values.size] ++ shape))
      | .arrayRef .. => throw (diagnostic "array references cannot be nested in literals")
  | .measure operand => do
      let count ← checkOperand context scopes operand true
      pure (.scalar (.bit (some count)))
  | .durationOf _ => pure (.scalar .duration)
where
  inferBuiltin (context : CheckContext) (scopes : Scopes) (name : String)
      (arguments : Array Expression) : Except Diagnostic ResolvedType := do
    let inferred ← arguments.mapM (inferExpression context scopes)
    match name, inferred.toList with
    | "sizeof", [_] | "sizeof", [_, _] => pure (.scalar (.uint context.target.uintWidth))
    | "popcount", [_] => pure (.scalar (.uint context.target.uintWidth))
    | "real", [.scalar (.complex width)] | "imag", [.scalar (.complex width)] =>
        pure (.scalar (.float width))
    | "exp", [value@(.scalar (.complex _))] |
        "sqrt", [value@(.scalar (.complex _))] => pure value
    | "mod", [.scalar left, .scalar right] =>
        if isNumeric left && isNumeric right then pure (.scalar (promotedNumeric left right))
        else throw (diagnostic "mod requires integer or floating-point arguments")
    | "sin", [_] | "cos", [_] | "tan", [_] | "arcsin", [_] | "arccos", [_] |
        "arctan", [_] | "exp", [_] | "log", [_] | "sqrt", [_] |
        "floor", [_] | "ceiling", [_] => pure (.scalar (.float context.target.floatWidth))
    | "rotl", [value, _] | "rotr", [value, _] => pure value
    | _, _ => throw (diagnostic s!"unknown builtin or invalid arguments: {name}/{arguments.size}")

  checkOperand (context : CheckContext) (scopes : Scopes) (operand : Operand)
      (quantum : Bool) : Except Diagnostic Nat := do
    match operand with
    | .hardware _ =>
        if quantum then pure 1 else throw (diagnostic "hardware qubit used as a classical operand")
    | .identifier name indices =>
        let binding ← match lookupBinding scopes name with
          | some value => pure value
          | none => throw (diagnostic s!"use of undeclared operand '{name}'")
        let count ← match binding.type with
          | .scalar (.qubit count) =>
              if quantum then pure count else throw (diagnostic s!"'{name}' is quantum")
          | .scalar (.bit none) =>
              if quantum then throw (diagnostic s!"'{name}' is classical") else pure 1
          | .scalar (.bit (some count)) =>
              if quantum then throw (diagnostic s!"'{name}' is classical") else pure count
          | _ => throw (diagnostic s!"'{name}' is not a gate operand")
        for group in indices do for index in group do let _ ← inferExpression context scopes index
        if indices.isEmpty then pure count else pure 1

/-- Infers an expression type from an already-validated analysis and explicit lexical bindings. -/
def TypeAnalysis.inferExpressionType
    (analysis : TypeAnalysis) (target : TargetConfig)
    (bindings : List (String × ResolvedType)) (expression : Expression) :
    Except Diagnostic ResolvedType :=
  let context : CheckContext :=
    { target, constants := analysis.constants, callables := analysis.callables,
      gates := analysis.gates }
  let scope : Scope := bindings.map fun binding =>
    { name := binding.1, type := binding.2, writable := false }
  inferExpression context [scope] expression

```

## Statement and control-flow checking

Statement checking threads lexical scopes through native OpenQASM control flow. Each
nested block receives an explicit scope stack, so declarations, mutability, and shadowing
are checked without a global symbol table.

The same pass enforces writable assignment roots, loop-only control statements,
gate-body restrictions, subroutine return types, callable and gate arities, quantum versus
classical operand widths, and measurement destinations. Because expression inference is
called from the relevant statement case, errors are reported with the operation that
imposes the constraint rather than in a disconnected post-pass.

```lean

private def assignmentRoot? : Expression → Option String
  | .identifier name => some name
  | .index value _ => assignmentRoot? value
  | _ => none

private def allowedInGate : Statement → Bool
  | .gateCall .. | .aliasDeclaration .. | .breakStatement | .continueStatement => true
  | .scope .. | .forStatement .. | .annotated .. | .pragma _ => true
  | _ => false

private partial def checkStatements (context : CheckContext) (initial : Scopes)
    (statements : Array Statement) : Except Diagnostic Scopes := do
  let mut scopes := initial
  for statement in statements do
    if context.inGate && !allowedInGate statement then
      throw (diagnostic "gate bodies may contain only gate calls, aliases, and loop control")
    match statement with
    | .includeFile _ | .pragma _ | .calibrationGrammar _ | .calStatement _ |
        .defcalStatement _ _ => pure ()
    | .qubit name size | .qreg name size =>
        if context.inSubroutine then
          throw (diagnostic "subroutines cannot declare qubits")
        let type ← resolveType context.target context.constants (.scalar "qubit" size)
        scopes ← addBinding scopes ⟨name, type, false⟩
    | .bit name size | .creg name size =>
        let type ← resolveType context.target context.constants (.scalar "bit" size)
        scopes ← addBinding scopes ⟨name, type, true⟩
    | .classicalDeclaration type name initializer =>
        let type ← resolveType context.target context.constants type
        match initializer with
        | some value =>
            let actual ← inferExpression context scopes value
            unless compatible type actual do
              throw (diagnostic s!"initializer for '{name}' has type {repr actual}; expected {repr type}")
        | none => pure ()
        scopes ← addBinding scopes ⟨name, type, true⟩
    | .constDeclaration type name value =>
        let type ← resolveType context.target context.constants type
        match type with
        | .scalar (.qubit _) | .scalar .void | .array .. | .arrayRef .. =>
            throw (diagnostic "const declarations require a classical scalar type")
        | _ => pure ()
        let actual ← inferExpression context scopes value
        unless compatible type actual do
          throw (diagnostic s!"constant '{name}' has type {repr actual}; expected {repr type}")
        scopes ← addBinding scopes ⟨name, type, false⟩
    | .ioDeclaration input type name =>
        unless context.topLevel do throw (diagnostic "input/output declarations are only valid globally")
        let type ← resolveType context.target context.constants type
        match type with
        | .arrayRef .. | .scalar (.qubit _) | .scalar .void =>
            throw (diagnostic "program I/O requires a classical scalar or fixed-shape array type")
        | _ => pure ()
        scopes ← addBinding scopes ⟨name, type, !input⟩
    | .aliasDeclaration name value =>
        let type ← inferExpression context scopes value
        scopes ← addBinding scopes ⟨name, type, false⟩
    | .assignment target _ value =>
        let name ← match assignmentRoot? target with
          | some name => pure name
          | none => throw (diagnostic "assignment target must be an indexed identifier")
        let binding ← match lookupBinding scopes name with
          | some binding => pure binding
          | none => throw (diagnostic s!"assignment to undeclared identifier '{name}'")
        unless binding.writable do throw (diagnostic s!"'{name}' is read-only")
        let expected ← inferExpression context scopes target
        let actual ← inferExpression context scopes value
        unless compatible expected actual do
          throw (diagnostic s!"assignment to '{name}' has type {repr actual}; expected {repr expected}")
    | .expression value => let _ ← inferExpression context scopes value
    | .scope body => let _ ← checkStatements { context with topLevel := false } ([] :: scopes) body
    | .ifStatement condition thenBody elseBody =>
        let conditionType ← inferExpression context scopes condition
        unless isConditionType conditionType do
          throw (diagnostic "if condition must have bool or bit type")
        let _ ← checkStatements { context with topLevel := false } ([] :: scopes) thenBody
        match elseBody with
        | some body => let _ ← checkStatements { context with topLevel := false } ([] :: scopes) body
        | none => pure ()
    | .whileStatement condition body =>
        let conditionType ← inferExpression context scopes condition
        unless isConditionType conditionType do
          throw (diagnostic "while condition must have bool or bit type")
        let loopContext := { { context with topLevel := false } with
          loopDepth := context.loopDepth + 1 }
        let _ ← checkStatements loopContext ([] :: scopes) body
    | .forStatement type iterator iterable body =>
        let iteratorType ← resolveType context.target context.constants type
        unless isLoopIteratorType iteratorType do
          throw (diagnostic "for-loop iterator must have a classical scalar type")
        let iterableType ← inferExpression context scopes iterable
        let elementType ← match iterableType with
          | .scalar (.bit (some _)) => pure (.scalar (.bit none))
          | .array element shape =>
              unless shape.size == 1 do
                throw (diagnostic "for-loop arrays must be one-dimensional")
              pure (.scalar element)
          | _ => throw (diagnostic "for-loop iterable must be a range, set, bit register, or rank-one array")
        unless compatible iteratorType elementType do
          throw (diagnostic s!"for-loop values have type {repr elementType}; iterator expects {repr iteratorType}")
        let inner ← addBinding ([] :: scopes) ⟨iterator, iteratorType, true⟩
        let loopContext := { { context with topLevel := false } with
          loopDepth := context.loopDepth + 1 }
        let _ ← checkStatements loopContext inner body
    | .breakStatement | .continueStatement =>
        unless context.loopDepth > 0 do throw (diagnostic "break/continue is only valid in a loop")
    | .endStatement => pure ()
    | .returnStatement value =>
        match context.returnType with
        | none => throw (diagnostic "return is only valid inside a subroutine")
        | some none =>
            if value.isSome then throw (diagnostic "void subroutine cannot return a value")
        | some (some expected) =>
            let value ← match value with
              | some value => pure value
              | none => throw (diagnostic "non-void subroutine must return a value")
            let actual ← inferExpression context scopes value
            unless compatible expected actual do
              throw (diagnostic s!"return has type {repr actual}; expected {repr expected}")
    | .switchStatement value cases defaultBody =>
        let _ ← inferExpression context scopes value
        for entry in cases do
          for candidate in entry.1 do let _ ← inferExpression context scopes candidate
          let _ ← checkStatements { context with topLevel := false } ([] :: scopes) entry.2
        match defaultBody with
        | some body => let _ ← checkStatements { context with topLevel := false } ([] :: scopes) body
        | none => pure ()
    | .defStatement .. | .externStatement .. | .gateDefinition .. =>
        unless context.topLevel do
          throw (diagnostic "def, extern, and gate declarations are only valid globally")
    | .gateCall modifiers name parameters _ operands =>
        let signature ← match findGate? context name with
          | some signature => pure signature
          | none => throw (diagnostic s!"unknown gate '{name}'")
        unless parameters.size == signature.parameterCount do
          throw (diagnostic s!"gate '{name}' expects {signature.parameterCount} parameters, got {parameters.size}")
        for parameter in parameters do let _ ← inferExpression context scopes parameter
        let mut controlCount := 0
        for modifier in modifiers do
          match modifier with
          | .control _ count =>
              let added ← match count with
                | none => pure 1
                | some count => positiveNat context.constants "control count" count
              controlCount := controlCount + added
          | .power exponent => let _ ← inferExpression context scopes exponent
          | .inverse => pure ()
        unless operands.size == signature.qubitCount + controlCount do
          throw (diagnostic s!"gate '{name}' expects {signature.qubitCount + controlCount} operands after modifiers, got {operands.size}")
        for operand in operands do let _ ← inferExpression context scopes (.measure operand)
    | .measure source target =>
        let _ ← inferExpression context scopes (.measure source)
        match target with
        | some (.hardware _) =>
            throw (diagnostic "measurement result cannot target a hardware qubit")
        | some (.identifier name indices) =>
            let binding ← match lookupBinding scopes name with
              | some binding => pure binding
              | none => throw (diagnostic s!"measurement target '{name}' is undeclared")
            unless binding.writable do throw (diagnostic s!"measurement target '{name}' is read-only")
            match binding.type with
            | .scalar (.bit _) => pure ()
            | _ => throw (diagnostic s!"measurement target '{name}' must have bit type")
            for group in indices do
              for index in group do let _ ← inferExpression context scopes index
        | none => pure ()
    | .reset operand => let _ ← inferExpression context scopes (.measure operand)
    | .barrier operands | .nopStatement operands =>
        for operand in operands do let _ ← inferExpression context scopes (.measure operand)
    | .boxStatement _ body =>
        let _ ← checkStatements { context with topLevel := false } ([] :: scopes) body
    | .delayStatement designator operands =>
        let _ ← inferExpression context scopes designator
        for operand in operands do let _ ← inferExpression context scopes (.measure operand)
    | .annotated _ statement =>
        scopes ← checkStatements context scopes #[statement]
  pure scopes

```

## Declaration collection

A first pass evaluates global integer constants; a second gathers callable and gate
signatures. This ordering makes widths and shapes available before any body is checked.

```lean

private def collectConstants (target : TargetConfig) (program : Program) :
    Except Diagnostic ConstantEnvironment := do
  let mut constants : ConstantEnvironment := []
  for statement in program.statements do
    match statement with
    | .constDeclaration type name value =>
        if constants.any (fun entry => entry.1 == name) then
          throw (diagnostic s!"duplicate constant '{name}'")
        let resolved ← resolveType target constants type
        match resolved with
        | .scalar (.sint _) | .scalar (.uint _) | .scalar (.bit _) |
            .scalar (.angle _) | .scalar .boolean =>
            let value ← evalConstInt constants value
            constants := (name, value) :: constants
        | _ => pure ()
    | _ => pure ()
  pure constants

private def collectSignatures (target : TargetConfig) (constants : ConstantEnvironment)
    (program : Program) : Except Diagnostic (Array CallableSignature × Array GateSignature) := do
  let mut callables := #[]
  let mut gates := builtinGates
  for statement in program.statements do
    match statement with
    | .includeFile "stdgates.inc" =>
        for signature in standardGates do
          if !gates.any (fun existing => existing.name == signature.name) then
            gates := gates.push signature
    | .defStatement name arguments returnType _ =>
        validateUserIdentifier name
        if callables.any (fun signature => signature.name == name) then
          throw (diagnostic s!"duplicate subroutine '{name}'")
        let arguments ← arguments.mapM fun argument => resolveType target constants argument.type
        let returnType ← returnType.mapM (resolveType target constants)
        match returnType with
        | some (.array ..) | some (.arrayRef ..) | some (.scalar (.qubit _)) =>
            throw (diagnostic "subroutine return signatures require a classical scalar type")
        | _ => pure ()
        callables := callables.push ⟨name, arguments, returnType⟩
    | .externStatement name arguments returnType =>
        validateUserIdentifier name
        if callables.any (fun signature => signature.name == name) then
          throw (diagnostic s!"duplicate callable '{name}'")
        let arguments ← arguments.mapM (resolveType target constants)
        let returnType ← returnType.mapM (resolveType target constants)
        match returnType with
        | some (.array ..) | some (.arrayRef ..) | some (.scalar (.qubit _)) =>
            throw (diagnostic "extern return signatures require a classical scalar type")
        | _ => pure ()
        callables := callables.push ⟨name, arguments, returnType⟩
    | .gateDefinition name parameters qubits _ =>
        validateUserIdentifier name
        if gates.any (fun signature => signature.name == name) then
          throw (diagnostic s!"duplicate or reserved gate '{name}'")
        gates := gates.push ⟨name, parameters.size, qubits.size⟩
    | _ => pure ()
  pure (callables, gates)

```

## Whole-program analysis

The public pass composes collection, global checking, and isolated body checking. Its
result is either one complete `TypeAnalysis` or an array-shaped diagnostic interface ready
for the elaborator.

```lean

/-- Performs target-aware type resolution, scope checking, and arity validation. -/
def analyzeTypes (target : TargetConfig) (program : Program) :
    Except (Array Diagnostic) TypeAnalysis := do
  let result : Except Diagnostic TypeAnalysis := do
    let constants ← collectConstants target program
    let (callables, gates) ← collectSignatures target constants program
    let context : CheckContext := { target, constants, callables, gates }
    let global ← checkStatements context [[]] program.statements
    for statement in program.statements do
      match statement with
      | .defStatement name arguments _returnType body =>
          let signature := callables.find? (fun candidate => candidate.name == name) |>.get!
          let constantScope := global.head!.filter fun binding =>
            program.statements.any fun statement => match statement with
              | .constDeclaration _ constantName _ => constantName == binding.name
              | _ => false
          let mut localScopes : Scopes := [[], constantScope]
          for pair in arguments.zip signature.arguments do
            localScopes ← addBinding localScopes ⟨pair.1.name, pair.2,
              match pair.1.type with | .arrayRef false _ _ _ => false | _ => true⟩
          let bodyContext := { { { context with topLevel := false } with
            returnType := some signature.returnType, inSubroutine := true } with loopDepth := 0 }
          let _ ← checkStatements bodyContext localScopes body
      | .gateDefinition _name parameters qubits body =>
          let constantScope := global.head!.filter fun binding =>
            program.statements.any fun statement => match statement with
              | .constDeclaration _ constantName _ => constantName == binding.name
              | _ => false
          let mut localScopes : Scopes := [[], constantScope]
          for parameter in parameters do
            localScopes ← addBinding localScopes ⟨parameter,
              .scalar (.angle target.angleWidth), false⟩
          for qubit in qubits do
            localScopes ← addBinding localScopes ⟨qubit, .scalar (.qubit 1), false⟩
          let bodyContext := { { context with topLevel := false, inGate := true } with loopDepth := 0 }
          let _ ← checkStatements bodyContext localScopes body
      | _ => pure ()
    let mut inputs := #[]
    let mut outputs := #[]
    for statement in program.statements do
      match statement with
      | .ioDeclaration input type name =>
          let field := IOField.mk name (← resolveType target constants type)
          if input then inputs := inputs.push field else outputs := outputs.push field
      | _ => pure ()
    pure ⟨constants, inputs, outputs, callables, gates⟩
  match result with
  | .ok analysis => pure analysis
  | .error error => throw #[error]

end Frontend

```

## Public type-analysis facade

The outer namespace exposes stable aliases and one entry point while leaving checker
implementation details under `Frontend`.

```lean

abbrev ResolvedQASMType := Frontend.ResolvedType
abbrev QASMTypeAnalysis := Frontend.TypeAnalysis

def analyzeTypes (target : TargetConfig) (program : SourceProgram) :
    Except (Array Diagnostic) QASMTypeAnalysis :=
  Frontend.analyzeTypes target program

end QASM
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
