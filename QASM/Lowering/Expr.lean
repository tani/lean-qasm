    import LiterateLean
    import QASM.Lowering.Context
    open scoped LiterateLean

# Expression lowering

Checked source expressions become typed IR expressions with resolved identifiers, operators, callables, and literal widths.

The transformation is value-preserving but representation-closing:

```mermaid
flowchart LR
    Source["checked source expression"] --> Resolve["resolve IDs, widths, operators"]
    Resolve --> IR["typed IR expression"]
    Resolve -->|unsupported target feature| Capability["explicit capability node"]
```

SI duration literals use a single base unit. For example,

```math
1\,\mathrm{ns}=10^{-9}\,\mathrm{s},
\qquad
1\,\mu\mathrm{s}=10^{-6}\,\mathrm{s}.
```

```lean
namespace QASM.Lowering

open QASM

```

## Literals and closed operator vocabularies

Literal normalization removes separators without changing the value selected during
typing. SI durations are converted to seconds; target-relative `dt` remains an explicit
unsupported capability. Operator and builtin maps are closed so a source spelling that
survived checking but lacks an IR constructor becomes a lowering diagnostic rather than a
runtime string dispatch.

```lean
private def normalizedFloatText (raw : String) : String :=
  let raw := raw.replace "_" ""
  let raw := if raw.startsWith "." then "0" ++ raw else raw
  if raw.endsWith "." then raw ++ "0" else raw

private def parseFloat (raw : String) : Except QASM.Diagnostic Float := do
  let raw := normalizedFloatText raw
  let json ← match Lean.Json.parse raw with
    | .ok value => pure value
    | .error message => throw (diagnostic s!"invalid floating-point literal '{raw}': {message}")
  match Float.fromJson? json with
  | .ok value => pure value
  | .error message => throw (diagnostic s!"invalid floating-point literal '{raw}': {message}")

private def durationSeconds (raw : String) : Except QASM.Diagnostic Float := do
  let units : List (String × Float) := [
    ("ns", 0.000000001), ("us", 0.000001), ("µs", 0.000001),
    ("ms", 0.001), ("s", 1.0)
  ]
  match units.find? (fun entry => raw.endsWith entry.1) with
  | some (unit, scale) => pure ((← parseFloat (raw.dropEnd unit.length |>.toString)) * scale)
  | none => throw (diagnostic s!"timing literal '{raw}' requires target timing capability")

private def unaryOp : String → Except QASM.Diagnostic QASM.IR.UnaryOp
  | "!" => pure .not
  | "-" => pure .neg
  | "~" => pure .bitnot
  | operator => throw (diagnostic s!"unresolved unary operator '{operator}'")

def binaryOp : String → Except QASM.Diagnostic QASM.IR.BinaryOp
  | "+" => pure .add
  | "-" => pure .sub
  | "*" => pure .mul
  | "/" => pure .div
  | "%" => pure .mod
  | "**" => pure .pow
  | "<<" => pure .shl
  | ">>" => pure .shr
  | "&" => pure .band
  | "|" => pure .bor
  | "^" => pure .bxor
  | "&&" => pure .land
  | "||" => pure .lor
  | "==" => pure .eq
  | "!=" => pure .ne
  | "<" => pure .lt
  | "<=" => pure .le
  | ">" => pure .gt
  | ">=" => pure .ge
  | "++" => pure .concat
  | operator => throw (diagnostic s!"unresolved binary operator '{operator}'")

private def builtin : String → Option QASM.IR.Builtin
  | "popcount" => some .popcount
  | "sizeof" => some .sizeof
  | "real" => some .real
  | "imag" => some .imag
  | "sin" => some .sin
  | "cos" => some .cos
  | "tan" => some .tan
  | "arcsin" => some .arcsin
  | "arccos" => some .arccos
  | "arctan" => some .arctan
  | "sqrt" => some .sqrt
  | "exp" => some .exp
  | "log" => some .log
  | "floor" => some .floor
  | "ceiling" => some .ceiling
  | "mod" => some .mod
  | "rotl" => some .rotl
  | "rotr" => some .rotr
  | _ => none

private def namedConstant? (target : QASM.TargetConfig) : String → Option QASM.IR.Expr
  | "pi" | "π" => some { type := .scalar (.float target.floatWidth), node := .floatLit 3.141592653589793 }
  | "tau" | "τ" => some { type := .scalar (.float target.floatWidth), node := .floatLit 6.283185307179586 }
  | "euler" | "ℇ" => some { type := .scalar (.float target.floatWidth), node := .floatLit 2.718281828459045 }
  | _ => none

```

## Recursive expression translation

Every emitted expression carries its resolved type and source origin. Identifiers become
stable variable or declaration IDs, calls distinguish subroutines, externs, and builtins,
and casts retain only their already-resolved target type. Measurement is deliberately
excluded: the process pass hoists that effect before invoking this pure translation.

```lean
partial def expression (source : QASM.Frontend.Expression) : LowerM QASM.IR.Expr := do
  let context ← get
  let inferred ← inferType source
  let type := resolvedType inferred
  let origin := sourceOrigin context.options
  let node ← match source with
    | .literal (.integer raw) =>
        pure (.intLit (QASM.Value.integerLiteral raw |>.asInt))
    | .literal (.float raw) => pure (.floatLit (← parseFloat raw))
    | .literal (.imaginary raw) =>
        pure (.imaginaryLit (← parseFloat (raw.dropEnd 2 |>.trimAscii |>.toString)))
    | .literal (.boolean value) => pure (.boolLit value)
    | .literal (.bitstring raw) =>
        pure (.bitstringLit (raw.toList.filterMap (fun char =>
          if char == '0' then some false else if char == '1' then some true else none) |>.toArray))
    | .literal (.timing raw) =>
        if raw.endsWith "dt" then pure (.unsupported .timing s!"timing literal {raw}")
        else pure (.durationLit (← durationSeconds raw))
    | .identifier name =>
        match lookupLocalConstant? context name with
        | some value => pure (.intLit value)
        | none => match lookupBinding? context name with
          | some binding => pure (.var binding.var.id)
          | none => match lookupConstant? context name with
            | some constant => pure (.const constant.id)
            | none => match namedConstant? context.options.target name with
              | some value => pure value.node
              | none => throw (diagnostic s!"identifier '{name}' was not resolved during lowering")
    | .hardwareQubit index =>
        pure (.unsupported .physicalQubit s!"physical qubit ${index} in expression")
    | .unary operator operand => pure (.unary (← unaryOp operator) (← expression operand))
    | .binary operator lhs rhs =>
        pure (.binary (← binaryOp operator) (← expression lhs) (← expression rhs))
    | .call name arguments =>
        let arguments ← arguments.mapM expression
        match lookupCallable? context name with
        | some callable => pure (.callSubroutine callable.id arguments)
        | none => match lookupExtern? context name with
          | some external =>
              pure (.unsupported .externalFunction s!"extern #{external.id.value} '{name}'")
          | none => match builtin name with
            | some function => pure (.builtin function arguments)
            | none => throw (diagnostic s!"callable '{name}' was not resolved during lowering")
    | .cast _ _ value | .arrayCast _ _ _ value =>
        pure (.cast type (← expression value))
    | .index value indices => pure (.index (← expression value) (← indices.mapM expression))
    | .range start step stop =>
        pure (.range (← start.mapM expression) (← step.mapM expression) (← stop.mapM expression))
    | .set values => pure (.set (← values.mapM expression))
    | .array values => pure (.array (← values.mapM expression))
    | .measure _ => throw (diagnostic "measurement must lower to Op.measure, not Expr")
    | .durationOf body => pure (.unsupported .timing s!"durationof({body})")
  pure { type, node, origin }

```

## Classical assignment paths

An `LValue` separates its stable root variable from each nested selector group. This
preserves multidimensional source indexing while allowing the interpreter to read and
rebuild the root value exactly once. Physical qubits cannot become classical targets, and
measurement targets preserve bit widths inferred for the selected destination.

```lean
private partial def lvalueParts : QASM.Frontend.Expression →
    Except QASM.Diagnostic (String × Array (Array QASM.Frontend.Expression))
  | .identifier name => pure (name, #[])
  | .index value indices => do
      let (name, groups) ← lvalueParts value
      pure (name, groups.push indices)
  | value => throw (diagnostic s!"invalid lvalue {value.toQasm}")

def lvalue (source : QASM.Frontend.Expression) : LowerM QASM.IR.LValue := do
  let context ← get
  let (name, groups) ← match lvalueParts source with
    | .ok value => pure value
    | .error error => throw error
  let binding ← match lookupBinding? context name with
    | some binding => pure binding
    | none => fail s!"lvalue root '{name}' was not resolved"
  let groups ← groups.mapM fun group => group.mapM expression
  let targetType := resolvedType (← inferType source)
  let result : QASM.IR.LValue :=
    { root := binding.var.id, indices := groups,
      type := targetType, origin := sourceOrigin context.options }
  pure result

def operandLValue (source : QASM.Frontend.Operand) : LowerM QASM.IR.LValue := do
  match source with
  | .hardware index => fail s!"physical qubit ${index} cannot be a classical target"
  | .identifier name groups =>
      let context ← get
      let binding ← match lookupBinding? context name with
        | some binding => pure binding
        | none => fail s!"target '{name}' was not resolved"
      let targetExpression := groups.foldl (init := QASM.Frontend.Expression.identifier name)
        fun value indices => .index value indices
      let type ← inferType targetExpression
      let lowered ← groups.mapM fun group => group.mapM expression
      let targetType := match type with
        | .scalar (.bit width) => QASM.IR.Type.scalar (.bit width)
        | other => resolvedType other
      let result : QASM.IR.LValue :=
        { root := binding.var.id, indices := lowered,
          type := targetType, origin := sourceOrigin context.options }
      pure result

```

## Quantum operands and call arguments

Quantum operands refer to allocated variables plus flattened selectors; they never carry
classical values. Argument lowering follows the checked parameter type: qubits become
quantum operands, array references become lvalues with explicit mutability, and all other
arguments remain typed expressions.

```lean
def quantumOperand (source : QASM.Frontend.Operand) : LowerM QASM.IR.QuantumOperand := do
  match source with
  | .hardware index => pure (.physical index)
  | .identifier name groups =>
      let context ← get
      let binding ← match lookupBinding? context name with
        | some binding => pure binding
        | none => fail s!"quantum operand '{name}' was not resolved"
      unless binding.quantum do fail s!"operand '{name}' is not quantum"
      let indices ← groups.foldl (init := pure #[]) fun result group => do
        pure ((← result) ++ (← group.mapM expression))
      pure (.wire binding.var.id indices false)

partial def quantumExpressionOperand
    (source : QASM.Frontend.Expression) : LowerM QASM.IR.QuantumOperand := do
  match source with
  | .identifier name => quantumOperand (.identifier name #[])
  | .index (.identifier name) indices => quantumOperand (.identifier name #[indices])
  | value => fail s!"quantum argument '{value.toQasm}' is not an operand"

def argument (expected : QASM.Frontend.ResolvedType)
    (source : QASM.Frontend.Expression) : LowerM QASM.IR.Argument :=
  match expected with
  | .scalar (.qubit _) => .quantum <$> quantumExpressionOperand source
  | .arrayRef mutable _ _ _ => do pure (.arrayRef (← lvalue source) mutable)
  | _ => .expr <$> expression source

end QASM.Lowering
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
