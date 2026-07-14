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

structure CheckedProgram where
  program : Program
  constants : ValueEnvironment
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
  if diagnostics.isEmpty then pure ⟨program, environment⟩ else throw diagnostics

end Frontend

abbrev Diagnostic := Frontend.Diagnostic
abbrev CheckedSourceProgram := Frontend.CheckedProgram

def check (program : SourceProgram) : Except (Array Diagnostic) CheckedSourceProgram :=
  Frontend.check program

end QASM
```
