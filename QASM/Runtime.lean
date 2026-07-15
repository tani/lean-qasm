    import LiterateLean
    import Lean

    open scoped LiterateLean

# Portable OpenQASM runtime model and value carrier

This module defines the runtime value carrier, backend boundary abstractions,
gate logs, constant conversion, and array conversion foundations used by generated code from `elab`.

```lean
namespace QASM

/-- Target-dependent widths used for unsized OpenQASM classical types. -/
structure TargetConfig where
  intWidth : Nat := 64
  uintWidth : Nat := 64
  floatWidth : Nat := 64
  angleWidth : Nat := 64
  deriving Repr, Inhabited, BEq

namespace TargetConfig

def default : TargetConfig := {}

def validate (config : TargetConfig) : Except String Unit := do
  if config.intWidth == 0 then throw "intWidth must be positive"
  if config.uintWidth == 0 then throw "uintWidth must be positive"
  if config.angleWidth == 0 then throw "angleWidth must be positive"
  unless config.floatWidth == 32 || config.floatWidth == 64 do
    throw "floatWidth must be either 32 or 64"

end TargetConfig

inductive Dialect where
  | v3_0
  | extended
  deriving Repr, Inhabited, BEq

structure ElabOptions where
  target : TargetConfig := .default
  dialect : Dialect := .v3_0
  includePaths : Array System.FilePath := #[]
  deriving Inhabited

```

## Classical values and shaped arrays

The public boundary uses distinct Lean types for each OpenQASM scalar family. Widths
remain in the types where Lean can enforce them, while the array wrappers record the
shape invariant needed when input and output values cross the generated-program boundary.

```lean

/-- The scalar OpenQASM `bit` type.  It is intentionally distinct from `bit[1]`. -/
structure Bit where
  value : Bool
  deriving Repr, Inhabited, BEq, DecidableEq

/-- Unsigned fixed-width OpenQASM integer. -/
structure UInt (width : Nat) where
  bits : BitVec width
  deriving Repr, BEq

/-- Signed two's-complement fixed-width OpenQASM integer. -/
structure SInt (width : Nat) where
  bits : BitVec width
  deriving Repr, BEq

/-- Fixed-width OpenQASM angle, represented modulo `2π`. -/
structure Angle (width : Nat) where
  bits : BitVec width
  deriving Repr, BEq

/-- A target-sized floating-point value.  Elaboration currently accepts widths 32 and 64. -/
structure FloatN (width : Nat) where
  value : Float
  deriving Repr

structure ComplexN (width : Nat) where
  re : FloatN width
  im : FloatN width
  deriving Repr

/-- An OpenQASM duration expressed in SI seconds.  Backend-relative `dt` is not represented here. -/
structure Duration where
  seconds : Float
  deriving Repr, Inhabited, BEq

/-- A dense fixed-shape OpenQASM array used by generated input and output structures. -/
structure FixedArray (element : Type u) (shape : List Nat) where
  data : Array element
  size_eq : data.size = shape.foldl (· * ·) 1

namespace FixedArray

def rank (_ : FixedArray element shape) : Nat := shape.length

def expectedSize (_ : FixedArray element shape) : Nat := shape.foldl (· * ·) 1

end FixedArray

/-- A dense row-major array whose rank is checked by the elaborator. -/
structure NDArray (element : Type u) (rank : Nat) where
  shape : Array Nat
  data : Array element
  rank_eq : shape.size = rank

```

## Portable unitary expressions

Quantum operations are represented as backend-independent data. The standard-gate
expansion deliberately bottoms out in `U`, global phase, sequencing, and modifiers, so
backends receive a compact semantic description instead of source-level syntax.

```lean

inductive ControlPolarity where
  | positive
  | negative
  deriving Repr, Inhabited, BEq

/-- Backend-independent unitary syntax produced by native Lean gate functions. -/
inductive Unitary (qubit : Type u) where
  | U (theta phi lambda : Float) (target : qubit)
  | gphase (gamma : Float)
  | named (name : String) (parameters : Array Float) (targets : Array qubit)
  | sequence (operations : Array (Unitary qubit))
  | inverse (operation : Unitary qubit)
  | power (exponent : Float) (operation : Unitary qubit)
  | controlled (polarity : ControlPolarity) (controls : Array qubit)
      (operation : Unitary qubit)

instance : Nonempty (Unitary qubit) := ⟨.gphase 0.0⟩

namespace Unitary

/-- The exact OpenQASM 3.0 `stdgates.inc` definitions, expressed using only `U` and `gphase`. -/
partial def standard (name : String) (parameters : Array Float) (targets : Array qubit) :
    Unitary qubit :=
  let pi := 3.141592653589793
  let parameter (index : Nat) := parameters[index]?.getD 0.0
  if name == "gphase" then .gphase (parameter 0) else
  match targets.toList with
  | [] => .named name parameters targets
  | first :: rest =>
    let second := rest.head?.getD first
    let third := rest.drop 1 |>.head?.getD first
    let controlled (operation : Unitary qubit) :=
      .controlled .positive #[first] operation
    match name with
    | "U" => .U (parameter 0) (parameter 1) (parameter 2) first
    | "p" => controlled (.gphase (parameter 0))
    | "x" => .sequence #[.U pi 0.0 pi first, .gphase (-pi / 2.0)]
    | "y" => .sequence #[.U pi (pi / 2.0) (pi / 2.0) first, .gphase (-pi / 2.0)]
    | "z" => standard "p" #[pi] #[first]
    | "h" => .sequence #[.U (pi / 2.0) 0.0 pi first, .gphase (-pi / 4.0)]
    | "s" => .power 0.5 (standard "z" #[] #[first])
    | "sdg" => .inverse (.power 0.5 (standard "z" #[] #[first]))
    | "t" => .power 0.5 (standard "s" #[] #[first])
    | "tdg" => .inverse (.power 0.5 (standard "s" #[] #[first]))
    | "sx" => .power 0.5 (standard "x" #[] #[first])
    | "rx" => .sequence #[
        .U (parameter 0) (-pi / 2.0) (pi / 2.0) first,
        .gphase (-parameter 0 / 2.0)]
    | "ry" => .sequence #[
        .U (parameter 0) 0.0 0.0 first, .gphase (-parameter 0 / 2.0)]
    | "rz" => .sequence #[
        .gphase (-parameter 0 / 2.0), .U 0.0 0.0 (parameter 0) first]
    | "cx" => controlled (standard "x" #[] #[second])
    | "cy" => controlled (standard "y" #[] #[second])
    | "cz" => controlled (standard "z" #[] #[second])
    | "cp" => controlled (standard "p" #[parameter 0] #[second])
    | "crx" => controlled (standard "rx" #[parameter 0] #[second])
    | "cry" => controlled (standard "ry" #[parameter 0] #[second])
    | "crz" => controlled (standard "rz" #[parameter 0] #[second])
    | "ch" => controlled (standard "h" #[] #[second])
    | "swap" => .sequence #[
        standard "cx" #[] #[first, second], standard "cx" #[] #[second, first],
        standard "cx" #[] #[first, second]]
    | "ccx" => .controlled .positive #[first, second] (standard "x" #[] #[third])
    | "cswap" => controlled (standard "swap" #[] #[second, third])
    | "cu" => .sequence #[
        standard "p" #[parameter 3 - parameter 0 / 2.0] #[first],
        controlled (.U (parameter 0) (parameter 1) (parameter 2) second)]
    | "CX" => controlled (.U pi 0.0 pi second)
    | "phase" | "u1" => .U 0.0 0.0 (parameter 0) first
    | "cphase" => controlled (standard "phase" #[parameter 0] #[second])
    | "id" => .U 0.0 0.0 0.0 first
    | "u2" => .sequence #[
        .gphase (-(parameter 0 + parameter 1 + pi / 2.0) / 2.0),
        .U (pi / 2.0) (parameter 0) (parameter 1) first]
    | "u3" => .sequence #[
        .gphase (-(parameter 1 + parameter 2 + parameter 0) / 2.0),
        .U (parameter 0) (parameter 1) (parameter 2) first]
    | _ => .named name parameters targets

end Unitary

```

## Broadcasting and the backend boundary

OpenQASM gate operands broadcast lane-wise. Once their widths agree, generated code
uses the `QuantumBackend` class as its only effectful quantum interface.

```lean

/-- Validates OpenQASM's singleton-or-common-width gate broadcasting rule. -/
def broadcastWidth (operands : Array (Array qubit)) : Except String Nat := do
  if operands.isEmpty then return 1
  let width := operands.foldl (fun width operand => max width operand.size) 0
  if width == 0 then throw "cannot apply a gate to an empty operand"
  for operand in operands do
    unless operand.size == 1 || operand.size == width do
      throw s!"gate operand widths are not broadcast-compatible: expected 1 or {width}, got {operand.size}"
  pure width

/-- Selects one lane after `broadcastWidth` has validated all operand sizes. -/
def broadcastLane (operands : Array (Array qubit)) (lane : Nat) : Array qubit :=
  operands.filterMap fun operand => operand[if operand.size == 1 then 0 else lane]?

inductive Barrier (qubit : Type u) where
  | all
  | targets (qubits : Array qubit)

/-- The only execution boundary generated portable QASM programs depend on. -/
class QuantumBackend (m : Type u → Type v) (Qubit Error : outParam (Type u)) where
  allocate : Nat → m (Except Error (Array Qubit))
  apply : Unitary Qubit → m (Except Error Unit)
  measure : Qubit → m (Except Error Bool)
  reset : Qubit → m (Except Error Unit)
  barrier : Barrier Qubit → m (Except Error Unit)

```

## Recording gates and reporting execution failures

User-defined gates are first recorded with a pure backend. Keeping that recording
separate from execution makes whole-gate modifiers portable, while `RunError` names the
failures generated programs may expose independently of a concrete device.

```lean

/-- Failure modes that cannot occur while recording a well-typed gate body. -/
inductive UnitaryBuilderError where
  | nonUnitaryOperation (operation : String)
  deriving Repr, Inhabited

/--
A pure backend used by generated code to turn a user-defined gate invocation into portable
`Unitary` syntax.  This lets modifiers apply to the complete user gate instead of losing its
definition behind a backend-specific name.
-/
abbrev UnitaryBuilder (qubit : Type) := StateM (Array (Unitary qubit))

instance : QuantumBackend (UnitaryBuilder qubit) qubit UnitaryBuilderError where
  allocate _ := pure (.error (.nonUnitaryOperation "qubit allocation in a gate"))
  apply operation := do
    modify (·.push operation)
    pure (.ok ())
  measure _ := pure (.error (.nonUnitaryOperation "measurement in a gate"))
  reset _ := pure (.error (.nonUnitaryOperation "reset in a gate"))
  barrier _ := pure (.error (.nonUnitaryOperation "barrier in a modified gate"))

inductive RunError (backendError : Type u) where
  | backend (error : backendError)
  | indexOutOfBounds (name : String) (index size : Nat)
  | shapeMismatch (name : String) (expected actual : Array Nat)
  | divisionByZero
  | invalidCast (message : String)
  | typeMismatch (expected actual : String)
  | uninitializedRead (name : String)
  | rangeStepZero
  | unsupportedFloatWidth (width : Nat)
  | internal (message : String)
  deriving Repr

```

## The internal runtime value

Generated local variables share one compact carrier. The carrier preserves the width
and shape information needed by OpenQASM operations, then codecs restore precise Lean
types at the external input and output boundary.

```lean

/--
Runtime carrier used inside generated native Lean functions.  The elaborator still resolves every
operator before emitting code; this carrier keeps generated local declarations compact while
retaining OpenQASM's fixed-width metadata at the program boundary.
-/
inductive Value where
  | bit (value : Bool)
  | integer (value : Int)
  | sint (width : Nat) (value : Int)
  | uint (width : Nat) (value : Int)
  | float (value : Float)
  | float32 (value : Float32)
  | complex (real imaginary : Float)
  | complex32 (real imaginary : Float32)
  | angle (width : Nat) (bits : Nat)
  | duration (seconds : Float)
  | boolean (value : Bool)
  | bits (value : Array Bool)
  | array (value : Array Value)
  | uninitialized
  | unit
  deriving Repr, Inhabited, BEq

namespace Value

private def digitValue (char : Char) : Option Nat :=
  if '0' ≤ char && char ≤ '9' then some (char.toNat - '0'.toNat)
  else if 'a' ≤ char && char ≤ 'f' then some (char.toNat - 'a'.toNat + 10)
  else if 'A' ≤ char && char ≤ 'F' then some (char.toNat - 'A'.toNat + 10)
  else none

def integerLiteral (raw : String) : Value :=
  let text := raw.replace "_" ""
  let (base, digits) :=
    if text.startsWith "0b" || text.startsWith "0B" then (2, text.drop 2)
    else if text.startsWith "0o" || text.startsWith "0O" then (8, text.drop 2)
    else if text.startsWith "0x" || text.startsWith "0X" then (16, text.drop 2)
    else (10, text.toSlice)
  let number := digits.toString.toList.foldl (fun acc char =>
    match digitValue char with
    | some digit => acc * base + digit
    | none => acc) 0
  .integer number

def bitstringLiteral (raw : String) : Value :=
  .bits ((raw.toList.filterMap fun char =>
    if char == '0' then some false else if char == '1' then some true else none).reverse.toArray)

def typeName : Value → String
  | .bit _ => "bit"
  | .integer _ => "integer literal"
  | .sint width _ => s!"int[{width}]"
  | .uint width _ => s!"uint[{width}]"
  | .float _ => "float[64]"
  | .float32 _ => "float[32]"
  | .complex .. => "complex[float[64]]"
  | .complex32 .. => "complex[float[32]]"
  | .angle width _ => s!"angle[{width}]"
  | .duration _ => "duration"
  | .boolean _ => "bool"
  | .bits valueBits => s!"bit[{valueBits.size}]"
  | .array _ => "array"
  | .uninitialized => "uninitialized"
  | .unit => "void"

def truthy : Value → Bool
  | .bit value => value
  | .boolean value => value
  | .integer value => value != 0
  | .sint _ value | .uint _ value => value != 0
  | .float value => value != 0.0
  | .float32 value => value != (0 : Float32)
  | .complex real imaginary => real != 0.0 || imaginary != 0.0
  | .complex32 real imaginary =>
      real != (0 : Float32) || imaginary != (0 : Float32)
  | .angle _ rawBits => rawBits != 0
  | .duration seconds => seconds != 0.0
  | .bits value => value.any id
  | .array value => !value.isEmpty
  | .uninitialized | .unit => false

def asInt : Value → Int
  | .integer value => value
  | .sint _ value | .uint _ value => value
  | .angle _ rawBits => rawBits
  | .bit true => 1
  | .bit false => 0
  | .boolean true => 1
  | .boolean false => 0
  | .float value => value.toInt64.toInt
  | .float32 value => value.toInt64.toInt
  | .complex real _ => real.toInt64.toInt
  | .complex32 real _ => real.toInt64.toInt
  | .duration seconds => seconds.toInt64.toInt
  | .bits value =>
      (value.foldl (fun (accumulator, place) currentBit =>
        (if currentBit then accumulator + place else accumulator, place * 2))
        ((0 : Int), (1 : Int))).1
  | .array value => value.size
  | .uninitialized | .unit => 0

def asNat (value : Value) : Nat := value.asInt.toNat

def resolveIndex (size : Nat) (value : Value) : Nat :=
  let index := value.asInt
  if index < 0 then size - index.natAbs else index.toNat

def resolveIndex? (size : Nat) (value : Value) : Except String Nat := do
  let index := value.asInt
  if index < -(Int.ofNat size) || index ≥ Int.ofNat size then
    throw s!"index {index} is outside a value of size {size}"
  pure (if index < 0 then size - index.natAbs else index.toNat)

def asFloat : Value → Float
  | .float value => value
  | .float32 value => value.toFloat
  | .complex real _ => real
  | .complex32 real _ => real.toFloat
  | .duration seconds => seconds
  | .angle width rawBits =>
      if width == 0 then 0.0
      else (UInt64.ofNat rawBits).toFloat * 6.283185307179586 /
        (UInt64.ofNat ((2 : Nat) ^ width)).toFloat
  | .integer value =>
      if value < 0 then -(UInt64.ofNat value.natAbs).toFloat
      else (UInt64.ofNat value.natAbs).toFloat
  | .boolean true => 1.0
  | .boolean false => 0.0
  | value =>
      let integer := value.asInt
      if integer < 0 then -(UInt64.ofNat integer.natAbs).toFloat
      else (UInt64.ofNat integer.natAbs).toFloat

def asComplex : Value → Float × Float
  | .complex real imaginary => (real, imaginary)
  | .complex32 real imaginary => (real.toFloat, imaginary.toFloat)
  | value => (value.asFloat, 0.0)

private def modulus (width : Nat) : Int :=
  (2 : Int) ^ width

private def normalizedUnsigned (width : Nat) (value : Int) : Int :=
  if width == 0 then 0 else
    let modulus := modulus width
    ((value % modulus) + modulus) % modulus

private def integerBits (width : Nat) (value : Int) : Array Bool :=
  let value := normalizedUnsigned width value
  Array.ofFn fun index : Fin width =>
    (value.natAbs / (2 ^ index.val)) % 2 == 1

private def angleBits (width : Nat) (value : Value) : Nat :=
  if width == 0 then 0
  else
    let turns := value.asFloat / 6.283185307179586
    let wrapped := turns - turns.floor
    let scale := (UInt64.ofNat ((2 : Nat) ^ width)).toFloat
    (wrapped * scale).round.toUInt64.toNat % ((2 : Nat) ^ width)

```

### Casts and scalar arithmetic

Casts normalize values to OpenQASM widths before arithmetic begins. The rewrapping
helpers then retain the most informative operand representation across unary and binary
operators.

```lean

def cast (typeName : String) (width : Nat) (value : Value) : Value :=
  match typeName with
  | "bool" => .boolean value.truthy
  | "bit" => .bits (integerBits width value.asInt)
  | "uint" => .uint width (normalizedUnsigned width value.asInt)
  | "int" =>
      if width == 0 then .sint 0 0 else
        let unsigned := normalizedUnsigned width value.asInt
        let signBoundary := (2 : Int) ^ (width - 1)
        if unsigned ≥ signBoundary then .sint width (unsigned - modulus width)
        else .sint width unsigned
  | "float" =>
      if width == 32 then .float32 value.asFloat.toFloat32 else .float value.asFloat
  | "angle" => .angle width (angleBits width value)
  | "complex" =>
      let (real, imaginary) := value.asComplex
      if width == 32 then .complex32 real.toFloat32 imaginary.toFloat32
      else .complex real imaginary
  | "duration" => .duration value.asFloat
  | _ => value

/-- Casts every scalar in an array while preserving and validating its declared shape. -/
partial def castArray (typeName : String) (width : Nat) (shape : List Nat)
    (value : Value) : Value :=
  match shape with
  | [] => cast typeName width value
  | size :: rest =>
      match value with
      | .array values =>
          if values.size == size then
            .array (values.map (castArray typeName width rest))
          else .unit
      | _ => .unit

def scalarBit (value : Value) : Value := .bit value.truthy

def asArray : Value → Array Value
  | .array values => values
  | value => #[value]

partial def replicateShape : Array Nat → Value → Value
  | shape, default =>
      match shape.toList with
      | [] => default
      | size :: rest =>
          .array (Array.replicate size (replicateShape rest.toArray default))

private def rewrapInteger (template : Value) (value : Int) : Value :=
  match template with
  | .sint width _ => cast "int" width (.integer value)
  | .uint width _ => cast "uint" width (.integer value)
  | .angle width _ =>
      .angle width (normalizedUnsigned width value).natAbs
  | .bits valueBits => .bits (integerBits valueBits.size value)
  | .bit _ => .bit (value % 2 != 0)
  | _ => .integer value

private def rewrapIntegerFrom (left right : Value) (value : Int) : Value :=
  match left with
  | .integer _ => rewrapInteger right value
  | _ => rewrapInteger left value

private def rewrapFloat (left right : Value) (value : Float) : Value :=
  match left, right with
  | .duration _, .duration _ => .duration value
  | .float32 _, .float32 _ => .float32 value.toFloat32
  | .float32 _, .integer _ | .integer _, .float32 _ =>
      .float32 value.toFloat32
  | _, _ => .float value

private def rewrapComplex (left right : Value) (real imaginary : Float) : Value :=
  match left, right with
  | .complex32 .., .complex32 .. =>
      .complex32 real.toFloat32 imaginary.toFloat32
  | .complex32 .., .float32 _ | .float32 _, .complex32 .. =>
      .complex32 real.toFloat32 imaginary.toFloat32
  | _, _ => .complex real imaginary

def unary (operator : String) (value : Value) : Value :=
  match operator with
  | "!" => .boolean (!value.truthy)
  | "-" => match value with
    | .float number => .float (-number)
    | .float32 number => .float32 (-number)
    | .complex real imaginary => .complex (-real) (-imaginary)
    | .complex32 real imaginary => .complex32 (-real) (-imaginary)
    | .duration seconds => .duration (-seconds)
    | _ => rewrapInteger value (-value.asInt)
  | "~" => rewrapInteger value (~~~value.asInt)
  | _ => value

private def intPow (base exponent : Int) : Int :=
  if exponent < 0 then 0 else base ^ exponent.toNat

def binary (operator : String) (left right : Value) : Value :=
  let ints (operation : Int → Int → Int) :=
    rewrapIntegerFrom left right (operation left.asInt right.asInt)
  let floats (operation : Float → Float → Float) :=
    rewrapFloat left right (operation left.asFloat right.asFloat)
  let integerComparison (operation : Int → Int → Bool) :=
    .boolean (operation left.asInt right.asInt)
  let floatComparison (operation : Float → Float → Bool) :=
    .boolean (operation left.asFloat right.asFloat)
  let hasComplex := match left, right with
    | .complex .., _ | .complex32 .., _ | _, .complex .. | _, .complex32 .. => true
    | _, _ => false
  let hasFloat := match left, right with
    | .float _, _ | .float32 _, _ | .duration _, _ |
        _, .float _ | _, .float32 _ | _, .duration _ => true
    | _, _ => false
  let complexAdd :=
    let (leftReal, leftImaginary) := left.asComplex
    let (rightReal, rightImaginary) := right.asComplex
    rewrapComplex left right (leftReal + rightReal) (leftImaginary + rightImaginary)
  let complexSubtract :=
    let (leftReal, leftImaginary) := left.asComplex
    let (rightReal, rightImaginary) := right.asComplex
    rewrapComplex left right (leftReal - rightReal) (leftImaginary - rightImaginary)
  let complexMultiply :=
    let (leftReal, leftImaginary) := left.asComplex
    let (rightReal, rightImaginary) := right.asComplex
    rewrapComplex left right (leftReal * rightReal - leftImaginary * rightImaginary)
      (leftReal * rightImaginary + leftImaginary * rightReal)
  let complexDivide :=
    let (leftReal, leftImaginary) := left.asComplex
    let (rightReal, rightImaginary) := right.asComplex
    let denominator := rightReal * rightReal + rightImaginary * rightImaginary
    if denominator == 0.0 then .unit else
      rewrapComplex left right
        ((leftReal * rightReal + leftImaginary * rightImaginary) / denominator)
        ((leftImaginary * rightReal - leftReal * rightImaginary) / denominator)
  let complexPower :=
    let (baseReal, baseImaginary) := left.asComplex
    let (exponentReal, exponentImaginary) := right.asComplex
    let magnitude := (baseReal * baseReal + baseImaginary * baseImaginary).sqrt
    let phase := Float.atan2 baseImaginary baseReal
    let logMagnitude := magnitude.log
    let resultReal := exponentReal * logMagnitude - exponentImaginary * phase
    let resultImaginary := exponentReal * phase + exponentImaginary * logMagnitude
    let scale := resultReal.exp
    rewrapComplex left right
      (scale * resultImaginary.cos) (scale * resultImaginary.sin)
  let valuesEqual :=
    if hasComplex then
      let leftValue := left.asComplex
      let rightValue := right.asComplex
      leftValue.1 == rightValue.1 && leftValue.2 == rightValue.2
    else if hasFloat then left.asFloat == right.asFloat
    else left == right
  match operator with
  | "+" => if hasComplex then complexAdd else if hasFloat then floats (· + ·) else ints (· + ·)
  | "-" => if hasComplex then complexSubtract else if hasFloat then floats (· - ·) else ints (· - ·)
  | "*" => if hasComplex then complexMultiply else if hasFloat then floats (· * ·) else ints (· * ·)
  | "/" =>
      if hasComplex then complexDivide
      else if hasFloat then
        if right.asFloat == 0.0 then .unit else floats (· / ·)
      else if right.asInt == 0 then .unit else ints (· / ·)
  | "%" =>
      if hasFloat then
        if right.asFloat == 0.0 then .unit
        else
          let quotient := (left.asFloat / right.asFloat).toInt64.toFloat
          floats (fun _ _ => left.asFloat - quotient * right.asFloat)
      else if right.asInt == 0 then .unit else ints (· % ·)
  | "**" =>
      if hasComplex then complexPower
      else if hasFloat then floats Float.pow
      else ints intPow
  | "<<" => ints (fun a b => a <<< b.toNat)
  | ">>" => ints (fun a b => a >>> b.toNat)
  | "&" => ints (fun a b => Int.ofNat (a.natAbs &&& b.natAbs))
  | "|" => ints (fun a b => Int.ofNat (a.natAbs ||| b.natAbs))
  | "^" => ints (fun a b => Int.ofNat (a.natAbs ^^^ b.natAbs))
  | "&&" => .boolean (left.truthy && right.truthy)
  | "||" => .boolean (left.truthy || right.truthy)
  | "==" => .boolean valuesEqual
  | "!=" => .boolean (!valuesEqual)
  | "<" => if hasFloat then floatComparison (· < ·) else integerComparison (· < ·)
  | "<=" => if hasFloat then floatComparison (· ≤ ·) else integerComparison (· ≤ ·)
  | ">" => if hasFloat then floatComparison (· > ·) else integerComparison (· > ·)
  | ">=" => if hasFloat then floatComparison (· ≥ ·) else integerComparison (· ≥ ·)
  | "++" => match left, right with
    | .bits left, .bits right => .bits (left ++ right)
    | .array left, .array right => .array (left ++ right)
    | _, _ => .array (left.asArray ++ right.asArray)
  | _ => .unit

def compound (operator : String) (left right : Value) : Value :=
  let base := if operator.endsWith "=" then operator.dropEnd 1 |>.copy else operator
  if operator == "=" then right
  else if operator == "~=" then unary "~" right
  else binary base left right

```

### Selection, mutation, and ranges

Indexing is shared by bits and arrays, including negative indices and set-valued
selectors. Updates mirror selection recursively, and ranges are materialized with the
inclusive endpoint semantics expected by the source language.

```lean

private def selectBits (bits : Array Bool) (selector : Value) : Value :=
  match selector with
  | .array selectors =>
      .bits (selectors.filterMap fun selector =>
        bits[resolveIndex bits.size selector]?)
  | selector =>
      match bits[resolveIndex bits.size selector]? with
      | some selectedBit => .bit selectedBit
      | none => .unit

private def bitsOfValue : Value → Option (Array Bool)
  | .bit value => some #[value]
  | .bits values => some values
  | .sint width value | .uint width value => some (integerBits width value)
  | .angle width rawBits => some (integerBits width rawBits)
  | _ => none

private def indexOne (value selector : Value) : Value :=
  match bitsOfValue value with
  | some valueBits => selectBits valueBits selector
  | none =>
      match selector with
      | .array selectors => .array (selectors.map (indexOne value))
      | selector =>
          let values := value.asArray
          values[resolveIndex values.size selector]?.getD .unit

def index (value : Value) (indices : Array Value) : Value :=
  indices.foldl indexOne value

private def updateSelectedBits
    (bits : Array Bool) (selector newValue : Value) : Array Bool :=
  match selector with
  | .array selectors =>
      let replacements := (bitsOfValue newValue).getD #[newValue.truthy]
      Id.run do
        let mut updated := bits
        for offset in [:selectors.size] do
          let position := resolveIndex updated.size selectors[offset]!
          if position < updated.size then
            updated := updated.set! position
              (replacements[offset]?.getD newValue.truthy)
        return updated
  | selector =>
      let position := resolveIndex bits.size selector
      if position < bits.size then bits.set! position newValue.truthy else bits

private def restoreBits (template : Value) (bits : Array Bool) : Value :=
  let numeric := (.bits bits : Value).asInt
  match template with
  | .bit _ => .bit (bits[0]?.getD false)
  | .bits _ => .bits bits
  | .sint width _ => cast "int" width (.integer numeric)
  | .uint width _ => cast "uint" width (.integer numeric)
  | .angle width _ => .angle width (normalizedUnsigned width numeric).natAbs
  | _ => template

partial def setIndex (value : Value) (indices : Array Value) (newValue : Value) : Value :=
  match indices.toList with
  | [] => newValue
  | selector :: rest =>
      match bitsOfValue value with
      | some valueBits =>
          if rest.isEmpty then restoreBits value (updateSelectedBits valueBits selector newValue)
          else value
      | none =>
          let values := value.asArray
          match selector with
          | .array selectors =>
              let replacements := newValue.asArray
              let updated := Id.run do
                let mut updated := values
                for offset in [:selectors.size] do
                  let position := resolveIndex updated.size selectors[offset]!
                  match updated[position]? with
                  | none => pure ()
                  | some old =>
                      let replacement := replacements[offset]?.getD newValue
                      updated := updated.set! position
                        (setIndex old rest.toArray replacement)
                return updated
              .array updated
          | selector =>
              let position := resolveIndex values.size selector
              match values[position]? with
              | none => value
              | some old => .array (values.set! position (setIndex old rest.toArray newValue))

def range (start step stop : Value) : Array Value := Id.run do
  let first := start.asInt
  let increment := step.asInt
  let last := stop.asInt
  if increment == 0 then return #[]
  let mut values := #[]
  let mut current := first
  if increment > 0 then
    while current ≤ last do
      values := values.push (.integer current)
      current := current + increment
  else
    while current ≥ last do
      values := values.push (.integer current)
      current := current + increment
  return values

```

### Mathematical built-ins

These helpers implement the portable classical built-ins. Backend-relative timing and
other hardware-sensitive operations never enter this table.

```lean

private partial def popcount (value : Nat) : Nat :=
  if value == 0 then 0 else value % 2 + popcount (value / 2)

private partial def dimensionSize (value : Value) (dimension : Nat) : Nat :=
  if dimension == 0 then value.asArray.size
  else match value.asArray[0]? with
    | some first => dimensionSize first (dimension - 1)
    | none => 0

private def rotateBits (value : Value) (distance : Int) : Value :=
  let bits := (bitsOfValue value).getD #[]
  if bits.isEmpty then value else
    let width : Int := bits.size
    let normalized := ((distance % width) + width) % width
    let rotated := Id.run do
      let mut result := Array.replicate bits.size false
      for index in [:bits.size] do
        let destination := (Int.ofNat index + normalized).toNat % bits.size
        result := result.set! destination bits[index]!
      return result
    restoreBits value rotated

private def complexExp (value : Value) : Value :=
  let (real, imaginary) := value.asComplex
  let scale := real.exp
  rewrapComplex value value (scale * imaginary.cos) (scale * imaginary.sin)

private def complexSqrt (value : Value) : Value :=
  let (real, imaginary) := value.asComplex
  let magnitude := (real * real + imaginary * imaginary).sqrt
  let resultReal := ((magnitude + real) / 2.0).sqrt
  let resultImaginaryMagnitude := ((magnitude - real) / 2.0).sqrt
  let resultImaginary := if imaginary < 0.0 then -resultImaginaryMagnitude
    else resultImaginaryMagnitude
  rewrapComplex value value resultReal resultImaginary

def builtin (name : String) (arguments : Array Value) : Value :=
  match name, arguments.toList with
  | "popcount", [value] => .integer (popcount value.asInt.natAbs)
  | "sizeof", [value] => .integer (dimensionSize value 0)
  | "sizeof", [value, dimension] => .integer (dimensionSize value dimension.asNat)
  | "real", [value] => rewrapFloat value value value.asComplex.1
  | "imag", [value] => rewrapFloat value value value.asComplex.2
  | "sin", [value] => rewrapFloat value value value.asFloat.sin
  | "cos", [value] => rewrapFloat value value value.asFloat.cos
  | "tan", [value] => rewrapFloat value value value.asFloat.tan
  | "arcsin", [value] => rewrapFloat value value value.asFloat.asin
  | "arccos", [value] => rewrapFloat value value value.asFloat.acos
  | "arctan", [value] => rewrapFloat value value value.asFloat.atan
  | "sqrt", [value@(.complex _ _)] | "sqrt", [value@(.complex32 _ _)] =>
      complexSqrt value
  | "sqrt", [value] => rewrapFloat value value value.asFloat.sqrt
  | "exp", [value@(.complex _ _)] | "exp", [value@(.complex32 _ _)] =>
      complexExp value
  | "exp", [value] => rewrapFloat value value value.asFloat.exp
  | "log", [value] => rewrapFloat value value value.asFloat.log
  | "floor", [value] => rewrapFloat value value value.asFloat.floor
  | "ceiling", [value] => rewrapFloat value value value.asFloat.ceil
  | "mod", [left, right] => binary "%" left right
  | "rotl", [value, distance] => rotateBits value distance.asInt
  | "rotr", [value, distance] => rotateBits value (-distance.asInt)
  | _, _ => .unit

end Value

```

## Fixed-width wrapper operations

Small namespaces expose canonical conversions for the scalar wrappers used in generated
signatures. Signed integers explicitly decode their two's-complement representation.

```lean

namespace UInt

def ofNat (value : Nat) : UInt width := ⟨BitVec.ofNat width value⟩

def toNat (value : UInt width) : Nat := value.bits.toNat

end UInt

namespace SInt

private def unsignedValue (width : Nat) (value : Int) : Nat :=
  if width == 0 then 0 else
    let modulus : Int := (2 : Int) ^ width
    (((value % modulus) + modulus) % modulus).toNat

def ofInt (value : Int) : SInt width := ⟨BitVec.ofNat width (unsignedValue width value)⟩

def toInt (value : SInt width) : Int :=
  if width == 0 then 0 else
    let unsigned := value.bits.toNat
    let signBoundary := (2 : Nat) ^ (width - 1)
    if unsigned < signBoundary then Int.ofNat unsigned
    else Int.ofNat unsigned - Int.ofNat ((2 : Nat) ^ width)

end SInt

namespace Angle

def ofNat (value : Nat) : Angle width := ⟨BitVec.ofNat width value⟩

def toNat (value : Angle width) : Nat := value.bits.toNat

end Angle

```

## Crossing the generated-program boundary

`ValueCodec` is the single conversion protocol between native Lean fields and runtime
values. Scalar instances validate initialization, while the array instance checks both
rank and every nested extent before constructing its proof-bearing result.

```lean

/-- Conversion between native generated Lean fields and the compact internal carrier. -/
class ValueCodec (element : Type u) where
  encode : element → Value
  decode : Value → Except String element

namespace ValueCodec

def toValue [ValueCodec element] (value : element) : Value :=
  ValueCodec.encode value

def fromValue [ValueCodec element] (value : Value) : Except String element :=
  ValueCodec.decode value

private def expectInitialized (value : Value) : Except String Unit :=
  match value with
  | .uninitialized => throw "read of an uninitialized OpenQASM value"
  | .unit => throw "an expression produced no value"
  | _ => pure ()

instance : ValueCodec Bool where
  encode value := .boolean value
  decode value := do
    expectInitialized value
    pure value.truthy

instance : ValueCodec Bit where
  encode value := .bit value.value
  decode value := do
    expectInitialized value
    pure ⟨value.truthy⟩

instance : ValueCodec (BitVec width) where
  encode value := .bits (Array.ofFn fun index : Fin width => value.getLsb index)
  decode value := do
    expectInitialized value
    let actual := match value with
      | .bit scalar => #[scalar]
      | .bits values => values
      | _ => Array.ofFn fun index : Fin width =>
          value.asInt.natAbs / (2 ^ index.val) % 2 == 1
    unless actual.size == width do
      throw s!"expected bit[{width}], got {value.typeName}"
    let numeric := actual.foldr (fun current accumulator =>
      accumulator * 2 + if current then 1 else 0) 0
    pure (BitVec.ofNat width numeric)

instance : ValueCodec (UInt width) where
  encode value := .uint width value.toNat
  decode value := do
    expectInitialized value
    pure (.ofNat value.asNat)

instance : ValueCodec (SInt width) where
  encode value := .sint width value.toInt
  decode value := do
    expectInitialized value
    pure (.ofInt value.asInt)

instance : ValueCodec (Angle width) where
  encode value := .angle width value.toNat
  decode value := do
    expectInitialized value
    match Value.cast "angle" width value with
    | .angle _ rawBits => pure (.ofNat rawBits)
    | _ => throw "internal angle conversion failure"

instance : ValueCodec Float where
  encode value := .float value
  decode value := do
    expectInitialized value
    pure value.asFloat

instance : ValueCodec Float32 where
  encode value := .float32 value
  decode value := do
    expectInitialized value
    pure value.asFloat.toFloat32

instance : ValueCodec (FloatN width) where
  encode value := if width == 32 then .float32 value.value.toFloat32 else .float value.value
  decode value := do
    expectInitialized value
    pure ⟨value.asFloat⟩

instance : ValueCodec (ComplexN width) where
  encode value :=
    if width == 32 then
      .complex32 value.re.value.toFloat32 value.im.value.toFloat32
    else .complex value.re.value value.im.value
  decode value := do
    expectInitialized value
    let components := value.asComplex
    pure ⟨⟨components.1⟩, ⟨components.2⟩⟩

instance : ValueCodec Duration where
  encode value := .duration value.seconds
  decode value := do
    expectInitialized value
    pure ⟨value.asFloat⟩

private partial def flatten : Value → Array Value
  | .array values => values.flatMap flatten
  | value => #[value]

private partial def hasShape : List Nat → Value → Bool
  | [], .array _ => false
  | [], .uninitialized | [], .unit => false
  | [], _ => true
  | size :: rest, .array values =>
      values.size == size && values.all (hasShape rest)
  | _ :: _, _ => false

private partial def nest (shape : List Nat) (values : Array Value) : Value :=
  match shape with
  | [] => values[0]?.getD .uninitialized
  | size :: rest =>
      let stride := rest.foldl (· * ·) 1
      .array (Array.range size |>.map fun index =>
        nest rest (values.extract (index * stride) ((index + 1) * stride)))

instance [ValueCodec element] : ValueCodec (FixedArray element shape) where
  encode value :=
    nest shape (value.data.map ValueCodec.encode)
  decode value := do
    expectInitialized value
    unless hasShape shape value do
      throw s!"expected array shape {shape}, got {value.typeName} with a different nesting"
    let flattened := flatten value
    let expected := shape.foldl (· * ·) 1
    if size_eq : flattened.size = expected then
      let decoded ← Array.mapM' ValueCodec.decode flattened
      pure ⟨decoded.val, by simpa [expected] using decoded.property.trans size_eq⟩
    else
      throw s!"expected array shape {shape}, got {flattened.size} scalar elements"

end ValueCodec

```

## Reproducible program metadata

The final records identify source origins and target settings without coupling execution
to a backend. They are emitted beside every generated program for diagnostics and
reproducibility.

```lean

structure ProgramOrigin where
  name : String
  digest : UInt64
  deriving Repr, Inhabited, BEq

/-- Stable metadata emitted beside every generated native Lean program. -/
structure CheckedProgramInfo where
  versionMajor : Nat := 3
  versionMinor : Nat := 0
  target : TargetConfig := .default
  origins : Array ProgramOrigin := #[]
  annotations : Array String := #[]
  pragmas : Array String := #[]
  deriving Repr, Inhabited

end QASM
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
