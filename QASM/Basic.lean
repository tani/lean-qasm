import Lean
import LiterateLean

# QASM basic embedded language and interpreter

This module implements a small executable subset of OpenQASM 3.0. It combines
an abstract syntax tree, a checked embedded syntax, static validation, source
serialization, and a state vector interpreter.

The supported statements are:

- `OPENQASM 3.0;`
- `include "...";`
- `qubit[n] q;`
- `bit[n] c;`
- `x q[i];`
- `h q[i];`
- `z q[i];`
- `cx q[i], q[j];`
- `measure q[i] -> c[j];`

Whole-register operations are also supported:

- `h q;`
- `x q;`
- `measure q -> c;`

Programs can be executed directly:

    #eval execute bell

or:

    #eval execute qasm {
      ...
    }

Qubit indexing is little endian:

- `q[0]` is the least significant basis-index bit.

```lean
namespace Qasm
```

## Abstract syntax tree

The syntax tree preserves register names and optional element indices. A
missing index denotes a whole register operation.

`Ref` represents a reference to a quantum or classical register. Its `name`
field stores the source name and its optional `index` selects one zero based
element. If `index` is `none`, the reference denotes the whole register.

`Stmt` represents the supported statement forms:

- `version` records an `OPENQASM major.minor;` declaration.
- `includeFile` records an include directive without loading the file.
- `qubit` and `bit` declare quantum and classical registers.
- `gate1` and `gate2` apply named gates to one or two references.
- `measure` copies a measured quantum result into classical storage.

`Program` is the statements of a source file in their original order.

```lean
structure Ref where
  name : String
  index : Option Nat
  deriving Repr, Inhabited, BEq

inductive Stmt where
  | version :
      Nat →
      Nat →
      Stmt
  | includeFile :
      String →
      Stmt
  | qubit :
      String →
      Nat →
      Stmt
  | bit :
      String →
      Nat →
      Stmt
  | gate1 :
      String →
      Ref →
      Stmt
  | gate2 :
      String →
      Ref →
      Ref →
      Stmt
  | measure :
      Ref →
      Ref →
      Stmt
  deriving Repr, Inhabited, BEq

abbrev Program := List Stmt
```

## OpenQASM serialization

Each syntax node can be rendered back to normalized OpenQASM source. Programs
place one statement on each line.

`Ref.toQasm` renders either a bare register name or an indexed reference.
`Stmt.toQasm` renders one statement including its terminating semicolon.
`Program.toQasm` validates before joining the rendered statements with newline
characters. Invalid AST values therefore cannot be serialized as OpenQASM.

```lean
def Ref.toQasm : Ref → String
  | ⟨name, none⟩ =>
      name
  | ⟨name, some index⟩ =>
      s!"{name}[{index}]"

def Stmt.toQasm : Stmt → String
  | .version major minor =>
      s!"OPENQASM {major}.{minor};"

  | .includeFile filename =>
      s!"include \"{filename}\";"

  | .qubit name size =>
      s!"qubit[{size}] {name};"

  | .bit name size =>
      s!"bit[{size}] {name};"

  | .gate1 gate arg =>
      s!"{gate} {arg.toQasm};"

  | .gate2 gate arg₁ arg₂ =>
      s!"{gate} {arg₁.toQasm}, {arg₂.toQasm};"

  | .measure src dst =>
      s!"measure {src.toQasm} -> {dst.toQasm};"

private def Program.toQasmUnchecked (program : Program) : String :=
  String.intercalate "\n" (program.map Stmt.toQasm)
```

## Static validation

Validation walks statements in source order while accumulating declared
registers. This enforces declaration before use and produces the earliest
actionable error.

`RegisterKind` distinguishes quantum storage from classical storage.
`RegisterInfo` pairs that kind with a positive register size, and `RegisterEnv`
associates source names with their declarations.

`Program.validate` checks declaration order, register kinds, index bounds, and
the OpenQASM version. It returns the first human readable error. Gate support
is checked later by the interpreter rather than by static validation.

Identifiers intentionally use the ASCII subset `[A-Za-z_][A-Za-z0-9_]*` of
the ANTLR `Identifier` rule and exclude every reserved lexer keyword. Include
filenames use the double quoted `StringLiteral` subset emitted by the printer.

```lean
inductive RegisterKind where
  | quantum
  | classical
  deriving Repr, Inhabited, BEq

structure RegisterInfo where
  kind : RegisterKind
  size : Nat
  deriving Repr, Inhabited, BEq

abbrev RegisterEnv := List (String × RegisterInfo)

private def openQasmKeywords : List String := [
  "OPENQASM", "include", "defcalgrammar", "def", "cal", "defcal", "gate",
  "extern", "box", "let", "break", "continue", "if", "else", "end",
  "return", "for", "while", "in", "switch", "case", "default", "nop",
  "pragma", "input", "output", "const", "readonly", "mutable", "qreg",
  "qubit", "creg", "bool", "bit", "int", "uint", "float", "angle",
  "complex", "array", "void", "duration", "stretch", "gphase", "inv",
  "pow", "ctrl", "negctrl", "durationof", "delay", "reset", "measure",
  "barrier", "true", "false", "im"
]

private def isAsciiLetter (char : Char) : Bool :=
  ('A' ≤ char && char ≤ 'Z') || ('a' ≤ char && char ≤ 'z')

private def isAsciiDigit (char : Char) : Bool :=
  '0' ≤ char && char ≤ '9'

private def isIdentifierStart (char : Char) : Bool :=
  isAsciiLetter char || char == '_'

private def isIdentifierRest (char : Char) : Bool :=
  isIdentifierStart char || isAsciiDigit char

def isValidIdentifier (name : String) : Bool :=
  match name.toList with
  | [] =>
      false
  | first :: rest =>
      isIdentifierStart first &&
      rest.all isIdentifierRest &&
      !(openQasmKeywords.contains name)

private def validateIdentifier (name : String) : Except String Unit := do
  unless isValidIdentifier name do
    throw s!"invalid OpenQASM identifier: {name}"

def isValidIncludeFilename (filename : String) : Bool :=
  !filename.isEmpty && filename.toList.all fun char =>
    char != '"' && char != '\r' && char != '\n' && char != '\t'

private def validateIncludeFilename (filename : String) : Except String Unit := do
  unless isValidIncludeFilename filename do
    throw s!"invalid OpenQASM include filename: {filename}"

private def lookupRegister?
    (env : RegisterEnv)
    (name : String) :
    Option RegisterInfo :=
  match env.find? (fun entry => entry.1 == name) with
  | none =>
      none
  | some entry =>
      some entry.2

private def registerKindName : RegisterKind → String
  | .quantum =>
      "quantum"
  | .classical =>
      "classical"

private def validateRef
    (env : RegisterEnv)
    (ref : Ref)
    (expectedKind : Option RegisterKind := none) :
    Except String Unit := do
  validateIdentifier ref.name

  let info ←
    match lookupRegister? env ref.name with
    | none =>
        throw s!"undeclared register: {ref.name}"
    | some info =>
        pure info

  match expectedKind with
  | none =>
      pure ()

  | some expected =>
      if info.kind == expected then
        pure ()
      else
        throw s!"register {ref.name} is {registerKindName info.kind}, but {registerKindName expected} was expected"

  match ref.index with
  | none =>
      pure ()

  | some index =>
      if index < info.size then
        pure ()
      else
        throw s!"index {index} is out of bounds for register {ref.name}[{info.size}]"

private def validateStmt
    (env : RegisterEnv)
    (stmt : Stmt) :
    Except String RegisterEnv := do
  match stmt with
  | .version _ _ =>
      throw "duplicate OpenQASM version declaration"

  | .includeFile filename =>
      validateIncludeFilename filename
      pure env

  | .qubit name size =>
      validateIdentifier name
      if size == 0 then
        throw s!"quantum register {name} must have positive size"
      else if (lookupRegister? env name).isSome then
        throw s!"duplicate register declaration: {name}"
      else
        pure ((name, ⟨.quantum, size⟩) :: env)

  | .bit name size =>
      validateIdentifier name
      if size == 0 then
        throw s!"classical register {name} must have positive size"
      else if (lookupRegister? env name).isSome then
        throw s!"duplicate register declaration: {name}"
      else
        pure ((name, ⟨.classical, size⟩) :: env)

  | .gate1 gate arg =>
      validateIdentifier gate
      validateRef env arg (some .quantum)
      pure env

  | .gate2 gate arg₁ arg₂ =>
      validateIdentifier gate
      validateRef env arg₁ (some .quantum)
      validateRef env arg₂ (some .quantum)
      pure env

  | .measure src dst =>
      validateRef env src (some .quantum)
      validateRef env dst (some .classical)
      pure env

private def validateStatements
    (env : RegisterEnv)
    (stmts : List Stmt) :
    Except String Unit := do
  match stmts with
  | [] =>
      pure ()

  | stmt :: rest =>
      let env ← validateStmt env stmt
      validateStatements env rest

def Program.validate (program : Program) : Except String Unit := do
  match program with
  | [] =>
      throw "empty OpenQASM program"

  | .version 3 0 :: rest =>
      validateStatements [] rest

  | .version major minor :: _ =>
      throw s!"unsupported OpenQASM version: {major}.{minor}"

  | _ =>
      throw "the first statement must be `OPENQASM 3.0;`"

def Program.toQasm (program : Program) : Except String String := do
  program.validate
  pure program.toQasmUnchecked
```

## Embedded OpenQASM syntax

The following syntax categories describe register references and statements.
The `qasm` term syntax requires the unique version declaration first and then
collects the remaining statements into a `Qasm.Program`.

```lean

declare_syntax_cat qasmRef
declare_syntax_cat qasmStmt

syntax ident : qasmRef
syntax ident "[" num "]" : qasmRef

syntax "include" str ";" : qasmStmt
syntax "qubit" "[" num "]" ident ";" : qasmStmt
syntax "bit" "[" num "]" ident ";" : qasmStmt
syntax "measure" qasmRef "->" qasmRef ";" : qasmStmt

syntax ident qasmRef ";" : qasmStmt
syntax ident qasmRef "," qasmRef ";" : qasmStmt

syntax (name := qasmProgram)
  "qasm" "{" "OPENQASM" scientific ";" qasmStmt* "}" : term

open Lean
open Lean Macro

private abbrev LeanTermSyntax :=
  TSyntax `term
```

## Macro expansion

Macro expansion translates the surface syntax into explicit constructors.
OpenQASM version errors are reported at expansion time when possible.

```lean

private def ensureIdentifierAt (stx : Syntax) (name : String) : MacroM Unit := do
  unless isValidIdentifier name do
    Macro.throwErrorAt stx s!"invalid OpenQASM identifier: {name}"

private def ensureIncludeFilenameAt
    (stx : Syntax)
    (filename : String) : MacroM Unit := do
  unless isValidIncludeFilename filename do
    Macro.throwErrorAt stx s!"invalid OpenQASM include filename: {filename}"

private def ensureVersionAt (version : TSyntax `scientific) : MacroM Unit := do
  let (mantissa, decimalExponent, exponent) :=
    version.getScientific

  unless
      mantissa == 30 &&
      decimalExponent &&
      exponent == 1 do
    Macro.throwErrorAt
      version
      "only `OPENQASM 3.0;` is supported"

private def expandRef :
    Syntax →
    MacroM LeanTermSyntax
  | `(qasmRef| $name:ident[$index:num]) => do
      let nameString := name.getId.toString
      let indexValue := index.getNat
      ensureIdentifierAt name nameString

      `(Qasm.Ref.mk
          $(quote nameString)
          (some $(quote indexValue)))

  | `(qasmRef| $name:ident) => do
      let nameString := name.getId.toString
      ensureIdentifierAt name nameString

      `(Qasm.Ref.mk
          $(quote nameString)
          none)

  | stx =>
      Macro.throwErrorAt
        stx
        "invalid OpenQASM register reference"

private def expandStmt :
    Syntax →
    MacroM LeanTermSyntax
  | `(qasmStmt| include $filename:str;) => do
      let filenameString := filename.getString
      ensureIncludeFilenameAt filename filenameString

      `(Qasm.Stmt.includeFile
          $(quote filenameString))

  | `(qasmStmt| qubit[$size:num] $name:ident;) => do
      let nameString := name.getId.toString
      let sizeValue := size.getNat
      ensureIdentifierAt name nameString

      `(Qasm.Stmt.qubit
          $(quote nameString)
          $(quote sizeValue))

  | `(qasmStmt| bit[$size:num] $name:ident;) => do
      let nameString := name.getId.toString
      let sizeValue := size.getNat
      ensureIdentifierAt name nameString

      `(Qasm.Stmt.bit
          $(quote nameString)
          $(quote sizeValue))

  | `(qasmStmt| measure $src:qasmRef -> $dst:qasmRef;) => do
      let srcTerm ← expandRef src
      let dstTerm ← expandRef dst

      `(Qasm.Stmt.measure
          $srcTerm
          $dstTerm)

  | `(qasmStmt| $gate:ident $arg:qasmRef;) => do
      let gateName := gate.getId.toString
      let argTerm ← expandRef arg
      ensureIdentifierAt gate gateName

      `(Qasm.Stmt.gate1
          $(quote gateName)
          $argTerm)

  | `(qasmStmt| $gate:ident $arg₁:qasmRef, $arg₂:qasmRef;) => do
      let gateName := gate.getId.toString
      let arg₁Term ← expandRef arg₁
      let arg₂Term ← expandRef arg₂
      ensureIdentifierAt gate gateName

      `(Qasm.Stmt.gate2
          $(quote gateName)
          $arg₁Term
          $arg₂Term)

  | stx =>
      Macro.throwErrorAt
        stx
        "unsupported OpenQASM statement"

macro_rules
  | `(qasm { OPENQASM $version:scientific; $stmts:qasmStmt* }) => do
      ensureVersionAt version

      let init : LeanTermSyntax ←
        `(([] : Qasm.Program))

      let statements ← stmts.foldrM
        (β := LeanTermSyntax)
        (init := init)
        fun stmt rest => do
          let stmtTerm ← expandStmt stmt.raw
          `($stmtTerm :: $rest)

      `(Qasm.Stmt.version 3 0 :: $statements)
```

## Complex amplitudes

The interpreter uses a compact complex number type backed by Lean `Float`
values. It is intended for executable simulation rather than exact proofs.

`CFloat` stores real and imaginary components. Its namespace provides zero,
one, addition, subtraction, negation, real scaling, and squared magnitude.

```lean
structure CFloat where
  re : Float
  im : Float
  deriving Repr, Inhabited

namespace CFloat

def zero : CFloat :=
  ⟨0.0, 0.0⟩

def one : CFloat :=
  ⟨1.0, 0.0⟩

def add (lhs rhs : CFloat) : CFloat :=
  ⟨lhs.re + rhs.re, lhs.im + rhs.im⟩

def sub (lhs rhs : CFloat) : CFloat :=
  ⟨lhs.re - rhs.re, lhs.im - rhs.im⟩

def neg (value : CFloat) : CFloat :=
  ⟨-value.re, -value.im⟩

def scale (factor : Float) (value : CFloat) : CFloat :=
  ⟨factor * value.re, factor * value.im⟩

def normSq (value : CFloat) : Float :=
  value.re * value.re + value.im * value.im

end CFloat
```

## Runtime state

The machine stores one global state vector and maps each source register onto
its quantum or classical runtime storage.

`QuantumRegisterInfo` records the first global qubit index and the number of
consecutive qubits in a register. `ClassicalRegisterInfo` owns its bit array.

`Machine` is the internal interpreter state. Its amplitude array has
`2 ^ qubitCount` entries, while its register tables map source names to runtime
storage. `Machine.empty` is the zero qubit state with one amplitude equal to
one.

`ExecutionResult` exposes the total qubit count, the final little endian state
vector, and classical registers in declaration order.

```lean
structure QuantumRegisterInfo where
  offset : Nat
  size : Nat
  deriving Repr, Inhabited

structure ClassicalRegisterInfo where
  bits : Array Bool
  deriving Repr, Inhabited

structure Machine where
  qubitCount : Nat
  amplitudes : Array CFloat
  qregs : List (String × QuantumRegisterInfo)
  cregs : List (String × ClassicalRegisterInfo)
  deriving Repr, Inhabited

def Machine.empty : Machine where
  qubitCount := 0
  amplitudes := #[CFloat.one]
  qregs := []
  cregs := []

structure ExecutionResult where
  qubitCount : Nat
  amplitudes : Array CFloat
  classical : List (String × Array Bool)
  deriving Repr, Inhabited

private def lookupQuantumRegister?
    (machine : Machine)
    (name : String) :
    Option QuantumRegisterInfo :=
  match machine.qregs.find? (fun entry => entry.1 == name) with
  | none =>
      none
  | some entry =>
      some entry.2

private def lookupClassicalRegister?
    (machine : Machine)
    (name : String) :
    Option ClassicalRegisterInfo :=
  match machine.cregs.find? (fun entry => entry.1 == name) with
  | none =>
      none
  | some entry =>
      some entry.2
```

## Register allocation

Declaring qubits extends the state vector with zero amplitudes while retaining
the existing state in the subspace where all new qubits are zero.

```lean

private def declareQuantumRegister
    (machine : Machine)
    (name : String)
    (size : Nat) :
    Machine :=
  let oldDimension :=
    machine.amplitudes.size

  let newQubitCount :=
    machine.qubitCount + size

  let newDimension : Nat :=
    2 ^ newQubitCount

  let newAmplitudes :=
    Id.run do
      let mut result :=
        Array.replicate newDimension CFloat.zero

      for index in [0:oldDimension] do
        result :=
          result.set! index machine.amplitudes[index]!

      return result

  {
    machine with
    qubitCount := newQubitCount
    amplitudes := newAmplitudes
    qregs :=
      (name, {
        offset := machine.qubitCount
        size := size
      }) :: machine.qregs
  }

private def declareClassicalRegister
    (machine : Machine)
    (name : String)
    (size : Nat) :
    Machine :=
  {
    machine with
    cregs :=
      (name, {
        bits := Array.replicate size false
      }) :: machine.cregs
  }
```

## Register reference resolution

Indexed references resolve to one storage location. Whole register references
resolve to locations in increasing source index order.

```lean

private def resolveQuantumRef
    (machine : Machine)
    (ref : Ref) :
    Except String (List Nat) := do
  let info ←
    match lookupQuantumRegister? machine ref.name with
    | none =>
        throw s!"unknown quantum register: {ref.name}"
    | some info =>
        pure info

  match ref.index with
  | some index =>
      if index < info.size then
        pure [info.offset + index]
      else
        throw s!"quantum-register index out of range: {ref.name}[{index}]"

  | none =>
      pure (
        (List.range info.size).map
          (fun index => info.offset + index)
      )

private def resolveClassicalRef
    (machine : Machine)
    (ref : Ref) :
    Except String (List (String × Nat)) := do
  let info ←
    match lookupClassicalRegister? machine ref.name with
    | none =>
        throw s!"unknown classical register: {ref.name}"
    | some info =>
        pure info

  match ref.index with
  | some index =>
      if index < info.bits.size then
        pure [(ref.name, index)]
      else
        throw s!"classical-register index out of range: {ref.name}[{index}]"

  | none =>
      pure (
        (List.range info.bits.size).map
          (fun index => (ref.name, index))
      )
```

## Basis index operations

Qubits use little endian indexing, so the mask for qubit `n` is `2 ^ n`.

```lean

private def qubitMask (qubitIndex : Nat) : Nat :=
  2 ^ qubitIndex

private def bitAt
    (basisIndex : Nat)
    (qubitIndex : Nat) :
    Bool :=
  ((basisIndex / qubitMask qubitIndex) % 2) == 1
```

## Single qubit gates

Gate implementations update paired amplitudes in place within an `Id` block.
The supported names are `id`, `x`, `h`, and `z`.

```lean

private def applyXAt
    (machine : Machine)
    (qubitIndex : Nat) :
    Machine :=
  let mask :=
    qubitMask qubitIndex

  let newAmplitudes :=
    Id.run do
      let mut result :=
        machine.amplitudes

      for basisIndex in [0:result.size] do
        if !(bitAt basisIndex qubitIndex) then
          let pairedIndex :=
            basisIndex + mask

          let amplitude₀ :=
            result[basisIndex]!

          let amplitude₁ :=
            result[pairedIndex]!

          result :=
            result.set! basisIndex amplitude₁

          result :=
            result.set! pairedIndex amplitude₀

      return result

  {
    machine with
    amplitudes := newAmplitudes
  }

private def applyHAt
    (machine : Machine)
    (qubitIndex : Nat) :
    Machine :=
  let mask :=
    qubitMask qubitIndex

  let factor :=
    1.0 / Float.sqrt 2.0

  let newAmplitudes :=
    Id.run do
      let mut result :=
        machine.amplitudes

      for basisIndex in [0:result.size] do
        if !(bitAt basisIndex qubitIndex) then
          let pairedIndex :=
            basisIndex + mask

          let amplitude₀ :=
            result[basisIndex]!

          let amplitude₁ :=
            result[pairedIndex]!

          let transformed₀ :=
            CFloat.scale
              factor
              (CFloat.add amplitude₀ amplitude₁)

          let transformed₁ :=
            CFloat.scale
              factor
              (CFloat.sub amplitude₀ amplitude₁)

          result :=
            result.set! basisIndex transformed₀

          result :=
            result.set! pairedIndex transformed₁

      return result

  {
    machine with
    amplitudes := newAmplitudes
  }

private def applyZAt
    (machine : Machine)
    (qubitIndex : Nat) :
    Machine :=
  let newAmplitudes :=
    Id.run do
      let mut result :=
        machine.amplitudes

      for basisIndex in [0:result.size] do
        if bitAt basisIndex qubitIndex then
          result :=
            result.set!
              basisIndex
              (CFloat.neg result[basisIndex]!)

      return result

  {
    machine with
    amplitudes := newAmplitudes
  }

private def applyGate1At
    (machine : Machine)
    (gate : String)
    (qubitIndex : Nat) :
    Except String Machine :=
  if gate == "x" then
    pure (applyXAt machine qubitIndex)
  else if gate == "h" then
    pure (applyHAt machine qubitIndex)
  else if gate == "z" then
    pure (applyZAt machine qubitIndex)
  else if gate == "id" then
    pure machine
  else
    throw s!"unsupported one-qubit gate: {gate}"

private def applyGate1Many
    (machine : Machine)
    (gate : String) :
    List Nat →
    Except String Machine
  | [] =>
      pure machine

  | qubitIndex :: rest => do
      let next ←
        applyGate1At machine gate qubitIndex

      applyGate1Many next gate rest
```

## Two qubit gates

The controlled X implementation swaps target pairs only when the control bit
is set. Equal control and target indices are rejected.

```lean

private def applyCXAt
    (machine : Machine)
    (control : Nat)
    (target : Nat) :
    Except String Machine := do
  if control == target then
    throw "the control and target of `cx` must be distinct"

  let targetMask :=
    qubitMask target

  let newAmplitudes :=
    Id.run do
      let mut result :=
        machine.amplitudes

      for basisIndex in [0:result.size] do
        if
            bitAt basisIndex control &&
            !(bitAt basisIndex target) then
          let pairedIndex :=
            basisIndex + targetMask

          let amplitude₀ :=
            result[basisIndex]!

          let amplitude₁ :=
            result[pairedIndex]!

          result :=
            result.set! basisIndex amplitude₁

          result :=
            result.set! pairedIndex amplitude₀

      return result

  pure {
    machine with
    amplitudes := newAmplitudes
  }

private def applyGate2At
    (machine : Machine)
    (gate : String)
    (arg₁ arg₂ : Nat) :
    Except String Machine :=
  if gate == "cx" then
    applyCXAt machine arg₁ arg₂
  else
    throw s!"unsupported two-qubit gate: {gate}"

private def applyGate2Pairs
    (machine : Machine)
    (gate : String) :
    List (Nat × Nat) →
    Except String Machine
  | [] =>
      pure machine

  | (arg₁, arg₂) :: rest => do
      let next ←
        applyGate2At machine gate arg₁ arg₂

      applyGate2Pairs next gate rest
```

## Measurement

Measurement computes the probability of zero, samples a bit, normalizes the
selected subspace, and records the result in classical storage.

```lean

private def probabilityZero
    (machine : Machine)
    (qubitIndex : Nat) :
    Float :=
  Id.run do
    let mut probability :=
      0.0

    for basisIndex in [0:machine.amplitudes.size] do
      if !(bitAt basisIndex qubitIndex) then
        probability :=
          probability +
            CFloat.normSq machine.amplitudes[basisIndex]!

    return probability

private def collapseAt
    (machine : Machine)
    (qubitIndex : Nat)
    (outcome : Bool)
    (probabilityOfZero : Float) :
    Machine :=
  let selectedProbability :=
    if outcome then
      1.0 - probabilityOfZero
    else
      probabilityOfZero

  let normalizationFactor :=
    1.0 / Float.sqrt selectedProbability

  let newAmplitudes :=
    Id.run do
      let mut result :=
        Array.replicate
          machine.amplitudes.size
          CFloat.zero

      for basisIndex in [0:machine.amplitudes.size] do
        if bitAt basisIndex qubitIndex == outcome then
          result :=
            result.set!
              basisIndex
              (CFloat.scale
                normalizationFactor
                machine.amplitudes[basisIndex]!)

      return result

  {
    machine with
    amplitudes := newAmplitudes
  }

private def updateClassicalRegisters
    (registers : List (String × ClassicalRegisterInfo))
    (name : String)
    (index : Nat)
    (value : Bool) :
    Except String (List (String × ClassicalRegisterInfo)) :=
  match registers with
  | [] =>
      throw s!"unknown classical register: {name}"

  | (registerName, info) :: rest =>
      if registerName == name then
        if index < info.bits.size then
          let updatedInfo : ClassicalRegisterInfo := {
            info with
            bits := info.bits.set! index value
          }

          pure ((registerName, updatedInfo) :: rest)
        else
          throw s!"classical-register index out of range: {name}[{index}]"
      else do
        let updatedRest ←
          updateClassicalRegisters
            rest
            name
            index
            value

        pure ((registerName, info) :: updatedRest)

private def setClassicalBit
    (machine : Machine)
    (name : String)
    (index : Nat)
    (value : Bool) :
    Except String Machine := do
  let updatedRegisters ←
    updateClassicalRegisters
      machine.cregs
      name
      index
      value

  pure {
    machine with
    cregs := updatedRegisters
  }

private def randomUnit : IO Float := do
  let value ←
    IO.rand 0 999999

  pure (Float.ofScientific value true 6)

private def measureOne
    (machine : Machine)
    (qubitIndex : Nat)
    (classicalRegister : String)
    (classicalIndex : Nat) :
    IO (Except String Machine) := do
  let p₀ :=
    probabilityZero machine qubitIndex

  let randomValue ←
    randomUnit

  let outcome : Bool :=
    !(randomValue < p₀)

  let collapsed :=
    collapseAt machine qubitIndex outcome p₀

  pure <|
    setClassicalBit
      collapsed
      classicalRegister
      classicalIndex
      outcome

private def measurePairs
    (machine : Machine) :
    List (Nat × (String × Nat)) →
    IO (Except String Machine)
  | [] =>
      pure (.ok machine)

  | (qubitIndex, classicalRegister, classicalIndex) :: rest => do
      match ←
        measureOne
          machine
          qubitIndex
          classicalRegister
          classicalIndex with
      | .error message =>
          pure (.error message)

      | .ok next =>
          measurePairs next rest
```

## Statement execution

Statements are interpreted sequentially. Whole register binary operations and
measurements require equally sized operands before locations are paired.

```lean

private def executeStmt
    (machine : Machine)
    (stmt : Stmt) :
    IO (Except String Machine) := do
  match stmt with
  | .version _ _ =>
      pure (.ok machine)

  | .includeFile _ =>
      pure (.ok machine)

  | .qubit name size =>
      pure (.ok (declareQuantumRegister machine name size))

  | .bit name size =>
      pure (.ok (declareClassicalRegister machine name size))

  | .gate1 gate arg =>
      match resolveQuantumRef machine arg with
      | .error message =>
          pure (.error message)

      | .ok qubits =>
          pure (applyGate1Many machine gate qubits)

  | .gate2 gate arg₁ arg₂ =>
      match
          resolveQuantumRef machine arg₁,
          resolveQuantumRef machine arg₂ with
      | .error message, _ =>
          pure (.error message)

      | _, .error message =>
          pure (.error message)

      | .ok qubits₁, .ok qubits₂ =>
          if qubits₁.length != qubits₂.length then
            pure (.error s!"gate `{gate}` received register operands of different sizes: {qubits₁.length} and {qubits₂.length}")
          else
            pure (
              applyGate2Pairs
                machine
                gate
                (List.zip qubits₁ qubits₂)
            )

  | .measure src dst =>
      match
          resolveQuantumRef machine src,
          resolveClassicalRef machine dst with
      | .error message, _ =>
          pure (.error message)

      | _, .error message =>
          pure (.error message)

      | .ok qubits, .ok classicalBits =>
          if qubits.length != classicalBits.length then
            pure (.error s!"measurement operands have different sizes: {qubits.length} and {classicalBits.length}")
          else
            measurePairs
              machine
              (List.zip qubits classicalBits)

private def executeStatements
    (machine : Machine) :
    List Stmt →
    IO (Except String Machine)
  | [] =>
      pure (.ok machine)

  | stmt :: rest => do
      match ← executeStmt machine stmt with
      | .error message =>
          pure (.error message)

      | .ok next =>
          executeStatements next rest
```

## Program execution

Public execution validates first, initializes an empty machine, and exposes a
snapshot containing the final state vector and classical registers.

`Program.execute` starts from the all zero state. Measurement uses `IO`
randomness and collapses the state vector. Static and runtime failures are
returned as `Except.error` values rather than raised as exceptions.

```lean

private def classicalSnapshot
    (machine : Machine) :
    List (String × Array Bool) :=
  machine.cregs.reverse.map
    (fun entry => (entry.1, entry.2.bits))

def Program.execute
    (program : Program) :
    IO (Except String ExecutionResult) := do
  match program.validate with
  | .error message =>
      pure (.error message)

  | .ok () =>
      match ← executeStatements Machine.empty program with
      | .error message =>
          pure (.error message)

      | .ok machine =>
          pure (.ok {
            qubitCount := machine.qubitCount
            amplitudes := machine.amplitudes
            classical := classicalSnapshot machine
          })
```

## Execution convenience syntax

The `execute program` term is a readable shorthand for
`Qasm.Program.execute program`.

```lean
macro "execute " program:term : term =>
  `(Qasm.Program.execute $program)

end Qasm
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
