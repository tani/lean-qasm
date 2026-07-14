import Lean
import LiterateLean

# Qasm embedded language and interpreter

This module implements a small executable subset of OpenQASM 2.0. It combines
an abstract syntax tree, a checked embedded syntax, static validation, source
serialization, and a state vector interpreter.

The supported statements are:

- `OPENQASM 2.0;`
- `include "...";`
- `qreg q[n];`
- `creg c[n];`
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

```lean

/-- A reference to a quantum or classical register.

When `index` is absent, the reference denotes the whole register. When it is
present, it selects one zero-based register element.
-/
structure Ref where
  /-- The register name as it appears in OpenQASM source. -/
  name : String
  /-- An optional zero-based element index. -/
  index : Option Nat
  deriving Repr, Inhabited, BEq

/-- The abstract syntax of the supported OpenQASM 2.0 statement subset. -/
inductive Stmt where
  /-- An `OPENQASM major.minor;` version declaration. -/
  | version :
      Nat →
      Nat →
      Stmt
  /-- An `include "file";` directive. Includes are recorded but not loaded. -/
  | includeFile :
      String →
      Stmt
  /-- A quantum-register declaration with its name and size. -/
  | qreg :
      String →
      Nat →
      Stmt
  /-- A classical-register declaration with its name and size. -/
  | creg :
      String →
      Nat →
      Stmt
  /-- A named single-qubit gate applied to one reference. -/
  | gate1 :
      String →
      Ref →
      Stmt
  /-- A named two-qubit gate applied to two references. -/
  | gate2 :
      String →
      Ref →
      Ref →
      Stmt
  /-- A measurement from a quantum reference into a classical reference. -/
  | measure :
      Ref →
      Ref →
      Stmt
  deriving Repr, Inhabited, BEq

/-- An OpenQASM program represented as its statements in source order. -/
abbrev Program := List Stmt
```

## OpenQASM serialization

Each syntax node can be rendered back to normalized OpenQASM source. Programs
place one statement on each line.

```lean

/-- Render a register reference using OpenQASM syntax. -/
def Ref.toQasm : Ref → String
  | ⟨name, none⟩ =>
      name
  | ⟨name, some index⟩ =>
      s!"{name}[{index}]"

/-- Render one abstract-syntax statement as OpenQASM 2.0 source. -/
def Stmt.toQasm : Stmt → String
  | .version major minor =>
      s!"OPENQASM {major}.{minor};"

  | .includeFile filename =>
      s!"include \"{filename}\";"

  | .qreg name size =>
      s!"qreg {name}[{size}];"

  | .creg name size =>
      s!"creg {name}[{size}];"

  | .gate1 gate arg =>
      s!"{gate} {arg.toQasm};"

  | .gate2 gate arg₁ arg₂ =>
      s!"{gate} {arg₁.toQasm}, {arg₂.toQasm};"

  | .measure src dst =>
      s!"measure {src.toQasm} -> {dst.toQasm};"

/-- Render a program as newline-separated OpenQASM statements. -/
def Program.toQasm (program : Program) : String :=
  String.intercalate "\n" (program.map Stmt.toQasm)
```

## Static validation

Validation walks statements in source order while accumulating declared
registers. This enforces declaration before use and produces the earliest
actionable error.

```lean

/-- Distinguishes quantum registers from classical registers during validation. -/
inductive RegisterKind where
  | quantum
  | classical
  deriving Repr, Inhabited, BEq

/-- Static information recorded for a declared register. -/
structure RegisterInfo where
  /-- Whether the register stores qubits or classical bits. -/
  kind : RegisterKind
  /-- The positive number of elements declared for the register. -/
  size : Nat
  deriving Repr, Inhabited, BEq

/-- Register declarations accumulated while validating source order. -/
abbrev RegisterEnv := List (String × RegisterInfo)

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
  | .version major minor =>
      if major == 2 && minor == 0 then
        pure env
      else
        throw s!"unsupported OpenQASM version: {major}.{minor}"

  | .includeFile _ =>
      pure env

  | .qreg name size =>
      if size == 0 then
        throw s!"quantum register {name} must have positive size"
      else if (lookupRegister? env name).isSome then
        throw s!"duplicate register declaration: {name}"
      else
        pure ((name, ⟨.quantum, size⟩) :: env)

  | .creg name size =>
      if size == 0 then
        throw s!"classical register {name} must have positive size"
      else if (lookupRegister? env name).isSome then
        throw s!"duplicate register declaration: {name}"
      else
        pure ((name, ⟨.classical, size⟩) :: env)

  | .gate1 _ arg =>
      validateRef env arg (some .quantum)
      pure env

  | .gate2 _ arg₁ arg₂ =>
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

/-- Check declaration order, register kinds, bounds, and the OpenQASM version.

Validation returns the first human-readable error. It does not execute the
program or check whether a gate name is supported by the interpreter.
-/
def Program.validate (program : Program) : Except String Unit := do
  match program with
  | [] =>
      throw "empty OpenQASM program"

  | .version 2 0 :: rest =>
      validateStatements [] rest

  | .version major minor :: _ =>
      throw s!"unsupported OpenQASM version: {major}.{minor}"

  | _ =>
      throw "the first statement must be `OPENQASM 2.0;`"
```

## Embedded OpenQASM syntax

The following syntax categories describe register references and statements.
The `qasm` term syntax collects them into a `Qasm.Program`.

```lean

declare_syntax_cat qasmRef
declare_syntax_cat qasmStmt

syntax ident : qasmRef
syntax ident "[" num "]" : qasmRef

syntax "OPENQASM" scientific ";" : qasmStmt

syntax "include" str ";" : qasmStmt
syntax "qreg" ident "[" num "]" ";" : qasmStmt
syntax "creg" ident "[" num "]" ";" : qasmStmt
syntax "measure" qasmRef "->" qasmRef ";" : qasmStmt

syntax ident qasmRef ";" : qasmStmt
syntax ident qasmRef "," qasmRef ";" : qasmStmt

syntax (name := qasmProgram)
  "qasm" "{" qasmStmt* "}" : term

open Lean
open Lean Macro

private abbrev LeanTermSyntax :=
  TSyntax `term
```

## Macro expansion

Macro expansion translates the surface syntax into explicit constructors.
OpenQASM version errors are reported at expansion time when possible.

```lean

private def expandRef :
    Syntax →
    MacroM LeanTermSyntax
  | `(qasmRef| $name:ident[$index:num]) => do
      let nameString := name.getId.toString
      let indexValue := index.getNat

      `(Qasm.Ref.mk
          $(quote nameString)
          (some $(quote indexValue)))

  | `(qasmRef| $name:ident) => do
      let nameString := name.getId.toString

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
  | `(qasmStmt| OPENQASM $version:scientific;) => do
      let (mantissa, decimalExponent, exponent) :=
        version.getScientific

      unless
          mantissa == 20 &&
          decimalExponent &&
          exponent == 1 do
        Macro.throwErrorAt
          version
          "only `OPENQASM 2.0;` is supported"

      `(Qasm.Stmt.version 2 0)

  | `(qasmStmt| include $filename:str;) => do
      let filenameString := filename.getString

      `(Qasm.Stmt.includeFile
          $(quote filenameString))

  | `(qasmStmt| qreg $name:ident[$size:num];) => do
      let nameString := name.getId.toString
      let sizeValue := size.getNat

      `(Qasm.Stmt.qreg
          $(quote nameString)
          $(quote sizeValue))

  | `(qasmStmt| creg $name:ident[$size:num];) => do
      let nameString := name.getId.toString
      let sizeValue := size.getNat

      `(Qasm.Stmt.creg
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

      `(Qasm.Stmt.gate1
          $(quote gateName)
          $argTerm)

  | `(qasmStmt| $gate:ident $arg₁:qasmRef, $arg₂:qasmRef;) => do
      let gateName := gate.getId.toString
      let arg₁Term ← expandRef arg₁
      let arg₂Term ← expandRef arg₂

      `(Qasm.Stmt.gate2
          $(quote gateName)
          $arg₁Term
          $arg₂Term)

  | stx =>
      Macro.throwErrorAt
        stx
        "unsupported OpenQASM statement"

macro_rules
  | `(qasm { $stmts:qasmStmt* }) => do
      let init : LeanTermSyntax ←
        `(([] : Qasm.Program))

      stmts.foldrM
        (β := LeanTermSyntax)
        (init := init)
        fun stmt rest => do
          let stmtTerm ← expandStmt stmt.raw
          `($stmtTerm :: $rest)
```

## Complex amplitudes

The interpreter uses a compact complex number type backed by Lean `Float`
values. It is intended for executable simulation rather than exact proofs.

```lean

/-- A complex number backed by machine floating-point components. -/
structure CFloat where
  /-- Real component. -/
  re : Float
  /-- Imaginary component. -/
  im : Float
  deriving Repr, Inhabited

namespace CFloat

/-- The complex value zero. -/
def zero : CFloat :=
  ⟨0.0, 0.0⟩

/-- The complex value one. -/
def one : CFloat :=
  ⟨1.0, 0.0⟩

/-- Add two complex values componentwise. -/
def add (lhs rhs : CFloat) : CFloat :=
  ⟨lhs.re + rhs.re, lhs.im + rhs.im⟩

/-- Subtract two complex values componentwise. -/
def sub (lhs rhs : CFloat) : CFloat :=
  ⟨lhs.re - rhs.re, lhs.im - rhs.im⟩

/-- Negate both components of a complex value. -/
def neg (value : CFloat) : CFloat :=
  ⟨-value.re, -value.im⟩

/-- Scale a complex value by a real factor. -/
def scale (factor : Float) (value : CFloat) : CFloat :=
  ⟨factor * value.re, factor * value.im⟩

/-- Return the squared magnitude `re² + im²`. -/
def normSq (value : CFloat) : Float :=
  value.re * value.re + value.im * value.im

end CFloat
```

## Runtime state

The machine stores one global state vector and maps each source register onto
its quantum or classical runtime storage.

```lean

/-- Runtime location of a quantum register in the global state vector. -/
structure QuantumRegisterInfo where
  /-- First global qubit index owned by the register. -/
  offset : Nat
  /-- Number of consecutive qubits in the register. -/
  size : Nat
  deriving Repr, Inhabited

/-- Mutable runtime contents of a classical register. -/
structure ClassicalRegisterInfo where
  bits : Array Bool
  deriving Repr, Inhabited

/-- Internal interpreter state.

The amplitude array has `2 ^ qubitCount` entries. Register tables map source
names to their runtime storage.
-/
structure Machine where
  qubitCount : Nat
  amplitudes : Array CFloat
  qregs : List (String × QuantumRegisterInfo)
  cregs : List (String × ClassicalRegisterInfo)
  deriving Repr, Inhabited

/-- The initial zero-qubit machine, whose sole amplitude is one. -/
def Machine.empty : Machine where
  qubitCount := 0
  amplitudes := #[CFloat.one]
  qregs := []
  cregs := []

/-- Observable state returned after successful execution. -/
structure ExecutionResult where
  /-- Total number of allocated qubits. -/
  qubitCount : Nat
  /-- Final state vector in little-endian basis-index order. -/
  amplitudes : Array CFloat
  /-- Classical registers in declaration order. -/
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

private def qubitMask (qubit : Nat) : Nat :=
  2 ^ qubit

private def bitAt
    (basisIndex : Nat)
    (qubit : Nat) :
    Bool :=
  ((basisIndex / qubitMask qubit) % 2) == 1
```

## Single qubit gates

Gate implementations update paired amplitudes in place within an `Id` block.
The supported names are `id`, `x`, `h`, and `z`.

```lean

private def applyXAt
    (machine : Machine)
    (qubit : Nat) :
    Machine :=
  let mask :=
    qubitMask qubit

  let newAmplitudes :=
    Id.run do
      let mut result :=
        machine.amplitudes

      for basisIndex in [0:result.size] do
        if !(bitAt basisIndex qubit) then
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
    (qubit : Nat) :
    Machine :=
  let mask :=
    qubitMask qubit

  let factor :=
    1.0 / Float.sqrt 2.0

  let newAmplitudes :=
    Id.run do
      let mut result :=
        machine.amplitudes

      for basisIndex in [0:result.size] do
        if !(bitAt basisIndex qubit) then
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
    (qubit : Nat) :
    Machine :=
  let newAmplitudes :=
    Id.run do
      let mut result :=
        machine.amplitudes

      for basisIndex in [0:result.size] do
        if bitAt basisIndex qubit then
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
    (qubit : Nat) :
    Except String Machine :=
  if gate == "x" then
    pure (applyXAt machine qubit)
  else if gate == "h" then
    pure (applyHAt machine qubit)
  else if gate == "z" then
    pure (applyZAt machine qubit)
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

  | qubit :: rest => do
      let next ←
        applyGate1At machine gate qubit

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
    (qubit : Nat) :
    Float :=
  Id.run do
    let mut probability :=
      0.0

    for basisIndex in [0:machine.amplitudes.size] do
      if !(bitAt basisIndex qubit) then
        probability :=
          probability +
            CFloat.normSq machine.amplitudes[basisIndex]!

    return probability

private def collapseAt
    (machine : Machine)
    (qubit : Nat)
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
        if bitAt basisIndex qubit == outcome then
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
    (qubit : Nat)
    (classicalRegister : String)
    (classicalIndex : Nat) :
    IO (Except String Machine) := do
  let p₀ :=
    probabilityZero machine qubit

  let randomValue ←
    randomUnit

  let outcome : Bool :=
    !(randomValue < p₀)

  let collapsed :=
    collapseAt machine qubit outcome p₀

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

  | (qubit, classicalRegister, classicalIndex) :: rest => do
      match ←
        measureOne
          machine
          qubit
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

  | .qreg name size =>
      pure (.ok (declareQuantumRegister machine name size))

  | .creg name size =>
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

```lean

private def classicalSnapshot
    (machine : Machine) :
    List (String × Array Bool) :=
  machine.cregs.reverse.map
    (fun entry => (entry.1, entry.2.bits))

/-- Validate and execute an OpenQASM program from the all-zero initial state.

Measurement uses `IO` randomness and collapses the state vector. Static and
runtime failures are returned as `Except.error` values rather than exceptions.
-/
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

/-- Term syntax for `Qasm.Program.execute program`. -/
macro "execute " program:term : term =>
  `(Qasm.Program.execute $program)

end Qasm
```
