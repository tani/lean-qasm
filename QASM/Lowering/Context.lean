    import LiterateLean
    import QASM.Frontend.Typing
    import QASM.IR.Program
    open scoped LiterateLean

# IR lowering context

Lowering assigns stable identifiers before walking bodies, then carries explicit lexical scopes while translating the checked frontend tree.

Lowering state separates the three identity spaces and a stack of lexical environments:

```mermaid
flowchart TD
    Context --> Analysis["immutable type analysis"]
    Context --> Counters["VarId / DeclId / CallableId counters"]
    Context --> Scopes["lexical scope stack"]
    Scopes --> Binding
    Binding --> IRVar["resolved IR variable"]
```

Monotone allocation gives each fresh variable an ID $v_{n+1}$ with
$v_{n+1} > v_n$, while scope exit changes visibility but never reuses an identity.

```lean
namespace QASM.Lowering

open QASM

```

## State and stable identity

`Context` combines immutable checking results with the mutable identities assigned during
lowering. Declaration IDs are global to the compilation unit, callable IDs inhabit their
own namespace, and variable IDs advance monotonically across nested scopes. A `Binding`
retains the source type for subsequent inference and the resolved IR variable for emitted
references; quantum gate parameters additionally carry their fixed circuit positions.

```lean
structure LoweringOptions where
  target  : QASM.TargetConfig := .default
  dialect : QASM.Dialect := .v3_0
  origins : Array (String × UInt64) := #[]
  deriving Inhabited

structure Binding where
  var           : QASM.IR.Var
  sourceType    : QASM.Frontend.ResolvedType
  writable      : Bool
  quantum       : Bool
  wirePositions : Option (Array Nat) := none
  deriving Inhabited

structure ConstantEntry where
  id   : QASM.IR.DeclId
  name : String
  type : QASM.Frontend.ResolvedType
  deriving Inhabited

structure ExternEntry where
  id   : QASM.IR.DeclId
  name : String
  deriving Inhabited

structure CallableEntry where
  id   : QASM.IR.CallableId
  name : String
  deriving Inhabited

structure GateEntry where
  kind           : QASM.IR.PrimitiveKind
  name           : String
  parameterCount : Nat
  qubitCount     : Nat
  deriving Inhabited

structure DeclarationTables where
  constants  : Array ConstantEntry := #[]
  externs    : Array ExternEntry := #[]
  callables  : Array CallableEntry := #[]
  gates      : Array GateEntry := #[]
  nextDeclId : Nat := 0
  deriving Inhabited

structure Context where
  options : LoweringOptions
  analysis : QASM.Frontend.TypeAnalysis
  tables : DeclarationTables
  scopes : List (List Binding) := [[]]
  localConstants : QASM.Frontend.ConstantEnvironment := []
  nextVarId : Nat := 0
  deriving Inhabited

abbrev LowerM := StateT Context (Except QASM.Diagnostic)

```

## Diagnostics and representation conversion

Lowering reuses frontend diagnostics so parse, type, and lowering failures share one
public error channel. These conversion functions are intentionally structural: all target
defaults and array dimensions were resolved by typing, so conversion cannot perform new
inference. Primitive gate recognition similarly maps only the checked standard vocabulary;
an unknown name must already have a user declaration.

```lean
def diagnostic (message : String) : QASM.Diagnostic := ⟨message⟩

def fail {α : Type} (message : String) : LowerM α :=
  throw (diagnostic message)

def sourceOrigin (options : LoweringOptions) : QASM.IR.SourceSpan :=
  { fileName := options.origins[0]?.map (·.1) |>.getD "" }

def scalarType : QASM.Frontend.ResolvedScalar → QASM.IR.ScalarTy
  | .bit width => .bit width
  | .sint width => .sint width
  | .uint width => .uint width
  | .float width => .float width
  | .angle width => .angle width
  | .boolean => .boolean
  | .complex width => .complex width
  | .duration => .duration
  | .stretch => .stretch
  | .qubit count => .qubit count
  | .void => .void

def resolvedType : QASM.Frontend.ResolvedType → QASM.IR.Type
  | .scalar value => .scalar (scalarType value)
  | .array element shape => .array (scalarType element) shape
  | .arrayRef mutable element shape rank => .arrayRef mutable (scalarType element) shape rank

def targetConfig (target : QASM.TargetConfig) : QASM.IR.TargetConfig :=
  { intWidth := target.intWidth, uintWidth := target.uintWidth,
    floatWidth := target.floatWidth, angleWidth := target.angleWidth }

def dialect : QASM.Dialect → QASM.IR.Dialect
  | .v3_0 => .v3_0
  | .extended => .extended

def primitiveKind? : String → Option QASM.IR.PrimitiveKind
  | "U" => some .u
  | "gphase" => some .gphase
  | "p" => some .p
  | "x" => some .x
  | "y" => some .y
  | "z" => some .z
  | "h" => some .h
  | "s" => some .s
  | "sdg" => some .sdg
  | "t" => some .t
  | "tdg" => some .tdg
  | "sx" => some .sx
  | "rx" => some .rx
  | "ry" => some .ry
  | "rz" => some .rz
  | "cx" | "CX" => some .cx
  | "cy" => some .cy
  | "cz" => some .cz
  | "ch" => some .ch
  | "swap" => some .swap
  | "cp" => some .cp
  | "crx" => some .crx
  | "cry" => some .cry
  | "crz" => some .crz
  | "ccx" => some .ccx
  | "cswap" => some .cswap
  | "cu" => some .cu
  | "phase" => some .phase
  | "cphase" => some .cphase
  | "id" => some .id
  | "u1" => some .u1
  | "u2" => some .u2
  | "u3" => some .u3
  | _ => none

```

## Preassigning declaration identities

OpenQASM permits a body to refer to declarations that appear later in source. The initial
scan therefore assigns every constant, extern, subroutine, and user gate its stable ID
before any body is lowered. Checked standard-gate signatures fill the same lookup table
without consuming declaration IDs, while unresolved signatures are rejected as an
inconsistency between typing and lowering.

```lean
private partial def unannotated : QASM.Frontend.Statement → QASM.Frontend.Statement
  | .annotated _ statement => unannotated statement
  | statement => statement

private def collectDeclaredEntries
    (options : LoweringOptions) (analysis : QASM.Frontend.TypeAnalysis)
    (program : QASM.Frontend.Program) : Except QASM.Diagnostic DeclarationTables := do
  let mut tables : DeclarationTables := {}
  let mut nextCallableId := 0
  for original in program.statements do
    match unannotated original with
    | .constDeclaration type name _ =>
        let resolved ← QASM.Frontend.resolveType options.target analysis.constants type
        tables := { tables with
          constants := tables.constants.push { id := ⟨tables.nextDeclId⟩, name, type := resolved }
          nextDeclId := tables.nextDeclId + 1 }
    | .externStatement name _ _ =>
        tables := { tables with
          externs := tables.externs.push { id := ⟨tables.nextDeclId⟩, name }
          nextDeclId := tables.nextDeclId + 1 }
    | .defStatement name _ _ _ =>
        tables := { tables with
          callables := tables.callables.push { id := ⟨nextCallableId⟩, name } }
        nextCallableId := nextCallableId + 1
    | .gateDefinition name parameters qubits _ =>
        let id : QASM.IR.DeclId := ⟨tables.nextDeclId⟩
        tables := { tables with
          gates := tables.gates.push
            { kind := .userDefined id, name,
              parameterCount := parameters.size, qubitCount := qubits.size }
          nextDeclId := tables.nextDeclId + 1 }
    | _ => pure ()
  for signature in analysis.gates do
    unless tables.gates.any (·.name == signature.name) do
      match primitiveKind? signature.name with
      | some kind =>
          let entry : GateEntry :=
            { kind, name := signature.name,
              parameterCount := signature.parameterCount, qubitCount := signature.qubitCount }
          tables := { tables with gates := tables.gates.push entry }
      | none =>
          throw (diagnostic s!"type analysis returned unresolved gate '{signature.name}'")
  pure tables

def Context.initialize
    (options : LoweringOptions) (analysis : QASM.Frontend.TypeAnalysis)
    (program : QASM.Frontend.Program) : Except QASM.Diagnostic Context := do
  pure { options, analysis, tables := ← collectDeclaredEntries options analysis program }

```

## Lexical lookup and type reuse

Bindings are searched from the innermost scope outward; global declaration tables remain
separate so shadowing cannot alter a resolved declaration ID. Expression inference is
delegated back to the completed `TypeAnalysis` with the current lexical bindings, avoiding
a second and potentially divergent type checker inside lowering.

```lean
def lookupBinding? (context : Context) (name : String) : Option Binding :=
  context.scopes.findSome? fun scope => scope.find? (·.var.name == name)

def lookupConstant? (context : Context) (name : String) : Option ConstantEntry :=
  context.tables.constants.find? (·.name == name)
def lookupLocalConstant? (context : Context) (name : String) : Option Int :=
  (context.localConstants.find? (·.1 == name)).map (·.2)


def lookupExtern? (context : Context) (name : String) : Option ExternEntry :=
  context.tables.externs.find? (·.name == name)

def lookupCallable? (context : Context) (name : String) : Option CallableEntry :=
  context.tables.callables.find? (·.name == name)

def lookupGate? (context : Context) (name : String) : Option GateEntry :=
  context.tables.gates.find? (·.name == name)

def lookupCallableSignature? (context : Context) (name : String) :
    Option QASM.Frontend.CallableSignature :=
  context.analysis.callables.find? (·.name == name)

def typeBindings (context : Context) : List (String × QASM.Frontend.ResolvedType) :=
  context.scopes.flatMap (·.map fun binding => (binding.var.name, binding.sourceType)) ++
    context.tables.constants.toList.map fun entry => (entry.name, entry.type)

def inferType (expression : QASM.Frontend.Expression) : LowerM QASM.Frontend.ResolvedType := do
  let context ← get
  match context.analysis.inferExpressionType context.options.target (typeBindings context) expression with
  | .ok type => pure type
  | .error error => throw error
def evalConstInt (expression : QASM.Frontend.Expression) : LowerM Int := do
  let context ← get
  match QASM.Frontend.evalConstInt
      (context.localConstants ++ context.analysis.constants) expression with
  | .ok value => pure value
  | .error error => throw error


```

## Binding and scope lifecycle

Fresh bindings update only the current lexical frame and record whether later assignments
are legal. Scope operations are explicit because gate and subroutine lowering temporarily
replace the caller's scope stack, then restore it after collecting local declarations.

```lean
def freshBinding (name : String) (type : QASM.Frontend.ResolvedType)
    (writable : Bool) (wirePositions : Option (Array Nat) := none) : LowerM Binding := do
  let context ← get
  let var : QASM.IR.Var :=
    { id := ⟨context.nextVarId⟩, name, type := resolvedType type,
      origin := sourceOrigin context.options }
  let binding : Binding :=
    { var, sourceType := type, writable, wirePositions,
      quantum := match type with | .scalar (.qubit _) => true | _ => false }
  let scopes := match context.scopes with
    | [] => [[binding]]
    | scope :: rest => (binding :: scope) :: rest
  set { context with scopes, nextVarId := context.nextVarId + 1 }
  pure binding

def pushScope : LowerM Unit := modify fun context => { context with scopes := [] :: context.scopes }

def popScope : LowerM Unit := modify fun context =>
  { context with scopes := context.scopes.drop 1 }

def replaceScopes (scopes : List (List Binding)) : LowerM Unit :=
  modify fun context => { context with scopes }

end QASM.Lowering
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
