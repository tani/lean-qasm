    import LiterateLean
    import QASM.Lowering.Proc
    open scoped LiterateLean

# Declaration lowering

Top-level declaration lowering reuses the preassigned declaration and callable identifiers while isolating gate and subroutine lexical scopes.

```lean
namespace QASM.Lowering

open QASM

```

## Value and boundary declarations

Constants, externs, and I/O fields reuse the IDs assigned during context initialization.
Types are resolved through the completed analysis, and I/O declarations also create
lexical bindings for the program body. Inputs are read-only there; outputs remain writable
and later become fields in the generated boundary structures.

```lean
private def resolveDeclarationType (type : QASM.Frontend.TypeSpec) :
    LowerM QASM.Frontend.ResolvedType := do
  let context ← get
  match QASM.Frontend.resolveType context.options.target context.analysis.constants type with
  | .ok value => pure value
  | .error error => throw error

def constantDeclaration (type : QASM.Frontend.TypeSpec) (name : String)
    (value : QASM.Frontend.Expression) : LowerM QASM.IR.ConstantDecl := do
  let context ← get
  let entry ← match lookupConstant? context name with
    | some entry => pure entry
    | none => fail s!"constant '{name}' has no resolved declaration ID"
  let type ← resolveDeclarationType type
  let value ← expression value
  let result : QASM.IR.ConstantDecl :=
    { id := entry.id, name := name, type := resolvedType type, value := value,
      origin := sourceOrigin context.options }
  pure result

def externDeclaration (name : String) (arguments : Array QASM.Frontend.TypeSpec)
    (returnType : Option QASM.Frontend.TypeSpec) : LowerM QASM.IR.ExternDecl := do
  let context ← get
  let entry ← match lookupExtern? context name with
    | some entry => pure entry
    | none => fail s!"extern '{name}' has no resolved declaration ID"
  let parameters ← arguments.mapM resolveDeclarationType
  let returnType ← match returnType with
    | some type => resolveDeclarationType type
    | none => pure (.scalar .void)
  let result : QASM.IR.ExternDecl :=
    { id := entry.id, name := name, parameters := parameters.map resolvedType,
      returnType := resolvedType returnType, origin := sourceOrigin context.options }
  pure result

def ioDeclaration (name : String) (type : QASM.Frontend.TypeSpec)
    (input : Bool) : LowerM QASM.IR.IODecl := do
  let context ← get
  let type ← resolveDeclarationType type
  let binding ← freshBinding name type (!input)
  let result : QASM.IR.IODecl :=
    { var := binding.var, origin := sourceOrigin context.options }
  pure result

```

## Pure gate declarations

A gate body is lowered in an isolated scope whose parameters are target-width angles and
whose qubit parameters occupy known wire positions. The resulting declaration stores a
pure categorical `Circuit`; restoring the outer scopes afterward prevents gate-local
bindings from leaking into the compilation unit.

```lean
def gateDeclaration (name : String) (parameterNames qubitNames : Array String)
    (body : Array QASM.Frontend.Statement) : LowerM QASM.IR.GateDecl := do
  let outer ← get
  let gate ← match lookupGate? outer name with
    | some gate => pure gate
    | none => fail s!"gate '{name}' has no resolved declaration"
  let id ← match gate.kind with
    | .userDefined id => pure id
    | _ => fail s!"user gate '{name}' resolved as a standard primitive"
  replaceScopes [[]]
  modify fun context => { context with localConstants := [] }
  let parameterType : QASM.Frontend.ResolvedType :=
    .scalar (.angle outer.options.target.angleWidth)
  let mut parameters := #[]
  for parameter in parameterNames do
    let binding ← freshBinding parameter parameterType false
    parameters := parameters.push binding.var
  let mut qubits := #[]
  for index in [:qubitNames.size] do
    let binding ← freshBinding qubitNames[index]! (.scalar (.qubit 1)) false (some #[index])
    qubits := qubits.push binding.var
  let circuit ← gateBody qubitNames.size body
  let after ← get
  set { after with scopes := outer.scopes, localConstants := outer.localConstants }
  let result : QASM.IR.GateDecl :=
    { id := id, name := name, parameters := parameters, qubits := qubits, body := circuit,
      origin := sourceOrigin outer.options }
  pure result

```

## Effectful subroutine declarations

Subroutines use their checked signature to establish parameter mutability and resolved
types. Their bodies lower to `Proc`, local bindings are wrapped in one explicit scope, and
the caller's lowering environment is restored after construction. Recursive references
are valid because callable IDs were assigned before any body was visited.

```lean
def subroutineDeclaration (name : String)
    (arguments : Array QASM.Frontend.ArgumentDefinition)
    (returnType : Option QASM.Frontend.TypeSpec) (body : Array QASM.Frontend.Statement) :
    LowerM QASM.IR.SubroutineDecl := do
  let outer ← get
  let callable ← match lookupCallable? outer name with
    | some callable => pure callable
    | none => fail s!"subroutine '{name}' has no resolved callable ID"
  let signature ← match lookupCallableSignature? outer name with
    | some signature => pure signature
    | none => fail s!"subroutine '{name}' has no checked signature"
  replaceScopes [[]]
  modify fun context => { context with localConstants := [] }
  let mut parameters := #[]
  for pair in arguments.zip signature.arguments do
    let writable := match pair.1.type with | .arrayRef false _ _ _ => false | _ => true
    let binding ← freshBinding pair.1.name pair.2 writable
    parameters := parameters.push binding.var
  let loweredBody ← statements body
  let afterBody ← get
  let parameterIds := parameters.map (·.id)
  let bindings : List Binding := afterBody.scopes.headD []
  let locals := (bindings.reverse.filter fun binding =>
    !parameterIds.contains binding.var.id).map (·.var) |>.toArray
  let loweredBody := if locals.isEmpty then loweredBody else .scope locals loweredBody
  let after ← get
  set { after with scopes := outer.scopes, localConstants := outer.localConstants }
  let returnType ← match returnType with
    | some type => resolveDeclarationType type
    | none => pure (.scalar .void)
  let result : QASM.IR.SubroutineDecl :=
    { id := callable.id, name := name, parameters := parameters,
      returnType := resolvedType returnType,
      body := loweredBody, origin := sourceOrigin outer.options }
  pure result

end QASM.Lowering
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
