    import LiterateLean
    import QASM.IR.Source
    import QASM.IR.Name
    import QASM.IR.Type
    import QASM.IR.Expr
    import QASM.IR.Circuit
    import QASM.IR.Proc
    open scoped LiterateLean

# Compilation-unit declarations

Compilation-unit declarations keep pure gate circuits separate from effectful subroutine
processes. Each declaration combines stable identity, display metadata, resolved types,
and origin exactly once; downstream consumers never consult the source AST.

The compilation unit keeps declaration families separate while sharing resolved identity
and source metadata:

```mermaid
flowchart TD
    Metadata["version / target / origins"] --> Program
    Constants --> Program
    Gates["pure gate circuits"] --> Program
    Subroutines["effectful processes"] --> Program
    IO["inputs / outputs"] --> Program
```

This separation prevents a gate body from acquiring process effects by representation
accident.

```lean
namespace QASM.IR

```

## Compilation metadata

Version, target widths, dialect, origins, include digests, annotations, and pragmas make a
canonical program reproducible without coupling execution to source files. Directives are
retained as ordered data but have no portable runtime meaning.

```lean
structure Version where
  major : Nat := 3
  minor : Nat := 0
  deriving Repr, BEq, Inhabited

structure TargetConfig where
  intWidth   : Nat := 64
  uintWidth  : Nat := 64
  floatWidth : Nat := 64
  angleWidth : Nat := 64
  deriving Repr, BEq, Inhabited

inductive Dialect
  | v3_0
  | extended
  deriving Repr, BEq, DecidableEq, Inhabited

structure ProgramOrigin where
  name   : String
  digest : UInt64
  deriving Repr, BEq, Inhabited

structure IncludeInfo where
  filename     : String
  resolvedPath : String := ""
  digest       : UInt64 := 0
  origin       : SourceSpan := {}
  deriving Repr, BEq, Inhabited

structure Annotation where
  keyword : String
  content : Option String := none
  origin  : SourceSpan := {}
  deriving Repr, BEq, Inhabited

structure Pragma where
  content : String
  origin  : SourceSpan := {}
  deriving Repr, BEq, Inhabited

```

## Values and external boundaries

I/O declarations expose typed variables, constants store their resolved expression, and
named types or externs occupy the declaration-ID namespace. These records contain enough
information for emission and boundary generation even when a capability prevents portable
execution.

```lean
structure IODecl where
  var    : Var
  origin : SourceSpan := {}
  deriving Repr, BEq, Inhabited

structure ConstantDecl where
  id     : DeclId
  name   : Name
  type   : «Type»
  value  : Expr
  origin : SourceSpan := {}
  deriving Repr, BEq, Inhabited

structure TypeDecl where
  id     : DeclId
  name   : Name
  type   : «Type»
  origin : SourceSpan := {}
  deriving Repr, BEq, Inhabited

structure ExternDecl where
  id         : DeclId
  name       : Name
  parameters : Array «Type» := #[]
  returnType : «Type»
  origin     : SourceSpan := {}
  deriving Repr, BEq, Inhabited

```

## Gates and subroutines

Gate parameters and qubits bind a pure `Circuit`; subroutine parameters bind an effectful
`Proc` and an explicit return type. Separate `DeclId` and `CallableId` spaces make this
semantic distinction visible in every reference.

```lean
structure GateDecl where
  id         : DeclId
  name       : Name
  parameters : Array Var := #[]
  qubits     : Array Var := #[]
  body       : Circuit
  origin     : SourceSpan := {}
  deriving Repr, BEq, Inhabited

structure SubroutineDecl where
  id         : CallableId
  name       : Name
  parameters : Array Var := #[]
  returnType : «Type»
  body       : Proc
  origin     : SourceSpan := {}
  deriving Repr, BEq, Inhabited

end QASM.IR
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
