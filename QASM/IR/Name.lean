    import LiterateLean
    open scoped LiterateLean

# IR names and resolved identifiers

References use stable numeric identifiers, while names remain display metadata only.
Variables, declarations, and callables use distinct ID types so accidental cross-namespace
lookup is rejected by Lean. Capabilities identify semantics that require a target, and
control polarity is shared by circuit IR, runtime unitaries, and diagrams.

The identifier spaces remain deliberately disjoint even when their underlying natural
numbers coincide:

```mermaid
flowchart LR
    SourceName["source name"] --> VarId
    SourceName --> DeclId
    SourceName --> CallableId
    VarId --> Values["local values"]
    DeclId --> Declarations
    CallableId --> Calls
```

The arrows show resolution domains, not coercions: no ID kind converts implicitly into
another.

```lean
namespace QASM.IR

abbrev Name := String

structure VarId where
  value : Nat
  deriving Repr, BEq, DecidableEq, Hashable, Inhabited

structure DeclId where
  value : Nat
  deriving Repr, BEq, DecidableEq, Hashable, Inhabited

structure CallableId where
  value : Nat
  deriving Repr, BEq, DecidableEq, Hashable, Inhabited

inductive Capability
  | externalFunction
  | calibration
  | timing
  | physicalQubit
  deriving Repr, BEq, DecidableEq, Hashable, Inhabited

inductive ControlPolarity
  | positive
  | negative
  deriving Repr, BEq, DecidableEq, Hashable, Inhabited

end QASM.IR
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
