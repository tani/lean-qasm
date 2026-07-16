    import LiterateLean
    open scoped LiterateLean

# Categorical wire interfaces

Interfaces are ordered lists of quantum and classical wires at categorical circuit
boundaries. Order is semantic: tensor concatenates interfaces and permutations describe
how positions move, so an interface is deliberately not a set or a width alone.

Sequential order and parallel composition are captured by list structure:

```math
I \otimes J \;=\; I \mathbin{+\!\!+} J,
\qquad
|I \otimes J| = |I| + |J|.
```

Thus two interfaces with the same width can still differ by wire order or wire kind.

```lean
namespace QASM.IR

inductive WireTy where
  | qubit
  | bit
  deriving Repr, BEq, DecidableEq, Hashable, Inhabited

abbrev Interface := List WireTy

end QASM.IR
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
