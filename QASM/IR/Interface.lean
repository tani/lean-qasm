    import LiterateLean
    open scoped LiterateLean

# Categorical wire interfaces

Interfaces are ordered lists of quantum and classical wires at categorical circuit
boundaries. Order is semantic: tensor concatenates interfaces and permutations describe
how positions move, so an interface is deliberately not a set or a width alone.

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
