    import LiterateLean
    import QASMVerification.Semantics
    import QASMVerification.Refinement
    import QASMVerification.QFT
    open scoped LiterateLean

# Mathematical verification entry point

Import this library explicitly for mathematical reasoning. Its three group entry points
are QASMVerification.Semantics, QASMVerification.Refinement and QASMVerification.QFT.
The executable QASM library has no dependency on these modules. The original QFT gate product equals the normalized
positive-sign Fourier matrix for every register size, including physical swaps. All Proc
constructors have bidirectional finite-execution refinement through the shared control
machine. The actual Option interpreter and its public boundary instantiate that theorem.
The residual QFT body additionally has every-size total correctness in the exact
bit-angle/ideal-matrix model: finite normal execution, restored locals, unique Fourier
action and no faults. Atomic callback graphs preserve finite classical execution;
Float backend accuracy and external-effect models remain separate obligations.
No added axioms or placeholder proofs supply those connections.

```lean

```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
