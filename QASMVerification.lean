    import LiterateLean
    import QASMVerification.Quantum
    import QASMVerification.ExactReal
    import QASMVerification.AngleRefinement
    import QASMVerification.RuntimeLaws
    import QASMVerification.QFTSwapLaws
    import QASMVerification.QFTSparseLaws
    import QASMVerification.QFTMatrixLaws
    import QASMVerification.FourierLaws
    import QASMVerification.TraceRefinement
    import QASMVerification.QFTLaws
    import QASMVerification.RefinementLaws
    import QASMVerification.GateLaws
    import QASMVerification.Program
    import QASMVerification.Native
    import QASMVerification.Instrument
    import QASMVerification.Circuit
    import QASMVerification.QFT
    open scoped LiterateLean

# Mathematical verification entry point

Import this library explicitly for mathematical reasoning. The executable QASM library
has no dependency on these modules. The original QFT gate product equals the normalized
positive-sign Fourier matrix for every register size, including physical swaps. All Proc
constructors have bidirectional finite-execution refinement through the shared control
machine. The actual Option interpreter and its public boundary instantiate that theorem.
Atomic callback graphs preserve finite classical execution; backend matrix accuracy,
external-effect models and the residual QFT program contract remain separate obligations.
No added axioms or placeholder proofs supply those connections.

```lean

```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
