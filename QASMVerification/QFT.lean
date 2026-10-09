    import LiterateLean
    import QASMVerification.QFT.Model
    import QASMVerification.QFT.Angles
    import QASMVerification.QFT.Reference
    import QASMVerification.QFT.Fourier
    import QASMVerification.QFT.Matrix
    import QASMVerification.QFT.Sparse
    import QASMVerification.QFT.Core
    import QASMVerification.QFT.Swaps
    import QASMVerification.QFT.Execution
    import QASMVerification.QFT.Loops
    import QASMVerification.QFT.Program
    open scoped LiterateLean

# QFT verification entry point

The model, exact angle arithmetic, reference gate execution, Fourier analysis and
residual-loop proofs are grouped here. Import this entry point to obtain the every-size
matrix equality and qftProgramCorrect_all for the exact shared-machine model.
The original IR loops remain in QASM.IR.QFT; Float backend accuracy is a separate proof.

```lean

```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
