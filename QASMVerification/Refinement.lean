    import LiterateLean
    import QASMVerification.Refinement.Proc
    import QASMVerification.Refinement.Control
    import QASMVerification.Refinement.Machine
    import QASMVerification.Refinement.Runtime
    import QASMVerification.Refinement.Trace
    import QASMVerification.Refinement.TotalCorrectness
    open scoped LiterateLean

# Structured execution refinement entry point

This group connects declarative Proc semantics to structured evaluation, the shared
control machine and the actual Option interpreter. It also provides trace-to-matrix
refinement and total-correctness transport. These generic laws cover every Proc
constructor; program-specific termination and backend accuracy are separate obligations.

```lean

```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
