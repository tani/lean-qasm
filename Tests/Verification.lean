    import LiterateLean
    import QASMVerification
    open scoped LiterateLean

# Verification proof-dependency audit

This standalone module exposes the kernel dependencies of the main mathematical and
runtime-refinement results. It deliberately audits the concrete runtime-angle theorem
separately from the conditional total-correctness transport theorem. The every-size path-weight theorem and bidirectional structured Proc simulation are
also audited. They do not assert the remaining gate-product or partial-interpreter obligations.

```lean
#print axioms QASMVerification.nativeProfile_unitary
#print axioms QASMVerification.hadamard_nativeRecipe
#print axioms QASMVerification.runtimeHalves_exact
#print axioms QASMVerification.qft_runtime_phase
#print axioms QASMVerification.qftSteps_valid
#print axioms QASMVerification.runQFT_iff
#print axioms QASMVerification.qftCorrect_one
#print axioms QASMVerification.qft_target_block
#print axioms QASMVerification.qft_top_hadamard
#print axioms QASMVerification.reverseBits_involution
#print axioms QASMVerification.qftPathAmplitude_reversed_eq_fourier
#print axioms QASMVerification.proc_simulation
#print axioms QASMVerification.proc_lifting
#print axioms QASMVerification.trace_proc_refinement_iff
#print axioms QASMVerification.routing_compose
#print axioms QASMVerification.circuitEval_boundaries
#print axioms QASMVerification.totalCorrect_transfer
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
