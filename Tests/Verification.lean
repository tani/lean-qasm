    import LiterateLean
    import QASMVerification
    open scoped LiterateLean

# Verification proof-dependency audit

This standalone module exposes the kernel dependencies of the main mathematical and
runtime-refinement results. It deliberately audits the concrete runtime-angle theorem
separately from the conditional total-correctness transport theorem. The general QFT
Fourier obligation and full interpreter refinement are not asserted here.

```lean
#print axioms QASMVerification.nativeProfile_unitary
#print axioms QASMVerification.hadamard_nativeRecipe
#print axioms QASMVerification.runtimeHalves_exact
#print axioms QASMVerification.qft_runtime_phase
#print axioms QASMVerification.qftSteps_valid
#print axioms QASMVerification.runQFT_iff
#print axioms QASMVerification.qftCorrect_one
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
