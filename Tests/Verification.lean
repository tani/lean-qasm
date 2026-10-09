    import LiterateLean
    import QASMVerification
    open scoped LiterateLean

# Verification proof-dependency audit

This standalone module exposes the kernel dependencies of the original every-size QFT
matrix equality, residual-loop total correctness, shared control machine and concrete
Option interpreter refinement. The residual QFT theorem uses exact bit angles and
ideal complex matrices, with normal termination, restored locals and no faults. It
also audits runtime angle normalization and the conditional total-correctness transport
separately; finite successful execution does not assert arbitrary-program termination
or exact Float-to-real backend behavior.

```lean
#print axioms QASMVerification.nativeProfile_unitary
#print axioms QASMVerification.hadamard_nativeRecipe
#print axioms QASMVerification.runtimeHalves_exact
#print axioms QASMVerification.qft_runtime_phase
#print axioms QASMVerification.qftSteps_valid
#print axioms QASMVerification.runQFT_iff
#print axioms QASMVerification.qftCorrect_one
#print axioms QASMVerification.qftCorrect_all
#print axioms QASMVerification.qftProgramCorrect_all
#print axioms QASMVerification.QFTExecution.inner_iterations
#print axioms QASMVerification.QFTExecution.body_totalCorrect
#print axioms QASMVerification.QFTExecution.body_action
#print axioms QASMVerification.QFTExecution.machine_eval_iff
#print axioms QASMVerification.qftCore_matrix
#print axioms QASMVerification.swapRange_matrix
#print axioms QASMVerification.control_refinement_iff
#print axioms QASMVerification.Machine.machine_proc_refinement_iff
#print axioms QASMVerification.runtimeKernel_normal
#print axioms QASMVerification.runFrom_refinement_iff
#print axioms QASMVerification.run_refinement_iff
#print axioms QASM.Execution.ControlMachine.drive_failure
#print axioms QASMVerification.qft_target_block
#print axioms QASMVerification.qft_top_hadamard
#print axioms QASMVerification.hadamard_row_action
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
