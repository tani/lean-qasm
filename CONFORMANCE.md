# OpenQASM 3.0 conformance

LeanQASM targets the official `spec/v3.0.0` grammar from the OpenQASM
repository. Progress is measured in five equally weighted feature bundles;
a bundle contributes 20 percentage points only when all of its acceptance
tests pass.

| Bundle | Status | Contents |
| --- | --- | --- |
| Quantum core frontend | Complete (20%) | Lexer, version/include, register declarations, gate calls, measure, reset, barrier, normalized printing |
| Expressions and types | Complete (40%) | Full precedence expression AST, scalar/array types, declarations, assignments, normalized printing and constant checking |
| Structured language | Complete (60%) | Scopes, control flow, subroutines, extern and gate declarations, scope checking and normalized printing |
| Advanced quantum/timing | Complete (80%) | Gate modifiers, timing, calibration syntax, pragmas, annotations and structured backend capabilities |
| Semantic closure | Planned | Complete static semantics, backend-independent execution and full official fixture audit |

The grammar, examples, and license under `Tests/Fixtures/OpenQASM30` are copied
from the official `spec/v3.0.0` tag. Backend-dependent extern, calibration,
physical-qubit, and timing operations will be represented and checked, but the
fixed state-vector simulator will report a structured unsupported-capability
error when their behavior cannot be determined by the core specification.
