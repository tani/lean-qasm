# OpenQASM 3.0 conformance

LeanQASM targets the official `spec/v3.0.0` grammar from the OpenQASM
repository. Progress is measured in five equally weighted feature bundles;
a bundle contributes 20 percentage points only when all of its acceptance
tests pass. The percentage measures completion of this explicitly documented
subset roadmap; it does not claim that backend-dependent OpenPulse behavior is
portable or executable by the state-vector backend.

| Bundle | Status | Contents |
| --- | --- | --- |
| Quantum core frontend | Complete (20%) | Lexer, version/include, register declarations, gate calls, measure, reset, barrier, normalized printing |
| Expressions and types | Complete (40%) | Full precedence expression AST, scalar/array types, declarations, assignments, normalized printing and constant checking |
| Structured language | Complete (60%) | Scopes, control flow, subroutines, extern and gate declarations, scope checking and normalized printing |
| Advanced quantum/timing | Complete (80%) | Gate modifiers, timing, calibration syntax, pragmas, annotations and structured backend capabilities |
| Semantic closure | Complete (100%) | Static scope/capability closure, bounded backend-independent simulation, `parseFile`, switch/range completion, and 21/21 official example syntax audit and 10/10 official invalid-fixture rejection audit |

The grammar, examples, and license under `Tests/Fixtures/OpenQASM30` are copied
from the official `spec/v3.0.0` tag. Backend-dependent extern, calibration,
physical-qubit, and timing operations will be represented and checked, but the
frontend reports them as structured required capabilities. The fixed
state-vector simulator covers the documented backend-independent embedded
subset and requires an explicit `SimulationOptions` resource limit.
