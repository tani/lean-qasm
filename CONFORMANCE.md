# OpenQASM 3.0 conformance

LeanQASM targets the official `spec/v3.0.0` grammar.  “Parsed” below means the
standalone frontend has an AST node for the construct.  “Lowered” means
`elab_qasm` emits executable portable Lean.  Target-only behavior is never
silently guessed.

## Portable lowering

| Area | Status | Lean mapping |
| --- | --- | --- |
| Source embedding | Lowered | Raw `begin_qasm` / `end_qasm` is a `String`; QASM text is not tokenized as Lean |
| Grammar audit | Tested | All 21 official 3.0 example programs parse; all 10 official invalid grammar fixtures are rejected |
| Classical types | Lowered | `bool`, scalar `bit`, `bit[n]`, fixed `int`/`uint`, `float[32/64]`, `angle`, `complex[float[32/64]]`, and SI `duration` |
| Arrays | Lowered | Rank 1–7 fixed arrays, nested literals, default initialization, indexing, multidimensional slicing, concatenation, array references, `sizeof`, shape-preserving array casts, and typed I/O codecs |
| Expressions | Lowered | Numeric/Boolean/bitwise operators, fixed-width casts, complex arithmetic, ranges and sets, constants, and the OpenQASM builtins represented by the 3.0 grammar |
| Declarations and I/O | Lowered | Classical/quantum declarations, old-style `qreg`/`creg`, constants, aliases, typed `input`/`output`, scopes, assignment, and measurement assignment including indexed targets |
| Control flow | Native Lean | QASM `for`, `if`, `while`, `break`, `continue`, and `end`; iterator values are converted to the declared scalar type |
| Subroutines | Native Lean | `def`, scalar/qubit arguments, readonly/mutable array references with writeback, nested calls in expressions, return/measurement return, and direct recursion |
| Gates | Portable IR | `U`, `gphase`, intrinsic `stdgates.inc`, user gates, register broadcasting, and `inv`/`pow`/`ctrl`/`negctrl`; modified user gates are recorded as a `Unitary.sequence` before wrapping |
| Quantum instructions | Backend interface | Allocation, unitary application, measurement, reset, and barrier use `QuantumBackend`; their surrounding program remains portable Lean |
| Includes | Lowered | File and embedded source, recursive relative includes, search paths, cycle diagnostics, `stdgates.inc`, and digest metadata for every source origin |
| Directives | Retained | Pragmas and annotations are stored in `CheckedProgramInfo`; their implementation-defined meaning is not interpreted |
| Post-3.0 syntax | Opt-in | `switch` and `nop` lower only with `Dialect.extended`; strict `Dialect.v3_0` is the default |

`Inputs` and `Outputs` use native Lean boundary types such as `QASM.SInt 32`,
`BitVec n`, `Float`, `QASM.ComplexN 64`, and
`QASM.FixedArray element shape`.  Generated local code uses `QASM.Value` after
target-aware static type and shape checking.

Direct recursion is emitted as a Lean `partial def`.  Such a program’s generated
subroutines and `run` require `[Inhabited qasmQubit]`, which supplies Lean’s
partial-definition implementation and does not add a quantum operation.

## Deliberate backend boundary

The frontend parses and retains these OpenQASM host-language constructs, but
portable elaboration rejects them with a capability diagnostic:

| Construct | Reason |
| --- | --- |
| `extern` | Requires a target/host ABI and implementation of the external symbol |
| `defcalgrammar`, `cal`, `defcal` | Calibration bodies use a selected companion grammar and device pulse model |
| Physical qubits `$n` | Mapping and availability belong to the target |
| `dt`, `delay`, gate/box duration designators, `durationof`, `stretch` | Require a target clock, scheduler, or calibrated instruction durations |

SI duration literals (`ns`, `us`, `µs`, `ms`, `s`) and classical duration
arithmetic are portable and are represented in seconds; only target-relative
timing crosses the boundary.

## Known non-backend limitations

These are the remaining places where the implementation is not a complete
semantic validator for every valid or invalid OpenQASM 3.0 program:

- Type diagnostics do not yet carry AST source spans. Lexer/parser errors have
  line and column information, while later diagnostics identify the construct
  textually.
- Runtime-dependent invalid indexing is currently represented by an empty or
  unchanged selection, and runtime division/remainder by zero produces an
  invalid internal value that is reported when it reaches a typed output.
  Compile-time dimensions, shapes, fixed widths, and constant zero range steps
  are rejected statically.
- The portable floating implementation is limited to IEEE-like 32- and 64-bit
  values. Vendor-specific float widths and exact vendor choices for overflow,
  angle narrowing, and floating exceptional values are not modeled.
- The normalized AST printer preserves program structure but not comments or
  original whitespace. The raw `begin_qasm` string remains lossless.
- Calibration blocks are opaque text in the host AST; LeanQASM does not parse a
  companion OpenPulse grammar.

The generated API intentionally does not claim a hardware instruction set,
pulse grammar, timing scheduler, extern ABI, simulator, or noise model.
Backends receive portable `Unitary` trees and may compile them to their target.

The grammar, examples, and license under `Tests/Fixtures/OpenQASM30` are copied
from the official `spec/v3.0.0` tag.
