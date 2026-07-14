# LeanQASM

`LeanQASM` is a minimal OpenQASM 3.0 embedded DSL and state-vector interpreter
written in Lean 4. Its checked tutorial uses
[LiterateLean](https://github.com/tani/literate-lean), so documentation examples
are compiled together with the library.

## Build and test

```sh
lake build
lake test
```

## Use

Import the library and construct a program with the `qasm` syntax:

```lean
import QASM

open QASM

def bell : QASM.Program :=
  begin_qasm
    OPENQASM 3.0;
    include "stdgates.inc";
    qubit[2] q;
    bit[2] c;
    h q[0];
    cx q[0], q[1];
    measure q -> c;
  end_qasm

#eval simulate bell
```

The core implementation uses LiterateLean for its own documentation. Downstream
programs and examples remain ordinary Lean after `import QASM`; literate fences are
not part of the library interface.

The DSL is a grammar-safe OpenQASM 3.0 subset. It requires exactly one leading
version declaration, uses modern `qubit` and `bit` declarations, restricts
names to non-keyword ASCII identifiers, and validates include filenames.
`Program.toQasm` returns `Except String String` so invalid AST values are never
serialized as OpenQASM.

OpenQASM source text can also be parsed independently of Lean syntax:

```lean
match QASM.parse "OPENQASM 3.0; qubit q; h q;" with
| .ok program => IO.println program.toQasm
| .error error => IO.eprintln s!"{error}"
```

The staged compatibility matrix is tracked in [CONFORMANCE.md](CONFORMANCE.md).

## Documentation

The source includes API documentation on public declarations and a literate,
compiler-checked walkthrough in `QASM/Guide.lean`. Import it directly when
exploring the documented examples:

```lean
import QASM.Guide

#check QASM.Guide.bell
#check QASM.Guide.runBell
```

## Acknowledgements

This project is developed under the umbrella of the AutoRes Lean-Quantum
Project.
