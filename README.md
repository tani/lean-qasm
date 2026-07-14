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

open Qasm

def bell : Qasm.Program :=
  qasm {
    OPENQASM 3.0;
    include "stdgates.inc";
    qubit[2] q;
    bit[2] c;
    h q[0];
    cx q[0], q[1];
    measure q -> c;
  }

#eval execute bell
```

The core implementation uses LiterateLean for its own documentation. Downstream
programs and examples remain ordinary Lean after `import QASM`; literate fences are
not part of the library interface.

The DSL is a grammar-safe OpenQASM 3.0 subset. It requires exactly one leading
version declaration, uses modern `qubit` and `bit` declarations, restricts
names to non-keyword ASCII identifiers, and validates include filenames.
`Program.toQasm` returns `Except String String` so invalid AST values are never
serialized as OpenQASM.

## Documentation

The source includes API documentation on public declarations and a literate,
compiler-checked walkthrough in `QASM/Guide.lean`. Import it directly when
exploring the documented examples:

```lean
import QASM.Guide

#check Qasm.Guide.bell
#check Qasm.Guide.runBell
```
