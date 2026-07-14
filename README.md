# qasmv

`qasmv` is a minimal OpenQASM 2.0 embedded DSL and state-vector interpreter
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
import Qasmv

open Qasm

def bell : Qasm.Program :=
  qasm {
    OPENQASM 2.0;
    include "qelib1.inc";
    qreg q[2];
    creg c[2];
    h q[0];
    cx q[0], q[1];
    measure q -> c;
  }

#eval execute bell
```

Because the core module is written with LiterateLean, commands following
`import Qasmv` belong in a `lean` fenced block as shown above. Markdown prose
may be placed between fenced blocks in the same `.lean` source file.

## Documentation

The source includes API documentation on public declarations and a literate,
compiler-checked walkthrough in `Qasmv/Guide.lean`. Import it directly when
exploring the documented examples:

```lean
import Qasmv.Guide

#check Qasm.Guide.bell
#check Qasm.Guide.runBell
```
