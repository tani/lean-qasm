    import LiterateLean

    open scoped LiterateLean

# QASM module bootstrap

`QASM.lean` is the library entry point that re-exports the core components
from `QASM.Runtime` through `QASM.Elab`.

```lean
import QASM.Runtime
import QASM.Source
import QASM.Frontend
import QASM.Semantics
import QASM.Typing
import QASM.Elab
```

<!--
vim: set filetype=markdown :
Local Variables:
mode: markdown
End:
-->
