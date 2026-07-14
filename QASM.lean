    import LiterateLean

    open scoped LiterateLean

# QASM module bootstrap

`QASM.lean` はライブラリの入口です。`QASM.Runtime` から `QASM.Elab` までの
主要コンポーネントを再エクスポートします。

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
