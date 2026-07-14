import Lake

open Lake DSL

package qasmv

require LiterateLean from git
  "https://github.com/tani/literate-lean.git" @ "main"

@[default_target]
lean_lib Qasmv

@[default_target]
lean_lib QasmvDocs where
  roots := #[`Qasmv.Guide]

@[test_driver]
lean_exe qasmv_tests where
  root := `Tests.Main
