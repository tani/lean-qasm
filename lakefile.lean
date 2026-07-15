import Lake

open Lake DSL

package LeanQASM

require LiterateLean from git
  "https://github.com/tani/literate-lean.git" @ "main"

require "leanprover-community" / "proofwidgets" @ git "v0.0.105"

@[default_target]
lean_lib QASM where
  roots := #[`QASM]

@[test_driver]
lean_exe lean_qasm_tests where
  root := `Tests.Main
