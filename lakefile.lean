import Lake
open Lake DSL

package duality {
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`pp.structureInstances, false⟩, ⟨`linter.oldObtain, false⟩]
}

require "leanprover-community" / "mathlib" @ git "master"

@[default_target]
lean_lib Duality {
  globs := #[.submodules `Duality]
}
