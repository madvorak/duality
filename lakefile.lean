import Lake
open Lake DSL

package duality {
  moreServerOptions := #[⟨`autoImplicit, false⟩, ⟨`pp.structureInstances, false⟩, ⟨`linter.oldObtain, false⟩]
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib Duality {
  globs := #[.submodules `Duality]
  moreLeanArgs := #["-DautoImplicit=false"]
}
