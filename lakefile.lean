import Lake
open Lake DSL

package duality {
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`pp.structureInstances, false⟩, ⟨`linter.oldObtain, false⟩]
}

require "linters" from git "https://github.com/madvorak/leanters" @ "main"

@[default_target]
lean_lib Duality {
  globs := #[.submodules `Duality]
}
