import Lake
open Lake DSL

require VersoBlueprint from "/private/tmp/r9-v-work/vbp"
package ProjectTemplate where
  precompileModules := false
  leanOptions := #[⟨`experimental.module, true⟩]

@[default_target]
lean_lib ProjectTemplate where
