import Lake
open Lake DSL

package «Matematicas_en_Lean4» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «MatematicasEnLean4» {
  -- add any library configuration options here
}
