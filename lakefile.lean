import Lake
open Lake DSL

package «iteratecnextlean» {
  precompileModules := true
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

lean_lib «Tutorial» {
  -- add any library configuration options here
}

@[default_target]
lean_exe «Main» {

}
