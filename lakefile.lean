import Lake
open Lake DSL

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.12.0"

package "learning-lean" where
  -- add package configuration options here

lean_lib «LearningLean» where
  -- bruh

@[default_target]
lean_exe "learning-lean" where
  root := `Main
