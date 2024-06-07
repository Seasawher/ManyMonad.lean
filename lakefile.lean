import Lake
open Lake DSL

package «ManyMonad» where
  -- add package configuration options here

lean_lib «ManyMonad» where
  -- add library configuration options here

@[default_target]
lean_exe «manymonad» where
  root := `Main
