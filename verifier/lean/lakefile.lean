import Lake
open Lake DSL

package vapor where
  -- We mirror Cedar's structure: a small spec, then theorems.

lean_lib Vapor where
  -- Default settings; subdirs are picked up automatically.

@[default_target]
lean_exe vapor where
  root := `Main
