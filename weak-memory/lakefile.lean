import Lake
open Lake DSL

package weakMemory where
  version := v!"0.1.0"

lean_lib WeakMemory

@[default_target]
lean_exe weakMemoryDemo where
  root := `Main
