import Lake
open Lake DSL

package verifiedCompiler where
  version := v!"0.1.0"

lean_lib VerifiedCompiler

@[default_target]
lean_exe verifiedCompilerDemo where
  root := `Main
