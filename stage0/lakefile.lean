import Lake
open Lake DSL System

/-- Stage 0 compiles checked Gabbro to S0IR. Program execution belongs to the assembly runner.
    The compiler reuses the grammar package and its Mathlib checkout. -/
package stage0 where
  packagesDir := "../grammatik/.lake/packages"
  weakLeanArgs := #["-j2", "-M16384", "-DElab.async=true"]

require grammatik from "../grammatik"
require runner from "../runner"

@[default_target]
lean_lib Stage0

@[default_target]
lean_exe stage0 where
  root := `Stage0.Haupt
