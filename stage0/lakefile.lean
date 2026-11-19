import Lake
open Lake DSL System

/-- Stage 0 compiles checked Gabbro to S0IR. Program execution belongs to the assembly runner.
    The compiler reuses the grammar package and its Mathlib checkout. -/
package stage0 where
  packagesDir := "../grammatik/.lake/packages"
  weakLeanArgs := #["-j1", "-M16384", "-DElab.async=true", "-DmaxHeartbeats=400000"]

require grammatik from "../grammatik"
require runner from "../runner"

@[default_target]
lean_lib Stage0

/-- Witnesses that run the whole compiler on a source text inside Lean: each needs more memory than the
    package default, so they form a library of their own that the guardian builds one module at a time. -/
lean_lib Stage0Heavy where
  roots := #[`Stage0.Zeugen.Pipeline.AdapterReasonWitness, `Stage0.Zeugen.Pipeline.DynWitness,
    `Stage0.Zeugen.Pipeline.FallibleIndirectWitness, `Stage0.Zeugen.Pipeline.OptionalForeignWitness,
    `Stage0.Zeugen.Pipeline.ParametricModuleWitness, `Stage0.Zeugen.Pipeline.RangeFoldsWitness,
    `Stage0.Zeugen.Pipeline.TaggedGateWitness, `Stage0.StartImageProben,
    `Stage0.Senke.Images.InitialWitness]
  moreLeanArgs := #["-M45056"]

/-- Explicit review modules for bounded importer checks. -/
lean_lib Stage0Review where
  roots := #[`Nachpruefung.Teil1, `Nachpruefung.Teil2]

@[default_target]
lean_exe stage0 where
  root := `Stage0.Haupt
