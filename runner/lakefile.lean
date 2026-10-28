import Lake
open Lake DSL

/-- The verified x86-64 runner of `S0IR` (`dokumente/PLAN-SELF-HOSTING.md` §2.2): the IR, the x86-64 subset the
    runner uses, the runner's bytes and their proof. Core Lean only (no Mathlib): the proofs are over `BitVec`. -/
package runner where
  weakLeanArgs := #["-j4", "-M8192"]

@[default_target]
lean_lib Runner

/-- Writes the runner binary and test images. Off the trust path: it only prints the bytes the proofs are about. -/
@[default_target]
lean_exe runner where
  root := `Runner.Haupt
