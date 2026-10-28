import Lake
open Lake DSL System

/-- Stage 0 of self-hosting (`dokumente/PLAN-SELF-HOSTING.md` §2): the Lean runtime for the Gabbro subset S0. It
    shares the Mathlib checkout of `grammatik/` (no second clone) and builds `grammatik` in place. The one piece of
    C (`c/syscall.c`, a booked wall) is the generic system-call trampoline. -/
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

target syscall.o pkg : FilePath := do
  let oFile := pkg.buildDir / "c" / "syscall.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "syscall.c"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC", "-O2"] "cc"

extern_lib gabbrosyscall pkg := do
  let o ← fetch <| pkg.target ``syscall.o
  let name := nameToStaticLib "gabbrosyscall"
  buildStaticLib (pkg.staticLibDir / name) #[o]
