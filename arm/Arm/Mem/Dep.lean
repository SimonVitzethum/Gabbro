/-
  File:      Arm/Mem/Dep.lean
  Subject:   Dependency detection by perturbation: re-run an `Eff` tree with
             one read value changed and compare the later events.
  Sail:      the replayed effects are `__ReadMem`/`__WriteMem` of
             sail-arm/arm-v9.4-a/src/mem.sail lines 44-57, as in
             `Arm/Mem/Trace.lean`; the limitation proved here is that the
             `Eff` interface (`Arm/Isa/Monad.lean`) hides data flow inside Lean
             continuations, so syntactic (register-flow) dependencies in the
             sense of the Arm ASL are invisible to any function of events.
-/
import Arm.Mem.Exec

namespace Arm

/-- Instrumented run: events plus the event id of each read, in read order. -/
structure DepOut where
  evs : List Ev
  rids : List Nat
  deriving Repr

/-- Like `runEff`, but records every read's event id in `rids`. -/
def runDep : Nat → Eff Unit → CoreId → Nat → Nat → (Nat → Nat) → Option (DepOut × Nat × Nat)
  | 0, _, _, _, _, _ => none
  | f + 1, e, core, next, nr, sup =>
    match e with
    | .ret _ => some ({ evs := [], rids := [] }, next, nr)
    | .rdX _ k => runDep f (k 0) core next nr sup
    | .wrX _ _ k => runDep f k core next nr sup
    | .rdV _ k => runDep f (k 0) core next nr sup
    | .wrV _ _ k => runDep f k core next nr sup
    | .rdPC k => runDep f (k 0) core next nr sup
    | .wrPC _ k => runDep f k core next nr sup
    | .rdNZCV k => runDep f (k 0) core next nr sup
    | .wrNZCV _ k => runDep f k core next nr sup
    | .rdSys _ k => runDep f (k 0) core next nr sup
    | .wrSys _ _ k => runDep f k core next nr sup
    | .rdMem a k =>
      let v := sup nr
      match runDep f (k v) core (next + 1) (nr + 1) sup with
      | none => none
      | some (o, nx, nrr) =>
        some ({ evs := { id := next, core, kind := .read a, val := v } :: o.evs,
                rids := next :: o.rids }, nx, nrr)
    | .wrMem a v k =>
      match runDep f k core (next + 1) nr sup with
      | none => none
      | some (o, nx, nrr) =>
        some ({ evs := { id := next, core, kind := .write a, val := v } :: o.evs,
                rids := o.rids }, nx, nrr)
    | .bar b k =>
      match runDep f k core (next + 1) nr sup with
      | none => none
      | some (o, nx, nrr) =>
        some ({ evs := { id := next, core, kind := .barrier b, val := 0 } :: o.evs,
                rids := o.rids }, nx, nrr)
    | .raise _ => some ({ evs := [], rids := [] }, next, nr)

end Arm

/-
CUTS: skeleton only. `evsOf`, `AgreeExcept`/`pert`, `cmpEv`/`cmpLater`,
`detect`, the influence relations, the soundness proofs, the xor-invisibility
theorem and the per-kind witnesses are NOT yet written.
-/
