/-
  File:      Grammatik/X86/HwKapsteinTsoLocked.lean
  Subject:   Capstone: TSO projection of the locked and direct-memory tags.

  Lane 1325: follow-up of lane 1295 (`HwKapsteinTso.lean`). Classifies the
  union tags 1295 left open where this lane owns them (lockRmw, lockFetch,
  system): locked XADD steps equal the accepted TSO locked event
  (`lockSchritt` over `LockedOps`, footprint `Fuss` named, own buffer
  drained first, foreign buffers untouched); MFENCE and the nine
  memory-unchanged system legs are silent on the projection; INT n
  delivery installs memory directly (FINDING, no single TSO event).
  Every accepted definition is reused unchanged, never redefined.
-/
import Grammatik.X86.HwKapsteinTso
import Grammatik.X86.HwKapsteinSteps

namespace Gabbro.Grammatik.X86

/-- A memory-unchanged snapshot leg is silent on the TSO projection:
    the plug installs core data and the same memory while every buffer
    is kept by construction. -/
theorem kap_system_still_of_mem (m : HwMaschine) (c : Nat)
    (st : SysSteuer) (ev : SysEreignis) (k' : HwKern)
    (st' : SysSteuer)
    (h : sysSnapSchritt m c st ev = .ok k' st' m.mem)
    (m' : HwMaschine)
    (had : adapterSystem.schritt m c (st, ev) = some m') :
    kapTso m' = kapTso m := by
  have hplug := adapterSystem_ok m c (st, ev) k' st' m.mem h
  rw [hplug] at had
  cases had
  rfl

/- CUTS:
    Skeleton only: the generic silent-leg transport
    `kap_system_still_of_mem`. Per-form legs, the locked-RMW event,
    lockFetch inheritance, the INT n FINDING, union lifts and the
    joint witness follow.
-/

#print axioms kap_system_still_of_mem

end Gabbro.Grammatik.X86
