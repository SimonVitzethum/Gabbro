/-
  File:      Grammatik/X86/HwLockRmw.lean
  Subject:   LOCK XADD / LOCK CMPXCHG and MFENCE on the coherent machine.

  Lane 1119: lifts the accepted `LockedInstructionExecution` vocabulary
  (`LockAnweisung`, `lockSchrittVoll`, `lockSchritt`/`casSchritt`) onto the
  coherent `HwMaschine`/`HwSchritt` of `HardwareExecution`, replacing the
  refusal `adapterLocked662`/`hwLock_verweigert` by an admitted step under
  its guards. The old evaluator is lifted, never redefined.
-/
import Grammatik.X86.HardwareExecution
import Grammatik.X86.LockedInstructionExecution

namespace Gabbro.Grammatik.X86

/-- Project core `c` of the coherent machine to a locked machine:
    canonical core view plus the shared buffers. -/
def lockMaschineVonHw (m : HwMaschine) (c : Nat) : LockMaschine :=
  ⟨projZustand m c, m.puffer⟩

/-- The projection carries the shared TSO view. -/
theorem lockMaschineVonHw_tso (m : HwMaschine) (c : Nat) :
    toTSO (lockMaschineVonHw m c) = tsoAnsicht m := rfl

/-- Re-embed a locked successor: core data moves, foreign core data and
    both profiles stay. Memory and buffers come from the locked step. -/
def einbettenLock (m : HwMaschine) (c : Nat)
    (lm' : LockMaschine) : HwMaschine :=
  setTso (setKernDaten m c ⟨lm'.zu.register, lm'.zu.flags, lm'.zu.rip,
    (m.kerne c).xmm, (m.kerne c).fp⟩) ⟨lm'.zu.speicher, lm'.puffer⟩

/-- Re-embedding preserves well-formedness (profiles untouched). -/
theorem einbettenLock_wf (m : HwMaschine) (c : Nat)
    (lm' : LockMaschine) (h : HwWf m) : HwWf (einbettenLock m c lm') :=
  setTso_wf _ _ (setKernDaten_wf _ _ _ h)

/-- One admitted LOCK/RMW step on the coherent machine: run the accepted
    `lockSchrittVoll` on the core projection with the machine profiles;
    only `.ok` is admitted, everything else refuses with `none`. -/
def hwLockSchritt (m : HwMaschine) (c : Nat)
    (a : LockAnweisung) : Option HwMaschine :=
  match lockSchrittVoll a c (lockMaschineVonHw m c) m.hw (m.bereit c) with
  | .ok lm' _ => some (einbettenLock m c lm')
  | _ => none

/-- The LOCK/RMW producer plug: the admitted step as an `HwAdapter`. -/
def adapterLockRmw : HwAdapter LockAnweisung := ⟨hwLockSchritt⟩

/- CUTS:
    Skeleton only: projection, re-embedding with `HwWf` preservation,
    and the admitted-step adapter shell. NOT proved yet: exact agreement
    with `lockSchrittVoll`, planted refusals, two-core witness.
-/

#print axioms lockMaschineVonHw_tso
#print axioms einbettenLock_wf
