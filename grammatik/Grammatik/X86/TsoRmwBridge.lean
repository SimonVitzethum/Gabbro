/-
  File:      Grammatik/X86/TsoRmwBridge.lean
  Subject:   TSO to W bridge: LOCK XADD / LOCK CMPXCHG as read-modify-write
             steps over the coherent machine.

  Lane 1145: lifts the accepted LOCK/RMW producer (`HwLockRmw`:
  `adapterLockRmw`, `hwLockSchrittEv`, `hwLock_xadd_stimmt`,
  `hwLock_cmpxchg_ok_stimmt`, `hwLock_cmpxchg_nein_stimmt`) and the
  accepted connection vocabulary (`LockXaddFetch`, `LockCmpxchgSuccess`,
  `CasRetryBound`, `LockedInstructionExecution`, `LockedOps`) to the
  read-modify-write shape the W `rmw` field consumes: single RMW events
  over full word footprints that chain without loss. The old evaluator
  is lifted, never redefined. No bounded-retry or fairness claim.

  Manual provenance: none new -- Intel SDM 325462-093US Sep 2026 via
  the accepted 662 module (LOCK Vol. 2A 3-565/3-566, XADD Vol. 2D
  6-27/6-28, CMPXCHG Vol. 2A 3-193/3-194). This lane adds no new
  silicon claim beyond reusing those rows.
-/
import Grammatik.X86.HwLockRmw
import Grammatik.X86.LockXaddFetch
import Grammatik.X86.LockCmpxchgSuccess
import Grammatik.X86.CasRetryBound

namespace Gabbro.Grammatik.X86

/-- The TSO-to-RMW bridge plug: the accepted admitted LOCK/RMW step,
    reused unchanged (never a second evaluator). -/
def tsoRmwAdapter : HwAdapter LockAnweisung := adapterLockRmw

/-- The bridge plug preserves well-formedness (profiles untouched):
    exactly the accepted plug lemma, lifted. -/
theorem tsoRmwAdapter_wf (m : HwMaschine) (c : Nat)
    (a : LockAnweisung) (m' : HwMaschine)
    (h : tsoRmwAdapter.schritt m c a = some m') (hwf : HwWf m) :
    HwWf m' :=
  adapterLockRmw_wf m c a m' h hwf

/- CUTS:
    Skeleton: bridge plug with `HwWf` preservation only.
    NOT proved here, and not claimed: everything in §2-§4 of the lane
    task (exact RMW agreement, refusals, joint witness), any W/GX
    refinement, any hardware correspondence beyond self-consistency.
-/

#print axioms tsoRmwAdapter_wf

end Gabbro.Grammatik.X86
