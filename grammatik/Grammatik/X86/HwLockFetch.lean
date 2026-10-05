/-
  File:      Grammatik/X86/HwLockFetch.lean
  Subject:   LOCK family on the coherent machine: fetched-byte dispatch,
             narrower widths and other addressing modes as stated
             refusals, split-lock (cache-line crossing) as refusal.

  Lane 1209: follow-up of lane 1119 (`HwLockRmw.lean`). The 1119 plug
  takes a PARSED `LockAnweisung`; fetch stays with the single-core
  662 `lockByteschritt`. This module adds fetched-byte dispatch ON
  `HwMaschine` (decode from the core's fetched window, execute
  permission, `ExtendedExecution` discipline via 662 `decodeLockExt`),
  the SIB addressing mode 662 accepts, and split-lock refusal.
  Narrower widths (8/16/32-bit) and non-mod=2 modes have no 662 row:
  they are refused here at the decoder, never executed.
  The old evaluators are lifted, never redefined.
-/
import Grammatik.X86.HwLockRmw

namespace Gabbro.Grammatik.X86

/-- Fetched decode on the coherent machine: the 662 `lockFetch` on the
    core projection (actual executable bytes at the core RIP, combined
    decoder, length and execute-permission checks). -/
def hwLockFetch (m : HwMaschine) (c : Nat) :
    Option (LockAnweisung × List Byte) :=
  lockFetch (lockMaschineVonHw m c)

/-- The coherent fetch IS the 662 fetch on the projection: no second
    fetch model. -/
theorem hwLockFetch_aus_projektion (m : HwMaschine) (c : Nat) :
    hwLockFetch m c = lockFetch (lockMaschineVonHw m c) := rfl

/- CUTS:
     Skeleton only: fetched decode `hwLockFetch` as the 662 fetch on
     the core projection. NOT proved here: the fetched step, split-lock
     refusal, narrower-width / other-mode refusals, agreement with the
     parsed plug, witness. See task lane 1209.
-/

#print axioms hwLockFetch_aus_projektion
