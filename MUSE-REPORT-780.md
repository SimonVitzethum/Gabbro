# MUSE-REPORT-780: MFENCE drain-own semantics

Lane 780, clone /home/simon/Dokumente/gabbro-muse/a780, branch muse/780.
Owned files only: `grammatik/Grammatik/X86/MfenceDrainOwn.lean` (new),
`grammatik/Grammatik.lean` (one import line), this report.

## What was done

New module `Grammatik.X86.MfenceDrainOwn` proves MFENCE as
drain-then-gate on the acting core only. It reuses without redefining:
the ONE canonical `TSOZustand`/`flushKern`/`loadByte`/`TSOErreichbar`
(`X86.TSO`), the bounded local drain `drainVoll`/`drainKernN` plus the
two-core witness `fdStart/fdS2/fdS3/fdX` (`X86.FenceDrain`), the gate
`lockSchritt .mfence` (`X86.LockedOps`), and the canonical MFENCE
bytes/decoder `pinMfence`/`decodeLock`/`pin_lock_mfence_decodiert`
(`X86.LockedInstructionExecution`, grounded there at MFENCE Vol. 2B 4-15,
Intel SDM 325462-093US Sep 2026, snapshot verified 2026-10-02).

Definitions:
- `mfenceDrain (s c)` IS `drainVoll s c` (flush the OWN buffer fully).
- `mfenceSchrittAusBytes (bs s c)` drains only on the decoded MFENCE
  form (`some (.ok .mfence _, _)`); every other decode outcome is `none`.

Theorems (each premise used; no `sorry`/`admit`/`axiom`/`native_decide`):
- `mfenceBytes_dekodiert`, `mfenceSchrittAusBytes_ok`: byte dispatch.
- `mfenceDrain_leert`, `mfenceDrain_bereit`, `mfenceDrain_fremd`:
  own buffer emptied, fence ready, foreign buffers byte-identical.
- `mfenceDrain_ordnung`: after the drain the acting core forwards
  nothing; every readable load observes canonical memory (order half).
- `mfenceDrain_fifo`: two buffered stores become visible in issue
  order (oldest flushes first, frame preserved for the younger).
- `drainKernN_erreichbar_von`, `mfenceDrain_erreichbar_von`: drain
  steps ARE TSO steps; reached runs extend through MFENCE.
- `mfenceDrain_vs_gate`: the accepted gate refuses the nonempty buffer
  that the drain flushes, with an observable memory change.
- `mfenceDrain_loest_fremd_nicht`: PROVED refusal of MFENCE-everywhere
  (foreign entry survives byte-identical).
- `mfenceAbgeschnitten15_verweigert`,
  `mfenceAbgeschnitten15AE_verweigert`,
  `mfenceNachbarLFENCE_verweigert` (reg field 5, not 6),
  `mfenceMitLock_ist_ud` (LOCK+MFENCE is fence #UD),
  `mfenceSchrittAusBytes_nachbar_verweigert`,
  `mfenceSchrittAusBytes_lock_verweigert`: unsupported neighbours
  refuse explicitly.
- TARGET `MfenceDrainOwn_verbindung`: decoded MFENCE bytes + reached
  state + successful byte drain + foreign pending IMPLIES own-empty,
  fence-ready, foreign byte-identical and still pending, canonical
  loads on the acting core, and reached drained state.
- Companion `MfenceDrainOwn_verbindung_zeuge`: all premises jointly on
  `fdS2/fdS3` (two issues reach, one drain flushes, memory at `fdX`
  changes zero to one, core 1 buffer pending before and after).

## Last build result

`./lean-probe grammatik/Grammatik/X86/MfenceDrainOwn.lean`:
0 errors. `./lean-bau`: exit 0, 0 errors, 485 jobs, "Build completed
successfully". Axioms of the new theorems are subsets of
`[propext, Quot.sound]` (several depend on no axioms at all).
`gabbro_ziel` files untouched; no new axiom/sorry anywhere in the lane.

Note: two `./lean-bau` runs during this lane failed ONLY at the final
root-`Grammatik.lean` aggregator step with environment/resource errors
(`Eq.olean.private` unreadable once, `std::bad_alloc` once) while all
485 module jobs including this one built. A retry completed green with
no source change, so both were transient resource flakes, not proof
failures. Two inspection commands (`free`, repo-wide `grep` via bash)
were refused by the permission classifier during this lane; they were
not needed and not worked around.

## What remains open (see CUTS in the file)

Foreign drain (explicitly NOT claimed), SFENCE/LFENCE, LOCK RMW,
register/flag/RIP claims at TSO level (no such fields there; the
fetched level is reused, not restated), SSE2 gating (lives with the
accepted `lockSchrittVoll`), silicon timing/progress/cycles,
interrupts/devices/MMIO/DMA, faults beyond explicit refusal, and any
source/W/GX simulation or checker/contract/budget/goal change.

## Task feedback

Nothing in the task is believed wrong. One observation: the drain half
(`FenceDrain.drainVoll`), the gate half (`LockedOps.lockSchritt
.mfence`) and the fetched MFENCE (`LockedInstructionExecution`) each
existed; what was genuinely missing and is now closed is their
composition into one drain-then-gate byte-facing step with the order
theorems and the explicit no-foreign-discharge refusal.
