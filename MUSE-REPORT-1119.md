# MUSE-REPORT-1119: LOCK/RMW on the coherent machine

Clone: /home/simon/Dokumente/gabbro-muse/a1119, branch muse/1119.
Owned files only: `grammatik/Grammatik/X86/HwLockRmw.lean` (new),
`grammatik/Grammatik.lean` (one import line), this report.

## What was done

Connected the accepted LOCK/RMW family (`LockedInstructionExecution`
lane 662: LOCK XADD, LOCK CMPXCHG, MFENCE over `lockSchrittVoll`;
`LockedOps`: `lockSchritt`/`casSchritt`) to the coherent machine
(`HardwareExecution` lane 660: `HwMaschine`/`HwSchritt`), replacing the
refusal `adapterLocked662`/`hwLock_verweigert` by an admitted step.
The old evaluator is lifted, never redefined; no existing file was
edited except the import line.

New definitions (`grammatik/Grammatik/X86/HwLockRmw.lean`):

- `lockMaschineVonHw` (core projection to `LockMaschine`),
  `lockMaschineVonHw_tso` (carries the shared TSO view)
- `einbettenLock` (re-embedding), `einbettenLock_wf` (`HwWf` preserved)
- `hwLockSchritt` (admitted step: only `.ok` admitted),
  `hwLockSchrittEv` (keeps the accepted `LockEreignis`),
  `adapterLockRmw : HwAdapter LockAnweisung` (the producer plug)
- Observers `hwLockWort`, `hwLockReg` (core-indexed), `hwLockRip`,
  `hwLockBuf`, `hwLockSicht` (TSO-view byte load per core)
- Witness machines `hwLockWitStart/Nach1/Flush1/Bereit2/Nach2`
  (core 0 XADD 10->15 beside core 1 pending byte at 8200, drain,
  core 1 XADD 15->22), `hwLockWitUnaligned/OhneSse2/OhneLesen/
  OhneSchreiben/CmpxchgNein` (one broken guard each + positive twin)

New theorems:

- Bridge: `hwLockSchritt_als_event`, `hwLockSchritt_verweigert_bei`,
  `hwLockSchritt_ok_bei`
- Exact agreement (same guards as 662, same successor+event):
  `hwLock_xadd_stimmt` (+ read-back, kept buffers),
  `hwLock_cmpxchg_ok_stimmt`, `hwLock_cmpxchg_nein_stimmt`
  (write-back pins `schreibbar8`: failed CMPXCHG needs write
  permission), `hwLock_mfence_stimmt` (memory+buffers untouched)
- Plug: `adapterLockRmw_wf`
- General refusals: `hwLock_ud_bleibt_verweigert` (LOCK on
  register/fence stays refused), `hwLock_puffer_bleibt_verweigert`,
  `hwLock_unaligned_bleibt_verweigert`,
  `hwLock_mfence_ohne_sse2_verweigert`
- Closed pins (all `decide`/`rfl` on closed machines):
  `hwLockWit_anfang/nach1_wort/nach1_rax/nach1_fremd_buf/
  nach1_eigen_sicht/nach1_fremd_sicht/nach2_wort/nach2_rax1/
  gespült_sichtbar/fremd_ohne_fuss/mfence_ok/reg_ud/puffer/
  unaligned/sse2/lesefehler(+_art)/schreibfehler(+_art)/
  cmpxchg_nein_ok`
- Joint witness `hwLock_zeuge` (15 conjuncts: word 10->15->22 on
  two cores, owner-only forwarding 99 vs 0, shared 99 after drain,
  `HwWf`, all five refusal shapes)

## Verification

- `./lean-probe grammatik/Grammatik/X86/HwLockRmw.lean`: 0 errors.
- `./lean-bau`: `Build completed successfully (601 jobs).`
- `#print axioms hwLock_zeuge`: `[propext, Quot.sound]` (standard
  trio subset); all other main theorems likewise (no `sorry`,
  `admit`, `axiom`, `native_decide`, `unsafe`).
- No premises quantify over program syntax; no TARGET/`ZEUGE:` line
  in the task, so rule 13 needs no extra companion beyond the
  task-required `hwLock_zeuge` (non-degenerate: memory-changing
  steps on two cores, buffered store with owner-only forwarding).

## What remains open (see CUTS)

No fetched-byte dispatch on `HwMaschine` (plug takes parsed
`LockAnweisung`; fetch stays with 662 `lockByteschritt`); no W/GX
refinement or linearisation; no timing/progress claims; narrower
widths, other addressing modes and split-lock detection stay with
662. No hardware correspondence beyond self-consistency is claimed.

## Finding during the work

The first witness draft (core 1 XADD while holding its pending
byte) is correctly refused by the guards (own buffer must be
empty); the committed run drains core 1 first, which additionally
demonstrates foreign-drain independence. A full-file ordering fix
was needed once (§7 pins precede their §2-§4 lemmas physically);
resolved by moving the §7 block before CUTS, sections renumbered
to physical order.

## Task assessment

Nothing in the task appears wrong. One scoping note: the task text
says "aligned WortGruppe" as a guard, but the accepted 662
evaluator gates on `ausgerichtet8` (declared alignment contract),
not on the TSO `WortGruppe` drain guard; the lane lifts the 662
guard as stated and records the distinction in CUTS rather than
inventing a second alignment check.
