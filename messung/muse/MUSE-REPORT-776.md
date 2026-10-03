# MUSE-REPORT-776: LOCK CMPXCHG success as the single RMW access

Lane 776, clone `/home/simon/Dokumente/gabbro-muse/a776`, branch `muse/776`.
Owned files only: `grammatik/Grammatik/X86/LockCmpxchgSuccess.lean` (new),
`grammatik/Grammatik.lean` (one import line), this report.

## What was done

Proved the LOCK CMPXCHG (64-bit word row, REX.W + 0F B1) success case IS the
single RMW access, through fetched bytes. The main theorem
`LockCmpxchgSuccess_verbindung` takes a fetched
`lockByteschritt` admission plus the eight success guards (empty own buffer,
`ausgerichtet8`, `read64`, comparison-against-RAX, source register value,
`laengeOk`, `write64`, `lesbar8`) and concludes, for the single outcome event:

- full local barrier: buffers unchanged, own buffer empty before and after,
  no forwarding afterwards (`neuestens … = none`), direct canonical-memory
  operation (mirrors the `mfence_ordnung` shape);
- single RMW (`CmpxchgErfolgForm` + `RmwForm [ev] = true`): one event, read
  footprint = write footprint = full word `Fuss tgt`, observed `dest`
  replaced by `sval`;
- one atomicity unit: all three permission maps preserved, frame outside the
  footprint, exact read-back `some sval`, untouched RAX, exact comparison
  flags `(sub64 dest rax).2`, advanced RIP, and projection onto exactly one
  accepted `casSchritt` success step — the shape the W `rmw` field
  (`neu = wahl.ts + 1` at an exchange head) consumes. The lowering itself
  stays with the bridge (OPEN wave-B work, stated in CUTS).

Supporting results: `cmpxchg_erfolg_ohne_schatten` (admitted bytes route
through the common `decodeExt` dispatcher first — no shadowing),
`cmpxchg_erfolg_kein_split` (no non-RMW pair reproduces the success
observation, via `rmw_nur_mit_lock`), three fetched refusal pins
(`cmpxchg_erfolg_puffer_verweigert`, `cmpxchg_erfolg_unaligned_verweigert`,
`cmpxchg_erfolg_stumpf_verweigert`), and the joint witness
`LockCmpxchgSuccess_verbindung_zeuge` on `zeugCmpxchgOk` (word 10 -> 7,
memory-changing reached fetched run, all premises jointly inhabited).

## Exact new names

Def: `CmpxchgErfolgForm`. Theorems: `cmpxchg_erfolg_ohne_schatten`,
`cmpxchg_erfolg_kein_split`, `LockCmpxchgSuccess_verbindung`,
`lockFetch_zeugCmpxchgOk`, `effAddr_zeugCmpxchgOk`,
`LockCmpxchgSuccess_verbindung_zeuge`, `cmpxchg_erfolg_puffer_verweigert`,
`cmpxchg_erfolg_unaligned_verweigert`, `cmpxchg_erfolg_stumpf_verweigert`.
Axioms: at most `[propext, Quot.sound]` (subset of the `gabbro_ziel`
standard); no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.
Manual provenance: Intel SDM 325462-093US Sep 2026, LOCK Vol. 2A 3-565/3-566,
CMPXCHG Vol. 2A 3-193/3-194 (local snapshot, verified 2026-10-02).

## Build status

- `./lean-probe grammatik/Grammatik/X86/LockCmpxchgSuccess.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau` last line: `== exit 0; 0 error line(s) in the COMPLETE output`
  (`Build completed successfully (485 jobs)`).
- Note: three consecutive `./lean-bau` runs failed ONLY at the final root
  `Grammatik` aggregator with `failed to create thread` (exit 134) after all
  484 modules including this one had built — the documented virtual-address
  resource signature, not a proof failure. A control run with my import line
  suspended failed differently (stale `.ir` read after the crashed runs). The
  fourth run with the import restored went fully green; a fifth confirming run
  is the `exit 0` line above. No proof or import was changed to get there.

## What remains open

See the `CUTS` block in the file: no W/GX refinement (bridge-owned lowering),
failure path untouched (lives in `lockVoll_cmpxchg_fehlschlag_adapter`),
only the 64-bit word row and mod=2 base-plus-disp32 addressing, alignment as
profile contract, no timing/progress claims, no source/checker/goal change.

## Task remarks

Nothing in the task text is believed wrong. One scoping note: "mapping to the
W rmw field" is discharged as projection onto the accepted single
`casSchritt` success (the unit the field consumes), not as a constructed
`SchrittW` — building the latter here would duplicate the bridge owners'
explicitly OPEN work and need source-syntax premises out of scope for a
hardware lane.
