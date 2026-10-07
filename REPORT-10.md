# Report 10 — Multicore: barriers, acquire and release

## Done
- Skeleton `arm/Arm/Mem/Barriers.lean`: event predicates (`Ev.isRead`,
  `Ev.isWrite`, `Ev.isAcquire` = LDAR, `Ev.isAcquirePC` = LDAPR,
  `Ev.isRelease` = STLR), v1 shareability scope (`Domain.v1Orders`: only
  `ish`/`sy` order observers), `Ev.isDmbFull`, `poMem`, endpoint class
  helpers (`rdOf`, `wrOf`, `memOf`).
- One import line at the end area of `arm/Arm.lean` (`import Arm.Mem.Barriers`).
- Build: `./arm-bau` exit 0, 0 errors (7 jobs).

## New definitions
- `Arm.Ev.isRead/isWrite/isAcquire/isAcquirePC/isRelease`
- `Arm.Domain.v1Orders`
- `Arm.Ev.isDmbFull`
- `Arm.poMem`, `Arm.rdOf`, `Arm.wrOf`, `Arm.memOf`

## Next
- `bob : Exec -> Rel` (DMB full/ld/st clauses, release/acquire/acquirePC,
  `[L];po;[A]`), DSB/ISB coverage, theorems + MP witnesses.

## Open obstructions
- None yet.

## CUTS
- Predicates only; `bob`, DMB LD/ST clauses, DSB, ISB and all theorems open.
- v1 covers only the inner-shareable (plus full-system) domain; `nsh`/`osh`
  barriers order nothing in this version.
- Sail citations: `interface.sail:166-184`, `impdefs.sail:880-894`,
  `v8_base.sail:1911-1919`, `instrs64.sail:10271-10277,10342-10345,22746-22748`,
  `sail/lib/concurrency_interface/read_write_v1.sail`
  (AS_rel_or_acq, AS_acq_rcpc).
