# Report 10 — Multicore: barriers, acquire and release

## Done
- NEW `arm/Arm/Mem/Barriers.lean` + one import line in `arm/Arm.lean`
  (`import Arm.Mem.Barriers`).
- `bob : Exec -> Rel`, the barrier-ordered-before relation (Arm ARM B2.3)
  for agent 07's `OrderingParts.bob`, with all six clauses:
  - `dmbHolds`: DMB full `[R|W];po;[B];po;[R|W]`, LD `[R]..[R|W]`,
    ST `[W]..[W]` (B2.3.5);
  - `dsbHolds`: DSB orders the same data classes as the DMB of its type;
  - `acqHolds`: `[A];po;[R|W]` (LDAR), `[Q];po;[R]` (LDAPR/RCpc, reads only);
  - `relHolds`: `[R|W];po;[L]` (STLR);
  - `relAcqHolds`: `[L];po;[A]` and `[L];po;[Q]`;
  - `isbHolds`: read `;ctrl;` ISB `;po;` mem.
  All endpoint clauses are `any`-based; every proof goes through
  `List.any_eq_false` uniformly.
- Shareability v1 (`Domain.v1Orders`): only `ish`/`sy` barriers order
  observers; `nsh`/`osh` order nothing. Stated precisely, as the task allows.
- DSB/ISB at the data-memory level: DSB data classes (= DMB of its type);
  ISB control-dependency leg. Completion (DSB) and fetch (ISB) halves have
  no event in the model and stay CUTS — the file says so.
- Witnesses (all `by decide` on MP fixtures):
  - `mpNone`: `bob = []` (missing barrier NOT ordered);
  - `mpDmbSt`: `(0,2)` ordered; `mpDmbLd`: `(2,4)` ordered;
  - `mpRelAcq`: `(0,1)` release, `(2,3)` acquire;
  - `mpAcqPC`: `(0,1)` read ordered, write not (`bob = [(0,1)]`, RCpc);
  - `mpRelAcqSA`: same-core `(0,1)` ordered, by exactly the rel-acq leg;
  - `mpIsb`: `(0,2)` via ctrl+ISB; `mpDsbSt`: `(0,2)` via DSB ST.
- `plain_never_bob`: a fully plain execution has `bob x = []`, via
  `big_plain_split` (one whole-execution fact into six per-clause facts)
  and six `*_false_of_plain` clause lemmas; every one of the seven has a
  `_zeuge` on a non-degenerate fixture (`mpNone`, `mpDmbSt`, `plainEv`).
- `#print axioms`: `plain_never_bob` on
  `[propext, Classical.choice, Quot.sound]`; the six clause lemmas on
  `[propext, Quot.sound]`; `big_plain_split` on `[propext]`. Standard only.
- Last full build: `./arm-bau` exit 0, 0 errors (12 jobs, with the
  coordinator-placed sibling modules Trace/Exec/Dep/Axiomatic/Atomics);
  `./arm-probe arm/Arm/Mem/Barriers.lean` 0 errors (axiom lines quoted above).
- REUSE (rule 8): my skeleton copies of `Ev.isRead`/`Ev.isWrite` are deleted;
  `Barriers.lean` reuses agent 06's character-identical definitions
  (`Arm/Mem/Exec.lean:27-33`) via `import Arm.Mem.Exec`. This repaired a real
  integration collision (`Arm.Ev.isWrite.match_1` doubly defined) without
  touching any other agent's file. Proposal: move the shared event predicates
  into frozen `Event.lean` so no lane owns them.

## New definitions and theorems
- Predicates: `Ev.isAcquire/isAcquirePC/isRelease`,
  `Ev.isDmbFull/isDmbLd/isDmbSt/isDsbFull/isDsbLd/isDsbSt/isIsb`,
  `Domain.v1Orders`; helpers `poMem/ctrlMem/rdOf/wrOf/memOf`
  (`rdOf`/`wrOf` reuse agent 06's `Ev.isRead`/`Ev.isWrite`).
- Clauses + `bobHolds` + `bob`.
- Fixtures: `mpNone/mpDmbSt/mpDmbLd/mpRelAcq/mpAcqPC/mpRelAcqSA/mpIsb/mpDsbSt`,
  `plainEv`.
- Facts: `mp_none_bob_empty`, `mp_dmb_st_orders`, `mp_dmb_ld_orders`,
  `mp_rel_orders`, `mp_acq_orders`, `mp_acqpc_orders_read`,
  `mp_acqpc_write_unordered`, `mp_relacq_sa_orders`, `mp_relacq_sa_leg`,
  `mp_isb_orders`, `mp_dsb_st_orders`.
- Lemmas: six `*_false_of_plain` + six `*_zeuge`, `big_plain_split` +
  `big_plain_split_zeuge`, `plain_never_bob` + `plain_never_bob_zeuge`.

## Sail citations (in-file header)
- `sail-arm/arm-v9.4-a/src/interface.sail:166-184` (DxB, Barrier union);
- `impdefs.sail:880-894` (DataMemoryBarrier, DataSynchronizationBarrier,
  InstructionSynchronizationBarrier); `v8_base.sail:1911-1919`
  (MBReqDomain, MBReqTypes); `instrs64.sail:10271-10277` (DMB),
  `10342-10345` (DSB), `22746-22748` (ISB);
- `sail/lib/concurrency_interface/read_write_v1.sail`
  (AS_rel_or_acq = LDAR/STLR, AS_acq_rcpc = LDAPR);
- `sail/lib/concurrency_interface/barrier.sail` (`sail_barrier` event).

## Open obstructions
- None for my deliverables: all of `lanes/arm/10.md` is done, committed, green.
- Integration note (not mine to fix): `arm/Arm.lean`'s five extra import lines
  (Trace/Exec/Dep/Axiomatic/Atomics) and those five untracked files were placed
  by the coordinator and are left uncommitted by me; my committed files are
  `arm/Arm/Mem/Barriers.lean` and `REPORT-10.md` only (my `Arm.lean` import line
  was committed with the skeleton).

## CUTS (as in the file)
- v1 domains: `nsh`/`osh` order nothing; no per-observer filtering.
- DSB completion and ISB fetch halves have no model event (stated, not silent).
- `Exec` well-formedness is agent 06's; `bob` reads `po`/`ctrl` as given.
- `bob` is one leg for agent 07; co/rf/fr/addr/data/rmw/outer order not here.
- Frozen `Barrier` has no SB/SSBB/PSSBB form: proposed vocabulary follow-up.
- `excl` flag carries no extra `bob` edge (orders via `ord`/barriers).

## Lesson for the record (toolchain)
- In Lean 4.33.1, `!PRED = true` parses as `!(PRED = true)`, wrapping the
  hypothesis in `decide`. Hypotheses over `all` were therefore written
  explicitly parenthesised as `decide (... = false)` and split with
  `of_decide_eq_true` + `Bool.or_eq_false_iff` (both verified by `#check`
  before use). `Bool.not_eq_true` does not fire on `!decide` terms.
- `List.any_eq_false` concludes `¬(cond = true)` (a `Not`): after `intro`,
  the goal is `False`, so follow-up rewrites go `at hcon`.
- `match` arms bind fresh variables, so endpoint reasoning (`ev?`) was
  restated with `any` + `e.id == a`.
