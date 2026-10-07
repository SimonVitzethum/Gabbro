# REPORT-08 — Multicore litmus tests and execution enumerator

Clone: `/home/simon/Dokumente/gabbro-arm/work/08`, branch `arm/08`.

## What was done

Built the complete test bench in three new files, wired into `arm/Arm.lean`:

- `arm/Arm/Lit/Prog.lean` — litmus language: `DepKind` (addr/data/ctrl),
  `LitInstr` (ld/st/stReg/fence/dep with `AccOrd`), `Atom` (regEq/memEq),
  `LitProg` (cores, init, final).
- `arm/Arm/Lit/Enumerate.lean` — elaboration + enumeration + verdict:
  `locAddr`, `mkAccess`, `lookup`, `prefixPairs`, `inserts`, `perms`,
  `choices`, `Walk`/`walkInit`/`mkEv`/`addDep`/`applyPend`/`step`,
  `instrLocs`, `allLocs`, `initVal`, `initRows`, `Elab`/`elabEmpty`,
  `isReadEv`/`isWriteEv`/`readIds`, `elabInit`, `addCore`, `elabGo`,
  `elabProg`, `writesAtLoc`, `upd`, `nth`, `replayCore`, `fstOf`/`sndOf`,
  `coreTriples`/`corePair`, `rfCands`, `rfCombos`, `isInitWrite`,
  `coOrdersLoc`, `coCombos`, `applyVals`, `replayStores`, `mkExec`,
  `candidates`, `execRegs`, `evVal`, `coLast`, `memVals`, `Outcome`,
  `atomHoldReg`/`atomHoldMem`, `outcomeHolds`, `Verdict`, `checkOutcome`.
  Consistency stays an abstract parameter `cons : Exec -> Bool` until agent
  07's model lands. `rmw` is empty (no exclusives in the language); all
  accesses are 8 bytes with `excl := false`.
- `arm/Arm/Lit/Tests.lean` — 17 tests as data (`LitTest`, `allTests`):
  MP, MP+dmb.st, MP+dmb.ld, MP+dmb.st+dmb.ld, MP+rel+acq, SB, SB+dmb, LB,
  LB+data (dep markers), IRIW, 2+2W, R, S, CoRR, CoWW, CoRW, CoWR. Each has
  a FORBIDDEN and an ALLOWED outcome, the herd7 test name, and an explicit
  "from knowledge, not a measured copy" note. Runner `runTest`/`runAll`
  takes the future `cons` predicate.

## Proven / measured

- `upd_lookup`: `lookup (upd m k v) k = some v`, by `simp`; axioms
  propext, Classical.choice, Quot.sound (standard). Non-degeneracy
  witnesses by `rfl` (overwrite and unrelated-key cases).
- `prefixPairs_nil`, `perms_nil`, `choices_nil`: axiom-free; `testSane`
  axiom-free.
- By `rfl`: empty program has 1 candidate; single store has writes
  `[0, 1]` and 1 candidate; MP/SB/LB have 4 candidates each; CoRR has 18.
- Last build: `./arm-bau` → `== exit 0; 0 error line(s)`, 9 jobs, all green.

## Open

- Task item 4: `Arm/Mem/Axiomatic.lean` does NOT exist in this clone, so no
  test has been run against the real model and no expectation was adjusted.
  The runner is ready (`runAll cons`); disagreements will be reported as
  findings when the model lands. This is an open obstruction, not a result.
- `stReg` elaboration sets placeholder value 0, resolved per candidate by
  `replayStores`; `dep` markers with no producing load contribute no edge
  (documented in `applyPend`).

## CUTS (honest)

- Fixed 8-byte accesses; no sizes, alignment, exclusives/RMW, ISB/DSB
  semantics beyond event emission, no LDAPR-vs-LDAR distinction in
  enumeration (ords are carried on events for the future model).
- Init writes share synthetic core `nCores` with no `po` among them.
- `coOrdersLoc` pins the init write first; a location with zero or several
  init writes falls back to plain `perms` (cannot happen from `elabProg`).
- Expectation mapping to herd7 names is from knowledge and may drift in
  detail from herd sources; each test records its exact scenario so drift
  is checkable. CoWW/CoRW/CoWR shapes follow from per-location coherence
  as documented in their notes.

## Toolchain findings (for other agents)

- Multi-line `{ s with ..., ... }` as a function argument fails to parse
  (`unexpected identifier; expected '}'` at the first line break); the same
  update on ONE line checks. All `with`-updates in these files are
  single-line `let`s.
- `elab` is a Lean keyword and cannot be a definition name (renamed to
  `elabProg`).
- `fun r => r.1` fails on tuple-typed lambda variables (`cannot resolve
  projection`); pattern-matching lambdas or named projection helpers
  (`rowEv`/`rowLoc`/`rowVal`) work.

## FROZEN proposals

None. `Arm/Basic.lean` and `Arm/Mem/Event.lean` were sufficient unchanged.
