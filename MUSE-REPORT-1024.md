# MUSE-REPORT-1024: Exact review of author 874 (bounded unroll rule)

## CANDIDATE

CANDIDATE: 874 50be21340ec701c0e9615454af0524397bd89635

## VERDICT

VERDICT: ACCEPT (bounded: token-level rule lemma; see scope bounds below)

## What was done

Report-only exact review of the pinned snapshot
`.tmp/review/author-874/` (SNAPSHOT.json: head
50be21340ec701c0e9615454af0524397bd89635, base b040b155, 3 files,
clean). Verified clone `/home/simon/Dokumente/gabbro-muse/a1024`,
branch `muse/1024`, HEAD `b040b155` equals the snapshot base.
Independently read the full candidate file (409 lines), the complete
PATCH.diff (509 lines), the owner task, the author report, the build
evidence, DIRECT-COMPILER-DESIGN.md section 7 row, the reused
`CostSummary.targetWork_add` (grammatik/Grammatik/X86/CostSummary.lean:130),
the witness fixtures in `grammatik/Grammatik/ReferenzB.lean`
(`refEin_schreibt`, `refB_erreicht`, `refB_schreibt`), and the official
reference registry (Intel SDM 325462-093US, September 2026; AMD
unavailable, no AMD claim made). Reproduced the Lean check read-only
through the queued wrapper against the exact snapshot content.
Owns only this report; no source or live-control file touched.

## Exact new definitions/theorems (candidate)

Definitions: `UnrollCert`, `unrollZulassen`, `koerperSpur`,
`entrollt`, `entrolltOpt`, `UnrollNachweis`, `nachweisOk`.
Refusal: `unrollVerweigert_fusion` (DESIGN failure case),
`unrollVerweigert_trip`, `unrollVerweigert_rest`,
`unrollVerweigert_kNull`, probes `probe_unrollZulassen_ok`,
`probe_unrollZulassen_fusion`. Core: `koerperSpur_append`,
`spur_gleich`, `entrolltOpt_gilt`, `entrolltOpt_verweigert`, probe
`probe_koerperSpur`. Certificate: `nachweisOk_regel`, probes
`probe_nachweisOk`, `probe_nachweisOk_analyse`. Preservation:
`unrollBeob_gleich`, `unrollGleit_behält`, `koerperSpur_länge`,
`unrollBudget_gleich`, `unrollKosten_gleich`, `koerperSpur_mem`,
`unrollKeineNeuen`, `unrollArbeit_additiv`. Connection:
`OptUnrollBound_verbindung` with joint companion
`OptUnrollBound_verbindung_zeuge`. `grammatik/Grammatik.lean` gains
exactly one import line.

## Evidence and architecture review

- Lean reproduction: `./lean-probe` on the exact snapshot file prints
  `== 0 error(s) in the COMPLETE output; exit 0`, no warnings.
  Axioms: witness `[propext, Classical.choice, Quot.sound]` (only via
  the referenced `ReferenzB` fixtures, the standard witness pattern);
  every other theorem `[propext, Quot.sound]` or fewer; several defs
  axiom-free. Strict word-boundary scan: no `sorry`, `admit`, `axiom`,
  `native_decide`, `unsafe`, no `Prop`-typed premise; every premise is
  used; no conclusion restates a premise; nothing derives `ensures`;
  refusal yields `none` (keeps the certified translation, never a
  warning); faulting tokens keep position and order by list equality.
- DESIGN section 7 row match: premises (explicit `k` with
  `decide (0 < c.k)`, trip evidence `hTrip`, remainder path `restPfad`,
  duplication-never-fused `keineFusion`), certificate "B"
  (`UnrollNachweis`: `regel` + `blockAbbild` + `analyseNeu`, stale
  analysis refused by probe), failure case (fusion refuses via
  `unrollVerweigert_fusion` + `entrolltOpt_verweigert`).
- Witness (ZEUGE): jointly instantiates factor 2, `q = 3`, `r = 1`,
  `n = 7`, token `[(1, 2)]`, on non-degenerate `refD` (`einzahlen`
  writes its table, `refEin_schreibt`) beside reached F-run `MB`
  (`refB_erreicht`) with memory change `konto[0]` 0 to 100
  (`refB_schreibt`). Genuine joint non-degenerate memory-changing
  witness, not an empty run.
- Negative mutations: all four admission conjuncts have refusal
  theorems; fusion and stale-analysis probes present and decided.
- Hardware/reference-manual axis: the candidate claims no byte forms,
  no REX/register/width/flag semantics, no TSO/atomicity, no
  MXCSR/feature/interrupt gates, and no silicon correspondence. That
  absence is correctly bounded, not a gap: the no-fusion property rests
  on trace equality by construction plus the validator-decided
  `keineFusion`/`analyseNeu` premise, and the CUTS explicitly stop at
  token equality, kernel `bruch`/`gleitPasst` values and canonical
  `targetWork` counts. No invented determinism, no zeroed or ignored
  defined effect.
- Scope hygiene: no new diagnostic/gift/example/CLI numbers, no
  MARKE_EMIT change, no source/checker/Spec/goal/emitter edits,
  friend-reserved optimiser files untouched, English, CUTS block and
  `#print axioms` for every main theorem present.

## Bounds of this acceptance (not defects)

Token-list level only: no `Syntax` loop form, no
`execStmt`/`exec` correspondence (lowering lane's trip-evidence
production awaited, not invented); the task's contracts/call-log/
concurrency legs are corollaries of list equality, stated honestly in
the author report; no budget-simulation claim; `r < k` left to the
validator with the block map (sound: equality holds for any `r`, a
non-canonical admission only regroups, never fuses). Full
`while`/`traverse` lowering with trip evidence stays OPEN with the
lowering lane.

## Last build result

`./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`,
`Build completed successfully (510 jobs)` (this review tree holds the
base only; the candidate's own evidence records 511 jobs green).

## What remains open

Nothing in this candidate. The `while`/`traverse` lowering that
produces the token lists with trip-count evidence, and any
byte/hardware correspondence above the token level, belong to their
own lanes.

## Task remarks

Nothing in the task is wrong.
