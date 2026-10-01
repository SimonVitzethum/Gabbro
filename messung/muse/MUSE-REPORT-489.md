# MUSE-REPORT-489: Independent exact-candidate review of 409

Clone `/home/simon/Dokumente/gabbro-muse/a489`, branch `muse/489` verified.
Candidate: snapshot `.tmp/review/SNAPSHOT.json` (author 409, base `0b3132b7`,
present in this clone; candidate HEAD not fetched, reviewed via supplied
`author-409/PATCH.diff` + `dokumente/` tree + `BUILD-EVIDENCE.json`).
No other clone read. Worktree clean except this report.

## What was checked

Read the full candidate audit (`AUDIT-INVARIANT-LIFETIME.md`, 293 lines) and
`MUSE-REPORT-409.md` against the actual tree: `InvariantenOpt.lean` (550
lines) and `AufrufOpt.lean` (288 lines) read in the sections cited;
`Spec.lean` invariant legs (`InvTraeger`, `InvZu`, `InvRuheG`, `InvSichtG`,
`SperrWechselG`, `SperrSichtG`) confirmed present; `Grammatik.lean` umbrella
imports at lines 383/387 confirmed (= audit §0 anchor); OPTIMIZER.md rows C1
(212), C3 (214), S1 (231), I1 (363) confirmed ACCEPTED-HELPER-only /
PROPOSED as the audit states — no overclaim. `REVIEW-QUELLE-INVARIANTEN.md`
§5 confirms the `S = leer` bridge reference (§6 linkage honest, no
re-derivation). PATCH touches exactly the two owned files; no Lean, Rust,
emitter, checker, Spec, or friend path touched; no `sorry`/`admit`/`axiom`/
`native_decide`/`unsafe` in code (single grep hit is prose "admits").
English only.

Reproduced in this clone via queued `./lean-probe` (both 0 errors, then
deleted): positive (`isWahrAll (le (lit 2) (lit 5)) = true`, `isWahr wCond`,
ghost-pair length 2) and negative (`isWahrAll (.nicht .wahr) = false`,
`#check @slot_read_stabil` / `@exec_pruefung_inv` exhibiting the exact
assumed premises the audit quotes for F1/F2). BUILD-EVIDENCE.json is
consistent: one initial probe failure shown, then both green — the report
claims only the final green state, honestly.

## Semantic verdicts

- V1–V8: each verified at the cited lines; the characterisations are exact
  (e.g. `exec_pruefung_inv` proves by `cases s <;> simp [execBlock, h]` —
  tag proof-irrelevant, work by `h`; `slot_read_stabil` quantifies over any
  `t/f` with prose-only carrier refusal; `geistRekon_folge` is the
  constructor over its conclusion's fields; `InlinePflicht.hr` refuses
  fallible callees; `wit_step` shows slot reads `5`; `slot_read_stabil_zeuge`
  uses `σ' = σ`, degenerate as the audit itself notes in F3).
- F1–F9: none is presented as a false theorem; each is a correctly scoped
  prose-vs-statement or strength observation with the repair booked
  consumer-side (R1–R6). No invented bug: the audit explicitly refuses to
  call OPEN bridges defects and endorses both CUTS blocks. The one
  wording repair asked inside the audited files (F1 "consumes it by cases")
  is framed as a comment fix, not a defect — appropriate.
- No-consumer grep: reproduced over `grammatik/` + `bruecke/` — outside the
  two modules only umbrella imports, OPTIMIZER prose, and build artifacts.
  Claim holds for source `.lean` consumers.
- Claim ledger (May / May NOT, §6 + CUTS): bounded, matches the proved
  content; claims no invariant-derived optimisation justified today, no
  atomics/MMIO/concurrency/cost/fault/target coverage. No full-compiler
  closure claimed.
- No vacuity, no unused-premise issue (docs-only, no theorems added), no
  forged evidence, no duplicated IR, no safety weakening (R2/R3 explicitly
  demand carrier refusal and invalidation before any load-reuse consumer).

## Open / notes

- Line anchors will drift with future edits; the audit says so in CUTS.
  Nothing requested beyond this review.
- No `./lean-bau` run: candidate and this review touch no Lean source;
  mechanical evidence is the `./lean-probe` runs above (0 errors each).
- Minor, not verdict-relevant: MUSE-REPORT-409 says the two `.tmp` probes
  were "present" and reused — BUILD-EVIDENCE shows the first version
  failed and was fixed in-lane; final state green as reported. No action.

CANDIDATE: 409 bd672f0b915855fbfc030e7150d71d28f4af083a
VERDICT: ACCEPT
