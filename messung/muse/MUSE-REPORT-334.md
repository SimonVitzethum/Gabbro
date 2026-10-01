# MUSE-REPORT-334: independent review of candidate 331 (full optimiser specification)

Clone/toplevel verified: `/home/simon/Dokumente/gabbro-muse/a334`, branch `muse/334`.
Review target (pinned): `grammatik/OPTIMIZER.md` from author lane 331.

CANDIDATE:331 1726c0ec33ebdd3076b12a6a4a72228ab4599f7a
VERDICT:ACCEPT

## What was inspected

- Pinned candidate: `.tmp/review/author-331/grammatik/OPTIMIZER.md` (1041 total lines,
  842 non-empty useful lines, re-counted locally: matches the author's 842 claim and the
  requested ~500-900 band), plus `OWNER-TASK.md`, `MUSE-REPORT-331.md`, `PATCH.diff`
  header, `BUILD-EVIDENCE.json`, `SNAPSHOT.json` (base `6a0b028af57bd2e192030c647ba96de9ec837995`).
- Live tree cross-checks (this clone, no edits to sources): `grammatik/Grammatik/X86/`
  (20 files, `wc -l` total 11223, per-file counts identical to the candidate's §1.4 table),
  key definitions (`InvariantenOpt`: `alsLitOpt`, `litLeBool`, `isWahrAll`, `holdsBool`;
  `AufrufOpt`: `GeistAntwort`, `geistPaar`, `geistPaar_laenge`; `StaerkeReduktion`:
  `shlW`, `shrW`, `maskW`, `mod_pow2_and_mask`; `Typen`: `Register`, `Breite`, `Flags`,
  `Bedingung`; `TSO`: `TSOEintrag`, `TSOZustand`; `Speicher`: `lesbar8`, `read64`;
  `Zugriffe`: `Zugriff`; `Gleitprofil`: `MXCSR`, `mxcsrRundungRNE`; `Vektor` 651 lines),
  absence of `X86/IR.lean`, `X86/OptimizationRules.lean`, `X86/OptimizationWitnesses.lean`
  (all three absent, as the candidate states), `lanes/287.md`, `lanes/334.md`,
  `DIRECT-COMPILER.md`, `DIRECT-COMPILER-DESIGN.md`.
- Link check re-run locally on the candidate text: 77 markdown links, 0 bad resolved
  against `grammatik/`; the two reserved friend paths appear only as path strings,
  never as hyperlinks (zero `Optimization` links in link targets: no dead future-IR link).
- Proposed checker names (`OptCert`, `pruefeOpt`, `optSound`, `QuellAnnahmen`): absent
  from `grammatik/Grammatik/` (grep empty) and explicitly labelled PROPOSED interface
  sketches in §7.1, not claims.

## Checklist outcome (all required dimensions present)

- ONE shared typed IR, lane 287 status honest: §2.1 names exactly one IR, cites
  `../lanes/287.md` as PENDING, forbids inventing a parallel IR while waiting (§2.1,
  §11.5); reuse-actual-source-syntax fallback stated.
- Rule premises/certs/faults/flags/effects/aliases: §3 rows C/S/V/D/B/R/A/L/F/P/I/U/SIMD
  each carry pattern, fact source + validity scope, effect/fault/flag/call/cost gates,
  exact certificate content with recomputed checks, and a concrete refusal/counterexample
  (overflow-preserving fold, contract-only S1 refusal, load-CSE refusal, SSA-version B1,
  signed-negative R1, name-inequality A1, LICM fault-order L2, f32-vs-f64 F3, CMOV-memory
  fault / div speculation / shift masking / atomic-reread gates in §3.10, ghost-dropping I3,
  budget-preserving U1).
- Invariant lifetime, writer/holder windows: §4 reuses the goal's location model
  (entry/return/ruhe/holder/lock moves), versions facts by SSA, states writer blackout
  and continuous-holding scope, gives a generic safe example plus an external-callee
  invalidation counterexample; §4.5 forbids compiler-guessed `ensures` and
  refusal-into-warning.
- Call ghosts with actuals: §3.11/§4.6/`geistPaar` shape with actual `rho`/result/`s0`/`s1`,
  `geistPaar_laenge` + `FolgeLog` order, `forall rho` refusal, budget transfer in §6.3.
- Budget/stop vs machine work/hardware time: §6 separates the three quantities, maps each
  stop kind, keeps cheapening from extending acceptance, marks work/time transfer OPEN (§6.4).
- Per-width atomics/TSO/refinement cuts: §5.1 declares the TSO-into-W/GX bridge OPEN and
  forbids lemma reuse without it; §5.2-5.4 keep RMW indivisible, orderings exact, rereads
  unstable, local-fence-only, per-assignment reasoning; §5.6 gives MMIO its own profile.
- FP bridge/NaN/FMA: §3.9 defaults to REFUSE (F2-F4 refused, F1 narrow literal-only RNE),
  cites the file's own f32-vs-f64 counterexample and NaN/sticky/SSE gaps; §5.5 keeps MXCSR
  per-context.
- SIMD tail/fault: §3.13 admits nothing until per-lane correspondence, cross-lane fault
  order, tearing, budget transfer and tail handling are proved; scalarisation only as the
  conservative route.
- Flags/address/allocation/layout: P1-P4 plus hard gates (AF-none never false, CMOV-memory
  faults, no div speculation, shift masking, signed-div, atomic reread) in §3.10; spill
  privacy and layout-round bounds in §§8.3/9; final-address revalidation in §8.7.
- Generic Bool validators, soundness derived: §7.3 derives refinement from the `Bool`,
  bans `native_decide`/trusted-Rust/unchecked-SMT; §7.2/§7.4/§7.5 give per-pass cert
  schemas, map/rename/analysis checks, source-obligation reuse, and summary/link/image
  obligations that are never skipped; §7.6 is negative-default with listed conservative
  routes (`seqcst`-as-fallback correctly excluded); §7.7 keeps per-program proofs off the
  trust path.
- Source-computed full unit, no per-program trust: §§1.3/4.4/7.4/7.5 compute obligations,
  footprints and summaries from the full source text; no rule names a program (§0.4,
  §4.6, §11.4).
- Fast compiler including validation: §§8.1-8.7 give compact IR, revisioned shared analyses
  with invalidation, deterministic bounded work (fuel, worklists, parallelism determinism),
  untrusted cache with schema versioning and revalidation, optional-pass timeout with
  certified fallback, warm Lean batching with validated-vs-unvalidated latency reported
  separately, fetched-bytes final revalidation. No linear-complexity assumption for
  entailment solving (bounded-decide + keep-the-check fallback).
- No fresh speed claims / universal max: §10.6 records all throughput/RSS/latency/quality
  numbers UNKNOWN; §9 caps are MEASURE-THEN-CHOOSE; perf-word hits (`O3-like`, `10%`,
  `benchmark`, `throughput`, `faster`) are all in refusal/unknown/target-band context.
  `good O3-like` is a quality target without numbers, paired with safety-above-marginal-gains.
- Witness obligations non-degenerate: §10.1 requires generic statements plus joint `_zeuge`
  with a table some function writes and a memory-changing run step, citing HARD RULES §13;
  §10.2-10.3 require poison certs plus positive probes per pass and ten test rows
  (flagslive, faultorder, alias, locks/calls, budget, fp, vectortail, relocation,
  profile/cache, cachedirty).
- Safety above final ~10%, guarantees preserved: §§0.3/9 state tuning never weakens proof
  obligations and the last marginal ~10% needing unsound tricks is not pursued; §12.3 adds
  no guarantee to the goal and keeps silicon claims NOT CLAIMED; no Lean/Rust/Spec/goal/
  counter changes in the candidate (docs only).
- Friend handoff exact/isolated: §11.2 reserves exactly
  `Grammatik/X86/OptimizationRules.lean` + `Grammatik/X86/OptimizationWitnesses.lean`
  (matching the standing reservation), §11.3 excludes central IR/TSO/encoder/image/umbrella/
  Spec/shared-invariants/scheduling/pipeline/Rust, §11.4/11.5 give start order, acceptance
  contract and no-second-IR waiting work; §11/§11.6 state the friend has not started and no
  external messages were sent.
- Planned-vs-proved precision: per-row ACCEPTED-HELPER/PROPOSED/REFUSED labels, §1.4 helper
  inventory with exact line counts (all re-verified), O1-O10 register, and an honest CUTS
  block restating plan-only status. English throughout (remaining `Zielsatz`/`Beweis` hits
  are Lean path names, not prose).
- Observation (not a finding): sketched names `pruefeOpt`/`QuellAnnahmen` are German words,
  consistent with the tree's existing German-identifier convention (`geistPaar`, etc.) and
  explicitly PROPOSED; the "English file names" requirement is met (`OPTIMIZER.md`,
  `OptimizationRules.lean`, `OptimizationWitnesses.lean`).

## Findings

No material findings. No repair requested: every review dimension above is addressed with
concrete interfaces, tables, counterexamples and cuts, all verifiable claims re-verified
against the live tree, and no overclaim (bounded plan, not a full compiler) was found.

## Build / verification

Documentation review; the candidate adds no `.lean`/`.rs` inputs, so no `./lean-bau` run
was needed (no gratuitous build per task). `git status` was clean before this report;
this lane owns only `MUSE-REPORT-334.md`.

## Open

Nothing open on this lane's side. Integration (merge of candidate 331) is the owner's business.
