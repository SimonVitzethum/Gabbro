# MUSE-REPORT-321: Independent review of the central direct-compiler progress document

Lane 321 (review). Branch `muse/321`. Model: opencode-go/muse-spark-1.3-contributor.
No delegation, no model calls. Owned file only: this report. No source file modified.

## Reviewed candidate

- BASE commit: `1990abb2b651a634f5415dc9af67a85ea5e38c95`
- Document blob: `git rev-parse HEAD:dokumente/DIREKTER-COMPILER.md`
  = `ea10465dd8060a4668db568ee3c9174e50b1868b`
- Scope: `dokumente/DIREKTER-COMPILER.md` (209 lines) as a work/progress
  document only. Not a review of any Lean proof or Rust code.

## What was checked

1. Intended result section: direct x86-64 machine bytes incl. linking,
   relocations, entries, runtime; Lean-first then Rust; Rust output as
   untrusted evidence; end condition generic full source-to-final-byte
   validation for every admitted program; explicit non-claims (no
   validated executable yet, no per-example rules, mnemonic list /
   round-trip / isolated helper / assumed simulation do not suffice).
2. Optimisation section: `-O3`-like scope plus invariant-derived rules;
   preservation list covers values, faults, memory observations, IEEE,
   control state, contracts, call logs, concurrency, progress, budget/time;
   source/target/hardware timing kept separate; SIMD refused where unproved;
   no GCC/Clang `-O3` equivalence claimed; no guarantee weakened.
3. Sequence/closure section: 9-step Lean-first order; W/GX and `gabbro_ziel`
   named as existing source framework with the target refinement still
   required; tearing/LOCK/fences/retries/access-grouping listed as proved
   correspondence still needed; enabledness not fairness; OS/runtime/binding
   as user logic, only silicon/device/timing as hardware assumptions; all
   executed support bytes covered; lane 280 stopped with draft retained;
   whole chain OPEN.
4. Workflow section: 20-process cap matches snapshot manifest
   (`max_active: 20`); exact-candidate ACCEPT with green build and
   `propext, Classical.choice, Quot.sound`; non-degenerate witnesses;
   coordinator fallback and no automatic acceptance. Consistent with
   `.tmp/COORDINATOR-SNAPSHOT.json` states and peer-review mapping.
5. Ledger rows vs snapshot states: every row marked "Merged after
   review/checks" has its merge commit present in this base (all 29
   cited short hashes resolve via `git cat-file`) and its evidence
   report present under `messung/muse/` (all 29 checked present).
   Rows marked candidate/working/waiting (279/297, 287, 288, 290/306,
   291/307, 309/310/313/314, 311/315, 312/316, 317/318, 319/320, 280)
   match snapshot statuses; none is claimed merged. Task files
   `lanes/279,290,291,309,310,311,312,317,319.md` exist.
6. Historical numbers: 1468 passed / 0 failed / 1 ignored Rust suite and
   338/338 + 53 comparisons + 2 reverse probes trace to
   `dokumente/x86/WELLE-A.md` and `messung/muse/MUSE-REPORT-273.md`;
   the document labels them historical foundation regression, explicitly
   not a source-to-x86 validation result, with fresh whole-tree checks
   pending. No stale number is presented as current validation.
7. Lean module coverage in this base: `grammatik/Grammatik/X86/` holds 10
   modules (Typen, Wort, Ganzzahl, FlagBeweis, Speicher, SpeicherKommutation,
   Ausfuehrung, TSO, Bild, Gleitprofil); each carries a `CUTS:` block;
   `grep` finds no `sorry`/`admit`/`axiom` outside comments. The document
   claims only reviewed helpers with retained CUTS, never a complete
   compiler or closed chain.
8. Links: README lines 16-22, TODO section 2, AGENTS.md section 3 all
   point at the document with matching scope language ("not implemented",
   "no complete chain closed", "central record"). No contradiction found.

## New definitions/theorems

None. Documentation review; no Lean or Rust work done.

## Build result

`./lean-bau` not run: the task forbids gratuitous full builds for a
documentation review and no source file was touched, so no build state
could change. Working tree is clean except this report.

## Observations (not defects)

- Ledger refresh stamp is 2026-10-01 09:25 UTC; snapshot shows lanes 309
  and 310 became `report_ready` at 09:27/09:29, after the stamp. The rows
  say "Agent working", which understates rather than overstates progress.
- Snapshot records lane 307 (review of 291) as `report_ready` with a Lean
  merge-build integration failure. The 291 row says "Committed candidate;
  review/integration pending", which remains literally true (not merged),
  but the coordinator will want the repair loop, not this document, to
  carry that failure detail.

## Remaining open work (initial review)

The whole source-to-final-byte acceptance theorem; IR/lowering (287),
invariant optimisation (288), stack/ABI (309), call-log (310), strength
reduction (311), regions/ceiling (312), access extraction (317),
fetch/decode/step (319); pending reviews 297, 306, 307 (repair), 313-316,
318, 320; Rust implementation after reviewed Lean models; fresh
whole-tree checks for the publication containing this document.

## Verdict (initial review)

The candidate document accurately describes the bounded work and progress
at this base. It keeps planned, working, pending and merged states
distinct, bounds independent ACCEPT to exact delivered claims, reuses
cited historical measurements without promoting them, and claims no
complete compiler or full source-to-binary proof.

DOCUMENT-CANDIDATE (historical, superseded 2026-10-01): ea10465dd8060a4668db568ee3c9174e50b1868b
VERDICT (historical): ACCEPT

---

## Re-review: final document with publication check results (2026-10-01)

Fresh independent exact-document review of the scratch candidate
`.tmp/FINAL-DOCUMENT.md` against `.tmp/FINAL-DOCUMENT.diff`,
`.tmp/FINAL-DOCUMENT-CANDIDATE.json`, `.tmp/PUBLICATION-CHECKS.json`,
`.tmp/PUBLICATION-AXIOMS.log` and the refreshed
`.tmp/COORDINATOR-SNAPSHOT.json`. No source or central file edited;
owned file only: this report.

- Candidate identity: `git hash-object .tmp/FINAL-DOCUMENT.md` =
  `e0eb1416dd94fade99a0f9b4bfa7781c79619f93`, matching the candidate
  JSON blob; JSON head `5adbed739ab76006ed1f69f1348c8b0e5a9b84a4`;
  diff index line `ea10465d..e0eb1416` links old reviewed blob to new.
- Diff scope: exactly two hunks. (1) The "Fresh whole-tree checks ...
  pending below" bullet now records completed checks for implementation
  `77e6f362`. (2) One append-only history line for the same. Ledger,
  architecture, optimisation, sequence, workflow, non-claims and all
  merged-history lines are byte-unchanged.
- Measurement verification, claim by claim:
  - Lean "375 jobs, 0 errors": checks JSON lean section reports
    `exit_code 0`, `0 error line(s) in the COMPLETE output` and
    `Build completed successfully (375 jobs)`. Exact match.
  - Rust "1468 passed, 0 failed, 1 ignored": rust output reports
    `failing tests: 0` and `total: 1468 passed, 0 failed, 1 ignored`.
    Exact match.
  - Emission "338/338 translated, 53 end-to-end comparisons,
    2 reverse probes", exit 0: emission output reports `exit 0` and
    `53 durchgestochen, 338 von 338 uebersetzen, 2 umgekehrte Probe(n)`.
    Exact match.
  - "ASan remains unavailable and was not counted as passing": emission
    output states `ASan (Stufe 6b): NICHT GEFAHREN` and `Das ist keine
    bestandene Probe`. Exact match.
  - Goal axioms exactly `propext, Classical.choice, Quot.sound`:
    `PUBLICATION-AXIOMS.log` line 3 reports exactly that triple for
    `gabbro_ziel`. Exact match.
  - "implementation at `77e6f362`": checks JSON `checked_head` is
    `77e6f36296e83c9beb58ce9447415314a9f3ae0c`, an ancestor of this
    base. Exact match.
  - "Subsequent documentation/report-only commits do not change the
    checked code": `git diff 77e6f362..HEAD` over `grammatik crates
    instrumente laufzeit bibliothek beispiele` is empty; the delta is
    only `AGENTS.md` (one reviewed link line), `lanes/321.md` and this
    report. Verified.
- Claim boundaries unchanged: the new bullet keeps the historical
  paragraph above it intact, repeats no whole-chain claim, and the OPEN
  acceptance theorem plus all CUTS/ACCEPT-bound language are untouched.
  The lean log's per-theorem axiom lines cover only `X86/Gleitprofil`;
  the document claims no wider axiom cleanliness. No duration is
  claimed for the fresh checks (the JSON `wall_time_seconds` fields are
  chunk-metadata placeholders, not measurements).
- Refreshed snapshot vs unchanged ledger: 29 merged rows still correct;
  306/307/313/314/315 now `running`, 309/310/311/312/316/317
  `report_ready`, 319 still waiting. Every not-merged row still reads
  candidate/working/waiting/scheduled — conservative lags only
  (e.g. 309/310 still "Agent working"), no merged overclaim. The 307
  integration failure from the earlier snapshot is now superseded by a
  running repair; the 291 row's "pending" remains true.

New definitions/theorems: none. `./lean-bau` not run (documentation
review; no source touched; task forbids gratuitous full builds).

Remaining open work is unchanged from the initial review, minus the
fresh publication checks which are now recorded fact.

DOCUMENT-CANDIDATE (historical, superseded 2026-10-01): e0eb1416dd94fade99a0f9b4bfa7781c79619f93
VERDICT (historical): ACCEPT

---

## Re-review 2: root DIRECT-COMPILER.md candidate with full publication batch (2026-10-01)

Fresh independent exact-document review of the NEW scratch candidate
`.tmp/FINAL-DOCUMENT.md` (the root `DIRECT-COMPILER.md` content; the old
`dokumente/DIREKTER-COMPILER.md` path in this stale base is NOT the
candidate) against `.tmp/FINAL-DOCUMENT-CANDIDATE.json`, the refreshed
`.tmp/COORDINATOR-SNAPSHOT.json`, `.tmp/PUBLICATION-CHECKS.json` and
`.tmp/PUBLICATION-AXIOMS.log`. No source or central file edited; owned
file only: this report. New author-323/reviewer-324 design is pending and
is not certified here.

- Candidate identity: `git hash-object .tmp/FINAL-DOCUMENT.md` =
  `d1c744e79582868c8eb8217a15af2bef8b826e86`, matching the candidate
  JSON blob; JSON head `4a2767a907959ba2e3dfdc78e0a6c2239d571c0d`. Neither
  object exists in this stale base (base `7c530647` predates the root
  move and later merges), so post-base merges are verified via the
  supplied snapshot metadata, not direct inspection; this limitation is
  recorded below.
- Root-move consistency: ledger evidence links are now root-relative
  (`messung/muse/...`, `lanes/...`) and detailed references carry the
  `dokumente/` prefix — internally consistent with a root-located
  document. Architecture, optimisation, sequence, workflow and non-claim
  sections are unchanged; the whole source-to-binary acceptance theorem
  remains OPEN and ACCEPT stays bounded to exact delivered claims.
- Ledger vs refreshed snapshot: all 42 `x86-merged:` markers in the
  document equal the snapshot merged set exactly (machine-compared,
  match). Every merged row reads "Merged after review/checks"; every
  other row (312 candidate/316 working, 317 working/318 candidate, 319
  working/320 scheduled per manifest `waiting_for_candidate`, 323
  candidate/324 working per state `running`, 287/288 working, 280
  stopped) matches the snapshot; nothing pending is claimed merged.
- Lane 307 resolved: snapshot shows `merged`, `review_round 2` with a
  retained round-1 `integration_failure` string. The document records
  both halves explicitly — the round-1 gate rejection
  (`x86-gate-rejection:307`, no failing candidate merged) and the
  round-2 integration (`x86-merged:307`). Consistent, and more precise
  than the raw snapshot field alone.
- Publication batch for `ce698d8f`: checks JSON `checked_head` matches
  the document's cited head; lean `exit_code 0` with `Build completed
  successfully (381 jobs)` supports "complete local Lean checks"; rust
  `1468 passed, 0 failed, 1 ignored` and emission `53 durchgestochen,
  338 von 338, 2 reverse probes`, exit 0, match the repeated figures;
  axioms log reports exactly `propext, Classical.choice, Quot.sound`;
  "Full source-to-binary validation remains OPEN" keeps the boundary.
  The document does not quote the new 381-job figure in the batch line —
  accurate but less precise; suggestion, not a defect.
- Notice-pin repair: 1570 + 1465 = 3035 bytes compared — internally
  consistent; proof statements and negative witnesses stated unchanged;
  evidence link is lane 322's report with snapshot `merged`. No wider
  claim is built on it.
- Lane 323/324: ledger and history claim only that a design is being
  prepared and that no speed measurement or expanded instruction support
  is claimed. Nothing unseen is certified.
- Limits of this isolated review: the two `x86-published:` master hashes
  (origin pushes) and the post-base merge commits/reports cannot be
  resolved in this stale offline base; they are coordinator-operational
  log entries re-verified by the merge gate (remote-ancestry check per
  the workflow section). No proof-relevant claim depends on them alone:
  every merged state is corroborated by the snapshot's exact-candidate
  review mapping, and every measurement by the checks/axioms evidence.

New definitions/theorems: none. `./lean-bau` not run (documentation
review; no source touched; task forbids gratuitous full builds).

Remaining open work: closing acceptance theorem; IR/lowering (287),
invariant optimisation (288), regions/ceiling (312/316), access
extraction (317/318), fetch/decode/step (319/320), design 323/324;
Rust backend implementation after reviewed Lean models.

DOCUMENT-CANDIDATE: d1c744e79582868c8eb8217a15af2bef8b826e86
VERDICT: ACCEPT
