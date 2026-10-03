# MUSE-REPORT-1014: Exact review of author 864 (redundant-load CSE rule)

CANDIDATE: 864 a4292cebe74e9f060e4cebc2109b6f7843d04eaa
VERDICT: ACCEPT

Acceptance is bounded to the candidate CUTS scope stated in this report.

## What was done

Report-only exact review of author 864. Inspected, inside this clone only:
`.tmp/review/SNAPSHOT.json`, `.tmp/review/author-864/OWNER-TASK.md`,
`.tmp/review/author-864/MUSE-REPORT-864.md`,
`.tmp/review/author-864/BUILD-EVIDENCE.json`,
`.tmp/review/author-864/PATCH.diff` (626 lines),
`.tmp/review/author-864/grammatik/Grammatik/X86/OptCseLoad.lean` (522 lines,
read in full). No source file was created or modified by this lane; no live
controls were touched; no other clone was read.

## Candidate shape (matches task)

- New file `grammatik/Grammatik/X86/OptCseLoad.lean` + one import line
  (`import Grammatik.X86.OptCseLoad`) in `grammatik/Grammatik.lean`.
- No new diagnostic/gift/example/CLI numbers, no MARKE changes, no
  source/checker/Spec/goal/emitter edits, no friend-reserved optimiser files.
- New names: `CseLoadCert`, `cseLoadZulassen`, `cseLoadVerweigert_publish`,
  `cseLoadVerweigert_token`, `cseLoadVerweigert_stabil`,
  `cseLoadVerweigert_objekt`, `cseLoadVerweigert_weite`,
  `cseLoadVerweigert_idx`, `probe_cseLoadZulassen_ok`,
  `probe_cseLoadZulassen_publish`, `probe_cseLoadZulassen_token`,
  `cseLoadWort`, `probe_cseLoadWort`, `cseLoadGleit_behält`,
  `probe_cseLoadGleit`, `CseLoadRewrite`, `cseLoadRewritePrueft`,
  `cseLoadRewrite_prueft`, `probe_cseLoadRewrite_ok`,
  `probe_cseLoadRewrite_publish`, `cseSlotN`, TARGET
  `OptCseLoad_verbindung`, companion `OptCseLoad_verbindung_zeuge`,
  witness helpers `zwIdx`, `zwIdx0`, `zwIdx1`, `zwLoad0`, `zwLoad1`,
  `zwVar`, `zwS1`, `zwR1`, `zwS2`, `zwS2'`, `zwR2`, `zwR2'`,
  `probe_zwIdx_orte`.

## Checks performed and evidence

1. Base identity: this clone HEAD is
   `b040b155159f47629542b0083e2f0a8a607f2b4c`, exactly the snapshot `base`.
   Tree was clean before and after this review.
2. Banned tactics: scanned the full candidate file for `sorry`, `admit`,
   `axiom`, `native_decide`, `unsafe`. Zero hits (only the English word
   "admitted" in two comments). No `Prop`-typed premise; no `intro _` /
   `have _ :=` discard found on inspection.
3. Axioms: author evidence prints every main theorem at a subset of
   `propext`, `Classical.choice`, `Quot.sound` (standard; `gabbro_ziel`
   untouched). Consistent with the claim.
4. Build evidence: author log shows `./lean-probe` 0 errors on the final
   file and `./lean-bau` green at 511 jobs. The log also shows the author
   worked through genuine red intermediates (field-projection and
   constructor-arity errors) to green, which reads as real development,
   not a pasted green file.
5. Base build reproduced here: `./lean-bau` on the unmodified base exits
   green (`Build completed successfully (510 jobs)`; candidate adds the
   511th). The candidate itself was NOT built in this lane: applying it
   would violate OWN ONLY (report file only). Base-HEAD match plus green
   base plus the author's complete-output logs is the stated evidence
   boundary.
6. Vocabulary presence: `refD`, `refEin_schreibt`, `refB_erreicht`,
   `refB_schreibt`, `keinRuf`, `gleitPasst`, `bruch`,
   `InvariantenOpt.slot_read_stabil` all exist at this base
   (`ReferenzB.lean`, `Typen.lean`, `Semantik.lean`, `Maschine.lean`,
   `InvariantenOpt.lean`); `OptCseLoad` is absent, so no name collision.
7. Premise use: every premise of `OptCseLoad_verbindung` is consumed
   (`hz` via `hIdx hz`/`hHalt hz`; `hOrte` for the orte equation;
   `hW` for the word image; `heV`, `hσ₁`, `hρ₁`, `hσ₂`, `hρ₂`, `hσ₂'`,
   `hρ₂'` via the two `rfl` unfoldings). The remaining `lean-probe`
   unused-variable warnings in the evidence attach to the witness's
   underscore-prefixed existential binders, which the proof still
   instantiates jointly — not a rule-4(d) discard.
8. Witness: `OptCseLoad_verbindung_zeuge` instantiates ALL premises
   jointly on `refD` (closed index `0`, double `konto[0]` load,
   `Endblock.leave` continuation) and closes with the non-degeneracy
   triple `refEin_schreibt ()`, `refB_erreicht`, `refB_schreibt`
   (table-writing function, reached run, slot `0 -> 100` memory change).
   Non-degenerate by the lane standard.
9. Negative mutations: every cert field has a proved refusal
   (publish-hoist, token invalidation, stability, object, width/align,
   index purity) plus concrete `decide` probes for the admitted,
   publish-hoist and token cases at both cert and rewrite-record level.
   The precise must-NOT-fire case (hoist above publish-acquire) is named
   and proved.
10. No `ensures` derived, no refusal weakened to a warning, no faulting
    form speculated above a guard (both window evals are total; downstream
    faults stay inside `rest`, which is unfolded, not claimed about).

## Architecture scope note (reviewed, not a defect)

This rule lives at the source `Syntax`/`Semantik` level
(`Expr.slot`/`Endblock.bind`/`World.lese`); it states no byte form,
REX/register/width/flag, MXCSR, feature-gate, interrupt or TSO claim.
Byte-facing execution, the generic `optSound` Bool-to-Prop bridge,
rest-induction over arbitrary continuations, non-adjacent
(dominator/avail) windows, float-typed `Endblock` windows, the formal
machine-work bound, silicon correspondence and the TSO/GX bridge are all
explicitly OPEN in the file CUTS. That boundary matches the owner task
(validator-decided side conditions, DESIGN section 7 row) and is stated
plainly, including why strict `execEnd` equality is false (eliminated
read event) and what is proved instead (exact handoff + spur
difference). One observation recorded and bounded: conclusion conjunct
(1) (value equality) follows from the conditional premises
`hIdx`/`hHalt` given `hz`; this is the task-sanctioned
validator-decided shape, and the theorem's independent content (orte
equations, exact spur difference, lock agreement, both `execEnd`
unfoldings, word image) is genuine. Not a rule-4(a) violation within the
task's stated soundness shape; the generic bridge remains OPEN and
labelled as such, so there is no fake closure.

## What remains open (candidate CUTS, endorsed)

`optSound`, downstream rest-induction, non-adjacent windows, float
`Endblock` windows, machine-work bound, silicon correspondence, TSO/GX
bridge. Full source-to-final-bytes validation is untouched by this rule,
as claimed.

## Task feedback

Nothing in either task is wrong. The owner task's ZEUGE requirement is
met jointly and non-degenerately. No repairs requested.

## Last `./lean-bau` result line (this lane, unmodified base)

`Build completed successfully (510 jobs)` — green; tree left clean.
Candidate build evidence (author env, same base): `== exit 0; 0 error
line(s) in the COMPLETE output`, `Build completed successfully (511 jobs)`.
