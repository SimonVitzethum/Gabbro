# MUSE-REPORT-1013: exact review of author 863 (pure CSE rule)

## Clone / branch verification

- Clone: `/home/simon/Dokumente/gabbro-muse/a1013` (this directory).
- Branch: `muse/1013` (`.git/HEAD` reads `ref: refs/heads/muse/1013`). Match, did not stop.
- Owned file only: `MUSE-REPORT-1013.md`. No source file was created or edited.
  `grammatik/Grammatik/X86/OptCsePure.lean` does not exist in this clone and
  `grammatik/Grammatik.lean` contains no `OptCsePure` import (only the base
  `OptFoldConst` line), consistent with the candidate being unmerged here.

## Review basis

- Pinned snapshot: `.tmp/review/SNAPSHOT.json` -> author 863,
  base `b040b155159f47629542b0083e2f0a8a607f2b4c`.
- Inspected: `.tmp/review/author-863/OWNER-TASK.md`,
  `.tmp/review/author-863/PATCH.diff` (full diff, 425 lines),
  `.tmp/review/author-863/MUSE-REPORT-863.md`,
  `.tmp/review/author-863/BUILD-EVIDENCE.json`,
  `.tmp/review/author-863/grammatik/Grammatik/X86/OptCsePure.lean` (tail/CUTS).
- Cross-checked every external name the candidate uses against this clone's
  base: `refD`, `refEin`, `refO`, `refP`, `refSp0`, `initB`, `MB`,
  `refEin_schreibt`, `refB_erreicht`, `refB_schreibt`, `keinRuf`,
  `vertragVon`, `gleitRechne`, `gleitPasst`, `bruch`, `GleitOp` all exist.
- Grepped the candidate for `sorry|admit|axiom|native_decide|unsafe|intro _|have _ :=`:
  only benign hits (the English word "admitted" in comments, the HARD RULES
  quote, the report's own "No ..." sentence). No forbidden tactic/command and
  no premise discard in the Lean code.

## CANDIDATE

CANDIDATE: 863 badf048e28fa3917ff5d430061fb524eb9224cb7

## VERDICT

VERDICT: ACCEPT (bounded; bounds listed below, all already declared in the
candidate's own CUTS).

## What the candidate does (verified from the PATCH)

New file `grammatik/Grammatik/X86/OptCsePure.lean` plus one import line in
`grammatik/Grammatik.lean`. No other file touched: no diagnostic/gift/example/
CLI numbers, no MARKE_EMIT changes, no source/checker/Spec/goal/emitter edits,
friend-reserved optimiser files untouched. Scope matches the owner task.

New names (all present in the diff):

- `CseCert` (5-Bool record), `cseZulassen` (admission conjunction)
- `cseVerweigert_tor`, `cseVerweigert_breite`, `cseVerweigert_modus`,
  `cseVerweigert_rein`, `cseVerweigert_verfuegbar`
- `probe_cseZulassen_ok`, `probe_cseZulassen_tor`, `probe_cseZulassen_rein`
- `cseZulassen_seiten`, `cseAdd_wert`, `cseWort_add`, `probe_cseWort`
- `cseGleit_behält`, `probe_cseGleit`
- `OptCsePure_verbindung` (ZEUGE target), `OptCsePure_verbindung_zeuge`
- File ends with a `CUTS:` block and `#print axioms` for every main theorem.

## Evidence for each review dimension

- Lean green: BUILD-EVIDENCE shows `./lean-probe` ending at 0 errors and
  `./lean-bau` with `== exit 0; 0 error line(s)`, `Build completed successfully
  (511 jobs)`. The evidence log also shows intermediate probe failures during
  development (Endblock arity, binder syntax, conjunction shape) that were
  repaired before the final commit, which is healthy process, not hidden red.
- Axioms: `OptCsePure_verbindung` and its witness print exactly
  `propext, Classical.choice, Quot.sound` (the `gabbro_ziel` standard);
  refusals/probes `propext` or none; `cseAdd_wert`/`cseWort_add` add only
  `Quot.sound`. As claimed.
- Premise use: every hypothesis is consumed (`simp`/`decide`/`omega`/
  `hEq hz`/unpacking in the connection's third and fourth conjuncts).
  Parameters appearing only in the goal type (`V O passes R rest` etc.) are
  part of the proved equalities, not discarded hypotheses.
- Witness: `OptCsePure_verbindung_zeuge` instantiates all premises jointly
  (`3 + 4`, all-true cert, `leave` continuation) on non-degenerate `refD`
  (`refEin_schreibt`) beside reached memory-changing run `MB`
  (`refB_erreicht`, `refB_schreibt`, slot `0 -> 100`). Genuine, not degenerate.
- Negative mutations: cross-gate (`probe_cseZulassen_tor`) and impure
  (`probe_cseZulassen_rein`) certificates are refused by decision; the five
  refusal theorems cover gate, width, mode, purity and availability kills.
- Architecture (byte forms, REX/width/flags, operands, pre-fault effects,
  TSO/atomicity, gates): the rule is a source-level pure-`add` rewrite; it
  claims no byte encoding, no register/flag semantics and no machine
  correspondence, and its CUTS explicitly disclaim silicon, TSO/GX and ABI.
  Nothing is invented: the float equation is an explicit conditional premise
  (`hEq` takes `hz`), labelled as the validator's recomputation obligation,
  not a proved hardware fact. The checker's range/`narrow` is stated as
  untouched, no `ensures` is derived, refusal falls back instead of warning,
  and faulting-above-guard shapes keep their refusal. No guarantee weakening
  and no desired-simulation premise found.
- Live reproduction: no queued-wrapper build was run in this clone. This is a
  report-only review owning no source, the candidate is not present here, and
  inspection surfaced no suspicious case requiring reproduction. Verification
  rests on the exact pinned PATCH, the author's build/axiom evidence, and the
  independent base-name checks above.

## Bounds of this acceptance (all declared in the candidate's CUTS)

1. Float leg is thin: `cseGleit_behält` derives `gleitPasst` equality by
   congruence from the assumed kernel equation `hEq`. This is the
   task-ordered "validator-decided side condition" shape and is honestly
   labelled, so it is not a hidden assumption, but downstream users must know
   the float preservation assumes the recomputation, not proves it.
2. Contracts/call-logs/concurrency/budget are covered implicitly through
   whole-outcome `execEnd` equality (proved by `rfl`, kernel-checked like lane
   860's fold connection), not as explicit per-aspect conjuncts; `orte = []`
   and budget wording live in comments. The formal machine-work bound is
   correctly left OPEN per IR-VALIDIERUNG.
3. Second-site reuse is value-level re-evaluation; no cross-`bind` variable
   threading, no `sub`/`mul`/`div`/`rem`/`neg` Endblock connection, no
   block-window float rewrite. All stated in CUTS.
4. Cosmetic: the witness's `_hC`/`_hW` binders are underscore-prefixed but
   still proved (`by decide`); no rule-4(d) discard. No repair needed.

## Last `./lean-bau` result line

No build was run in this clone (report-only lane, no source owned or
changed). Author's last line for the candidate: `Build completed successfully
(511 jobs).` with `== exit 0; 0 error line(s) in the COMPLETE output`.

## What remains open

Nothing in this review remains open: the verdict is ACCEPT. The candidate's
own open list (float block window, further operators, variable threading,
machine-work bound, silicon/TSO/ABI) stays with the lowering/hardware lanes.

## Anything in the task believed wrong

Nothing. The ZEUGE names match the delivered theorems, and the
"validator-decided side conditions" instruction is honoured by conditional
premises plus admission unpacking rather than uncheckable Props.
