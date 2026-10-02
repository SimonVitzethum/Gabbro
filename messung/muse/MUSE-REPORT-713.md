# MUSE-REPORT-713: Independent review of author-712 audit (candidate f7900631)

Clone `/home/simon/Dokumente/gabbro-muse/a713`, branch `muse/713` (verified:
toplevel and branch match; `git status` clean except this report).
Owned deliverable: this file only. Report-only exact author-candidate review;
no source, import, witness, test or PR-branch change made here.

CANDIDATE: 712 f79006310b9fc55a59b48056bedafc15c98471bb
(base `011ff474004a8a617338584d68b13a64c87b1051`, 2 files, clean).
Author patch (`.tmp/review/author-712/PATCH.diff`) holds exactly the two owned
files: `MUSE-REPORT-712.md`, `dokumente/x86/UPSTREAM-PR-2-LEAN-REVIEW.md`.
No Lean/Rust source touched by the candidate. Docs-only, so no in-clone
`./lean-bau` regression is possible from it.

VERDICT: ACCEPT

The author audit is accurate. Every load-bearing claim was independently
re-checked against the exact pinned PR sources in my own clone
(`.tmp/UPSTREAM-PRS/pr-1`, `.tmp/UPSTREAM-PRS/pr-2`). No missed
correctness/safety/validation bug, no invented proof completion, no weakened
refusal, no stale candidate, no architectural conflict omitted. ACCEPT means
the audit is accurate; it does NOT approve or merge upstream PR2 itself, and
it does not clear the PR's two blocking renames.

## Independent verification performed (all in-clone, no network)

1. Pins and scope: PR2 head `987b286d…` / base `5d5a72e…` and PR1 head
   `5d5a72e…` match METADATA fields exactly; PR2 base = PR1 head, so PR2
   targets the PR1 branch, not master. PR2 PATCH file list = 27 files: 18 new
   `grammatik/Grammatik/X86/*.lean`, `grammatik/Grammatik.lean`, 8 Rust files
   under `crates/gabbro-check/src/x86/`. No `Spec.lean`, goal, emitter or CLI
   file present. PR1 `OptimizationRules.lean` / `OptimizationWitnesses.lean`
   are byte-identical (sha256) in both snapshots.
2. BLOCKING 1 reproduced statically: `def waehle` exists in BOTH
   `FeatureProfile.lean:72` and new `ISASelect.lean:703`, all inside
   `namespace Gabbro.Grammatik.X86`, and PR2 `Grammatik.lean` imports both
   (lines 422 and 476). Aggregation must fail exactly as the author's fixture
   log reports (`environment already contains …waehle…`). Real, not stale.
3. BLOCKING 2 confirmed: `def layoutOk` in BOTH `TableLayout.lean:80` and new
   `ISARelax.lean:132`, same namespace, both imported (`Grammatik.lean` lines
   396 and 478). Masked behind finding 1, as the audit states.
4. BLOCKING 3 (process) confirmed from PR2 METADATA body text: "How to test"
   builds four witness modules per-module, and the body claims full
   `lake build` "fails only in `Parser/ElementTiefProben.lean`". Per-module
   green (475/476 per author log) is consistent with an aggregator-only
   failure, so the body's test procedure cannot catch items 1-2 and its
   full-build sentence is contradicted. Merge gate must be the full build.
5. Theorem-shape claims: `pipeline_refuses` (`Pipeline.lean`) concludes only
   `rip = exitAdr` + `WorldRep` (no stub, no `rax`, no stop); the stub
   sentence (`exitAdr + 10`, `exitReg = r`, stop) lives in
   `pipeline_refuses_loaded` / `pipeline_refuses_compiled`
   (`PipelineImage.lean`) — both conclusions read verbatim. MUST-FIX 6/7 valid.
6. Structural gap (§6) confirmed: `Pipeline.lean` imports only
   `OptimizationRules`, `SourceAssignmentLowering`, `EffectiveAddress`,
   `ExpressionLoweringDeep`; `PipelineImage.lean` adds only
   `Pipeline`/`LoadedExecution`/`ValidatorSkeleton`/`TableLayout`. No
   `ISA`/`ISAExecution`/`ISASelect`/`ISARelax`/`CompactForms`/`IntegerCore`
   import anywhere on the closing path; lowered type is pilot `Befehl`. The
   unified-ISA libraries are proved but unwired, as stated.
7. Precision items confirmed: `laufBytesI_layout` needs
   `∀ i ∈ is, faelltDurchI i = true` (straight-line only, CUTS says so);
   `aluPilotBefehl` maps `.and'`/`.or'` to `none` (AND/OR excluded from
   `equiv_aluImm8`); `equiv_jump8_target` is target equality only;
   `senkTief_tief_ok` docstring says "PLANTED REFUSAL" over a positive
   `= some […]` proof; `cfgOk` decides all working-reg `≠ .rsp` plus
   disjointness with `abbOf_mem`/`cfgOk_frei` lemmas (the §8 rsp non-finding
   is substantiated, not hand-waved).
8. Witness non-vacuity confirmed: `pipeline_correct_zeuge` jointly
   instantiates validate/`LayoutSep`/`CodeAt`/`WorldRep`/`EnvRepr`/source run
   with slot values 7 → 35 and 9 → 6 (memory changes); `by decide` used
   94 times in `PipelineWitnesses.lean`; `pw_ohne_optimiser_verweigert`
   present (fold is load-bearing).
9. Hygiene confirmed: zero `sorry`/`native_decide`; `admit` (6) and `axiom`
   (3) hits over the X86 dir are prose only ("admission", "hardware axiom");
   no `axiom` declarations; `unsafe` zero. `CUTS` present in all 18 new files
   (inside doc-comment blocks, not at line start). `#print axioms`
   code lines: 860 over the 18 new files + 88 over PR1's two (21 + 67) =
   948 exactly as claimed. Theorem/lemma declarations: 907 column-0 in the
   18 new + 2 indented + 102 in PR1 = 1011 exactly as claimed. (My first
   column-0-only grep read 1009; the 2 indented theorems close the gap, so
   the audit's figure is exact, not drifted.)
10. Rust count confirmed: 137 `#[test]` across
    `crates/gabbro-check/src/x86/*.rs` by the stated directory-glob rule.

## Two precision notes (do not change the verdict)

- Of the 137 x86 `#[test]`s, 10 sit in pre-existing `typen.rs`, which PR2
  does not touch; 127 are in PR-changed files. The audit states its counting
  rule accurately and the PR-body figure describes a passing test run, so no
  correction is required — recorded here only so a future merge message does
  not write "137 new tests".
- I did not re-run the full Lean fixture build (queued-slot cost, long
  runtime). For the two BLOCKING items this is immaterial: same-namespace
  duplicate definitions with both files imported by the aggregator fail
  deterministically, the author's complete-output log shows exactly that
  error, and my static checks confirm both halves (duplicate defs + both
  imports). No finding rests on build-green inference.

## What remains open

- The two renames (`waehle` → e.g. `waehleInstr`; `layoutOk` → e.g.
  `relaxLayoutOk`, uses contained to the two new files + witnesses) plus the
  wording fixes (§7 items 3–9 of the author review) belong to the PR authors
  or a repair lane with merge rights. Re-verify after repair with the FULL
  `lake build`, and re-count axiom reports at merge time.
- Future obligations listed in author review §9 (unified-ISA wiring,
  branch-target layout theorem, G/GX concurrency, time, wider fragment,
  silicon correspondence, proved Rust equality, real-loader ELF) stay open
  and are correctly separated from present bugs.
- Anything in the lane task believed wrong: nothing material. The truncated
  line-21 in `lanes/713.md` is complete in effect — OWNER-TASK context from
  lane 712 plus METADATA/PATCH/source supplied everything needed.

## New definitions/theorems by this lane

None. Review-only lane; no Lean code added or modified, no witnesses required.

## Last `./lean-bau` result line

Not run in-clone: this lane changed no tracked source file (report-only), so
no Lean regression is possible from it. Lean evidence is the author's
fixture result, independently corroborated above:
`== exit 1; 3 error line(s) in the COMPLETE output` (aggregator-only failure
on the exact PR2 tree; 475/476 jobs green).
