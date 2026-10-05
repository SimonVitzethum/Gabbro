# MUSE-REPORT-1258: Independent exact review of author lane 1257 (PipelineSpillSplice)

CANDIDATE: 1257 da67bd3ff669467702cd121fc7e1150d1835b7f2

VERDICT: ACCEPT

## Scope and method

Report-only independent exact review of author lane 1257: pipeline spills,
splice save/reload at split points, callee-saved and arguments. New file
`grammatik/Grammatik/X86/PipelineSpillSplice.lean` (namespace
`PipeSpillSplice`, ~1150 lines) plus one import line in
`grammatik/Grammatik.lean` plus the author report.

Pinned snapshot `.tmp/review/SNAPSHOT.json`: author 1257, head
`da67bd3ff669467702cd121fc7e1150d1835b7f2`, base `515546d0`, files exactly
the three owned paths, clean true. Reviewed artefacts: the full PATCH.diff
(all 1250 lines), OWNER-TASK.md, MUSE-REPORT-1257.md, BUILD-EVIDENCE.json.

History: my first committed report (2f43e578) recorded that the author clone
was not readable from this lane and my own diff was empty, so no checklist
item could be checked then. It contained no substantive verdict. This report
supersedes it on the pinned snapshot with a merits-based result; nothing was
softened for formatting.

The reviewer touched only this report; no Lean edits were made by this lane.
The build line below is my-clone baseline; the candidate build record is the
pinned evidence.

## Checklist

1. Banned forms: no `sorry`, `admit`, `axiom`, `native_decide`, or `unsafe`
   anywhere in the new file; proofs use only `rfl`, `simp`, `rw`, `omega`,
   `decide`, `rcases`, `obtain`, `cases`, `exact`, `refine`, `induction`,
   `unfold`. No new axiom declarations. PASS.
2. Axiom standard: pinned evidence shows every theorem depends at most on
   `[propext, Classical.choice, Quot.sound]`; `spleiss_haelt_bedeutung_zeuge`
   depends on exactly the standard set; all defs and all `decide` probes are
   axiom-free; no `sorryAx`. PASS.
3. Touched files: only the new file, one appended import line, and the author
   report. `OptimizationRules.lean` / `OptimizationWitnesses.lean` untouched;
   no other existing file edited. PASS.
4. Premise use: every premise of every theorem is consumed. Samples checked:
   `spleiss_save_fremd` uses `hne`, `hwr`, `hrun`, `hq`; `spleiss_load_fremd`
   uses `hrd`, `hrun`, `hq`, `hqd`; `spleiss_paar_rundreise` threads `hpre`,
   `hwr`, `hrd`, `hsave`, `hmid`, `hslotmid`, `hload`, `hpost` into the
   composed run and `hne` into the clobber leg; `spleiss_haelt_bedeutung`
   passes `hval`, `hsep`, `hplan`, `hspleiss`, `hrahmen`, `O`, `passes`, `R`,
   states, and `hsrc` into the reused 1191 closing theorem; refusal theorems
   each use their shape premises. PASS.
5. Lift, not copy: fragments are lane 1191's `spillSaveCode` /
   `spillLoadCode`; runs go through `spillSave_lauf` / `spillLoad_lauf`; the
   closing theorem applies 1191's `spill_haelt_bedeutung` (itself over
   `pipeline_correct`); call reasoning reuses `rufOk`, `rufOk_teile`,
   `rufOk_argSchranke`, `spill_gerettet_getrennt`, `bereich_getrennt`,
   `lauf_anhang`. `lauf_praefix` is a small new list-run split lemma, not a
   second evaluator. No second IR or interpreter. PASS.
6. Refusals really refuse: eight general refusal theorems plus red-zone and
   high-slot refusals, each concluding validator `= false` from the matching
   validator leg; `decide` probes compute `false` on past-end, unsorted,
   address-register, table-overlap, out-of-frame, aliased, red-zone, and
   high-slot inputs and `true` on both positives; past-end and
   address-register are additionally proved through the refusal theorems.
   PASS.
7. Witness non-degeneracy: `spleiss_haelt_bedeutung_zeuge` runs the pipeline
   witness program with rows 7 -> 35 and 9 -> 6 (memory-changing source run);
   `spleiss_paar_rundreise_zeuge` saves/reloads `42` with byte-level change
   (`spillZeu_wechselt`) beside writer program `zeugenU`
   (`schreibt = ["konto"]`). Both reuse established family witnesses. PASS.
8. Silicon: no new encodings; fragments are 1191's accepted
   movImm64/store64/load64 constructors; argument carriage uses
   rdi/rsi/rdx/rcx/r8/r9 for `i < 6`, matching System V AMD64; six
   callee-saved words. No silicon claim beyond reused vocabulary. PASS.
9. CUTS honesty and claim size: CUTS lists proved work versus OPEN items
   (1227 homing absent so positions are bare; `slots.Nodup` inheritance so
   same-slot pairs stay per-pair; middle-segment non-interference and
   `daten` agreement as producer/deployer obligations; no loaded-image
   re-connection of spliced bytes; no TSO freshness beyond reused
   vocabulary; pilot-only shapes). No hardware-correspondence and no W/GX
   claim. PASS.
10. No desired-correctness premises, no weakened guarantees: validator
    projections extract `Bool = true` legs in the established family style;
    `R` is applied at actual values; worlds come from `execBlock` and `lauf`;
    no `intro _` or `have _ :=` discards. PASS.

## Nits (not verdict-changing)

- The author report claims "no warnings", but one intermediate probe shows a
  linter unused-variable warning for `t1m` (line ~982). Final probe reports
  0 errors and the build is green. Documentation nit only.
- In `spleissRuf_argTraeger`, `hi` is unused in the left-disjunct branch but
  used in the right; the premise is used by the proof overall. Fine.
- The owner task names lane 1227 homing, which is absent in-tree; the
  candidate honestly defines bare positions instead and records the
  constraint as OPEN. No hidden weakening: unsupported shapes are refused.
- The closing theorem's first conjunct is 1191's conclusion lifted through
  reused premises: declared reuse, not a new claim.

## Builds

- Reviewer-clone baseline (master without candidate):
  `Build completed successfully (658 jobs).`
- Pinned candidate evidence: final `./lean-bau`
  `Build completed successfully (644 jobs)`; final `./lean-probe`
  `0 error(s)`; both joint witnesses with standard axioms. The base differs
  from current master (author base `515546d0`), which explains the job count
  difference; the candidate's own record is green at the pinned head.

## Open

Full loaded-image re-connection of spliced bytes, homing decision, TSO
freshness, and non-pilot shapes remain OPEN per CUTS and are not claimed.
