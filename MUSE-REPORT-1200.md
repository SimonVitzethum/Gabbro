# MUSE-REPORT-1200: exact review of candidate 1199 (PipelineLoadedAll)

## VERDICT: ACCEPT

Candidate: lane 1199, pinned HEAD `046e4d94f36b2ad8d91e9a3e1f1f509f86f61004`
(base `4ed3590d85cf770cb098132aed8ee9752e29e013`), reviewed from the
coordinator snapshot `.tmp/review/author-1199/` (`PATCH.diff`, `MUSE-REPORT-1199.md`,
`BUILD-EVIDENCE.json`, `OWNER-TASK.md`) plus signature cross-checks against this
clone's tree. Files in candidate: `MUSE-REPORT-1199.md` (new),
`grammatik/Grammatik.lean` (one import line), `grammatik/Grammatik/X86/PipelineLoadedAll.lean`
(new, 732 lines). No other files touched.

## Checks performed and results

1. **No sorry/axiom/native_decide (merge-gate scope):** word-boundary grep over the new
   file for `sorry|admit|^axiom|native_decide|unsafe|split_ifs|norm_num|ring_nf|intro _|have _ :=`
   returns zero code matches (only prose/`#print axioms` lines). PASS.
2. **Axioms standard:** author's final `lean-probe`/`lean-bau` output lists every new
   theorem within `propext, Classical.choice, Quot.sound` (several need only a subset;
   pure `decide` probes depend on nothing). Matches the file's 35 `#print axioms` lines.
   No new axiom. PASS.
3. **Existing files untouched except one import line:** snapshot file list is exactly the
   three files above; `Grammatik.lean` diff is the single appended
   `import Grammatik.X86.PipelineLoadedAll`. No `OptimizationRules`/`OptimizationWitnesses`
   touch, no IR, no second interpreter. PASS.
4. **Lifted, not copied:** the five family theorems apply accepted closings unchanged —
   `spill_haelt_bedeutung` (`PipelineSpill.lean:448`), `einzelRuf_korrekt`
   (`PipelineCallsExec.lean:209`), `tabellen_schreiben_laufBytes` (`PipelineTables.lean:1137`),
   `pipeline_arbeit_korrekt` (`PipelineWork.lean:322`), `pipelineFloat_seq` /
   `pipelineFloat_refuses_validator` (`PipelineFloat.lean:95,313`), `verknuepft_korrekt`
   (`PipelineLink.lean:274`). All seven names verified present in this clone's tree; call
   argument orders spot-checked against callee signatures (`bildFuer cwCfg [] cwBody cwBytes
   piPs pwSigma piEs` matches `bildFuer c certs src bytes ps sigma es`; the `einzelRuf_korrekt`
   application matches premise order). No new evaluator, decoder, or semantics defined. PASS.
5. **Every premise used:** audited all five main theorems premise by premise; each is
   consumed (projected via `imageOk_layoutSep/codeAt/worldRep`, rewritten via `hst`, or
   passed to the lifted closing). No `intro _` / `have _ :=`. PASS.
6. **Refusals really refuse:** all seven poison probes (`gift_spill_code/ruf_rot/
   tabelle_fremd/float_profil/float_laenge/link_range/arbeit_mul`) are closed `by decide`
   goals (or reuse accepted probes) over concrete data; the green elaboration IS the firing
   proof. Shapes are genuine: spill frame overlapping code base, red-zone call, unlisted-table
   read, flush-to-zero profile (`0x9F80`), 16-byte float form, `rel32 2147483648` out of range,
   `2 * 3` with no deep lowering. PASS.
7. **Witnesses non-degenerate:** spill rows 7->35 / 9->6 through the real `execBlock`
   (`pw_quelle30` + `pw_quelle_vorher`); calls add byte-level frame-save change
   (`rufWit_wechselt`: result byte differs) plus argument round-trip (`rufWit_rundreise`,
   word 42); tables carry `zeRunChange` (byte 8216: 7 -> 42, `zeWriteRun`, verified in
   `PipelineTables.lean:994-1008`); work reuses the priced two-slot witness; floats store
   infinity with a byte inequality (`read64 ... = some 0x7FF0000000000000` plus `bytes ... ≠`).
   Single core throughout, which the CUTS disclose as inherited. PASS.
8. **Silicon facts:** no new hardware claims. Float lengths (4-byte `movsdRR`/`addsdRR`
   forms) are constructed `FpDecodiert` lengths consistent with the owning scalar family;
   the file explicitly refuses any byte-fetch connection for floats. No TSO/GX, no timing,
   no silicon-correspondence claim anywhere; CUTS list exactly what is not proved. PASS.
9. **No fake closure / no weakened guarantee:** float loaded-image correctness is
   sequence-over-loaded-memory plus refusal, not a byte-run relation — the honest maximum,
   as `FpBefehl` has no pilot byte encoding. The five-statement shape (instead of one
   functor) is justified against rule 4a in the author report. PASS.

## Non-blocking observations (not REPAIR grounds)

- `fragmentBytesGeladen` (the "one shared loaded-code predicate") is defined but never
  used by any theorem — the sharing is actually done by repeating the
  `imageOk`/`weltOk` projection pattern. Dead definition; suggest deleting it or threading
  it through in a follow-up.
- Lowercase `vertrag` binder (`{V : vertrag D}`) relies on autoImplicit unification to
  `Vertrag` (there is no lowercase definition; the tree uses `Vertrag`/`vertragVon`).
  It elaborates green with standard axioms and the author discloses it, but a tree-wide
  cleanup to `Vertrag` is coordinator business.
- One `./lean-bau` run in the build evidence failed first with a toolchain file-IO error
  (`.../Init/Data/Array/Count.olean.private`) on no source change; the immediate retry was
  fully green (627 jobs). I read this as apparatus noise, consistent with the author's
  recording — not a finding.

## Review limitation (honest partial status)

- `./lean-bau` on this reviewer clone (no Lean changes, only the untracked report):
  last result line `Build completed successfully (631 jobs).` — green, zero errors.
  (631 vs the author's 627 jobs: this clone's master base carries four more modules;
  expected base drift, no semantic impact on the candidate.) `./lean-probe` of the
  candidate file itself was not re-run here — the candidate branch is not present in
  this clone; the file-level evidence is the author's stepwise green probes plus the
  final `lean-bau exit 0` at the pinned commit, cross-checked by my static audit.
  The merge gate re-runs the build and `pruefe-kein-sorry.py` independently.
- Commit: performed below via `arbeitsprotokoll/.commitmsg` + `./commit.sh`
  (rule 8) after the green build.

## What remains open

Nothing from this review blocks the merge. Follow-ups for the coordinator: delete or use
`fragmentBytesGeladen`; lowercase-`vertrag` cleanup; the inherited CUTS (float byte-fetch,
multi-statement callees, block-level table reads, per-access W/GX bridge, silicon
correspondence) stay with their owners.
