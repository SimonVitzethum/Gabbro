# MUSE-REPORT-1178: Exact review of candidate 1177 (PipelineUnit)

Lane 1178, clone `/home/simon/Dokumente/gabbro-muse/a1178`, branch `muse/1178`
(verified: `pwd` + `git branch --show-current` match the lane file; STOP condition not triggered).
Owned file: only this report. No Lean or Rust changes made; branch was clean before and after.

## Candidate

- CANDIDATE 1177, pinned HEAD `10a3eabecaa99eaeb0dc35f09e259b2273161fa7`
  (base `062b979a6271b7b3044ab06be3f3cde411a0d4f1`), per staged
  `.tmp/review/SNAPSHOT.json`. Reviewed the exact staged snapshot:
  `.tmp/review/author-1177/grammatik/Grammatik/X86/PipelineUnit.lean`
  (1756 lines), `PATCH.diff`, `MUSE-REPORT-1177.md`, `OWNER-TASK.md`,
  `BUILD-EVIDENCE.json`. The author clone itself was not touched
  (permission boundary + HARD RULES 1); the staged snapshot is the exact
  review input and its file list matches the snapshot manifest
  (`MUSE-REPORT-1177.md`, `grammatik/Grammatik.lean`,
  `grammatik/Grammatik/X86/PipelineUnit.lean`, clean).
- Read the full 1756-line candidate file, not just the diff stat.

## VERDICT: ACCEPT

No defect found on any review dimension. Concrete evidence per check:

1. **No sorry/admit/axiom/native_decide/unsafe.** Mechanical grep over the
   exact file: zero hits (only prose "admitted entry"). Independent
   `./lean-probe` of the exact file: `== 0 error(s) ..., exit 0`, and no
   `sorryAx` in any printed axiom set. (Build history shows a transient
   `sorryAx` mid-development that was removed before the final state.)
2. **`#print axioms` standard.** All 72 prints elaborate; every set is a
   subset of `[propext, Classical.choice, Quot.sound]` (many `[propext]`
   alone). Independently confirmed by my own probe run (full list in output).
3. **Existing files untouched except one import line.** `PATCH.diff` has
   exactly three files; the `Grammatik.lean` hunk is the single line
   `+import Grammatik.X86.PipelineUnit`. No existing theorem edited,
   strength unchanged; reserved optimiser files untouched.
4. **Every premise used.** No `intro _`, no `have _ :=` anywhere.
   Spot-verified: `einheitSchluss_verbindung` (all nine legs consumed by
   the closing `simp`), `einheit_correct_entry` (hschluss via legs, hz +
   hargs via `pipeline_correct_entry`, O/passes/R via totality, v/hsrc
   via the tail-run equation), `einheit_ruf_req` / `einheit_ruf_ens`
   (call hypothesis via the ContractSites producer, hb via totality).
5. **Accepted evaluator lifted, not copied.** The only semantic facts used
   are the family's: `execStmt_assignSlot`, `callSite_vorOk`,
   `rufAt_ok_gibt_ens`, `pipeline_correct_entry`. All names resolve in the
   current tree (checked). No new executor, no second interpreter, no SSA IR.
6. **Planted refusals really refuse.** 11 poison probes, each by `rfl` or
   `decide` computing `none`/`false`: `gift_ruf`, `gift_ite`, `gift_bind`,
   `gift_ende_ruf`, `gift_endrueck`, `gift_bytes_falsch`,
   `gift_bild_falsch`, `gift_welt_falsch`, `gift_prolog_falsch`,
   `gift_eintritt_falsch`, `gift_requires_falsch` — one per `ohne_*` leg
   plus projection extras. Each refusal theorem is a direct `simp` unfolding
   of the decided check, so the probe genuinely exercises the leg.
7. **Witness non-degenerate.** `euD`: one table, entry function writes it;
   reached source run changes the slot `7 -> 42` (`euQuelle`,
   `euSlot42`); `einheit_correct_entry_zeuge` adds byte-level read-back
   `read64 ... = some 42` (`euLesen`); call-site witnesses execute a real
   call (`rufAt`) with duties at actual values. Premises are instantiated
   jointly, not piecemeal. Two-core check N/A: single-core per pipeline CUTS.
8. **Silicon facts.** No new hardware facts stated; encodings, fault
   classes and ordering come from the reused `pipeline_correct_entry`.
   No hardware-correspondence and no W/GX claim anywhere; CUTS explicitly
   inherit the pipeline bounds (pilot ISA only, one core, model memory, no
   time, no TSO, integer slots).
9. **CUTS honest; claim not larger than proof.** The missing
   `pipeline_refuses_*` byte theorem is declared weaker-than-ask with a
   sound reason: projected prefixes always run `.ok` (`rumpfBlock_total`),
   so that theorem shape is vacuous for this fragment; refusals are static
   and decided instead (seven `ohne_*` legs + per-function T3 verdicts).
   `t3_uExp108` is a `decide` computation, correctly labelled witness-only
   (off the trust path). The report's "weaker than the task ask" section
   matches the file CUTS.
10. **Task fidelity.** Generic over `UProg`/`lowerFnAt` (the T3 parsed-unit
    lowering); `requires`/`ensures`/duties carried via `einheitSchluss`
    legs + ContractSites producers; decided whole-unit check covers
    `List.finRange` (same coverage `lowerAllg` uses) with covering
    (`t3Einheit_gedeckt`) and refusal (`t3Stand_verweigert`,
    `t3Einheit_verweigert`) theorems. `GenericSourceByteCert` /
    `SourceCodeFrame` are not referenced, but the operative deliverable
    (parsed source unit to pipeline input with duties carried) is delivered
    through `UebersetzeAllg2`; those names were context pointers, not
    requirements. Not a defect.
11. **Contracts at their place, actual values** (rule 4b):
    `einheitSchluss_gibt_requires`, `einheit_ruf_req`, `einheit_ruf_ens`
    all conclude duties at the actual worlds/envs. No `forall rho` /
    `forall v` generalisation. No conclusion restates a premise (rule 4a);
    the `gibt_*` projections feed seven downstream theorems. Worlds come
    from the real `execBlock`/`execEnd` (rule 4c).

## Independent build checks (this lane)

- `./lean-bau` in this clone (unchanged base): green,
  `Build completed successfully (629 jobs).` (629 vs the author's 608:
  this master is newer than the candidate base; see note below.)
- `./lean-probe .tmp/review/author-1177/grammatik/Grammatik/X86/PipelineUnit.lean`
  (exact candidate file, elaborated read-only against this tree, no tree
  modification): `== 0 error(s) in the COMPLETE output; exit 0`, with the
  full `#print axioms` list inside the allowed set. This is a genuine
  independent check, and it additionally shows the candidate is robust to
  the base drift between its base and current master.
- Two cosmetic linter warnings remain (unused binder names `b`, `tail` in
  `einheit_correct_entry_zeuge`, lines 1449/1452): warnings only, already
  disclosed in the author report. Not verdict-relevant.

## Method notes / blockers encountered (honest record)

- Direct access to the author clone (`git -C .../a1177`) is denied by the
  permission classifier, and several `git` inspection commands
  (`git branch -a`, `git log`) were likewise rejected; simpler commands
  (`pwd`, `git branch --show-current`, `git status --short`, `echo`)
  worked. I therefore reviewed the coordinator-staged exact snapshot plus
  harness-captured `BUILD-EVIDENCE.json` instead of the live author clone.
- Copying the candidate into the buildable tree (`cp`) was rejected, and
  there is no delete tool, so I verified the build by probing the exact
  staged file in place (the wrapper resolves imports from the repo tree;
  read-only, branch left clean). `git status --short` after all checks:
  empty except this report.
- The candidate was NOT re-verified at its own base commit (its base
  `062b979a` predates this master's `c9e8e314`); instead it was verified
  against a newer tree, which is the stronger compatibility signal for the
  merge. The merge gate's mechanical checks (sorry scan, axioms) still
  apply at merge time as usual.

## What remains open (for the record, not for this candidate)

- Everything in the candidate CUTS: straight-line `assignSlot` fragment
  only; `ite`/calls/binders/locks/loops refused; `retGrund`/`leave`/`next`
  tails refused by `istRueck`; entry `ensures` not derived (user logic);
  pilot-ISA/one-core/model-memory/no-TSO bounds inherited from the pipeline.

Co-Authored-By: muse-agent-1178 <muse-agent-1178@noreply.invalid>
