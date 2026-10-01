# MUSE-REPORT-552: Independent exact-candidate review of 546 ContractSites

Clone verified: `/home/simon/Dokumente/gabbro-muse/a552`, branch `muse/552`.
Candidate: lane 546 work as pinned in `.tmp/review/SNAPSHOT.json`
(head `25800619e0949caabe07b110f61d3e493f733e44`, base `3dce9fa2`,
files `MUSE-REPORT-546.md`, `grammatik/Grammatik.lean`,
`grammatik/Grammatik/X86/ContractSites.lean`).
The author HEAD object is not present in this clone (lane branches stay
local); review is against the exact PATCH (502 lines), the staged file
copy under `.tmp/review/author-546/grammatik/`, the author task
(`OWNER-TASK.md`), the author report and `BUILD-EVIDENCE.json`.

CANDIDATE: 546 25800619e0949caabe07b110f61d3e493f733e44

## What was checked

1. Scope/ownership: PATCH touches only the report, one additive umbrella
   import (`import Grammatik.X86.ContractSites`) and the new file
   `grammatik/Grammatik/X86/ContractSites.lean` (392 lines). No edit to
   source Spec/checker/emitter, no friend-reserved
   `OptimizationRules.lean`/`OptimizationWitnesses.lean`, no second IR,
   no new executor. `grep` over the PATCH finds no `sorry`/`admit`/
   `axiom`/`native_decide`/`unsafe` outside the report's prose mention.
2. Name resolution against this clone: every reused name exists with the
   claimed shape — `AufrufOpt.InlinePflicht`/`rufAt_ok_vorOk`/
   `geistRekon_zeuge` (`X86/AufrufOpt.lean`), `rufAt_fall_nach`
   (`RufAtNachB.lean`), `ReqAmEintritt`/`EnsAmRueck`/`QEnsuresB`/
   `RufEnsCheck`/`mini_ens_am_ort`/`mini_qensures_falsch`
   (`VertragOrtB.lean`), `eP_zertifiziert` (`ZielOrtEinfadenZeuge.lean`),
   `execStmt` `.call` arm (`Semantik.lean` lines 735-741).
3. Semantics fidelity (read, not just typechecked):
   - `callSite_vorOk`: inverts the real `execStmt` call arm. The `R`-with-
     `evalArgs`-at-`lese`-world call shape matches `Semantik.lean`
     exactly; `grund` eliminated by `Fin.cast hr r |>.elim0` (uses `hr`),
     `logik`/`hardware` contradict `.ok` by constructor discrimination.
     The concluded `ReqAmEintritt` world/env is exactly the world/env the
     handler was called with. No `forall rho`/`forall v`; actual values
     throughout.
   - `rufAt_ok_gibt_ens`: sound corollary of the shared unfolding
     `rufAt_fall_nach` (same gate/body/tail shapes as
     `rufAt_ok_of_gates`); derives `RufEnsCheck` at the actual `v` plus
     the return-world identity. This is the return-duty extraction that
     `AufrufOpt` CUTS lists as OPEN — proved here in site form, not
     assumed. Minor overlap with `rufAt_nie_nachbedingung_iff_ens`
     (same unfolding family) but a genuinely useful extraction shape,
     not a duplicated desired conclusion.
   - `inlinePflicht_aus_rufAt` (`def` building `InlinePflicht`): fields
     all derived — `hp`/`hr` carried, `vorOk` from the gate, `nachOk`
     from `rufAt_ok_gibt_ens` with the `hread`/`hret` rewrites checked
     correct against the `InlinePflicht` field shapes. Note: its `h`
     premise pins the outcome world to the already-folded `sinv`; the
     witness shows this is dischargeable (via `hens.2`), so strong but
     not circular.
   - Obstruction: `vertrag_bricht_nach_schreiber`/`pruefe_requires_falsch_am_start`
     is concrete (`konto[0] = 0` vs required `5`, via `of_decide_eq_true`
     as in `geistRekon_zeuge`); `ort_statt_allquantor` reuses the
     inhabited mini contract to show quantifying away is false, not
     weaker. The empty `FernVertrag` inductive itself proves nothing
     beyond inadmissibility-by-construction; its force comes entirely
     from `ort_statt_allquantor`, which the author states plainly.
4. Witnesses: `rufAt_ok_gibt_ens_zeuge` is joint and non-degenerate
   (body + `.ok` outcomes both by `rfl`, written table
   `schreibt = true`, `0 -> 5` memory change, `Nonempty InlinePflicht`);
   `vertragStandort_lauf_zeuge` replays the reached five-step run with
   the real ghost pair, entry contract via `eP_zertifiziert`, and
   `FolgeLog`. `callSite_vorOk_zeuge` instantiates all premises jointly
   on the real `setze` call with the `execStmt` equation by `rfl`, but
   states no explicit `schreibt`/memory-change conjunct — the program
   (`eP`) is non-degenerate and sibling witnesses evidence it, so this
   is a style note, not a soundness gap.
5. N13 fit (`dokumente/x86/NEXT-PROOF-WAVE.md` line 180): non-gated half
   (site shapes over actual `Stmt`/`Endblock`, no `forall rho/v`) is
   delivered; gated lowering stays OPEN on lane 287 as the row demands.
   `Zugriffe` not imported — correct, it would be an unused import on
   the source side and belongs to the gated half. WITNESS+ deviation
   (reuse of proved `geistRekon_folge` instead of a new inline-log
   preservation proof, witnesses covering the site-duty side plus the
   same M5 log-shape run) is honestly disclosed in the report and CUTS.
   No claim beyond the bounded source-side scope is made.
6. Independent reproduction in this clone (candidate file staged
   temporarily, import appended, both removed afterwards):
   - `./lean-probe grammatik/Grammatik/X86/ContractSites.lean`:
     `== 0 error(s) in the COMPLETE output; exit 0`, all ten
     `#print axioms` standard (`[propext]` once, otherwise exactly
     `[propext, Classical.choice, Quot.sound]`).
   - `./lean-bau`: `Build completed successfully (421 jobs)` including
     `Built Grammatik.X86.ContractSites` and `Built Grammatik`
     (job count differs from the author's 416 only because master moved
     forward since; the candidate builds clean on current master).
   - After the check the staged file was deleted and
     `grammatik/Grammatik.lean` restored via `git checkout`; `git status
     --short` is clean except this report.

## CUTS (of the candidate, confirmed accurate)

IR/SCFG lowering closure WAITING on lane 287; `hp`/`hr` carried not
discharged against caller footprint/lock floor; direct `Stmt.call` only
(no `callInd`/`bindCallInd`, no separate `Block.bindCall` wrap — return
half at the `rufAt` outcome); no executable body-splice simulation (same
cut as `AufrufOpt`); no budget/timing claims. The candidate's CUTS block
says exactly this.

## Minor notes (not repair-blockers)

- `callSite_vorOk_zeuge` would be stronger with an explicit
  `(eD.signatur eSetze).schreibt () = true` conjunct; the mechanical
  inhabitation gate may want it restated there.
- `callSite_vorOk` carries `hp : RufPasst` structurally (needed to form
  `Stmt.call`) without the proof script naming it; standard and
  unavoidable, not a rule-3 violation in substance.
- Follow-up outside this candidate: `AufrufOpt.lean` CUTS still lists
  return-duty extraction as OPEN; `rufAt_ok_gibt_ens` proves it in site
  form, so that CUTS entry can be reworded at merge (author already
  suggests this; the file is owned elsewhere).

VERDICT: ACCEPT
