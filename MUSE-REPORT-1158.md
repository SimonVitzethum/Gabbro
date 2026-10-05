# MUSE-REPORT-1158 — Exact review of candidate 1157 (pipeline calls)

## Clone / branch

- Clone `/home/simon/Dokumente/gabbro-muse/a1158`, branch `muse/1158` — verified (clean tree, HEAD `e8ddbe44` at review time).
- Owned file only: `MUSE-REPORT-1158.md`. No other file created or modified.

## Candidate under review

CANDIDATE: 1157 f80385f004b27cd3ef4c4ff1542c96f86b44e1c7

- Author lane 1157, pinned HEAD `f80385f004b27cd3ef4c4ff1542c96f86b44e1c7`, base `062b979a6271b7b3044ab06be3f3cde411a0d4f1` (per `.tmp/review/SNAPSHOT.json`).
- Files (per snapshot): `MUSE-REPORT-1157.md`, `grammatik/Grammatik.lean` (one import line), `grammatik/Grammatik/X86/PipelineCalls.lean` (new, 542 lines).
- Review basis: exact snapshot under `.tmp/review/author-1157/` (`PATCH.diff`, `MUSE-REPORT-1157.md`, `OWNER-TASK.md`, `BUILD-EVIDENCE.json`, candidate `grammatik/` files). No author clone was touched; nothing outside this directory was read.

## Checks performed

- **Banned tokens:** no standalone `sorry` / `admit` / `native_decide` / `unsafe` / `axiom` declaration, no `split_ifs` / `norm_num` / `ring_nf` / `sorryAx` in `PipelineCalls.lean` (the only `admit` substring hits are English "admitted"). No `intro _` / `have _ :=` premise discard; no premise typed as `Prop` itself.
- **Premise use:** every premise of every theorem is consumed — `rufOk_teile` unpacks all five conjuncts; `rufOk_argSchranke` / `rufOk_getrennt` use arity, bound and validator premises via the accepted `argStapel_schranke` / `gerettet_stapel_getrennt`; `ladeErgebnis_nach_sichererListe` induction consumes the save list and the disjointness hypothesis; `pipeline_ruf_rahmen` consumes fit/bound/arity/save-room/red-zone plus both round-trips and the survival hypothesis (the `6 ≤ gerettet` conjunct stays in context for the `omega` frame arithmetic); `pipeline_ruf_gate` consumes fetch/executability/store/alignment premises.
- **Scope discipline:** only one existing file touched (`Grammatik.lean`, exactly one appended import at the candidate's base — the local tree has since moved on with `TsoReadBridge`/`PipelineLink`/`PipelineProfiles`, so the merger takes the union). No edits to `OptimizationRules.lean` / `OptimizationWitnesses.lean`. No new machine, decoder row, loader, or second IR/source interpreter: all heavy lifting is via accepted names verified present in this tree (`byteschritt_geholt_call`, `sichereListe_ladeListe_rundreise`, `sichere_lade_ergebnis_rundreise`, `sichereListe_rahmen_fremd`, `callGeprueft_fehlalign`, `sichereWort_ausserhalb`, `argReg_ab_sechs`, `argStapel_schranke`, `gerettet_stapel_getrennt`, `rsp8_versatz8`, `rufAlignOk`, `nachRufVersatz`, `callGeprueft`, `sichereErgebnis`/`ladeErgebnis`, `sichereListe`/`ladeListe`, `sichereWort`/`ladeWort`). The one new induction (`ladeErgebnis_nach_sichererListe`) is frame-level region reasoning over the reused vocabulary, not a duplicated model.
- **Planted refusals:** four probes, all closed by `decide`/reuse over accepted fixtures (`rufProbe_fehlalign` via `callGeprueft_fehlalign` + `alignSmis_fehlalign`; `rufProbe_rot` red-zone use; `rufProbe_rekursion` over-budget `3 > 2`; `rufProbe_schranke` out-of-frame slot 8). Fixtures (`alignDisp`, `alignS0`, `alignSmis`, `speicherZeuge`, `schlitz_disjunkt`, `writeBytesN_hit`, `read64_rahmen`, `sichere_lade_rundreise`) all exist in the accepted tree.
- **Witness:** `pipeline_ruf_rahmen_zeuge` jointly instantiates all `pipeline_ruf_rahmen` premises on a seven-argument call (frame `{0,64}`, layout `{1,6,1}`, result word 9 at slot 0, arg word 42 at slot 7) with reached saves, an observed zero-to-9 byte change (`rufWit_wechselt`), a reload (`rufWit_rundreise`), an aligned site, an admitted recursion depth, and a misaligned refusal twin. Non-degenerate in the task's stated sense (memory-changing step). It is machine-level (`Speicher`), not source-level (no tables) — but the file states no theorem over program syntax, so no mechanical inhabitation duty applies, and the author discloses this plainly (see below).
- **Silicon facts:** no new silicon claims. Register order (`rdi,rsi,rdx,rcx,r8,r9`), `rax` return, six callee-saved names, 16-byte alignment, one-word call drop with offset 8, and the red-zone ban are all stated against — and proved by `decide`/reuse over — the accepted `Stapel` / `CallAlign16` / `StackExecution` vocabulary. Nothing contradicts the supplied Intel SDM extracts; no new encoding or fault class is introduced.
- **Axioms:** per `BUILD-EVIDENCE.json`, every `#print axioms` output is a subset of `[propext, Classical.choice, Quot.sound]` (standard). The file ends with `#print axioms` for every definition/theorem plus an honest `CUTS` block.
- **Claim size:** the CUTS and the author report state exactly what is weaker than the task text — the callee body is an abstracted result-word write, so there is deliberately NO source `execBlock`/contract-to-bytes correspondence; TSO/GX spill privacy is cited (`ComposeSpillPrivacy_verbindung`), not re-proved; push/pop emission is cited, not redone; the recursion bound is a stated number with runtime enforcement OPEN. No hardware-correspondence, W/GX, loader, cost, or time claim is made. The report's "honest weaknesses" section matches the file's CUTS.
- **Build evidence:** `BUILD-EVIDENCE.json` shows the full arc — green `lean-probe` (0 errors), intermediate red probes during construction (all repaired in later probes), final `lean-bau` green at 608 jobs on the candidate base, followed by a clean commit (`f80385f0`, tree clean afterwards). The two transient `lean-bau` failures (thread-spawn resource abort, then stale-olean reads from the crashed run) are apparatus, credibly documented, and the final green run rebuilt the artifacts with no source change.

## Last `./lean-bau` result line (this clone, clean base without the candidate)

`Build completed successfully (610 jobs).` (608 at the candidate base + 2 from newer accepted modules since; no failure.)

## Verdict

VERDICT: ACCEPT

The candidate is exactly what it claims: a frame/byte-gate extension over reused accepted vocabulary with an honest, weaker-than-task statement and a non-degenerate memory-changing witness. No banned tactics, no standard-axiom violation, no scope violation, no copied evaluator, refusals that genuinely refuse, silicon facts inherited from accepted producers, and CUTS that draw the boundary where the proof actually ends (notably: no source correspondence claimed). The disclosed weakness (abstracted callee body instead of a real `execBlock`-to-bytes call correspondence) is a documented OPEN gap, not a hidden one — it is correctly sized as follow-up work, not as a reason to repair this candidate.

## What remains open (for follow-up lanes, not this candidate)

- Real source-to-bytes call correspondence (`execBlock` + executed callee bytes), per-access TSO/GX spill story (owners 573/574 interfaces), emitted/verfied callee save-restore code, and runtime enforcement of the recursion budget — all already listed in the candidate's CUTS.
- Merge note: `Grammatik.lean` needs the trivial import-line union at integration (candidate base predates `TsoReadBridge`/`PipelineLink`/`PipelineProfiles`).
