# MUSE-REPORT-1196: Exact review of candidate 1195 (Pipeline block-size induction)

## Scope

- Review-only lane. Own file: `MUSE-REPORT-1196.md`.
- Clone verified: `/home/simon/Dokumente/gabbro-muse/a1196`, branch `muse/1196`.
- Candidate: lane 1195, HEAD `6cfe01cad7ab5664b78fab6227422fa02ddf1aec`, base `4ed3590d85cf770cb098132aed8ee9752e29e013` (per `.tmp/review/SNAPSHOT.json`).
- Review inputs read: `.tmp/review/author-1195/PATCH.diff` (602 lines), `grammatik/Grammatik/X86/PipelineBlockInduct.lean` (510 lines), `MUSE-REPORT-1195.md`, `BUILD-EVIDENCE.json`, owner task. No files outside this clone touched.

## Candidate contents

- New file `grammatik/Grammatik/X86/PipelineBlockInduct.lean` (`Gabbro.Grammatik.X86.PipeBlock`), one import line appended to `grammatik/Grammatik.lean`, plus report. No other files touched.
- `KetteLauf` chain + `decodiertZu_append`, `ketteLauf_lauf` (via reused `lauf_anhang`), `ketteLaenge_sum`; `deckung_append_pipe` (via reused `pipeSummary_expand`), `blockDeckung_eins`, `zeit_append_pipe` (via reused `laufKosten_anhang_erfolg`); `block_zwei_korrekt` (source `execBlock`, target `lauf`, `Deckung`, time, work, `senkBlock` equation via reused `senkBlock_assign`, transfer via reused `budgetAusfuehrung_transfer`); 5 refusal theorems + 4 poison probes; joint witnesses on the accepted `pw`/`PipePaket` package; CUTS + `#print axioms` for every main theorem.

## Checks (all pass)

- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`: `rg` for the tactic forms finds nothing; the only matches for the loose pattern are prose ("admitted summary", "admits") and `#print axioms` lines.
- `#print axioms` standard: BUILD-EVIDENCE lists every theorem depending only on subsets of `propext, Classical.choice, Quot.sound`.
- Existing files untouched except one import line: PATCH touches only `MUSE-REPORT-1195.md` (new), `grammatik/Grammatik.lean` (+1 import), new file. No optimiser files touched; no existing theorem edited.
- Every premise used: traced `block_zwei_korrekt` — `hlow1/hlow2` feed the lowering equation, `hsrc1/hsrc2` the source run, `hrun1/hrun2` the target run, `hdeck1/hdeck2` the coverage append, `hcost1/hcost2` the time append, `hb1/hb2` the per-step bound feeding the transfer. No `intro _` / `have _ :=`. Small lemmas likewise consume their premises.
- Accepted evaluator lifted, not copied: no new `senk`/`exec`/`lauf`/`decodiertZu`/`Deckung`/`pipeSummary` definitions; reuses `senkStmt`, `senkBlock_assign`, `senkTief_verweigert_tief`, `pipeSummary`/`pipeSummary_expand`, `decodiertZu`, `lauf_anhang`, `laufKosten_anhang_erfolg`, `budgetAusfuehrung_transfer`, whole `pw` package.
- Planted refusals really refuse: `senkStmt` catch-all `| _ => none` (Pipeline.lean:1384) covers `onOption`; `senkBlock` catch-all `| _, _, _, _, _, _ => none` covers `bind`, and a `retry` head routes through `senkStmt` none. `rfl`/`decide` refusals are therefore computation, not assertion. Deep-tree refusal reuses accepted `senkTief_verweigert_tief`.
- Witness non-degenerate: `PipePaket` (PipelineWork.lean:605) = contract writes table + source `7 -> 35` / `9 -> 6` + fetched-byte memory change at address 8192. `block_zwei_korrekt_zeuge` instantiates all premises jointly (two reached source steps, two 5-instruction chunk runs, coverage, time 8, bound 3) and all seven conclusions plus `PipePaket` via `rfl` + reused chunk facts. Single-core pipeline, so two-core criterion is N/A; memory-changing step present.
- Silicon: no new machine definitions, encodings, flag effects, fault classes or ordering in the new file (verified: no `Befehl`/`encode`/`decode`/`schritt` definitions). Nothing to contradict the Intel SDM extracts; family facts inherited unchanged.
- CUTS honest, no overclaim: per-chunk derivation, n-chunk dependent source chains beyond two conses, entry/image, TSO/concurrency, `forever`/calls all declared OPEN; the only TSO mention is an explicit non-claim. No hardware-correspondence or W/GX claim.
- Deliberate deviation (no new lowering) is stated plainly and justified by rule 16 + architecture decision 594; composition over the single canonical lowering is within the task and stronger, not a weakening.

## Build

- Author evidence: `./lean-probe .../PipelineBlockInduct.lean` `== 0 error(s)`; `./lean-bau` `Build completed successfully (627 jobs).`
- Independent run in this clone (clean base, candidate not applied per report-only scope): `./lean-bau` ends `Build completed successfully (630 jobs).`

## VERDICT: ACCEPT

Candidate 1195 at `6cfe01cad7ab5664b78fab6227422fa02ddf1aec` is accepted as reviewed. Follow-up (not a repair condition): n-chunk dependent source `Block` composition beyond two `assignSlot` conses.
