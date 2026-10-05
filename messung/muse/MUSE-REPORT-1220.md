# MUSE-REPORT-1220: exact review of author 1219 (PipelineChunkDerive)

CANDIDATE: 1219 d5c490c885f9e602a50c396efa2faeb51bce2512
VERDICT: ACCEPT

## Identity and scope
- Reviewer clone `/home/simon/Dokumente/gabbro-muse/a1220`, branch `muse/1220`, verified inside this clone only.
- Report-only independent exact review. The pinned snapshot `.tmp/review/SNAPSHOT.json` names author 1219 at head d5c490c885f9e602a50c396efa2faeb51bce2512 over base 988d75ef42521f5d437a0cb4b9d92b5d5c2e38f2, files `MUSE-REPORT-1219.md`, `grammatik/Grammatik.lean`, `grammatik/Grammatik/X86/PipelineChunkDerive.lean`, clean true.
- Reviewed artefacts (all in scope under `.tmp/review/author-1219/`): `PATCH.diff` (985 lines), the new Lean file (853 lines, read in full), `MUSE-REPORT-1219.md`, `OWNER-TASK.md`, `BUILD-EVIDENCE.json`. Nothing outside this clone was touched.

## Checks performed
- Forbidden tactics: precise grep over the new Lean file for word-boundary `sorry` / `admit` / leading `axiom` / `native_decide` / `unsafe` / `sorryAx` returns no match. The only hits for the loose pattern are the English word "admitted" in comments (layout/representation premises) and `#print axioms` lines.
- Axioms: author probe evidence lists every main theorem under subsets of `[propext, Classical.choice, Quot.sound]` (standard). No new axiom.
- Existing files: the patch touches exactly the three snapshotted files. `grammatik/Grammatik.lean` gains exactly one line, `import Grammatik.X86.PipelineChunkDerive`, in import position. No other existing file is edited; reserved optimiser files untouched.
- Premise use: no `intro _`, no `have _ :=`, no `forall rho` / `forall v` contract quantification in the new file. Spot-checked threading: `hlow` feeds the inversion in `chunk_lauf_abgeleitet`; `hc`/`hsep`/`hW`/`hE` feed the value/address run, store preservation, permission and environment; induction hypotheses consume the per-chunk equations in all four n-chunk theorems. Doc comments state the use per theorem and match the proofs.
- Accepted evaluator lifted, not copied: the file reuses `senkStmt`, `senkWertT`, `senkWertT_gerade`, `assignT_lauf`, `worldRep_store`, `repOk_int`, `constInt?_sound`, `execBlock_cons_stmtOk`, `senkBlock_assign`, `decodiertZu` with `decodiertZu_map_kanon` / `decodiertZu_append` / `arbeit_decodiert`, `pipeSummary` with `pipeSummary_expand` / `deckung_pipeChunk` / `deckung_append_pipe` / `deckung_leer`, `ketteLauf_lauf`, `ketteLaenge_sum`, `lauf_zu_laufBytes`, and lane 1195's `block_verweigert_tief_stmt` plus the whole `pw` witness package. No second IR, no second interpreter.
- Refusals fire by computation (read, not executed here): branch `ite` by `rfl` with joint witness and `gift1219_ite`; deep value at list level via the reused 1195 refusal with `gift1219_tief`; validator rejection for unlowerable lists with `gift1219_validate`. Each refusal has a witness/probe pair.
- Witnesses non-degenerate: every syntax-premise theorem carries a joint `_zeuge` conjoined with the shared `PipePaket` (one table the contract writes, memory-changing source step, target chunk runs, fetched-byte run). The n-chunk witnesses use three-chunk chains; the byte-level witness runs one chunk as a prefix of the accepted candidate bytes `pwBytes` reusing `pw_code` / `pw_worldRep` / `pw_envRepr30` with no new memory built.
- Silicon facts: no new hardware facts are stated. Instruction shapes (`movImm64` address materialisation, `store64` slot store) come out of the inversion of the accepted `senkStmt`, not from a duplicated model. Fault/ordering classes are inherited from the pipeline CUTS (single core, model memory), which the file restates.
- Claim size: CUTS are honest. Timing is explicitly open (no `laufKosten` aggregation, no time-transfer bound). The fragment is assignSlot-only with everything else refused. Machine is single core, model memory, no TSO/concurrency claim. The byte-level closing keeps code region, split and entry as named witnessed premises; the derived part is the straight-line shape (`chunks_flatten_gerade`). No hardware-correspondence or W/GX claim is made.
- Build evidence: author `BUILD-EVIDENCE.json` shows `./lean-probe` 0 errors on the final file and a final `./lean-bau` green `Build completed successfully (640 jobs)`. Two earlier full-build failures in the log are `failed to create thread` (exit 134), the documented oversubscription signature, with probes green throughout and the rerun green with no file change. Reviewer base build in this clone (no Lean changes, report-only lane): `./lean-bau` exit 0, final line `Build completed successfully (641 jobs).`

## Reasons for the verdict
- The deliverable matches the owner task: per-chunk runs and coverage derived from the lowering alone, n-chunk induction beyond two conses, validator plus soundness, three refusals with firing probes, joint non-degenerate witnesses, CUTS and `#print axioms` per theorem.
- No gate violation found on any checklist item: clean tactics, standard axioms, minimal existing-file footprint, premises used, reuse without duplication, computing refusals, honest scope.
- Process disclosures in the author report (stale commit message on one commit, one `sed` byte repair with byte-level verification, `cases`/`induction` elaboration notes) are honest and content-neutral; the content diff is reviewable per commit.

## Notes (non-blocking)
- The original lane text carried an unfilled `<full pinned HEAD>` placeholder and pointed at the author clone; the in-scope pinned snapshot resolved both. Future reviews should ship the hash and the snapshot from the start.
- Refusal firing was verified by reading the proof terms (`rfl` / `decide` / reuse of a proved refusal) together with the author's green probe log, not by executing the candidate in this clone, which owns no Lean files.
- Definitions/theorems added by this reviewer: none.
