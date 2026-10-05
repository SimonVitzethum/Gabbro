# MUSE-REPORT-1264: exact review of lane 1263 (per-chunk derivation for if/else and checks)

Lane 1264, report-only independent exact review of candidate 1263.
Clone `/home/simon/Dokumente/gabbro-muse/a1264`, branch `muse/1264`: verified.
Owned file only: `MUSE-REPORT-1264.md` (this file). No other file touched.

CANDIDATE: 1263 3ed024303887e47f65067e72ef6de4bd48c46080

Candidate: author 1263, pinned HEAD `3ed024303887e47f65067e72ef6de4bd48c46080`
(base `bd57fa7cff467a2c700a02b50775e6d14530ae9b`), snapshot files:
`MUSE-REPORT-1263.md`, `grammatik/Grammatik.lean` (one appended import line),
`grammatik/Grammatik/X86/PipelineChunkIte.lean` (new, 1010 lines).
Review read the candidate files only, from `.tmp/review/author-1263/`.

## Checks performed

- Forbidden patterns: precise grep for `\bsorry\b`, `\bsorryAx\b`,
  `\bnative_decide\b`, `\bunsafe\b`, `^\s*axiom\b`, `intro _`, `have _ :=`
  over `PipelineChunkIte.lean` returns NO match. A broad grep matches only
  the English word "admitted" in two prose comments and the 61
  `#print axioms` lines. No `split_ifs`/`norm_num`/`ring_nf` use.
- No `axiom` declaration exists, so non-standard axioms can only arrive via
  the imported accepted family modules. Author reports all `#print axioms`
  standard (propext / Classical.choice / Quot.sound at most); the file ends
  with a `#print axioms` line per main theorem plus an honest CUTS block.
- Existing files: only the one appended import line
  (`import Grammatik.X86.PipelineChunkIte`) in `Grammatik.lean`; no edit to
  `OptimizationRules`/`OptimizationWitnesses`, no other existing-file change.
- Premise use: spot-checked every generic theorem. Inversion theorems
  destructure the lowering equation `h`; `iteChunk_lauf_abgeleitet` and
  `pruefChunk_lauf_abgeleitet` forward every premise (`hc`, `hsep`, `hlow`,
  `hcode`, `hf`, `hrip`, `hW`, `hE`) into the accepted `senkBlock_korrektC`;
  coverage theorems feed `hlow` through the inversion into accepted
  `deckung_chunk_generisch`; `iteCheckValidate_sound` and
  `pipelineChunkIte_schluss` use all premises. No `intro _`, no discarded
  hypothesis, no `Prop`-typed premise, no conclusion restating a premise,
  no quantified-away contract parameters.
- Accepted evaluator lifted, not copied: `senkBlock_ite_inv`, `senkPruef`,
  `senkBedT`, `senkBlock_korrektC`, `deckung_chunk_generisch`,
  `sprungOk_addr`, `codeAt_von`, `addrOff_null` and the whole `pw`
  witness package (`PipePaket`/`pipePaket_hold`) are reused as black boxes.
  No second IR, no second interpreter, no `exec` redefinition. The
  `iteCheckValidate` recomputation validator is new surface, not a semantic
  duplicate.
- Refusals fire: `pipelineChunkIte_verweigert_traverse` and
  `pipelineChunkIte_verweigert_call` are `rfl` (the accepted `senkBlock`
  already yields `none` there); poison probes `gift1263_traverse` and
  `gift1263_call` apply them directly, each with a joint
  `..._zeuge` pairing the refusal with `pipePaket_hold`.
- Witnesses non-degenerate: every syntax-premise theorem has a joint
  `_zeuge` carrying the shared `PipePaket` package (one table its contract
  writes; source runs `7 -> 35`; memory-changing fetched-byte run). The ite
  then-branch `witIteT1263` performs a memory-changing store; the check
  chunk is witnessed on BOTH routes (passing `x = 30` fall-through and the
  concrete failing route `pruefChunk_grund1263` at `x = 70` reaching the
  refusal exit). The two syntax-free layout lemmas (`iteChunk_sprungZiele`,
  `iteChunk_sprungOk_entscheidung`) correctly carry no witness.
- Silicon: no new encodings invented. Jump layout reuses accepted
  `iteCode`/`iteSprung`/`iteEnde`/`sprungOk`/`sprungDisp`/`exitAdr`/
  `dispWort`; the witness literal lowerings (`witIteLowLit1263`,
  `witPruefLowLit1263`) are verified by `decide` against the Lean
  recomputation; `iteChunk_sprungOk_entscheidung` pins the gate to the
  32-bit round trip (out-of-range refused, never truncated) and the rel8
  short layout is explicitly left OPEN in `ISARelax`. Consistent with the
  supplied Intel SDM extracts scope (fixed-wide conditional/unconditional
  branch forms, no silicon fact asserted beyond the accepted family).
- Claims within proof: CUTS names exactly what is open (closed
  single-ite/single-check chunks only; no rel8; single core, model memory,
  no TSO/concurrency; entry/image/ABI via `PipelineImage`/`PipelineEntry`;
  timing a hardware assumption; unsupported shapes refused never guessed).
  No hardware-correspondence claim, no W/GX or TSO-bridge claim. The closing
  `pipelineChunkIte_schluss` composes validator soundness with accepted
  `senkBlock_korrektC` (fetched-byte run to real `execBlock` outcome).

## Last build result

- `./lean-bau` in this clone (baseline without the candidate applied):
  `== exit 0; 0 error line(s) in the COMPLETE output`,
  `Build completed successfully (661 jobs).`
- Candidate build evidence is the author's reported
  `./lean-probe ... == 0 error(s)` and `./lean-bau ... exit 0 (652 jobs)`;
  it was NOT re-executed here because applying the candidate would violate
  this lane's OWN-ONLY-report scope. All code-level review gates above were
  checked directly on the pinned snapshot instead.

## What remains open

- Nothing for this review: no follow-up owned by lane 1264.
- For the program (per the candidate's own CUTS): multi-chunk ite/check
  sequences, rel8 relaxation connection, multi-core/TSO, entry/image
  mapping composition.

## Notes on the task

- The review task named the author lane without spelling the hash inline; the
  pinned HEAD was taken from `.tmp/review/SNAPSHOT.json` (`3ed02430...`).
- No defect found in the candidate; no extra premise, no weakening, no
  fake closure.

VERDICT: ACCEPT
