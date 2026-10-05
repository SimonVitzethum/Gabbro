# MUSE-REPORT-1219: per-chunk runs derived from the lowering alone

Lane 1219, follow-up of lane 1195 (`PipelineBlockInduct.lean`).
Clone `/home/simon/Dokumente/gabbro-muse/a1219`, branch `muse/1219` (verified at start).

## What was done

NEW FILE `grammatik/Grammatik/X86/PipelineChunkDerive.lean`
(+ one `import Grammatik.X86.PipelineChunkDerive` line appended to
`grammatik/Grammatik.lean`). Namespace `PipeChunkDerive`.
Lane 1195 assumed per-chunk runs/coverage as premises of its two-chunk
theorem; here both are DERIVED from the lowering plus the admitted
layout/representation, and the induction covers n-chunk dependent
`assignSlot` chains (three-chunk witnesses throughout, induction over
the chunk list for arbitrary n).

Definitions (5): `AssignChunk` (assignSlot-only chain carrier: `t f i e
hw hL`; by construction no case split over the other statement forms),
`chunkStmt`, `blockAusChunks` (dependent `Block`, every `cons` threads
`Λ → Λ`), `chunksAusListe` (per-chunk `senkStmt`, `none` as soon as one
chunk refuses), `chunksValidate` (recompute-and-compare validator),
`witStmt1219`, `witChunk1219`, `deepChunk1219` (witness data).

Theorems (15 + 11 witnesses/probes):
- §1 `decodiertZu_map_kanon`; `senkStmt_assign_inv` (constant index,
  placed admitted slot, deeply lowered value from an accepted chunk)
  + `_zeuge`.
- §2 `chunk_lauf_abgeleitet` (source `execStmt` step AND target `lauf`
  run over the decoded chunk from the lowering alone, via the
  inversion + `assignT_lauf` + `worldRep_store`; write permission from
  the admitted `WorldRep`) + `_zeuge`.
- §3 `chunkCode_gerade`; `deckung_chunk_generisch` (admitted summary
  over generated length, deep-safe); `chunk_deckung_eins_abgeleitet`
  (budget 1 via 1165 `deckung_pipeChunk`) + `_zeuge`.
- §4 `senkBlock_chunkStmt`, `senkBlock_blockAusChunks` (lowering is the
  flattening), `ketteLauf_blockAusChunks` (n-chunk source+target runs,
  representation threaded), `deckung_blockAusChunks` (summed
  generated lengths), `chunks_flatten_gerade`, shared
  `chunksAusListe_drei1219` + four `_zeuge` on three witness chunks.
- §5 `pipelineChunkDerive_schluss` (`lauf`-level closing: source run,
  target run, coverage, work sum, lowering equation) + `_zeuge`;
  `pipelineChunkDerive_bytes` (byte-level closing in the style of
  `pipeline_correct`, via accepted `ketteLauf_lauf` +
  `lauf_zu_laufBytes`; code region/split/entry stay named admitted
  premises) + `_zeuge` (single chunk as prefix of `pwBytes`, reusing
  `pw_code`/`pw_worldRep`/`pw_envRepr30`, no new memory built);
  `chunksValidate_sound` + `_zeuge`.
- Refusals + poison probes: `chunkDerive_verweigert_ite` (generic,
  `rfl`) + `_zeuge` + `gift1219_ite`; `chunksAusListe_verweigert_tief`
  (deep value past scratch, reuses 1195 `block_verweigert_tief_stmt`)
  + `gift1219_tief`; `chunksValidate_verweigert_tief` +
  `gift1219_validate`. Every refusal fires by computation.

Checks: `./lean-probe` 0 errors after every addition (7 green
increments, 5 commits). Axioms: every `#print axioms` is a subset of
`[propext, Classical.choice, Quot.sound]` (standard; full list in
probe output). No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.
Last full build: `./lean-bau` → `Build completed successfully (640
jobs)`, 640/640, 0 errors. Note: two `./lean-bau` runs before that
failed with `failed to create thread` (exit 134) on my module after
~31s -- the documented environmental signature (AGENTS.md §9/§11,
machine oversubscribed by concurrent lanes), NOT a Lean error;
`./lean-probe` on the same file passed throughout, and the third
`./lean-bau` run went fully green with no file change.

## What remains open (also in the file's CUTS)

- Named hardware timing: no `laufKosten` aggregation or time-transfer
  bound here (stays a hardware assumption, composes through
  `BudgetExecution`; 1195 shows the shape).
- Fragment: only `assignSlot` chains; `ite`, checks, loops, calls,
  binds, globals, pointers, registers refused (`none`).
- Machine: single core, model memory, no TSO/concurrency (inherited
  from `Pipeline.lean`); entry/image/ABI via `PipelineImage`/
  `PipelineEntry`; no optimiser certificates (direct lowering,
  composes with `optimise_sound` upstream).

## Process notes / defects (honest)

1. Commit `ca34f02b` carries the §2 content under the §1 message
   ("chunk lowering inversion + joint witness"): I staged §2 with a
   stale `.commitmsg`. Direct `git commit --amend` is
   permission-denied in this environment (only `./commit.sh`, which
   has no amend path), so the label stands; the content diff is
   correct and reviewable per commit.
2. My first `Write` of the skeleton emitted a non-ASCII lookalike for
   the initial `v` in one `vertrag` token (found because `rg
   "vertrag"` missed line 31 while `rg "ertrag"` hit it; the `Edit`
   tool cannot match untypeable bytes). Repaired deterministically
   with `sed` + `\x56` escape on that one line (exception to the
   prefer-Edit rule: `Edit` was inapplicable), verified byte-level
   with case-sensitive `rg` controls and a green probe. No other
   non-ASCII bytes in owned files (checked via `rg "ertrag"` /
   `rg "Vertrag"` after every addition containing the word).
3. `cases h : e` substitutes `e` in the goal: in `senkStmt_assign_inv`
   and `chunksValidate_sound` the equation components became `rfl`
   goals -- used `rfl`, kept the pre-split equations where needed.
   `induction ... generalizing` orders the IH as `ih chunks h ...`,
   not `ih σ st ...` -- applied accordingly.
4. Nothing in the task statement looks wrong. One scoping remark:
   the task asks for a correctness theorem "in the style of
   `pipeline_correct_entry`", i.e. source `execBlock` related to the
   byte-level run on the loaded image. That full span is split here
   across `pipelineChunkDerive_schluss` (`lauf` level, everything
   derived) and `pipelineChunkDerive_bytes` (fetch level, code
   region/split/entry as named witnessed premises) -- the split is
   deliberate: the fetch leg adds no lowering information beyond the
   straight-line shape, which IS derived (`chunks_flatten_gerade`).
