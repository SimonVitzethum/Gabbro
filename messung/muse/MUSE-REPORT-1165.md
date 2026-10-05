# MUSE-REPORT-1165: Pipeline source budget to target work/time transfer

## What was done

New file `grammatik/Grammatik/X86/PipelineWork.lean` (+ one import line in
`grammatik/Grammatik.lean`) connects the source cost/budget accounting to
target retired-instruction work over the direct pipeline lowering, by
composing accepted modules only. No new interpreter, no second cost model,
no IR, no checker/Spec/goal/emitter change, no friend-reserved file.

Definitions/theorems (all in `Gabbro.Grammatik.X86.PipelineWork`):

- `pipeSummary`, `pipeSummary_ok`, `pipeSummary_max`, `pipeSummary_expand`:
  admitted pipeline summary, uniform maximum 6, expansion `src * 6`.
- `senkStmt_chunk_laenge`: lowered chunk = value code + 2 instructions.
- `senkWertT_cast`: deep lowering sees through a type cast.
- `senkStmt_flach_laenge`: shallow chunk is 3 or 5 instructions.
- `deckung_pipeChunk`: `Deckung` DERIVED from the chunk bound (never a premise).
- `pipeline_arbeit_zeit`: chunk + named costs give `t ≤ B * k`.
- `einheiten_pipe`: source steps / retired instructions / named time pinned apart.
- `pipeline_budget_arbeit`: `ComposeBudgetResum_verbindung` closed with the
  derived coverage (ghost + transfer + resumption + joint stop order).
- `pipeline_arbeit_korrekt`: validator closing in `pipeline_correct` style
  (fetched-run agreement + `bytes = encodeAll prog` + work/time bounds).
- Refusals: `senkTief_verweigert_mul`, `pipeline_arbeit_verweigert_mul`,
  `senkTief_verweigert_tief`, `pipeline_arbeit_verweigert_tief` (scratch
  exhaustion), `pipeline_arbeit_verweigert_knapp` (bound < 3),
  `pipeline_arbeit_verweigert_retry` (unbounded retry kills admission+transfer).
- Witness infrastructure: `pwTief0`, `pwChunkWit` (both `rfl`),
  `kosten_chunkWit` (time 8), `hb_chunkWit` (each ≤ 3), `deckung_pwProg`,
  `kosten_pwProg` (time 18), `hb_pwProg` (per-form cases, `ret` absent).
- Poison probes (all firing by computation): `gift_pipe_knapp`,
  `gift_pipe_mul`, `gift_pipe_tief`, `gift_pipe_retry`.
- `PipePaket` / `pipePaket_hold`: shared non-degenerate package (contract
  writes the table; source slots 7→35, 9→6 via real `execBlock`;
  fetched-byte run observably changes memory).
- `pwHT0`, `pwChunkCast`, and a `_zeuge` for every syntax-premise theorem:
  `senkStmt_chunk_laenge_zeuge`, `senkStmt_flach_laenge_zeuge`,
  `deckung_pipeChunk_zeuge`, `pipeline_arbeit_zeit_zeuge`,
  `einheiten_pipe_zeuge`, `pipeline_budget_arbeit_zeuge`,
  `pipeline_arbeit_korrekt_zeuge`,
  `pipeline_arbeit_verweigert_knapp_zeuge`, `senkWertT_cast_zeuge`,
  `pipeline_arbeit_verweigert_mul_zeuge`,
  `pipeline_arbeit_verweigert_tief_zeuge`,
  `pipeline_arbeit_verweigert_retry_zeuge`.

## Verification

- `./lean-probe grammatik/Grammatik/X86/PipelineWork.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau`: `Build completed successfully (608 jobs)`, exit 0.
- `#print axioms`: every theorem depends only on subsets of
  `propext, Classical.choice, Quot.sound` (no `sorry`/`axiom`/`native_decide`).
- An intermediate full-build run failed once with
  `lean::exception: failed to create thread` on this file (resource
  exhaustion at job 606/608, not a proof error); the retry passed with
  0 error lines. The standalone probe was green throughout.

## What remains open (see CUTS in the file)

Single shallow assignment chunks only (lit/var/one add-sub over atoms +
movImm + store); deep trees beyond scratch, checks/branches with jumps,
loops, calls, floats, pointers, aggregates, globals carry no bound (refused).
Multi-statement programs compose only over carried `Deckung` (no
block-size induction). Exhaustion timing, entry/image admission beyond
`CodeAt`, TSO/concurrency, and silicon latencies stay with their owners.
`tt` counts named per-form bounds only.

## Notes on the task / findings

- Nothing in the task statement was wrong; the scope was provable as stated.
- Work note (not a finding about the tree): in this file's namespace,
  `cases h with | frag … | weiter …` against `IstWert` did not bind the
  pattern variables, while `match h with | .frag … | .weiter …` works;
  `Pipeline.lean` uses the `cases … with` form successfully, so this is a
  resolution quirk of the new context, worth knowing for follow-up lanes.
- `Stmt.assignSlot` needs `(V := V) (l := l)` annotations at use sites
  (as in `Pipeline.lean` itself); without them `l` cannot be synthesized.

Co-Authored-By: muse-agent-1165 <muse-agent-1165@noreply.invalid>
