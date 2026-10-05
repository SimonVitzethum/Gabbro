# MUSE-REPORT-1168: Exact review of candidate 1167 (PipelineRegAlloc)

Lane 1168 (reviewer) — Pipeline: register allocation, spills and privacy validated.
Report-only exact review of the pinned snapshot in `.tmp/review/` (read inside
this clone only; the author clone was never touched). An earlier revision of
this report recorded BLOCKED for lack of candidate material; the pinned
`SNAPSHOT.json` plus `author-1167/` (`PATCH.diff`, candidate file, author
report, build evidence) has since arrived in-clone, so the full review below
was performed against the exact pinned bytes.

CANDIDATE: 1167 3bf5b44155c599c56f5ac5eaf7d035254dde89c6

VERDICT: ACCEPT

## What was reviewed (exact bytes)

- `SNAPSHOT.json`: author 1167, head `3bf5b441…`, base `062b979a…`,
  files `MUSE-REPORT-1167.md`, `grammatik/Grammatik.lean`,
  `grammatik/Grammatik/X86/PipelineRegAlloc.lean`, `clean: true`.
- `PATCH.diff` (541 lines): new 434-line `PipelineRegAlloc.lean`, exactly one
  added import line in `grammatik/Grammatik.lean`, author report. No other
  file touched — in particular no existing Lean file edited and no reserved
  optimiser file touched.
- `MUSE-REPORT-1167.md` and `BUILD-EVIDENCE.json` (full probe history plus
  final `./lean-bau` green at 608 jobs).

## Checklist findings

1. **Forbidden tokens:** `rg` over the pinned candidate file finds no `sorry`,
   `admit`, `axiom`, `native_decide`, `unsafe`, no `^axiom` declaration, and
   no discarded premise (`intro _`, `have _ :=`). Pass.
2. **Axioms:** build evidence `#print axioms` shows defs on nothing or
   `[propext]`, the closing theorems on exactly
   `[propext, Classical.choice, Quot.sound]` (inherited from the accepted
   `pipeline_correct`), one helper (`pipe_alloc_spillPrivat`) on
   `[propext, Quot.sound]`. All within the standard triple. Pass.
3. **Existing files:** only the single appended import line. Pass.
4. **Evaluator lifted, not copied:** the file reuses accepted `PipeCfg`,
   `cfgOk`, `abbOf`, `validate`, `pipeline_correct`, `Layout`/`LayoutSep`,
   `WorldRep`/`EnvRepr`, canonical `spillSlot` vocabulary,
   `Rahmen.schlitzNat`/`schlitzNat_schranke`, and the pipeline witnesses
   (`pwCfg`, `pwL`, `pwSrc`, `pwBytes`, `pw_quelle30`, `pw_validate`,
   `pw_layoutSep`, …). I confirmed each name exists in this clone's tree
   (`Pipeline.lean`, `PipelineWitnesses.lean`, `Stapel.lean`). No second IR,
   no second source interpreter (decision 594 respected). The `cfgOk`
   statement in this tree matches the conjunction the candidate extracts in
   `pipe_alloc_cfgOk` conjunct for conjunct, and `pwCfg.regs = [.r10]`
   makes `pipeA0_cfg` hold by `rfl`. Pass.
5. **Every premise used:** in `pipe_alloc_haelt_bedeutung` the validator
   hypothesis feeds both allocator legs, the frame-separation hypothesis
   feeds the privacy leg, and every source/pipeline premise is forwarded to
   `pipeline_correct`. Pass.
6. **Refusals really refuse:** five refusal probes by computation, each
   targeting a distinct validator leg, all verified by hand against the
   validator definition — clobbered registers (additionally through the
   refusal theorem `pipe_alloc_verweigert_kollision`), `rsp` in the homes
   (calling convention), a spilled live variable (`all Option.isSome`
   fails), reserve 99 outside a 2-slot frame, frame `[4096,4112)` over code
   `[4096,4178)`. One positive probe (`pipeA0_ok` by `decide`). Pass.
7. **Witness non-degenerate:** `pipe_alloc_haelt_bedeutung_zeuge` instantiates
   all premises jointly on `pwSrc` — a real `execBlock` run writing two
   slots, memory 7 → 35 and 9 → 6 (confirmed against `pw_quelle30` /
   `pw_quelle_vorher` in this tree). Memory-changing; single-core fragment,
   so no second core is relevant. Pass.
8. **Silicon facts:** `pipeAlleRegister` lists exactly the 16 x86-64 GPRs
   (exhaustiveness proved by `cases` over `Register`); `rsp`/`rbp` reserved
   as stack/frame pointers; frame `[16384,16400)` disjoint by computation
   from code `[4096,4178)` (`pwBytes.length = 82`) and tables at 8192/8200.
   Pass.
9. **CUTS honest, no overclaim:** spill *code* generation, sub-block
   liveness, callee-saved restore/argument passing, and TSO freshness are
   explicitly OPEN; the refusal `Bool` is stated to be validator admission,
   never a hardware fault; no W/GX or hardware-correspondence claim is made.
   The whole-block liveness argument is soundness prose around an
   unconditionally true proved statement (pairwise register disjointness),
   with incompleteness declared, not hidden. Pass.

## Non-blocking notes (no repair demanded)

- `open … OptimizationRules` in the candidate file appears unused; harmless.
- `rbp` has no dedicated probe, but it shares the exact decided conjunct
  with `rsp`, which is probed — coverage is by leg, and every leg is hit.
- The first `./lean-bau` in the evidence needed a re-run after a stale
  `RufAdaequatG.olean` read failure; documented as apparatus staleness with
  the green re-run recorded. Plausible and consistent with the final state.

## Verification runs

- Author pinned evidence: final `./lean-probe` 0 errors; `./lean-bau`
  `Build completed successfully (608 jobs).`
- Reviewer (this lane, this clone, no Lean changes of my own):
  `./lean-bau` last result line: `Build completed successfully (609 jobs).`

## Owned content

This report (`MUSE-REPORT-1168.md`) is the lane's only file. No Lean code
was written and no claim beyond the snapshot is approved.
