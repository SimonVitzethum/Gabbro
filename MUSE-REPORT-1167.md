# MUSE-REPORT-1167: Pipeline register allocation, spills and privacy validated

Clone `/home/simon/Dokumente/gabbro-muse/a1167`, branch `muse/1167`. Owned files only:
`grammatik/Grammatik/X86/PipelineRegAlloc.lean` (new),
`grammatik/Grammatik.lean` (one appended import line), this report.

## What was done

New file `grammatik/Grammatik/X86/PipelineRegAlloc.lean` (namespace
`Gabbro.Grammatik.X86.PipeRegAlloc`): a checked register allocator result
(untrusted candidate, decided validator) at the end-to-end pipeline level.

- Candidate `PipeRegAlloc`: per-variable home (`belegung`, `some r` =
  register, `none` = spilled), per-variable spill reserve (`spillVon`),
  holding frame (`rahmen`). Lowering configuration `pipeAllocCfg`
  (positional register list `pipeAllocRegs`, spilled reads as `rsp`).
- Validator `pipeRegAllocOk` (decided `Bool`): no spilled live variable,
  index-decided collision freedom `pipeKollisionsFrei`, calling
  convention (`rsp`/`rbp` reserved), working-register freshness exactly
  matching `cfgOk` over the allocated registers, every reserve in-frame,
  variables aligned with reserves, frame off the code region.
- `pipe_alloc_cfgOk`: a validated allocation yields exactly the checked
  `cfgOk` configuration the lowering needs.
- `PipeInterferenzFrei` + `pipe_kollisionsFrei_sound` +
  `pipe_alloc_interferenzFrei`: the decided check means no two distinct
  variables share a register. Liveness is whole-block and structural
  (context variables are never redefined, so every index below the
  assignment length is live throughout and every pair interferes).
- `PipeRahmenGetrennt` (per-program frame/table separation) +
  `PipeSpillPrivat` + `pipe_alloc_spillPrivat`: validated reserves use the
  canonical `spillSlot` addresses and are disjoint from every placed
  source slot (via `schlitzNat_schranke`).
- `pipe_alloc_verweigert_kollision`: a clobbering allocation (two
  distinct variables, one register) validates to `false`.
- `pipe_alloc_haelt_bedeutung`: if the pipeline validator accepts the
  bytes under the allocated configuration, every real `execBlock` run of
  the original block is matched by a fetched byte run with world and
  environment represented (via `pipeline_correct`), and the allocation is
  interference-free with private reserves. Every premise is used.
- Probes: positive `pipeA0_ok` (`pipeA0`: `x` in `r10`, reserve slot 0 in
  frame `[16384, 16400)`); refusals `pipe_probe_clash` (through the
  refusal theorem), `pipe_probe_rsp`, `pipe_probe_spill`,
  `pipe_probe_aussen`, `pipe_probe_code`, all by computation.
- Joint witness `pipe_alloc_haelt_bedeutung_zeuge` on the non-degenerate
  pipeline witness program `pwSrc` (writes two slots; memory 7 -> 35 and
  9 -> 6, so the run is memory-changing): all premises instantiated
  jointly, closing theorem applied.
- `grammatik/Grammatik.lean`: appended `import Grammatik.X86.PipelineRegAlloc`.

## Verification

- `./lean-probe grammatik/Grammatik/X86/PipelineRegAlloc.lean`: 0 errors.
- `./lean-bau` last result line: `Build completed successfully (608 jobs).`
- `#print axioms`: defs depend on nothing or `[propext]`; closing
  theorems on exactly `[propext, Classical.choice, Quot.sound]`
  (inherited from `pipeline_correct`). No `sorry`/`admit`/`axiom`/
  `native_decide`/`unsafe`. No existing file changed except the import line.
- First `./lean-bau` run failed transiently with `failed to read file
  .../RufAdaequatG.olean` at `[606/608]`; re-run completed 608 jobs
  green. Apparatus staleness, not a tree defect.

## What remains open (also in the file CUTS)

Spill code generation (a spilled live variable is refused; the lowering
has no spill code, as its own CUTS already state); liveness finer than
whole-block (sound over-approximation: an unused variable still needs a
register); callee-saved restore and argument passing (no calls in the
fragment); TSO freshness of spill slots (covered at the composed level by
`ComposeSpillPrivacy.lean`).

## Task critique

- "Live ranges from the source block structure" is realized as whole-block
  ranges derived from variable immutability. This is sound but incomplete;
  a finer recomputed liveness (in the style of `OptAllocLinear.lean`
  intervals) is explicitly open, not silently assumed.
- The task's `pipeline_correct_entry` style is met through
  `pipeline_correct` (block level, which the entry theorems wrap); no
  second interpreter or SSA IR was introduced (decision 594 respected).
- Name collisions avoided by measurement: `allocOk` (taken by
  `OptAllocLinear.lean`) became `pipeRegAllocOk`; two-arg `RahmenGetrennt`
  (taken by `Stapel.lean`) became `PipeRahmenGetrennt`.
- Two toolchain facts worth recording: `∀ r : Register` has no
  `Decidable` instance (bounded quantification over an explicit 16-list
  was used), and `&&`-chains destruct left-nested (`h.1.1.1.2`, not
  `h.2.2.2.1`).
