# MUSE-REPORT-428: ParallelMoves (continuous Lean proof reserve)

## Task
New reusable module `grammatik/Grammatik/X86/ParallelMoves.lean` plus one additive
umbrella import. Prove canonical pilot `movReg64` sequence scheduling / cycle-break
facts with explicit scratch liveness, alias premises and unchanged flags/memory,
through the REAL canonical execution (`schritt`/`lauf` of `Ausfuehrung.lean`),
never a duplicated move evaluator. Joint memory-changing reached-prefix witness
plus bad alias/scratch counterexamples. No free scratch register assumption.

## What was done
Created `grammatik/Grammatik/X86/ParallelMoves.lean` (namespace
`Gabbro.Grammatik.X86`, imports only `Grammatik.X86.Ausfuehrung`) and appended
`import Grammatik.X86.ParallelMoves` to `grammatik/Grammatik.lean`. No other file
touched. Consumer: register allocation parallel-copy resolution
(IR-VALIDIERUNG.md, DIRECT-COMPILER-DESIGN.md ABI): a parallel copy becomes a
sequential `movReg64` list, a 2-cycle is broken through a named scratch.

Definitions: `PMove` (one copy edge, `Register x Register`), `moveInstr`
(edge to canonical decoded instruction, length 3, the Codec length),
`expandMoves` (edge list to sequential instructions, pure syntax map, no
semantics), `swapMitScratch a b t` (save/overwrite/restore triple),
`tauschZeugeReg`/`tauschZeuge`/`tauschZeugeProg` (witness state and program).

Theorems (18, every premise used in its proof):
- `moveInstr_laenge`, `schritt_moveInstr`: edge length valid; edge steps as the
  canonical register `mov` (reuses `schritt_movReg64`).
- `moveInstr_speicher`, `moveInstr_flags`,
  `moveInstr_ziel`, `moveInstr_fremd` (memory/flags/untouched-register frames,
  reuse the canonical `schritt_movReg64_*` frames and `regSet_*`).
- `lauf_kopf`, `lauf_einzeln`: reached cons/singleton decomposition over
  canonical `lauf`. These did not exist anywhere in `Grammatik/X86` (checked by
  grep before writing); every lowering proof needs them.
- `expandMoves_speicher`, `expandMoves_flags`: whole-sequence memory/flag
  preservation by induction.
- `swapMitScratch_entfaltet`, `swap_tausch`: the 2-cycle swap through a
  distinct scratch exchanges payloads. Alias premises are load-bearing:
  `hbt` keeps `b` across the save, `hat` keeps `t` across the overwrite,
  `hab` keeps `a` across the restore.
- `swap_scratch_belegt`: scratch ends holding the old `a` value (liveness
  obligation for the allocator: `t` is dead after the swap).
- `swap_rahmen`: every uninvolved register is kept.
- `swap_speicher_flags`: swap changes no memory and preserves flags.
- `tausch_zeuge`: JOINT witness by `decide` over canonical `lauf`: a reached
  run whose prefix observably changes memory (`movImm` + `store` through the
  stack pointer, byte `0x00` to `42` at the stack top) and whose suffix swaps
  `rax = 7` / `rbx = 9`, with scratch `r10` ending at `7`. Non-degenerate:
  distinct payloads plus a real store-changing prefix.
- `naiv_ohne_scratch_verliert`: scratch-free `[rax<-rbx, rbx<-rax]` ends at
  `(9, 9)`, never the swap `(9, 7)`.
- `falscher_scratch_verliert`: scratch aliasing the first payload
  (`swapMitScratch rax rbx rax`) also ends at `(9, 9)`.

Axioms: each main theorem prints `[propext, Quot.sound]` (subset of the goal
standard), except `moveInstr_laenge` and `swapMitScratch_entfaltet` which
depend on no axioms. No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`,
no `Prop`-typed premise, no discarded premise.

Checks: `./lean-probe` on the module: 0 errors. Full `./lean-bau`: exit 0,
393 jobs, build completed successfully. `gabbro_ziel` axiom probe after the
merge-ready tree: exactly `[propext, Classical.choice, Quot.sound]`.

## What remains open (see CUTS in the file)
No general n-cycle scheduling (only the 2-cycle with one caller-provided
scratch; no liveness analysis, no allocator). No free scratch (deadness at the
program point is the allocator's obligation). Only `movReg64` (no narrow
widths, immediates, memory operands or flags-affecting forms). No decoder,
encoder, TSO bridge, concurrency, source correspondence, contract, cost,
timing, progress or whole-image claim. No per-access atomicity.

## Findings and remarks
1. Apparatus finding (Lean behaviour under load, no proof content affected):
   two proofs that each case-split the giant canonical `schritt` match term
   in one process deterministically crashed the checker with
   `lean::exception: failed to create thread` (exit 134), while each proof
   alone passed repeatedly and a size-matched padded file also passed. Fixed
   by deriving `lauf_einzeln` from `lauf_kopf` (small-constructor steps only),
   so exactly one proof performs the large split. Bisect scratch files used
   (`pm-*.lean` under `.tmp/`, gitignored, not committed).
2. Tactic note for followers: `cases h : schritt d s` substitutes the goal as
   well; for an existential goal mentioning `schritt` use
   `generalize ... at h ⊢` plus `rfl`, and close a `none = some _` hypothesis
   with full `simp at h`.
3. Naming: identifiers follow the established German vocabulary of the
   neighbouring canonical modules (`schritt`, `lauf`, `zeuge`, `tausch`,
   `rahmen`, `belegt`, `entfaltet`, `fremd`), as the task directed to resolve
   names from the accepted files; comments and docs are English.
4. Nothing in the task statement looks wrong. The `ZEUGE:`-style joint
   non-degenerate witness requirement is met by `tausch_zeuge`; rule 13
   strictly applies to source-syntax premises, which this machine-level module
   has none of.
