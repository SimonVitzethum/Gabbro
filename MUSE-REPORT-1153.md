# MUSE-REPORT-1153: Pipeline lowering onto the wider ISA

## What was done

New file `grammatik/Grammatik/X86/PipelineWide.lean` (+ one import line
in `grammatik/Grammatik.lean`), proving pilot-lowering vs wide-lowering
run equivalence for the compact imm/disp fragment, with decided
refusals for everything else. No existing file was changed except the
one import line; `OptimizationRules.lean`/`OptimizationWitnesses.lean`
untouched; no SSA IR, no second source interpreter.

Definitions: `wideDatOk` (decided coverage: `movImm64`/`load64`/
`store64`), `kanonW`/`kanonP` (canonical compact/pilot decodings),
`wideOk` (decided per-instruction validator: exactly the selector's
choice plus coverage), `wideSelect` (whole-program selection, `none`
= refused), `laufW` (compact run mirroring `Ausfuehrung.lauf`).

Theorems (all reuse accepted lemmas, nothing duplicated):
- `wideSchritt`: single-step exact equivalence (`kernGleich`:
  registers, flags, memory; RIP excluded) from any two agreeing
  states, via `kompaktWahl_movImm64/load64/store64`, for both
  success and explicit-refusal outcomes on each side.
- `wideSelect_korrekt`: whole-run version (both refuse, or both
  succeed agreeing), by induction with reused `optRel_bind`;
  bridges `lauf_cons`/`laufW_cons` (same shape as `ISASelect.laufI_cons`),
  decomposition `wideSelect_cons`, canonical lengths `kanonP_ok`
  (reused `laengeOk_encode`) and `kanonW_ok`/`kanonW_len`.
- Six poison refusals, each a decided computation:
  `wideSelect_refuses_add` (no compact analog),
  `wideSelect_refuses_push` (no compact analog),
  `wideSelect_refuses_jump` (refused even where the branch selector
  would succeed -- target preservation needs layout relaxation),
  `wideSelect_refuses_imm` (`0x100000001` is neither zero- nor
  sign-extended from its low 32 bits),
  `wideSelect_refuses_rbp` (`rbp` disp0 special case plus disp 200
  outside the signed-8-bit range),
  `wideSelect_refuses_tail` (covered head, refused tail).
- `wideSelect_korrekt_zeuge`: instantiates `wideSelect_korrekt` on
  the NON-DEGENERATE store program `[store64 rsp rax 8]` over the
  shared witness state `cwZustand` (RAX=10, rsp=8192, zeroed memory):
  selection succeeds, both runs reach successors agreeing on the
  observable, the word reads back as 10 at address 8200 while the
  initial byte there is 0 -- a real memory-changing step. Helper
  `bind_some_elim` (no axioms).

## Checks

- `./lean-probe grammatik/Grammatik/X86/PipelineWide.lean`:
  `== 0 error(s)`, axioms at most `[propext, Quot.sound]`
  (subset of the goal's standard axioms; `gabbro_ziel` untouched).
- `./lean-bau`: `Build completed successfully (608 jobs)`.
  Two transient environmental failures preceded it (one
  `failed to create thread`/exit 134 on the first attempt, one
  unreadable toolchain `Grind` olean on the second); both cleared on
  retry with zero source changes -- apparatus, not the tree.

## What remains open / what I believe is wrong or limited

- Narrow widths, multiply/divide, shifts, SETcc/CMOVcc have NO
  lowering here, only documented refusals in CUTS. This is honest
  but narrower than the task sentence: a 32-bit narrow op is not
  observable-equal to any 64-bit pilot op, and the
  `ExtendedExecution` families (`ExtInstr` over `FpZustand`) have no
  pilot source form to check against -- stating those validators
  needs width-specific value/flag bridges that do not exist yet.
- The source-`execBlock` leg stays with the pilot pipeline; this
  file proves pilot-vs-compact run equivalence only, plus no
  byte-level fetch bridge for compact bytes (no `CodeAt`/`laufBytes`
  over `encodeC` programs). No TSO, no time, no control flow.
- `kanonW_ok`'s proof replicates `ISA.encodeC_len`'s one-liner
  instead of importing `ISA.lean`, to keep the import footprint
  small; the comment cites the source. If the coordinator prefers
  the import, it is a two-line change.
