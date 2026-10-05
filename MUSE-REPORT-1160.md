# MUSE-REPORT-1160.md — Exact review of candidate 1159 (re-review, new pin)

CANDIDATE: 1159 2bb1edcde0b242666c33b994c68aa45a3a6045af

VERDICT: ACCEPT

## Task
Lane 1160: report-only independent exact review of candidate 1159
("Pipeline: arrays, records and pointers beyond integer slots").
Owned file only: `MUSE-REPORT-1160.md`.
Pinned snapshot `.tmp/review/SNAPSHOT.json` now names author 1159 at head
`2bb1edcde0b242666c33b994c68aa45a3a6045af` over base
`062b979a6271b7b3044ab06be3f3cde411a0d4f1`, touching
`MUSE-REPORT-1159.md`, `grammatik/Grammatik.lean` and
`grammatik/Grammatik/X86/PipelineTables.lean` (marked clean).
The coordinator staged the review package in-clone under
`.tmp/review/author-1159/`: `PATCH.diff` (1465 lines, the full
base-to-head diff), `grammatik/` copies, `MUSE-REPORT-1159.md`,
`OWNER-TASK.md`, `BUILD-EVIDENCE.json` (337-entry honest command log).
The previous round's procedural block is lifted: the new pin differs
from the old one (`087c4695…`) only by the author's repair-round report
note (evidence shows only `MUSE-REPORT-1159.md` added at the new head;
code blob `e7bacce3` unchanged), so this is a first substantive review,
not approval of a stale snapshot.

## What I did
- Verified clone path `/home/simon/Dokumente/gabbro-muse/a1160`, branch
  `muse/1160`. Own `master..HEAD` diff holds only this report.
- Read the complete staged `PATCH.diff` end to end (all 1336 lines of the
  new file, the one-line `Grammatik.lean` import, the author report),
  the full `BUILD-EVIDENCE.json` log, and `OWNER-TASK.md` §§20-26.
- Ran my own read-only scans over the staged diff: forbidden-token
  scan, helper-provenance check, discarded-premise check,
  toolchain-name check (see results below).

## Checklist results (LANE.md line 23)
- **No sorry/admit/axiom/native_decide/unsafe.** My scan finds zero
  tactic/term uses. The only matches are English prose ("no sorryAx",
  "No sorry/admit/…", "an admitted integer slot", the sorry-gate log
  line). No `axiom` declaration, no `sorryAx`. The staged axiom prints
  confirm no sorryAx anywhere.
- **Axiom standardness.** Staged `#print axioms` output (48 prints at
  file end, matching the build log tail) keeps every theorem inside
  propext / Classical.choice / Quot.sound — the standard triple, used
  as subsets (mostilih propext-only or propext+Quot.sound; the two
  lowering-correctness theorems and the closing theorem additionally
  Classical.choice). Nothing beyond the triple.
- **File scope.** Diff is exactly the 3 owned files: new
  `PipelineTables.lean` (1336 lines, 0 deletions elsewhere),
  `Grammatik.lean` gains the single trailing
  `import Grammatik.X86.PipelineTables` line, plus the author report.
  No existing theorem touched, no second import-line edit, optimiser
  files untouched.
- **Every premise used.** No `intro _` / `have _ :=` anywhere in the
  new file (scan clean). Spot-checked threading: `hc` via
  `cfgOk_regs` in `lesChunk_lauf`; `hτ` in the value cast of
  `senkLesen_korrekt`; `hsep` via `ankerSep_sound` in both correctness
  proofs; `hno`/`hnc`/`hk` close the refusal goals by computation;
  `hz`/`he2`-style lookups all feed the separation/world conclusions.
- **Accepted evaluator lifted, not copied.** The lane reuses
  `Layout`/`WorldRep`/`LayoutSep`, `senkWertT`, `assignT_lauf`,
  `worldRep_store`, `slotWort`/`slotWort_cast`, `repOk`/`RepSlot`,
  `read64`/`lesbar8`/`schreibbar8`, `effAddr_null`,
  `basisKeinForm`/`adrOk`/`basisKeinForm_ok`,
  `schritt_load64_erfolg`/`schritt_store64_erfolg`, `constInt?`
  (+`constInt?_sound` from the friend-reserved optimiser file, used
  read-only, file untouched), `lauf_zu_laufBytes`, `validate`,
  and the source `execStmt`/`eval` (never redefined). `pairwise_drei`
  is the accepted `PipelineImage.lean` helper (used there 3 times),
  not a duplicate. The genuinely new content is the anchor/address
  computation, the decided checks, and the lowering wrappers.
- **Planted refusals really refuse.** Eight poison probes plus two
  validator probes, every one closed `by decide` on closed terms
  (unlisted-table read/write, variable-index read/write, rbp-base
  read/write, `validate = true` anchored / `= false` unlisted) — and
  the staged final probe run reports 0 errors, with the full-tree
  build green. The rbp rationale is silicon-correct (mod=00 r/m=101
  is RIP-relative in 64-bit mode, never a plain base).
- **Witness non-degenerate.** `zeD` is a two-table × two-field record
  family (count 2, integer fields 0..1000); only the first table is
  anchored. `zeV.schreibt` is constantly true; `zeSrcWrite` runs the
  real `execStmt` (slot holds 42 afterwards); `zeWriteRun` shows a
  `lauf` run over the lowered store changing byte 8216 from 7 to 42
  by computation. All seven syntax-quantified theorems
  (`senkLesen_korrekt`, `senkSchreiben_korrekt`, the four refusal
  theorems, `tabellen_schreiben_laufBytes`) carry joint `_zeuge`
  theorems bundling every premise with the writing program and the
  memory-changing run. Single-core is per the pipeline's own CUTS.
- **Silicon facts.** No new hardware definitions: address
  materialisation + disp-0 load/store reuse the pilot shapes through
  the accepted step lemmas; the one new hardware-adjacent claim (rbp
  refusal) is correct and additionally fenced in CUTS as a
  conservative encoder anticipation, documented not derived.
- **CUTS honest, claim within proof.** The file-end CUTS enumerates
  covered / refused / NOT-covered (no block-level read integration,
  no scaled-index, no other slot types, no TSO/GX, no time, no second
  core), records the constant-index vacuity finding without weakening
  (bound rechecked anyway via `feldAdr_kein_oob`), and claims no
  hardware correspondence or W/GX bridge. The closing theorem
  concludes a genuine fetched-byte run (`laufBytes … = .weiter`,
  rip at code end, `execStmt` outcome represented) — exactly what its
  name promises.
- **HARD-RULES rule 4.** Refusal conclusions are computed equalities,
  not premise restatements; `R` is the family-standard oracle
  response function (not a quantified-away contract value);
  contracts appear as actual premises (`V.schreibt t = true`);
  worlds come from `execStmt`/`lauf`/`laufBytes`; no premise is
  discarded.
- **Rule 13.** Seven `_zeuge` companions as listed above, all joint
  and non-degenerate.
- **Rule 15.** No `norm_num`/`ring_nf`/`split_ifs`; tactics used are
  core/`omega`/`decide`/`simp`; every helper name resolves to the
  accepted tree (final staged probe: 0 errors).

## Deltas since the previous round
The old machine-readable line named `087c4695…`; the evidence log
shows that head was already fully green (probe 0 errors, 608-job
build, sorry-gate 0 violations) and the new head adds only the
repair-round report note. The previous round listed zero semantic
findings (it executed no checklist item); there was therefore nothing
to re-inspect semantically, and the author made no code change —
which I confirm is the right disposition, not a reopened defect.

## Residual limitations (stated, not blocking)
- I reviewed the coordinator-staged diff and evidence, not the live
  author clone; that `PATCH.diff` equals the pinned head is trusted
  to the staging (its internal consistency — hash references, 1420
  insertions / 0 deletions claim, green logs — checks out).
- I did not re-execute the candidate build (candidate code is not in
  my tree and ownership forbids importing it); the staged log shows
  the author's final `./lean-probe` at 0 errors and `./lean-bau`
  green at 608 jobs, plus a sorry-gate pass.

## Build status
- `./lean-bau` in this clone (master + this report only; no candidate
  code in scope): `Build completed successfully (612 jobs)` (from the
  previous round; tree unchanged since except this report).
- New definitions/theorems by this lane: none (report-only review).
- What remains open: serial integration/publication of candidate
  1159 stays with the coordinator/watcher, gated on this finding.
- Nothing in the owner task or lane file is believed wrong beyond
  what the previous round already recorded (placeholder pin in
  `LANE.md` itself; the sidecar snapshot carries the hash).
