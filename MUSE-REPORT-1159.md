# MUSE-REPORT-1159: Pipeline tables — arrays, records, pointers

Lane 1159, clone `/home/simon/Dokumente/gabbro-muse/a1159`, branch `muse/1159`.
Owned files only: `grammatik/Grammatik/X86/PipelineTables.lean` (new, ~1340 lines),
one import line in `grammatik/Grammatik.lean`, this report.

## What was delivered

`PipelineImage.lean` represents integer slots only. This lane adds table
extents — fixed arrays (indexed loads/stores with the checked bound),
records (field offsets/layout) and region pointers with their declared
extent — over the accepted lowering, reusing it unchanged:

- **Anchor** (`TabAnker`): per-table array base (`basis`), row length
  (`zeile`), record field offsets (`felder`, explicit per-table lists).
  `feldAdr` computes `base + k*rowLen + off`, `none` outside the
  declared extent (unlisted table, missing row length, unlisted field,
  or index outside `0 ..< count` via the decided `idxOkB`).
- **Layout** (`tabLayout : Layout D`): plugs the computed address
  directly into the accepted `senkStmt`/`senkBlock`/`validate`.
  `ankerSepB` (decided, over finite lists) gives `LayoutSep`
  (`ankerSep_sound`); `tabOkB`/`tabWeltB` (`platzOkB`-style, finite
  row/field enumeration) give `WorldRep` (`tabWorldRep`, via
  `slotWort`/`slotWort_cast`).
- **Lowering**: `senkLesen` (slot/durch reads at constant index to
  `movImm64` + pilot `load64` through the `basisKeinForm` address shape
  with checked `adrOk`) and `senkSchreiben` (`assignSlot`/`assignDurch`
  to value code + `movImm64` + `store64`, same shape as `senkStmt` with
  the bound checked). Pointer value is `Unit`, so `durch` reuses the
  same address plus its carrier equation.
- **Correctness**: `senkLesen_korrekt` (load leaves the exact source
  value word in `dst`, memory/env kept), `senkSchreiben_korrekt` (runs
  the real `execStmt` outcome via `assignT_lauf` + `worldRep_store`),
  and the closing `tabellen_schreiben_laufBytes` (fetched byte run
  reaches code end with `execStmt` outcome represented, via
  `lauf_zu_laufBytes`).
- **Refusals**: four generic theorems (unplaced slot, non-constant
  index, for reads and writes) plus concrete poison probes for every
  refusal: unlisted-table read/write, variable-index read/write,
  `rbp`-base read/write (all `= none` by computation), and
  validator-level `validate = true` for the anchored block /
  `= false` for the unlisted-table block.
- **Witnesses**: two-table two-field record declaration (`zeD`),
  anchor, direct and pointer-through programs, joint `_zeuge` for all
  seven syntax-quantified theorems on a non-degenerate program (table
  written by the function, `lauf` run changing byte 8216 from 7 to 42
  by computation), CUTS, and `#print axioms` for every theorem (all
  within propext/Classical.choice/Quot.sound; no sorryAx).

New definition/theorem names: see the CUTS block and axiom prints at
the end of `PipelineTables.lean`. Entry points: `tabLayout`,
`ankerSepB`/`ankerSep_sound`, `tabOkB`/`tabWeltB`/`tabWorldRep`,
`senkLesen`/`senkLesen_korrekt`, `senkSchreiben`/`senkSchreiben_korrekt`,
`tabellen_schreiben_laufBytes`, the four `*_verweigert_*`, the `ze*`
witness family.

## Verification

- `./lean-probe grammatik/Grammatik/X86/PipelineTables.lean`: 0 errors.
- `./lean-bau`: `Build completed successfully (608 jobs)` (this lane's
  file plus the whole `grammatik/` tree, including the new import).
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` in the new file.

## What remains open

Per CUTS: block-level integration of reads (needs a `senkBlock`
extension, existing files untouched by design); scaled-index
addressing; byte-slice/float/sum/fnptr representations; TSO/time/
multicore (as in the pipeline's own CUTS).

## Finding (task believed wrong in one point)

A *constant* out-of-extent index is unrepresentable: the index type
`.index (D.count t)` carries the bound (M103), so `constInt?`
recomputes only in-bounds values on well-typed programs and a pure
out-of-bounds refusal premise is vacuous. The first draft stated it
that way; it was restated over `feldAdr = none` (out-of-extent,
unlisted table/field, missing row length — uniformly witnessable),
with `feldAdr_kein_oob` kept as the address-level bound lemma. The
bounds duty is therefore discharged twice: once by typing, once by
the decided lowering check (defense in depth). The fir-ing refusals
are the coverage ones (unlisted tables/fields, variable indices —
no scaled addressing in the pilot ISA), all probed by computation.

## Repair round (review 1160)

Independent review lane 1160 returned VERDICT: REPAIR but its body is
exclusively procedural: the reviewer clone held no candidate objects
(HEAD == master, empty diff), so none of the checklist items
(sorry/axiom scan, axiom standardness, file-scope, premise-use,
witness non-degeneracy, CUTS honesty) was executed on this code.
It lists zero semantic findings against the deliverable.

Disposition: nothing to repair — no code change was made, and none is
owed. Making unprompted edits to satisfy a verdict with no findings
would risk exactly what the repair instruction forbids (weakening
guarantees or overstating proof). Self-verification in place of the
missed review, on candidate HEAD `087c4695`:
- `pruefe-kein-sorry.py --rev muse/1159 --diff master`: 0 violations
  (615 files, 1 recorded axiom declaration elsewhere).
- `git diff --stat master..HEAD`: exactly the 3 owned files, 1420
  insertions, 0 deletions (no existing theorem touched).
- `./lean-probe`: 0 errors; `./lean-bau`: 608 jobs green.
- `#print axioms`: every theorem within propext/Classical.choice/
  Quot.sound; no sorryAx.
The deliverable stands unchanged; re-review against the code (not the
empty clone) remains the review lane's open item, not this lane's.

