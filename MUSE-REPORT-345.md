# MUSE-REPORT-345: Reviewed organisation plan C1 — TableLayout

Lane 345, author. Branch `muse/345`. Reviewer: 383.

## What was done

New module `grammatik/Grammatik/X86/TableLayout.lean` (namespace
`Gabbro.Grammatik.X86`), plus one additive import at the end of
`grammatik/Grammatik.lean`. No other file touched (`git status` shows only
these two paths plus this report).

Computed table/global layout from the source `UProg` itself, over the
canonical target vocabulary (`Typen`/`Speicher`), with `Bild.Abschnitt`
mapping and `Regionen` allocation facts. No source file, checker, goal,
emitter, doc or friend path edited.

Definitions:

- `feldWeite` (8), `typWeite : Ty -> Nat` (bool 1 byte, else one word).
  Layout choice proved of the computed function, not a C `sizeof` fact.
- `zeilenWeite (tab : UTab)`, `tabUmfang (tab : UTab)`
  (`count.toNat * zeilenWeite`; `count <= 0` gives extent 0).
- `TabLayout` (`tab`/`basis`/`len`/`ausr`), `legeTabellen`, `layoutFuer`
  (contiguous placement from a base, each base rounded up via
  `Regionen.ausricht`).
- `alsRegion`, `eintragOk` (nonempty, aligned, no 64-bit wrap), `paarOk`
  (pairwise `regionDisjunkt`), `layoutOk` (conjunction).
- `abschnittVon` (BSS-style data `Abschnitt`), `hinweisOk` (a Rust layout
  hint is accepted only if `decide (hinweis = layoutFuer …)` holds AND
  `layoutOk` holds — re-decided, never a premise).
- `slotAufz` (carrier enumeration: one `(table, row, field)` per slot).

Theorems (every premise used; no `Prop`-typed premise; no discarded
hypothesis):

- `hinweisOk_layoutOk` — a checked hint equals the recomputation and passes
  `layoutOk`.
- `abschnittVon_ausr` — an accepted entry maps to a section whose declared
  `ausrOk` holds.
- `zeugenU_schreibt`, `zeugenLayout_wert`, `zeugenLayout_ok`,
  `zeugenSlot_ne` — witness unit (table `konto`, 2 rows, field
  `x in 0 .. 100`; function `setze` with `schreibt = ["konto"]`):
  layout value, acceptance, nonempty enumeration.
- `ueberlapp_verweigert` — `[4096, 4112)` vs `[4104, 4120)` refused.
- `unausgerichtet_verweigert` — base 4104 against declared `aligned 4096`
  refused.
- `layout_zeuge` (JOINT witness) — accepted layout AND nonempty enumeration
  AND a writing function AND the layout base inside its own extent AND a
  real memory change (`write64` of 42 at `natAdresse 4096` reads back and
  changes the byte; over canonical `Speicher`, at the layout base inside
  the computed `[4096, 4112)` extent).

## Check results

- `./lean-probe grammatik/Grammatik/X86/TableLayout.lean`: 0 errors. Axioms:
  all `[]`, `[propext]`, or `[propext, Quot.sound]` — inside the standard set.
- `./lean-bau`: exit 0, 0 error lines, `Build completed successfully (386 jobs)`.
- `gabbro_ziel` axiom probe (scratch file in `$TMPDIR`, removed after):
  `'Gabbro.Grammatik.Zielsatz.gabbro_ziel' depends on axioms:
  [propext, Classical.choice, Quot.sound]` — unchanged.

## What remains open (CUTS, also in the file)

No source-to-target correspondence, no per-access TSO refinement, no
`valX86_sound`, no timing claim. Refusal is validator admission, not a
hardware fault. `typWeite` is a layout choice, not a width bridge.
`abschnittVon` is a pure mapping; loader/entry contracts are open. Empty
tables refused; globals/statics/arenas/gates have no layout form here
(QUELLBRUECKE §3 gaps 2/4/6). Shared-IR-287 consumer side is WAITING.

## Task notes / possible mismatches

- Plan names `declOf`/`fieldRangeO`/`typAt` as deps; the layout reads the
  `UProg` tables/fields/counts directly (same source, avoidance of
  `Fin`-index plumbing in a computed layout). `typAt` shapes the per-field
  width only via the bool-membership test on `UTab.bools`, which is the same
  ground fact. No source behaviour invented, no admission tightened.
- The joint witness's memory change is target-side (canonical `Speicher`
  at the layout base), not a full source `exec` run: the source-exec bridge
  is the TSO-bridge lane's business and is honestly marked OPEN.
- `slotAufz` uses `toArray.toList.zipIdx`; elaborates and `decide`s fine on
  this toolchain (Lean 4.33.1).
