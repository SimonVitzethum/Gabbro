# MUSE-REPORT-870: Optimiser rule — alias commutation rule

Lane 870, clone `/home/simon/Dokumente/gabbro-muse/a870`, branch `muse/870`.
New module `grammatik/Grammatik/X86/OptAliasCommute.lean` (+1 import line in
`grammatik/Grammatik.lean`). No other files touched. No new diagnostic/gift/
example/CLI numbers, no MARKE changes, no source/checker/Spec/goal/emitter
edits, no friend-reserved optimiser files.

## What was done

DESIGN section 7 row implemented as specified: local premise "disjoint
objects + same interleaving evidence as load-CSE", certificate "B+C", failure
case "reorder across fence/lock/acquire-release on token evidence alone",
phase M. There is no accepted shared IR yet, so the rule is stated over the
real `Syntax`/`Semantik` fragment it covers (two slot stores, `World.storeSlot` /
`World.schreibSlot`), reusing `TableLayout`-style computed reasoning only where
stated as CUT; `CostSummary.expandBound` is reused for the budget conjunct.

Definitions:
- `AliasCommuteCert` (`fussDisjunkt`, `tokenErhalten`, `anteilStabil`,
  `ohneSchranke`), `aliasCommuteZulassen` (conjunction admission; a refused
  site keeps its certified unoptimised translation, never a warning).
  (Named `aliasCommuteZulassen` because `aliasZulassen` already exists in
  `X86/OverlapRefusal.lean` with a different type; the first full build
  caught the collision and it was renamed.)
- `AnteilStabil D σ t`: `D.geteilt t = false ∨ ∃ L, L ∈ σ.haelt` — the same
  kind of interleaving evidence load-CSE needs (private carrier or held lock).

Theorems (every premise used by its proof; no `sorry`/`admit`/`axiom`/
`native_decide`/`unsafe`):
- Refusals: `aliasVerweigert_schranke` (fence/lock/acquire-release between the
  sites refuses even with full token evidence), `aliasVerweigert_anteil`
  (shared motion without interleaving evidence), `aliasVerweigert_fuss`
  (name inequality is not disjointness), `aliasVerweigert_token`, plus probes
  `probe_aliasCommuteZulassen_ok/_schranke/_anteil`.
- Value core over ARBITRARY values/types (floats included): `storeSlot_hit`,
  `storeSlot_miss`, `aliasCommute_wert1/_wert2/_wert1h/_wert2h` (both orders
  deliver both values at proved-disjoint indices), `storeSlot_spur`.
- IEEE: `aliasGleit_behält` (admitted kernel-recomputed equation agrees under
  `gleitPasst`; the commute performs no float op, enters no rounding scope),
  `probe_aliasGleit`.
- Observations: `aliasCommute_haelt` (no lock taken/released),
...[truncated 2085 chars]
