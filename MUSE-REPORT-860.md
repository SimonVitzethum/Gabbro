# MUSE-REPORT-860: Optimiser rule — constant folding (lane 860)

## What was done

New file `grammatik/Grammatik/X86/OptFoldConst.lean` (~320 lines) plus the
one-line `import Grammatik.X86.OptFoldConst` at the end of
`grammatik/Grammatik.lean`. Nothing else touched: no source/checker/Spec/
goal/emitter edits, no friend-reserved optimiser files, no new
diagnostic/gift/example/CLI numbers, no MARKE_EMIT changes.

The DESIGN section 7 row implemented: local premise "operands literal,
width exact, no FP width change, `bruch` = `rundeBruch`", certificate
"local rewrite record plus recomputed analysis citations", failure case
"fold `float` via host `strtod` (double rounding); fold across MXCSR
scope", phase E. Read once: the real `Syntax`/`Semantik`
(`Expr`/`eval`/`execEnd`/`gleitRechne`/`gleitPasst`), `Typen`
(`Zahl`/`bruch`), `Gleitkomma.rundeBruch`, `X86.Typen`/`X86.Wort`,
`ReferenzB` fixture, `CostSummary`/`Budget` (for the budget argument),
IR-VALIDIERUNG export rows (`DutyExport`/`EffectExport`/`AtomicExport`/
`FpExport`/`CostExport`/`LowerMap` — doc-level, no Lean defs exist yet).

### Definitions

- `FoldCert`: validator-decided side conditions
  (`breiteOk`, `keineFPWeite`, `einfachGerundet`, `gleicheRundung` : Bool).
- `foldZulassen : FoldCert → Bool`: conjunction of all four.

### Theorems (exact names)

- `foldVerweigert_strtod`, `foldVerweigert_mxcsr`, `foldVerweigert_weite`:
  each DESIGN failure case forces `foldZulassen = false` (proved of the
  decided Bool).
- `foldAdd_wert`, `foldSub_wert`, `foldMul_wert`, `foldNeg_wert` (total,
  `rfl`); `foldDiv_wert`, `foldRem_wert` (keep the source `M102` premises
  `h0`, `h1'` forwarded unchanged — a zero divisor never reaches a fold).
  All over arbitrary `Int` values; "operands literal" is carried by the
  syntax rewrite, which fires only on `.lit`.
- `foldWort_add`: under validator-decided width-exactness
  (`0 ≤ x + y ∧ x + y < 2^64`) the folded sum reads back whole through the
  canonical `Wort` (no truncation/wrap).
- `foldGleit_behält`: the admitted float fold preserves value and
  `gleitPasst` outcome (same pushed value, same `logik bereich` outcome).
  The validator recomputation obligation is conditional on admission
  (`hEq` takes `hz`), so both premises are used; single `rundeBruch` and
  one rounding scope come from the certificate.
- `OptFoldConst_verbindung` (ZEUGE target): folding `x + y` under an
  `Endblock.bind` window with arbitrary continuation `rest` preserves
  (1) the evaluated value, (2) the `execEnd` outcome (same constructor,
  same successor worlds/environments — hence same faults, same downstream
  contract verdicts at actual values, no new call-log events, no new
  shared accesses for concurrency, unchanged step-budget accounting: same
  block shape, removed computation pure and unbudgeted), (3) the
  width-exact word image. IEEE is covered by `foldGleit_behält` (kernel
  `gleitRechne`, single rounding). No `ensures` derived, no refusal
  weakened, no faulting form speculated above its guard.
- `OptFoldConst_verbindung_zeuge`: joint witness — `3 + 4 → 7` on the
  non-degenerate `refD` (`refEin_schreibt`), beside the reached F-machine
  run `MB` (`refB_erreicht`, `refB_schreibt`: slot `0 -> 100`, memory
  really changes). All premises jointly instantiated and proved.
- Probes (all `decide`/`rfl`-closed kernel computations):
  `probe_foldZulassen_ok/_strtod/_mxcsr`, `probe_foldAdd/_Sub/_Mul/
  _Div/_Rem`, `probe_foldWort`, `probe_foldGleit` (`0.5 + 0.25 = 0.75` in
  one kernel rounding).

## Last build result

- `./lean-probe grammatik/Grammatik/X86/OptFoldConst.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`, no warnings.
- `./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`,
  `Build completed successfully (484 jobs)`.
- `#print axioms` for every theorem: subset of
  `propext, Classical.choice, Quot.sound` (the `gabbro_ziel` standard);
  `probe_foldWort` axiom-free. `gabbro_ziel` itself untouched (no edits on
  its import chain; new file not imported by it).

## What remains open (also in the file's CUTS block)

- No block-window float rewrite: value/`gleitPasst` preservation is proved
  at value level; the two-block `gleitLit`/`gleit` window with recomputed
  avail facts (DESIGN "A+B") stays with the lowering lane.
- No `div`/`rem`/`neg` syntax connection: values fold; only `add` gets the
  `Endblock` connection here.
- No formal `totalCost` inequality: same block shape minus one pure
  computation ⇒ step-budget accounting unchanged; level-(c) machine-work
  bound OPEN per IR-VALIDIERUNG (lane 278).
- No silicon correspondence, TSO/GX bridge, ABI/loader claims.

## What I believe is wrong in the task (minor)

- "Read the single accepted IR" — no accepted IR exists in-tree yet
  (IR287 draft uncommitted); worked from the real `Syntax`/`Semantik`
  fragment as the task allows.
- "TableLayout, CostSummary and the invariant/effect exports" — read, but
  only `Wort`/word-level facts were needed for a layer-A local rewrite;
  layout/cost/duty exports genuinely belong to the layer-B/C certificate
  the validator recomputes, so they are cited, not imported.
- Structuring finding (cost real time): `h ▸ e` casts with a variable
  equality proof block ALL computation (`Eq.rec` stuck), so an
  `assignSlot`-window connection cannot be proved by `rfl`; the cast-free
  `Endblock.bind` window with arbitrary continuation computes through and
  is strictly stronger (covers every downstream observation). Recommend
  this pattern to sibling optimiser lanes.
