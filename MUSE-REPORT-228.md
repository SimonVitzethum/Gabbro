# MUSE-REPORT-228: match semantics in Lean (exhaustiveness over ranges)

## What was done

New file `grammatik/Grammatik/CFormMatch.lean` (pure Lean, no new
diagnostic codes, no gift/example numbers) plus the import line in
`grammatik/Grammatik.lean`. No other existing file touched.

1. **Denotation** of integer-match arms mirrored from lane 222's
   `IntPat` (`ast.rs`, merged as `99d0e489`): `IArm.exact v`
   (`3 =>`), `IArm.range lo hi false` (`0 .. 255 =>`),
   `IArm.range lo hi true` (`0 ..< 256 =>`), with decidable test
   `trifftB`, Prop denotation `trifft`, and one iff per shape
   (`exact_trifft`, `range_incl_trifft`, `range_excl_trifft`).
2. **Expansion** to emitted case labels: `armKeys` (singleton /
   full enumeration / empty for inverted ranges) with one
   membership correspondence per shape (`mem_armKeys_exact`,
   `mem_armKeys_incl`, `mem_armKeys_excl`), joined by
   `trifft_mem_armKeys`. First-match dispatch `wahl` over the case
   table `fallListe`, with `trifft_wahl_some` (matched dispatches)
   and `wahl_none_weigert` (a miss refuses every arm).
3. **Exhaustiveness** `erschoepfend` (covered exactly over the
   scrutinee's TYPE range, or with an explicit default -- never
   asserted), decidable check `erschoepfendB` with correctness
   `erschoepfendB_richtig`, `erschoepfend_kein_fehlschlag` (no value
   without arm-or-default) and `erschoepfend_ohne_default`.
4. **Soundness against the emitted switch**: `SwDefExec` denotes
   `switch` WITH its default arm at the `Exec` level (`CS.sw` has no
   `default` constructor); `swDef_hit` / `swDef_miss` build each
   outcome, and `exec_sw_hit` / `exec_sw_miss` show each half IS
   `Exec (.sw …)` (`Exec.swHit` / `Exec.swMiss`).
5. **Witness** `match_exhaustive_zeuge` on the reference fixture:
   arms `[0 .. 99, 100]` over the table-driven scrutinee
   `matchLeser` (`konto[0]`, type `.int 0 100`), dispatched at `0`
   (range arm, start world) and at `100` (exact arm, post-write
   world), jointly with the reached F run `refB_erreicht` and the
   memory move `refB_schreibt` (`konto[0]`: `0 -> 100`).
   Non-degenerate: `konto` written by `einzahlen`, four reached
   steps including the writing leaf.

## Verification

- `./lean-probe grammatik/Grammatik/CFormMatch.lean`: 0 errors.
- `./lean-bau`: exit 0, "Build completed successfully (278 jobs)",
  0 error lines; `CFormMatch.olean` built as a dependency.
- `#print axioms`: every theorem within the standard three
  (`propext`, `Classical.choice`, `Quot.sound`) or a subset; the
  witness has exactly the three. No `sorry`/`admit`/`axiom`/
  `native_decide`/`unsafe` anywhere.
- Planted-defect check: mutating `matchArme` to drop the `100` arm
  (scratch copy, reverted) goes red with 3 errors -- `decide`
  refutes the coverage, both post-write dispatches fail.
- Rule-13 posture: no theorem quantifies over program syntax
  (`Vertrag`/`Stmt`/`Endblock`/`ErgExpr`/`Expr`/`Args`) in a premise;
  all premises are over `Int`, `IArm`, `CX`/`CS`/values, and every
  premise is used. The ZEUGE target is the joint existential itself.

## What remains open / what I believe is wrong or risky

- **Lane 227 is unmerged**, so the expansion shape (one `case`
  label per covered value + `default:`) is this lane's denotation of
  the task's "including the default arm", not a measured lowering.
  If 227 keeps ranges as ranges (nested `if`s) or shares bodies,
  `fallListe` needs a body map; denotation and exhaustiveness stand.
  Recorded in the file's CUTS.
- **No Gabbro `Stmt` for integer match exists** (`Syntax.lean` has
  only `onOption`/`onTag`/`onGrund`), so the correspondence is at
  the scrutinee-value level, not a `StmtCorr`. Weaker than a full
  statement correspondence -- said plainly per rule 4.
- `pruefe-cformen.py` has no integer-switch row yet (only
  `switch-reason`/`switch-tag`); there was nothing to flip. Lane 227
  will add the row naming this file's lemmas.

## Names of new definitions/theorems

`IArm`, `trifftB`, `trifft`, `exact_trifft`,
`range_incl_trifft`, `range_excl_trifft`, `aufzaehlung`,
`mem_aufzaehlung`, `armKeys`, `mem_armKeys_exact`,
`mem_armKeys_incl`, `mem_armKeys_excl`, `trifft_mem_armKeys`,
`fallListeAux`, `fallListe`, `wahl`, `lookup_mem_isSome`,
`mem_fallListeAux_of`, `trifft_wahl_some`, `wahl_none_weigert`,
`IntMatch`, `erschoepfend`, `werteListe`, `mem_werteListe`,
`erschoepfendB`, `erschoepfendB_richtig`,
`erschoepfend_kein_fehlschlag`, `erschoepfend_ohne_default`,
`SwDefExec`, `swDef_hit`, `swDef_miss`, `exec_sw_hit`,
`exec_sw_miss`, `matchArme`, `matchM`, `matchLeser`,
`matchLeser_start`, `matchLeser_nach`, `match_erschoepfend`,
`match_wahl_vor`, `match_wahl_nach`, `match_luecke_zeigt`,
`match_nicht_erschoepfend`, `match_exhaustive_zeuge`.
