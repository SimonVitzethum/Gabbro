/-
  File:      Grammatik/Isabelle/Absenkung_Parametrisch.lean
  Part of:   Gabbro -- Lean port of `grammatik/Beweise/Absenkung_Parametrisch.thy`
             (the lowering theorem, parametric over the target semantics;
             lane 168).

  What this file is: the finding that "the generated computes the model
  function" is FALSE, at a nameable place. It holds at the OCCUPIED slot
  (`absenkung_am_belegten_platz`) and falls at the free one
  (`absenkung_geht_am_freien_platz_auseinander` -- the model occupies the
  slot, the generated C leaves it free). What holds unconditionally is a
  case split with two branches (`absenkung_relabel`), and what the
  generator claims in prose is the weaker INVARIANT theorem
  (`relabel_erhaelt_wohlgeformt`) -- which holds, for a different reason
  than expected. The two counterexamples (aliasing without E4,
  `option.sonderwert` without E6) live in the weak locale: they satisfy
  E1--E3 and break the theorem.

  Model notes: the locales `zielraum`/`zielsemantik` are Lean structures
  (extends); `abbild` is the same definition (`deutebelegt` returns
  `Bool`, so the condition is `... = true` -- the same proposition).
  The `interpretation` proofs are structure instances (`aliasbruch`,
  `sonderwert_inst`, and the healthy `gesund` for the witnesses).
  Everything else -- `umhaengen`, `wohlgeformt`, `erreicht`, `ueber`,
  `umhaengen_erhaelt` -- is imported from `Table_Ops_Erhaltung`.

  No bridge to the model semantics: the named properties E1--E6 are
  about the C/machine target, which has no counterpart in
  `Semantik.lean` -- that absence is the point of the parametrisation.
-/
module

public import Grammatik.Isabelle.Absenkung_Parametrisch.Teil1
public import Grammatik.Isabelle.Absenkung_Parametrisch.Teil2
