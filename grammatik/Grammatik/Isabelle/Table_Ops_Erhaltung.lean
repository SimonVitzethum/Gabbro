/-
  File:      Grammatik/Isabelle/Table_Ops_Erhaltung.lean
  Part of:   Gabbro -- Lean port of `grammatik/Beweise/Table_Ops_Erhaltung.thy`
             (template `table.ops.erhaltung`, S5; lane 168).

  What this file is: the amortisation law (Part I -- once per operation,
  not per call site), THREE concrete generated mutations against the
  concrete invariant of the corpus (Part II -- `insert` needs a fresh
  slot and a reachable parent, `delete_leaf` needs a leaf, `relabel`
  needs the no-cycle condition `¬ über σ p s`), and two boundaries as
  counterexamples (Part III -- relinking falls WITHOUT its condition,
  and a connecting invariant is not covered).

  Model notes: the locale `traeger` is section-free explicit parameters
  (`wirkung`, `online`, and the `je_operation` assumption as an explicit
  premise per lemma -- Isabelle's `assumes` lines). The `slot` record is
  a Lean structure; `erreicht` and `ueber` are Lean inductives with the
  same two constructors each; `wohlgeformt`, `blatt`, the three
  mutations and `zwei` are the same definitions (function update is
  `upd` -- `Function.update` does not exist in this core).

  No bridge to the model semantics: the mutations are hand-defined
  model functions (that the emitted C bodies ARE these functions is not
  proved -- the same boundary as in the theory).
-/
module

public import Grammatik.Isabelle.Table_Ops_Erhaltung.Teil1
public import Grammatik.Isabelle.Table_Ops_Erhaltung.Teil2
