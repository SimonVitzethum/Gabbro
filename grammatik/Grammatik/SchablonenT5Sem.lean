/-
  File:      Grammatik/SchablonenT5Sem.lean
  Part of:   Gabbro -- the generator-template library (T5 of
             dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md), the
             SEMANTICS-TIED half.

  What this file is: soundness lemmas for the most-used templates of
  `crates/gabbro-check/src/schablonen.rs`, stated over the project's
  actual semantics -- the declaration `D`, the sequential semantics
  (`eval`, `execStmt` in `Semantik.lean`), the memory (`World`,
  `Ereignis`, `offen`), and the emitter layout (`EmitLay`,
  `EmitLay.trec_count` in `CSpeicher.lean`). Each template's premises
  are the shape the generator emits for a program; each conclusion is
  the obligation the template discharges for that program. Each
  `NAME_zeuge` instantiates the premises on a REAL program (`refD` /
  `refP`) by `decide` / computation, with the conclusion about that
  program's run. Modelled on the `Bewiesen` Isabelle theories in
  `beweise/*.thy`.

  Covered (corpus order): `table.indexschranke`, `table.absenkung`,
  `gruppe.sperrabdruck`, `option.sonderwert`, and the model-facing
  half of `device.konstruktor`. Precisely skipped (no counterpart in
  the Lean model): the layout arithmetic of `device.konstruktor`
  (`World` has no address cells; registers live behind the oracle)
  and `entry.abdruck` (no entry-path syntax, no register file in
  `World`, no preserves/clobbers sets in `Deklaration`).
-/

import Grammatik.ReferenzB
import Grammatik.CSpeicher

namespace Gabbro.Grammatik

/-- A concrete start world over `refD`: both `konto` slots read `0`,
    empty trace. -/
def semW0 : World refD where
  slots := fun _ _ _ => ⟨0, by decide, by decide⟩
  globs := fun g => nomatch g
  spur := []

/-! ## CUTS:
  - Skeleton only: `semW0` is defined; the five tied templates are open.
-/

#print axioms Gabbro.Grammatik.semW0

end Gabbro.Grammatik
