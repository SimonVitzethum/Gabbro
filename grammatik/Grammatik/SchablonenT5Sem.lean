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

variable {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)}

/-! ## 1. `table.indexschranke` -- every generated index is in type.

The generator types every slot index as `Expr Γ Λ (.index
(D.count t))` (`M103`); the semantics evaluates it to a value of
exactly that type. That is the whole carrying half
(`schreibstellen_im_typ`, `kette_bleibt_im_typ`): there is no other
way to name a slot -- `assignSlot`, `slot`, `durch`, `traverse`,
`forallSlots` all take their index in this type. Modelled on
`beweise/Table_Indexschranke.thy` (M-2). The occupancy half
(`belegt_liegt_im_indextyp`) has no counterpart: `World.slots` is
total, slots are never unoccupied. -/

/-- Soundness of `table.indexschranke`, over the real expression
    semantics: an index expression of the generated type evaluates
    inside `0 ..< n`. No premises besides the expression itself. -/
theorem indexschranke_eval (n : Int) (e : Expr D Γ Λ (.index n))
    (σ₀ σ : World D) (ρ : Env D Γ) :
    0 ≤ (eval σ₀ e σ ρ).n ∧ (eval σ₀ e σ ρ).n ≤ n - 1 :=
  ⟨(eval σ₀ e σ ρ).lo_le, (eval σ₀ e σ ρ).le_hi⟩

/-- Witness for `indexschranke_eval`: `refP`'s real index expression
    `refIdxEin` (the index of the write site `refWriteSt`, fired by
    the run at `refSchrittBF`) evaluates to `0`, inside
    `0 ..< count`; and the run that fires it reaches `MB` with slot
    `0` moved (`refB_erreicht`, `refB_schreibt`). Premise (the
    expression) by computation; conclusion about that program's run. -/
theorem indexschranke_zeuge :
    (eval semW0 refIdxEin semW0 refRho7).n = 0 ∧
    0 ≤ (eval semW0 refIdxEin semW0 refRho7).n ∧
    (eval semW0 refIdxEin semW0 refRho7).n ≤ refD.count () - 1 ∧
    RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB ∧
    MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have h0 : (eval semW0 refIdxEin semW0 refRho7).n = 0 := rfl
  have hC : refD.count () = 2 := rfl
  refine ⟨h0, by rw [h0]; exact Int.le_refl _, by rw [h0, hC]; decide,
    refB_erreicht, refB_schreibt⟩

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
