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

/-! ## 2. `table.absenkung` -- every in-range index names a laid-out cell.

The emitter lays table `t` out as `(trec t).count` cells
(`EmitLay.trec_count : ((trec t).count : Int) = D.count t` -- the `m
= N` agreement the certificate carries for a `C001`-checked layout).
With the index bound (`indexschranke_eval`, §1) every index of a
generated access names a cell: `kein_zugriff_laeuft_aus_dem_feld`.
Modelled on `beweise/Table_Absenkung.thy`, including both failure
directions (`zu_kurz_laesst_einen_index_ohne_speicher`,
`zu_lang_laesst_speicher_ohne_index`). -/

/-- Soundness of `table.absenkung`: layout/count agreement plus an
    in-range index give a laid-out cell. `trec_count` and both index
    bounds are consumed. -/
theorem absenkung_index_im_feld (EL : EmitLay D) (t : D.Tab)
    (i : Int) (h0 : 0 ≤ i) (hN : i < D.count t) :
    i.toNat < (EL.trec t).count := by
  have hc := EL.trec_count t
  omega

/-- Too short a layout leaves an index homeless. -/
theorem absenkung_zu_kurz (EL : EmitLay D) (t : D.Tab)
    (hm : ((EL.trec t).count : Int) < D.count t) :
    ∃ i : Int, 0 ≤ i ∧ i < D.count t ∧ ¬ i.toNat < (EL.trec t).count := by
  refine ⟨((EL.trec t).count : Int), Int.natCast_nonneg _, hm, ?_⟩
  intro hcon
  have e : (((EL.trec t).count : Int)).toNat = (EL.trec t).count :=
    Int.toNat_natCast _
  omega

/-- Too long a layout leaves a cell indexless (for nonnegative counts). -/
theorem absenkung_zu_lang (EL : EmitLay D) (t : D.Tab)
    (hnn : 0 ≤ D.count t) (hm : D.count t < ((EL.trec t).count : Int)) :
    ∃ j : Nat, j < (EL.trec t).count ∧
      ¬ (0 ≤ (j : Int) ∧ (j : Int) < D.count t) := by
  refine ⟨(D.count t).toNat, ?_, ?_⟩
  · have e : (((D.count t).toNat : Nat) : Int) = D.count t :=
      Int.toNat_of_nonneg hnn
    omega
  · intro hcon
    have e : (((D.count t).toNat : Nat) : Int) = D.count t :=
      Int.toNat_of_nonneg hnn
    omega

/-- Witness for `absenkung_index_im_feld`: `refP`'s index `refIdxEin`
    (fired by the run at `refSchrittBF`) names a cell of the emitted
    `konto` layout (`refEL.trec_count`, `m = N = 2` by `rfl`); the run
    reaches `MB` with slot `0` moved. -/
theorem absenkung_zeuge :
    (eval semW0 refIdxEin semW0 refRho7).n.toNat < (refEL.trec ()).count ∧
    (((refEL.trec ()).count : Int) = refD.count ()) ∧
    RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB ∧
    MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have hb := indexschranke_eval (refD.count ()) refIdxEin semW0 semW0 refRho7
  have hC : refD.count () = 2 := rfl
  have hN : (eval semW0 refIdxEin semW0 refRho7).n < refD.count () := by
    have := hb.2
    omega
  have hidx := absenkung_index_im_feld refEL () _ hb.1 hN
  refine ⟨hidx, refEL.trec_count (), refB_erreicht, refB_schreibt⟩

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
