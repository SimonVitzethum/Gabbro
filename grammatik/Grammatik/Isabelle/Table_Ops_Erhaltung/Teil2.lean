module

public import Grammatik.Isabelle.Table_Ops_Erhaltung.Teil1

@[expose] public section

namespace Gabbro.Grammatik.TableOps
set_option linter.unusedVariables false
variable {Op Z : Type}

theorem wσ_blatt5 : Blatt wσ 5 := by
  intro t tl ht
  by_cases heq : t = 5
  · rw [heq] at ht
    rw [wσ_frisch] at ht
    cases ht
  · have e : wσ t = some ({ elter := none } : Slot) := by
      show (if t = 5 then (none : Option Slot) else some { elter := none }) = _
      rw [if_neg heq]
    rw [e] at ht
    have htl : tl = { elter := none } := (Option.some_inj.mp ht).symm
    rw [htl]
    show (none : Option Nat) ≠ some 5
    decide

/-- Inversion for the witness table: `ueber` collapses to equality --
    relinking can never cycle here. -/
theorem ueber_wσ_inv (x s : Nat) (h : Ueber wσ x s) : x = s := by
  induction h with
  | here _ => rfl
  | hoeher x xl q s hs he _ _ =>
    by_cases hx : x = 5
    · rw [hx] at hs
      rw [wσ_frisch] at hs
      cases hs
    · have e : wσ x = some ({ elter := none } : Slot) := by
        show (if x = 5 then (none : Option Slot) else some { elter := none }) = _
        rw [if_neg hx]
      rw [e] at hs
      have hxl : xl = { elter := none } := (Option.some_inj.mp hs).symm
      rw [hxl] at he
      have he' : (none : Option Nat) = some q := he
      cases he'

theorem wσ_nueber (q : Nat) (hq : q ≠ 5) : ¬ Ueber wσ q 5 := by
  intro h
  have e := ueber_wσ_inv q 5 h
  exact absurd e hq

theorem erreicht_bleibt_bei_frischem_zeuge :
    Erreicht (upd wσ 5 (some ({ elter := none } : Slot))) 0 :=
  erreicht_bleibt_bei_frischem wσ 5 0 _ wσ_frisch wσ_erreicht0

theorem einfuegen_erhaelt_zeuge : Wohlgeformt (Einfuegen wσ 5 0) :=
  einfuegen_erhaelt wσ 5 0 wσ_wohlgeformt wσ_frisch wσ_erreicht0

theorem erreicht_ohne_blatt_zeuge (hne : 0 ≠ 5) :
    Erreicht (upd wσ 5 none) 0 :=
  erreicht_ohne_blatt wσ 5 0 wσ_blatt5 wσ_erreicht0 hne

theorem blatt_loeschen_erhaelt_zeuge : Wohlgeformt (BlattLoeschen wσ 5) :=
  blatt_loeschen_erhaelt wσ 5 wσ_wohlgeformt wσ_blatt5

theorem umhaengen_ausserhalb_zeuge (hnu : ¬ Ueber wσ 0 5) :
    Erreicht (Umhaengen wσ 5 0) 0 :=
  umhaengen_ausserhalb wσ 5 0 0 wσ_erreicht0 hnu

theorem umhaengen_ausserhalb_belegt_zeuge :
    Erreicht (Umhaengen wσ 5 0) 0 :=
  umhaengen_ausserhalb wσ 5 0 0 wσ_erreicht0 (wσ_nueber 0 (by decide))

theorem umhaengen_durch_s_zeuge (hsneu : Erreicht (Umhaengen wσ 5 0) 5) :
    Erreicht (Umhaengen wσ 5 0) 0 :=
  umhaengen_durch_s wσ 5 0 0 wσ_erreicht0 hsneu

theorem umhaengen_erhaelt_zeuge : Wohlgeformt (Umhaengen wσ 5 0) :=
  umhaengen_erhaelt wσ 5 0 wσ_wohlgeformt wσ_erreicht0
    (wσ_nueber 0 (by decide))

theorem umhaengen_erhaelt_am_belegten_platz_zeuge :
    Wohlgeformt (Umhaengen wσ 0 1) :=
  umhaengen_erhaelt_am_belegten_platz wσ 0 1 { elter := none }
    wσ_wohlgeformt wσ_belegt0 wσ_erreicht1
    (fun h => absurd (ueber_wσ_inv 1 0 h) (by decide))

/-- The witness operation: the identity, with the trivial invariant. -/
theorem folge_erhaelt_zeuge :
    (fun _ : Nat => True)
      (laufen (wirkung := fun (_ : Unit) (z : Nat) => z) ([] : List Unit) 0) :=
  folge_erhaelt (wirkung := fun (_ : Unit) (z : Nat) => z)
    (online := fun (_ : Nat → Prop) => True)
    (je := fun (_ : Unit) (I : Nat → Prop) (_ : True) (z : Nat) (h : I z) => h)
    (I := fun (_ : Nat) => True) ([] : List Unit) 0 trivial trivial

theorem erreichbares_erhaelt_zeuge : (fun _ : Nat => True) 0 :=
  erreichbares_erhaelt (wirkung := fun (_ : Unit) (z : Nat) => z)
    (online := fun (_ : Nat → Prop) => True)
    (je := fun (_ : Unit) (I : Nat → Prop) (_ : True) (z : Nat) (h : I z) => h)
    (I := fun (_ : Nat) => True) 0 0 trivial trivial ⟨[], rfl⟩

end Gabbro.Grammatik.TableOps
