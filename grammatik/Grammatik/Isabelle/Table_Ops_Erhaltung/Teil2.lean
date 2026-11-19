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

end Gabbro.Grammatik.TableOps
