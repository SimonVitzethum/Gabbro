module

public import Grammatik.Korpus.Referenz.ReferenzB
public import Grammatik.Bausteine.Arena.ArenaZucker
public import Grammatik.Bausteine.Arena.ArenaDyn.Teil2

@[expose] public section

namespace Gabbro.Grammatik.ArenaDyn

/-- `free`: der Slot wandert auf die Liste -- genau einmal (Doppel-Freigabe
    und Fremd-Slots sind `none`, wie `N586` am Prüfer). -/
def freiFree (F : FreiZustand) (i : Nat) : Option FreiZustand :=
  if h : i < F.belegt ∧ i ∉ F.frei then
    some ⟨F.belegt, i :: F.frei, fun j hj => by
      simp only [List.mem_cons] at hj
      cases hj with
      | inl heq => rw [heq]; exact h.1
      | inr hmem => exact F.hfrei j hmem⟩
  else none

/-- Von der Liste heißt unter der Marke: jeder gereichte Slot ist brauchbar. -/
theorem freiAlloc_unter_marke (F : FreiZustand) :
    (freiAlloc F).1 < (freiAlloc F).2.belegt := by
  cases F with
  | mk belegt frei hfrei =>
    cases frei with
    | nil => simp only [freiAlloc, Nat.lt_add_one]
    | cons i rest => simp only [freiAlloc, List.mem_cons, true_or, hfrei]

/-- Die Marke wächst nie zurück (auch nicht durch Wiederverwendung). -/
theorem freiAlloc_marke_monoton (F : FreiZustand) :
    F.belegt ≤ (freiAlloc F).2.belegt := by
  cases F with
  | mk belegt frei hfrei =>
    cases frei with
    | nil => simp only [freiAlloc, Nat.le_add_right]
    | cons _ _ => simp only [freiAlloc, Std.le_refl]

/-- Freigeben dann nehmen gibt denselben Slot zurück (LIFO-Rundlauf). -/
theorem frei_rundlauf (F : FreiZustand) (i : Nat)
    (h : i < F.belegt) (hn : i ∉ F.frei) (G : FreiZustand)
    (hg : freiFree F i = some G) : (freiAlloc G).1 = i := by
  unfold freiFree at hg
  rw [dif_pos ⟨h, hn⟩] at hg
  cases hg
  simp only [freiAlloc]

/-- Doppel-Freigabe ist eine Abweisung, kein zweites Glied: der Slot steht
    schon an der Spitze, also versagt die Bedingung (`i ∉`) beim zweiten Mal. -/
theorem frei_doppelt_nein (F : FreiZustand) (i : Nat) (G : FreiZustand)
    (hg : freiFree F i = some G) : freiFree G i = none := by
  have hG : G.frei = i :: F.frei := by
    unfold freiFree at hg
    split at hg
    · cases hg
      rfl
    · exact absurd hg (by simp only [reduceCtorEq, not_false_eq_true])
  have hmem : i ∈ G.frei := by
    rw [hG]
    exact List.mem_cons_self
  unfold freiFree
  rw [dif_neg (fun h => h.2 hmem)]

end Gabbro.Grammatik.ArenaDyn
