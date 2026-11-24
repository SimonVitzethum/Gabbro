module

public import Core.Beobachtung.SchrankenB8Aussagen

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine

/-- A freshly opened `rumpf` mark meets its bound: start and cut coincide, so the clock
    difference is zero and every declared bound is satisfied by `Nat.zero_le`. -/
theorem zeitRumpfNeu : zeitRumpfNeuAussage := by
  intro max d anfang cut clock kosten eq
  rw [← eq]
  simp only [ZeitInSchranken]
  refine ⟨Nat.le_refl anfang, Nat.le_refl (clock anfang), ?_⟩
  intro n _ _
  rw [Nat.sub_self]
  exact Nat.zero_le n

/-- A decided in-time check stays valid when the cut moves out: the checked instant is fixed,
    so only the order premises need extending by transitivity. -/
theorem zeitRechtzeitigErweitern : zeitRechtzeitigErweiternAussage := by
  intro max d geprueft anfang cut cut' clock kosten h cutLe cutClockLe
  simp only [ZeitInSchranken] at h ⊢
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  exact ⟨le_trans h1 cutLe, le_trans h2 cutClockLe, h3, le_trans h4 cutLe, h5,
    le_trans h6 cutClockLe, h7, h8⟩

/-- A decided late check stays valid when the cut moves out: same shape as the in-time case;
    the fallback cost premise is untouched because the check instant does not move. -/
theorem zeitSpaetErweitern : zeitSpaetErweiternAussage := by
  intro max d geprueft anfang cut cut' clock kosten h cutLe cutClockLe
  simp only [ZeitInSchranken] at h ⊢
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact ⟨le_trans h1 cutLe, le_trans h2 cutClockLe, h3, le_trans h4 cutLe, h5,
    le_trans h6 cutClockLe, h7, h8, h9⟩

end Gabbro.Core.Beobachtung
