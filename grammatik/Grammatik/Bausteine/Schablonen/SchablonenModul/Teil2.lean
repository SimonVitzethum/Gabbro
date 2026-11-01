module

public import Grammatik.Bausteine.Schablonen.SchablonenModul.Teil1

@[expose] public section

namespace Gabbro.Grammatik
namespace ModulLaufzeit

theorem faden_modul_zeuge :
    fwort 0 ((fSpur true 5).take 8) = 0 ∧ (fSpur true 5).take 8 = fSpur true 5 ∧
    fwort 0 ((fSpur true 5).take 4) = 1 ∧
    fwort 0 ((fSpur false 0).take 3) = 0 ∧ FEreignis.lauf ∉ fSpur false 0 := by
  refine ⟨by decide, ?_, by decide, by decide, by decide⟩
  rcases faden_modul_warte_korrekt true 5 0 8 (by decide) (by decide) with ⟨-, h⟩ | ⟨h, -⟩
  · exact h
  · exact absurd h (by decide)

end ModulLaufzeit

end Gabbro.Grammatik
