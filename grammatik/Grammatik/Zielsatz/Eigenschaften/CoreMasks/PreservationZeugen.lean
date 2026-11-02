module

public import Grammatik.Zielsatz.Eigenschaften.CoreMasks.KernMaskeZeuge

@[expose] public section

namespace Gabbro.Grammatik.Zielsatz.KernMaskeFix
open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz

/-- Preservation on two actual steps of the masking-lock fixture. The final
    state holds the lock and has a nonempty mask on core zero. -/
theorem maskeOk_schritt_zeuge : ∃ M1 M2 : RufMaschineG (wD true),
    RufSchrittG (wP true) (wO true) 0 (wZ0 true).m 1 M1 ∧
    RufSchrittG (wP true) (wO true) 0 M1 1 M2 ∧
    MaskeOk wk M2 (((wZ0 true).weiter wk 1 M1).weiter wk 1 M2).mask ∧
    () ∈ offen (M2.faeden 1).spur ∧
    (((wZ0 true).weiter wk 1 M1).weiter wk 1 M2).mask 0 ≠ [] := by
  obtain ⟨M1, M2, -, -, s1, s2, -, -, hh2, -, -, -⟩ := w_prefix true
  have hok : MaskeOk wk M2 (((wZ0 true).weiter wk 1 M1).weiter wk 1 M2).mask :=
    maskeOk_schritt s2 (maskeOk_schritt s1 (wStart true).2.1)
  exact ⟨M1, M2, s1, s2, hok, hh2,
    (maske_nichtleer_iff hok 0).2 ⟨1, (), rfl, rfl, hh2⟩⟩

end Gabbro.Grammatik.Zielsatz.KernMaskeFix
