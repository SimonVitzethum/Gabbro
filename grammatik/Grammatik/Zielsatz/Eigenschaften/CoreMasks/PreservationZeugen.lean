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

namespace Gabbro.Grammatik.Zielsatz.KernMaskeFix
open Gabbro.Grammatik

private theorem rankOracle : GutO (wO true) := by intro a; nomatch a
private theorem rankStages : StufenM (wP true) :=
  stufenM_of_ok (stufenOk_ohne (wP true) fun f => by cases f <;> rfl)

/-- Reachable rank preservation with an actually held masking lock. -/
theorem rangInvG_erreichbar_zeuge : ∃ M : RufMaschineG (wD true),
    RufErreichbarG (wP true) (wO true) 0 (wM0 true) M ∧
    RangInvG WFn.t (M.faeden 1) ∧ () ∈ offen (M.faeden 1).spur := by
  obtain ⟨M1, M2, -, -, s1, s2, -, -, hh, -, -, -⟩ := w_prefix true
  have hr : RufErreichbarG (wP true) (wO true) 0 (wM0 true) M2 :=
    .schritt _ _ _ (.schritt _ _ _ .start s1) s2
  refine ⟨M2, hr, ?_, hh⟩
  exact rangInvG_erreichbar rankOracle rankStages (wSp true) (wInit true)
    (fun t => by cases t <;> exact List.nodup_nil) hr 1

end Gabbro.Grammatik.Zielsatz.KernMaskeFix
