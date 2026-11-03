module

public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.RennfreiOrte.T2a

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- The event bound for group 7, including its complete cleanup trace. -/
theorem schritt_ev_g7 {P : Programm D} {O : Orakel D} {passes : Nat} (hO : GutO O)
    {M M' : RufMaschineG D} {f : Faden} (hs : RufSchrittG7 P O passes M f M')
    {C : D.Tab ⊕ D.Glob → Bool} (hC : (M.faeden f).kopf.rest.2.2.2.2.oR P C) :
    ∃ X, (M'.faeden f).spur = X ++ (M.faeden f).spur ∧
      EvOk C (TraegerSchreibt (M.faeden f).kopf.f) X := by
  have hW : ∀ c, schreibV (vertragVon D (M.faeden f).kopf.f) c =
      TraegerSchreibt (M.faeden f).kopf.f c := schreibV_vertragVon _
  cases hs with
  | dannVerbrauch => leseO
  | verbrauchWeiter l Γ Λ t member edge inv bound mass body rest k ρ hhead
      σ₁ hs₁ hw σ₂ hs₂ v hv σ₃ hs₃ m hm neu hneu hΛ =>
      simp only [rufUpdateG_self]
      rw [hhead] at hC
      simp only [GRest.oR] at hC
      refine ⟨leseEv σ₂ Λ mass.orte ++
        (leseEv σ₁ Λ (member.orte ++ edge.orte) ++ leseEv (M.weltVon f) Λ inv.orte), ?_,
        evOk_append (evOk_lese _ _ hC.2.2.2.1)
          (evOk_append (evOk_lese _ _ (by
            simp only [List.all_append, Bool.and_eq_true]; exact ⟨hC.1, hC.2.1⟩))
            (evOk_lese _ _ hC.2.2.1))⟩
      simp only [hs₃, hs₂, hs₁, lese_spur, List.append_assoc] <;> rfl
  | verbrauchLeer l Γ Λ t member edge inv bound mass body rest k ρ hhead
      σ₁ hs₁ hw σ₂ hs₂ hleer hkein neu hneu hΛ =>
      simp only [rufUpdateG_self]
      rw [hhead] at hC
      simp only [GRest.oR] at hC
      refine ⟨leseEv σ₁ Λ (member.orte ++ edge.orte) ++ leseEv (M.weltVon f) Λ inv.orte, ?_,
        evOk_append (evOk_lese _ _ (by
          simp only [List.all_append, Bool.and_eq_true]; exact ⟨hC.1, hC.2.1⟩))
          (evOk_lese _ _ hC.2.2.1)⟩
      simp only [hs₂, hs₁, lese_spur, List.append_assoc] <;> rfl
  | verbrauchFort l Γ Λ t member edge inv bound mass body rest vor k i ρ hhead
      σ₁ hs₁ m' hm' hfall neu hneu hΛ =>
      simp only [rufUpdateG_self]
      rw [hhead] at hC
      simp only [GRest.oR] at hC
      subst hs₁
      exact ⟨leseEv _ _ _, rfl, evOk_lese _ _ hC.2.2.2.1⟩
  | dannLeaveVerbrauch l Γ Λ t member edge inv bound mass body rest vor k restb i ρ
      hleave hhead σ' ρ' neu hstep hneu hkein σm hsm m' hm' hfall σ₁ hs₁ hw
      neu₁ hneu₁ hΛ =>
      simp only [rufUpdateG_self]
      rw [hhead] at hC
      simp only [GRest.oR] at hC
      refine ⟨leseEv σm Λ inv.orte ++ leseEv σ' Λ mass.orte, ?_,
        evOk_append (evOk_lese _ _ hC.2.2.2.1) (evOk_lese _ _ hC.2.2.2.2.1)⟩
      simp only [hs₁, hsm, lese_spur, List.append_assoc,
        leave_welt' _ _ _ _ _ _ _ _ hstep] <;> rfl
  | dannNextVerbrauch l Γ Λ t member edge inv bound mass body rest vor k restb i ρ
      hnext hhead σ' ρ' neu hstep hneu hkein σm hsm m' hm' hfall neum hneum hΛ =>
      simp only [rufUpdateG_self]
      rw [hhead] at hC
      simp only [GRest.oR] at hC
      rw [hsm, next_welt' _ _ _ _ _ _ _ _ hstep]
      exact ⟨leseEv _ _ _, rfl, evOk_lese _ _ hC.2.2.2.2.1⟩
  | rueckScopedWert ρ r e R hhead hret hscope hΛ σ₁ σ₂ hs₁ hs₂ neu hneu z hantwort =>
      simp only [rufUpdateG_self, rufAntwortG_spur hantwort]
      subst hs₂ hs₁
      rw [hhead] at hC
      obtain ⟨X, hX, hok⟩ := blatt_ev P O passes keinRuf hO C (.retScoped e R) rfl
        (GRest.scopedWert_oR hC hret) (M.weltVon f) ρ hΛ _ rfl
      exact ⟨X, hX, fun ev he c w hz => by rw [← hW]; exact hok ev he c w hz⟩
  | rueckScopedGrund ρ r grund R hhead hret hscope hΛ σ₂ hs₂ neu hneu z hantwort =>
      simp only [rufUpdateG_self, rufAntwortG_spur hantwort]
      subst hs₂
      obtain ⟨X, hX, hok⟩ := blatt_ev P O passes keinRuf hO C (.retWhyScoped grund R) rfl
        rfl (M.weltVon f) ρ hΛ _ rfl
      exact ⟨X, hX, fun ev he c w hz => by rw [← hW]; exact hok ev he c w hz⟩

end Gabbro.Grammatik
