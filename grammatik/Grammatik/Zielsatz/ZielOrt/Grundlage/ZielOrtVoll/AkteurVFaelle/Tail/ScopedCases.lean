module

public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVoll.AkteurVFaelle.Tail.Scoped
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtVoll.AkteurVFaelle.Tail.Teil20

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}


theorem akteurV_g7 (hO : GutO O) (hK : ∀ f, KoerperGutV P passes f)
    (hFrag : ∀ f, (P.rumpf f).vOk (kandP P (fussOrte P f)) = true) (e0 : Ereignis D)
    {M M' : RufMaschineG D} {u : Faden}
    (hs : RufSchrittG7 P O passes M u M')
    (hF : FadenV P O passes (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log) :
    FadenV P O passes (M'.faeden u) (M'.weltVon u) ∧ LogOk P (M'.faeden u).log := by
  cases hs with
  | dannVerbrauch l Γ Λ Λ'' t member edge inv bound mass body rest k ρ hhead =>
    exact akteurV_dannVerbrauch (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ'' := Λ'') (t := t) (member := member) (edge := edge) (inv := inv) (bound := bound) (mass := mass) (body := body) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead)
  | verbrauchWeiter l Γ Λ t member edge inv bound mass body rest k ρ hhead σ₁ hs₁ hw σ₂ hs₂ v hv σ₃ hs₃ m hm neu hneu hΛ =>
    exact akteurV_verbrauchWeiter (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (t := t) (member := member) (edge := edge) (inv := inv) (bound := bound) (mass := mass) (body := body) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (σ₂ := σ₂) (hs₂ := hs₂) (v := v) (hv := hv) (σ₃ := σ₃) (hs₃ := hs₃) (m := m) (hm := hm) (neu := neu) (hneu := hneu) (hΛ := hΛ)
  | verbrauchLeer l Γ Λ t member edge inv bound mass body rest k ρ hhead σ₁ hs₁ hw σ₂ hs₂ hleer hkein neu hneu hΛ =>
    exact akteurV_verbrauchLeer (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (t := t) (member := member) (edge := edge) (inv := inv) (bound := bound) (mass := mass) (body := body) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (σ₂ := σ₂) (hs₂ := hs₂) (hleer := hleer) (hkein := hkein) (neu := neu) (hneu := hneu) (hΛ := hΛ)
  | verbrauchFort l Γ Λ t member edge inv bound mass body rest vor k i ρ hhead σ₁ hs₁ m' hm' hfall neu hneu hΛ =>
    exact akteurV_verbrauchFort (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (t := t) (member := member) (edge := edge) (inv := inv) (bound := bound) (mass := mass) (body := body) (rest := rest) (vor := vor) (k := k) (i := i) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (m' := m') (hm' := hm') (hfall := hfall) (neu := neu) (hneu := hneu) (hΛ := hΛ)
  | dannLeaveVerbrauch l Γ Λ t member edge inv bound mass body rest vor k restb i ρ hleave hhead σ' ρ' neu hstep hneu hkein_nimmt σm hsm m' hm' hfall σ₁ hs₁ hw neu₁ hneu₁ hΛ =>
    exact akteurV_dannLeaveVerbrauch (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (t := t) (member := member) (edge := edge) (inv := inv) (bound := bound) (mass := mass) (body := body) (rest := rest) (vor := vor) (k := k) (restb := restb) (i := i) (ρ := ρ) (hleave := hleave) (hhead := hhead) (σ' := σ') (ρ' := ρ') (neu := neu) (hstep := hstep) (hneu := hneu) (hkein_nimmt := hkein_nimmt) (σm := σm) (hsm := hsm) (m' := m') (hm' := hm') (hfall := hfall) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu₁ := neu₁) (hneu₁ := hneu₁) (hΛ := hΛ)
  | dannNextVerbrauch l Γ Λ t member edge inv bound mass body rest vor k restb i ρ hnext hhead σ' ρ' neu hstep hneu hkein_nimmt σm hsm m' hm' hfall neum hneum hΛ =>
    exact akteurV_dannNextVerbrauch (D := D) (P := P) (O := O) (passes := passes) (hO := hO) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (t := t) (member := member) (edge := edge) (inv := inv) (bound := bound) (mass := mass) (body := body) (rest := rest) (vor := vor) (k := k) (restb := restb) (i := i) (ρ := ρ) (hnext := hnext) (hhead := hhead) (σ' := σ') (ρ' := ρ') (neu := neu) (hstep := hstep) (hneu := hneu) (hkein_nimmt := hkein_nimmt) (σm := σm) (hsm := hsm) (m' := m') (hm' := hm') (hfall := hfall) (neum := neum) (hneum := hneum) (hΛ := hΛ)
  | rueckScopedWert ρ r e R hhead hret hscope hΛ σ₁ hs₁ neu hneu hnonempty =>
    subst σ₁
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    exact ⟨fadenV_scopedWert hF ρ r e R hhead hret _, hL⟩
  | rueckScopedGrund ρ r grund R hhead hret hscope hΛ hnonempty =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    exact ⟨fadenV_scopedGrund hF ρ r grund R hhead hret _, hL⟩
  | rueckFreigabe ρ a L remaining hhead hnonempty =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    exact ⟨fadenV_scopedFreigabe hF ρ a L remaining hhead _, hL⟩
  | rueckFreigabeLetzte ρ a L hhead z hantwort =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    have hclean := fadenV_scopedFreigabe hF ρ a L [] hhead ((M.weltVon u).gibt L).spur
    refine fadenV_scopedAntwort hO hK e0 hclean hL ρ _ rfl ?_
    exact (rufAntwortG_rest_irrel (M.faeden u) _ _ _).trans hantwort
  | rueckScopedWertDirekt ρ r e R hhead hret hscope hΛ σ₁ hs₁ neu hneu hempty z hantwort =>
    subst σ₁
    rename_i l Γ Λ
    obtain ⟨scs, hg⟩ := R
    dsimp only at hempty
    subst hempty
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    have hclean := fadenV_scopedWert hF ρ r e _ hhead hret
      ((M.weltVon u).lese Λ e.orte).spur
    refine fadenV_scopedAntwort hO hK e0 hclean hL ρ _ rfl ?_
    exact (rufAntwortG_rest_irrel (M.faeden u) _ _ _).trans hantwort
  | rueckScopedGrundDirekt ρ r grund R hhead hret hscope hΛ hempty z hantwort =>
    rename_i l Γ Λ
    obtain ⟨scs, hg⟩ := R
    dsimp only at hempty
    subst hempty
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    have hclean := fadenV_scopedGrund hF ρ r grund _ hhead hret (M.faeden u).spur
    refine fadenV_scopedAntwort hO hK e0 hclean hL ρ _ rfl ?_
    exact (rufAntwortG_rest_irrel (M.faeden u) _ _ _).trans hantwort

end Gabbro.Grammatik
