module

public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtAx.AkteurAFaelle.Tail.Teil20

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D}


/-- The group-seven actor cases use one saved answer through cleanup and delivery. -/
theorem akteurA_gruppe7 (hO : GutO O) (hQ : AxVertragO Q O) (hK : ∀ f, KoerperGutA P passes Q f) (hlok : AxEnsLokal Q)
    (hFrag : ∀ f, (P.rumpf f).vOk (kandP P (fussOrte P f)) = true) (e0 : Ereignis D)
    {M M' : RufMaschineG D} {u : Faden}
    (hs : RufSchrittG7 P O passes M u M')
    (hF : FadenA P O passes Q (M.faeden u) (M.weltVon u))
    (hL : LogOk P (M.faeden u).log) :
    FadenA P O passes Q (M'.faeden u) (M'.weltVon u) ∧ LogOk P (M'.faeden u).log := by
  cases hs with
  | dannVerbrauch l Γ Λ Λ'' t member edge inv bound mass body rest k ρ hhead =>
    exact akteurA_dannVerbrauch (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (Λ'' := Λ'') (t := t) (member := member) (edge := edge) (inv := inv) (bound := bound) (mass := mass) (body := body) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead)
  | verbrauchWeiter l Γ Λ t member edge inv bound mass body rest k ρ hhead σ₁ hs₁ hw σ₂ hs₂ v hv σ₃ hs₃ m hm neu hneu hΛ =>
    exact akteurA_verbrauchWeiter (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (t := t) (member := member) (edge := edge) (inv := inv) (bound := bound) (mass := mass) (body := body) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (σ₂ := σ₂) (hs₂ := hs₂) (v := v) (hv := hv) (σ₃ := σ₃) (hs₃ := hs₃) (m := m) (hm := hm) (neu := neu) (hneu := hneu) (hΛ := hΛ)
  | verbrauchLeer l Γ Λ t member edge inv bound mass body rest k ρ hhead σ₁ hs₁ hw σ₂ hs₂ hleer hkein neu hneu hΛ =>
    exact akteurA_verbrauchLeer (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (t := t) (member := member) (edge := edge) (inv := inv) (bound := bound) (mass := mass) (body := body) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (σ₂ := σ₂) (hs₂ := hs₂) (hleer := hleer) (hkein := hkein) (neu := neu) (hneu := hneu) (hΛ := hΛ)
  | verbrauchFort l Γ Λ t member edge inv bound mass body rest vor k i ρ hhead σ₁ hs₁ m' hm' hfall neu hneu hΛ =>
    exact akteurA_verbrauchFort (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (t := t) (member := member) (edge := edge) (inv := inv) (bound := bound) (mass := mass) (body := body) (rest := rest) (vor := vor) (k := k) (i := i) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (m' := m') (hm' := hm') (hfall := hfall) (neu := neu) (hneu := hneu) (hΛ := hΛ)
  | dannLeaveVerbrauch l Γ Λ t member edge inv bound mass body rest vor k restb i ρ hleave hhead σ' ρ' neu hstep hneu hkein_nimmt σm hsm m' hm' hfall σ₁ hs₁ hw neu₁ hneu₁ hΛ =>
    exact akteurA_dannLeaveVerbrauch (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (t := t) (member := member) (edge := edge) (inv := inv) (bound := bound) (mass := mass) (body := body) (rest := rest) (vor := vor) (k := k) (restb := restb) (i := i) (ρ := ρ) (hleave := hleave) (hhead := hhead) (σ' := σ') (ρ' := ρ') (neu := neu) (hstep := hstep) (hneu := hneu) (hkein_nimmt := hkein_nimmt) (σm := σm) (hsm := hsm) (m' := m') (hm' := hm') (hfall := hfall) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (neu₁ := neu₁) (hneu₁ := hneu₁) (hΛ := hΛ)
  | dannNextVerbrauch l Γ Λ t member edge inv bound mass body rest vor k restb i ρ hnext hhead σ' ρ' neu hstep hneu hkein_nimmt σm hsm m' hm' hfall neum hneum hΛ =>
    exact akteurA_dannNextVerbrauch (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (hO := hO) (hQ := hQ) (hlok := hlok) (hK := hK) (hFrag := hFrag) (e0 := e0) (M := M) (u := u) (hF := hF) (hL := hL) (l := l) (Γ := Γ) (Λ := Λ) (t := t) (member := member) (edge := edge) (inv := inv) (bound := bound) (mass := mass) (body := body) (rest := rest) (vor := vor) (k := k) (restb := restb) (i := i) (ρ := ρ) (hnext := hnext) (hhead := hhead) (σ' := σ') (ρ' := ρ') (neu := neu) (hstep := hstep) (hneu := hneu) (hkein_nimmt := hkein_nimmt) (σm := σm) (hsm := hsm) (m' := m') (hm' := hm') (hfall := hfall) (neum := neum) (hneum := hneum) (hΛ := hΛ)
  | rueckScopedWert ρ r e R hhead hret hscope hΛ σ₁ hs₁ neu hneu hnonempty =>
      rename_i l Γ Λ
      simp only [RufMaschineG.weltVon, rufUpdateG_self]
      refine ⟨fadenA_lokal hF hhead ρ (.aufraeumen ⟨.inl (evalErg σ₁ e σ₁ ρ), σ₁⟩ R.scopes)
        σ₁.spur (fun σ hg hok => ?_), hL⟩
      subst σ₁
      have hv := evalErg_gleichAuf e (fun _ h => scopedWert_orteV hok hret h)
        (hg.lese Λ Λ e.orte e.orte) ρ
      refine ⟨σ.lese Λ e.orte, lese_laenge σ Λ e.orte, hg, trivial, fun calls O' => ?_⟩
      apply ZErg.folgt_of_gleich
      refine ZErg.gleich_trans (semV_scopedWert O' passes calls r e R hret σ ρ) ?_
      have hmem := World.gibt_foldl_speicher (σ.lese Λ e.orte) R.scopes
      exact ⟨⟨hmem.1.symm, hmem.2.symm⟩, hv⟩
  | rueckScopedGrund ρ r grund R hhead hret hscope hΛ hnonempty =>
      simp only [RufMaschineG.weltVon, rufUpdateG_self]
      refine ⟨fadenA_lokal hF hhead ρ (.aufraeumen ⟨.inr grund, M.weltVon u⟩ R.scopes)
        (M.faeden u).spur (fun σ hg hok => ?_), hL⟩
      exact ⟨σ, Nat.le_refl _, hg, trivial, fun calls O' =>
        ZErg.folgt_of_eq (semV_scopedGrund O' passes calls r grund R hret σ ρ)⟩
  | rueckFreigabe ρ a L remaining hhead hnonempty =>
      simp only [RufMaschineG.weltVon, rufUpdateG_self]
      refine ⟨fadenA_lokal hF hhead ρ (.aufraeumen a remaining)
        (.gibt L :: (M.faeden u).spur) (fun σ hg hok => ?_), hL⟩
      exact ⟨σ.gibt L, World.rang_le_gibt σ L, hg, trivial, fun calls O' => ZErg.folgt_refl _⟩
  | rueckFreigabeLetzte ρ a L hhead z ha =>
      simp only [RufMaschineG.weltVon, rufUpdateG_self, rufAntwortG_spur ha]
      have hdone := fadenA_lokal hF hhead (M.faeden u).kopf.rho
        (.zurueckgekehrt a : GRest D _ false _ _)
        (.gibt L :: (M.faeden u).spur) (W' := (M.weltVon u).gibt L) (fun σ hg hok => by
          refine ⟨σ.gibt L, World.rang_le_gibt σ L, hg, trivial, fun calls O' => ?_⟩
          cases a.1 <;> exact ZErg.folgt_refl _)
      refine fadenA_antwort hO hQ hK e0 _ hdone hL rfl ?_
      exact (rufAntwortG_rest_irrel (M.faeden u) _ _ _).trans ha
  | rueckScopedWertDirekt ρ r e R hhead hret hscope hΛ σ₁ hs₁ neu hneu hempty z ha =>
      rename_i l Γ Λ
      simp only [RufMaschineG.weltVon, rufUpdateG_self, rufAntwortG_spur ha]
      have hdone := fadenA_lokal hF hhead (M.faeden u).kopf.rho
        (.zurueckgekehrt ⟨.inl (evalErg σ₁ e σ₁ ρ), σ₁⟩ : GRest D _ false _ _)
        σ₁.spur (W' := σ₁) (fun σ hg hok => by
          have hgl : GleichAuf (fussOrte P (M.faeden u).kopf.f) (σ.lese Λ e.orte) σ₁ := by
            rw [hs₁]
            exact hg.lese Λ Λ e.orte e.orte
          have hv := evalErg_gleichAuf e (fun _ h => scopedWert_orteV hok hret h) hgl ρ
          refine ⟨σ.lese Λ e.orte, lese_laenge σ Λ e.orte, hgl, trivial, fun calls O' => ?_⟩
          exact ZErg.folgt_of_gleich (ZErg.gleich_trans
            (semV_scopedWert O' passes calls r e R hret σ ρ) ⟨⟨rfl, rfl⟩, hv⟩))
      have hres := fadenA_antwort hO hQ hK e0 _ hdone hL rfl
        ((rufAntwortG_rest_irrel (M.faeden u) _ _ _).trans ha)
      have hw : M.speicher.welt σ₁.spur = σ₁ := by
        subst hs₁
        exact Speicher.welt_speicher ((M.weltVon u).lese Λ e.orte)
      simpa only [hw] using hres
  | rueckScopedGrundDirekt ρ r grund R hhead hret hscope hΛ hempty z ha =>
      simp only [RufMaschineG.weltVon, rufUpdateG_self, rufAntwortG_spur ha]
      have hdone := fadenA_lokal hF hhead (M.faeden u).kopf.rho
        (.zurueckgekehrt ⟨.inr grund, M.weltVon u⟩ : GRest D _ false _ _)
        (M.faeden u).spur (W' := M.weltVon u) (fun σ hg hok => by
          exact ⟨σ, Nat.le_refl _, hg, trivial, fun calls O' =>
            ZErg.folgt_of_eq (semV_scopedGrund O' passes calls r grund R hret σ ρ)⟩)
      refine fadenA_antwort hO hQ hK e0 _ hdone hL rfl ?_
      exact (rufAntwortG_rest_irrel (M.faeden u) _ _ _).trans ha

end Gabbro.Grammatik
