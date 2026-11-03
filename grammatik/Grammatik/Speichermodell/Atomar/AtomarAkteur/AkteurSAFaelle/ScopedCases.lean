module

public import Grammatik.Speichermodell.Atomar.AtomarAkteur.AkteurSAFaelle.Scoped
public import Grammatik.Speichermodell.Atomar.AtomarAkteur.AkteurSAFaelle.B.Teil19

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration} {P : Programm D} {O : Orakel D} {passes : Nat}
variable {Q : AxEns D} {S : SperrInv D}

theorem akteurSA_g7 (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O) (hlok : AxEnsLokal Q)
    (hS : SperrInvOk S) {sp : Speicher D} (hsp : ∀ L, S.inv L sp = true)
    (hK : ∀ f, KoerperGutSA P passes Q S Tg f) (hM : ∀ f, MassPflicht P passes Q S Tg m zyk f)
    (hTV : ∀ c, Tg c → VertragsFrei P c)
    (hFragS : ∀ f, (P.rumpf f).gOk (kandP P (fussOrteG P f)) (regP (sicher P lok f)) = true)
    (hFS : ∀ f, FussSX P S lok Tg f)
    {M M' : RufMaschineG D} {u : Faden}
    (hs : RufSchrittG7 P O passes M u M')
    (hF : FadenSA P O passes Q S lok Tg m zyk (M.faeden u) (M.weltVon u)) (hL : LogOk P (M.faeden u).log)
    (hRS : RahmenStapelS P S lok M.speicher (RufSchluesselG (M.faeden u).kopf) (M.faeden u).stapel)
    (hSG : SperrInvG S M) :
    FadenSA P O passes Q S lok Tg m zyk (M'.faeden u) (M'.weltVon u) ∧ LogOk P (M'.faeden u).log := by
  cases hs with
  | dannVerbrauch l Γ Λ Λ'' t member edge inv bound mass body rest k ρ hhead =>
    exact akteurSA_dannVerbrauch (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (Λ'' := Λ'') (t := t) (member := member) (edge := edge) (inv := inv) (bound := bound) (mass := mass) (body := body) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead)
  | verbrauchWeiter l Γ Λ t member edge inv bound mass body rest k ρ hhead σ₁ hs₁ hw σ₂ hs₂ v hv σ₃ hs₃ mr hm neu hneu hΛ =>
    exact akteurSA_verbrauchWeiter (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (t := t) (member := member) (edge := edge) (inv := inv) (bound := bound) (mass := mass) (body := body) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (σ₂ := σ₂) (hs₂ := hs₂) (v := v) (hv := hv) (σ₃ := σ₃) (hs₃ := hs₃) (mr := mr) (hm := hm) (neu := neu) (hneu := hneu) (hΛ := hΛ)
  | verbrauchLeer l Γ Λ t member edge inv bound mass body rest k ρ hhead σ₁ hs₁ hw σ₂ hs₂ hleer hkein neu hneu hΛ =>
    exact akteurSA_verbrauchLeer (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (t := t) (member := member) (edge := edge) (inv := inv) (bound := bound) (mass := mass) (body := body) (rest := rest) (k := k) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (hw := hw) (σ₂ := σ₂) (hs₂ := hs₂) (hleer := hleer) (hkein := hkein) (neu := neu) (hneu := hneu) (hΛ := hΛ)
  | verbrauchFort l Γ Λ t member edge inv bound mass body rest vor k i ρ hhead σ₁ hs₁ m' hm' hfall neu hneu hΛ =>
    exact akteurSA_verbrauchFort (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (t := t) (member := member) (edge := edge) (inv := inv) (bound := bound) (mass := mass) (body := body) (rest := rest) (vor := vor) (k := k) (i := i) (ρ := ρ) (hhead := hhead) (σ₁ := σ₁) (hs₁ := hs₁) (m' := m') (hm' := hm') (hfall := hfall) (neu := neu) (hneu := hneu) (hΛ := hΛ)
  | dannLeaveVerbrauch l Γ Λ t member edge inv bound mass body rest vor k restb i ρ hleave hhead σ' ρ' neu hstep hneu hkein_nimmt σm hsm m' hm' hfall σ₁ hs₁ hw neu₁ hneu₁ hΛ =>
    subst hs₁
    exact akteurSA_dannLeaveVerbrauch (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (t := t) (member := member) (edge := edge) (inv := inv) (bound := bound) (mass := mass) (body := body) (rest := rest) (vor := vor) (k := k) (restb := restb) (i := i) (ρ := ρ) (hleave := hleave) (hhead := hhead) (σ' := σ') (ρ' := ρ') (neu := neu) (hstep := hstep) (hneu := hneu) (hkein_nimmt := hkein_nimmt) (σm := σm) (hsm := hsm) (m' := m') (hm' := hm') (hfall := hfall) (σ₁ := σm.lese Λ inv.orte) (hs₁ := rfl) (hw := hw) (neu₁ := neu₁) (hneu₁ := hneu₁) (hΛ := hΛ)
  | dannNextVerbrauch l Γ Λ t member edge inv bound mass body rest vor k restb i ρ hnext hhead σ' ρ' neu hstep hneu hkein_nimmt σm hsm m' hm' hfall neum hneum hΛ =>
    exact akteurSA_dannNextVerbrauch (D := D) (P := P) (O := O) (passes := passes) (Q := Q) (S := S) (lok := lok) (Tg := Tg) (m := m) (zyk := zyk) (hO := hO) (hRL := hRL) (hQ := hQ) (hlok := hlok) (hS := hS) (sp := sp) (hsp := hsp) (hK := hK) (hM := hM) (hTV := hTV) (hFragS := hFragS) (hFS := hFS) (M := M) (u := u) (hF := hF) (hL := hL) (hRS := hRS) (hSG := hSG) (l := l) (Γ := Γ) (Λ := Λ) (t := t) (member := member) (edge := edge) (inv := inv) (bound := bound) (mass := mass) (body := body) (rest := rest) (vor := vor) (k := k) (restb := restb) (i := i) (ρ := ρ) (hnext := hnext) (hhead := hhead) (σ' := σ') (ρ' := ρ') (neu := neu) (hstep := hstep) (hneu := hneu) (hkein_nimmt := hkein_nimmt) (σm := σm) (hsm := hsm) (m' := m') (hm' := hm') (hfall := hfall) (neum := neum) (hneum := hneum) (hΛ := hΛ)
  | rueckScopedWert ρ r e R hhead hret hscope hΛ σ₁ hs₁ neu hneu hnonempty =>
    subst σ₁
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    exact ⟨fadenSA_scopedWert hFS hF ρ r e R hhead hret _, hL⟩
  | rueckScopedGrund ρ r grund R hhead hret hscope hΛ hnonempty =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    exact ⟨fadenSA_scopedGrund hFS hF ρ r grund R hhead hret _, hL⟩
  | rueckFreigabe ρ a L remaining hhead hnonempty =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    exact ⟨fadenSA_scopedFreigabe hO hRL hQ hS hsp hK hF ρ a L remaining hhead _, hL⟩
  | rueckFreigabeLetzte ρ a L hhead z hantwort =>
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    have hclean := fadenSA_scopedFreigabe hO hRL hQ hS hsp hK hF ρ a L [] hhead ((M.weltVon u).gibt L).spur
    refine fadenSA_scopedAntwort hO hRL hQ hS hsp hK hFS hTV hclean hL hRS ρ a rfl ?_
    have hw : (M.weltVon u).speicher.welt ((M.weltVon u).gibt L).spur =
        (M.weltVon u).gibt L := Speicher.welt_speicher ((M.weltVon u).gibt L)
    rw [hw]
    exact (rufAntwortG_rest_irrel (M.faeden u) _ _ _).trans hantwort
  | rueckScopedWertDirekt ρ r e R hhead hret hscope hΛ σ₁ hs₁ neu hneu hempty z hantwort =>
    rename_i l Γ Λ
    subst σ₁
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    have hclean := fadenSA_scopedWert hFS hF ρ r e R hhead hret
      ((M.weltVon u).lese Λ e.orte).spur
    refine fadenSA_scopedAntwort (l := l) hO hRL hQ hS hsp hK hFS hTV hclean hL hRS ρ
      ⟨.inl (evalErg ((M.weltVon u).lese Λ e.orte) e
        ((M.weltVon u).lese Λ e.orte) ρ), (M.weltVon u).lese Λ e.orte⟩
      (by rw [hempty]) ?_
    exact (rufAntwortG_rest_irrel (M.faeden u) _ _ _).trans hantwort
  | rueckScopedGrundDirekt ρ r grund R hhead hret hscope hΛ hempty z hantwort =>
    rename_i l Γ Λ
    simp only [RufMaschineG.weltVon, rufUpdateG_self]
    have hclean := fadenSA_scopedGrund hFS hF ρ r grund R hhead hret (M.faeden u).spur
    refine fadenSA_scopedAntwort (l := l) hO hRL hQ hS hsp hK hFS hTV hclean hL hRS ρ
      ⟨.inr grund, M.weltVon u⟩ (by rw [hempty]) ?_
    exact (rufAntwortG_rest_irrel (M.faeden u) _ _ _).trans hantwort

end Gabbro.Grammatik
