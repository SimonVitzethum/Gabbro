module

public import Grammatik.Nichtinterferenz.Schritt
public import Grammatik.Nichtinterferenz.SchrittTreu.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}

theorem schrittK_von_g5 (P : Programm D) (O : Orakel D) (passes : Nat)
    {M M' : RufMaschineG D} {f : Faden} (hs : RufSchrittG5 P O passes M f M') :
    kSchrittK P O passes (M.faeden f).kern M.speicher = some ((M'.faeden f).kern, M'.speicher) := by
  cases hs with
  | rueckConsGrund _ _ r hperm restk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g
      hfg rho hrho s0 hs0 rg hrg hn =>
      subst hfg hrho hrg
      kstart
      rw [hpop]
      simp only [kr, kEnde, kEndeCons, GEntfaltbar, Stmt.istBlatt, Bool.false_eq_true, ↓reduceIte, kAusEnde, execStmt, kPopGrund,
        List.map_cons]
      simp only [RufRahmenG.kern, hcaller]
      rw [dif_pos (show (vertragVon D (M.faeden f).kopf.f).gruende = n from hn)]
      rfl
  | dannRetGrund _ _ r hperm restk kk ρ hhead caller rst hpop l Γ Λ Λ' τ n err restb k ρc hcaller hΛ g
      hfg rho hrho s0 hs0 rg hrg hn =>
      subst hfg hrho hrg
      kstart
      rw [hpop]
      simp only [kr, kDann, kDannCons, GEntfaltbar, Stmt.istBlatt, Bool.false_eq_true, ↓reduceIte, kAusDann, execStmt, kPopGrund,
        List.map_cons]
      simp only [RufRahmenG.kern, hcaller]
      rw [dif_pos (show (vertragVon D (M.faeden f).kopf.f).gruende = n from hn)]
      rfl
  | dannRegLies _ _ l Γ Λ Λ' r hk rest k ρ hhead v hv hz hΛ =>
      kstart
      simp only [kr, kDann]
      simp only [RufMaschineG.weltVon] at hv
      rw [hv]
      simp only [hz, if_true]
      rfl
  | dannRegLiesElseWahr _ _ l Γ Λ Λ' r hk zusage sonst rest k ρ hhead v hv σ₁ hs₁ hw neu hneu hΛ =>
      kstart
      subst hs₁
      simp only [kr, kDann]
      simp only [RufMaschineG.weltVon] at hv hw
      rw [hv]
      simp only
      rw [if_pos hw]
      rfl
  | dannRegLiesElseFalsch _ _ l Γ Λ Λ' r hk zusage sonst rest k ρ hhead v hv σ₁ hs₁ hw neu hneu hΛ =>
      kstart
      subst hs₁
      simp only [kr, kDann]
      simp only [RufMaschineG.weltVon] at hv hw
      rw [hv]
      simp only
      rw [if_neg (by rw [hw]; exact Bool.false_ne_true)]
      rfl
  | dannAwaits _ _ l Γ Λ Λ' g payload hp hL _ rest k ρ hhead hvis σ₁ hs₁ neu hneu hΛ =>
      kstart
      subst hs₁
      simp only [kr, kDann]
      simp only [RufMaschineG.weltVon] at hvis
      rw [if_pos hvis]
      rfl
  | dannExchange _ _ l Γ Λ Λ' g neuE hw hL rest k ρ hhead σ₁ hs₁ σ₂ hs₂ neu hneu hΛ =>
      kstart
      subst hs₂ hs₁
      rfl
  | dannGleit _ _ l Γ Λ Λ' l₁ h₁ l₂ h₂ op a b lo hi rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
      kstart
      subst hs₁
      simp only [kr, kDann]
      simp only [RufMaschineG.weltVon] at hv
      rw [hv]
      rfl
  | dannGleitLit _ _ l Γ Λ Λ' q lo hi rest k ρ hhead v hv =>
      kstart
      simp only [kr, kDann]
      rw [hv]
      rfl
  | dannGleitVon _ _ l Γ Λ Λ' l₁ h₁ e lo hi rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
      kstart
      subst hs₁
      simp only [kr, kDann]
      simp only [RufMaschineG.weltVon] at hv
      rw [hv]
      rfl
  | dannGleitNarrowOk _ _ l Γ Λ Λ' l₁ h₁ e lo hi sonst rest k ρ hhead σ₁ hs₁ v hv neu hneu hΛ =>
      kstart
      subst hs₁
      simp only [kr, kDann]
      simp only [RufMaschineG.weltVon] at hv
      rw [hv]
      rfl
  | dannGleitNarrowElse _ _ l Γ Λ Λ' l₁ h₁ e lo hi sonst rest k ρ hhead σ₁ hs₁ hn neu hneu hΛ =>
      kstart
      subst hs₁
      simp only [kr, kDann]
      simp only [RufMaschineG.weltVon] at hn
      rw [hn]
      rfl
  | dannBindAxiom _ _ l Γ Λ Λ' τ a args he hw hg hd hgd rest k ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      kstart
      subst hs₁
      simp only [kr, kDann]
      simp only [RufMaschineG.weltVon] at hax
      rw [hax]
      rfl
  | dannBindAxiomElseOk _ _ l Γ Λ Λ' τ a args he hr hw hg hd hgd err rest k ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      kstart
      subst hs₁
      simp only [kr, kDann]
      simp only [RufMaschineG.weltVon] at hax
      rw [hax]
      rfl
  | dannBindAxiomElseGrund _ _ l Γ Λ Λ' τ a args he hr hw hg hd hgd err rest k ρ hhead σ₁ hs₁ σ₂ r hax neu hneu hΛ =>
      kstart
      subst hs₁
      simp only [kr, kDann]
      simp only [RufMaschineG.weltVon] at hax
      rw [hax]
      rfl
  | dannBindAxiomOpt _ _ l Γ Λ Λ' e a args he hp hd hgd rest k ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      kstart
      subst hs₁
      simp only [kr, kDann]
      simp only [RufMaschineG.weltVon] at hax
      rw [hax]
      rfl
  | dannBindAxiomOptElseOk _ _ l Γ Λ Λ' e a args he hr hp hd hgd err rest k ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      kstart
      subst hs₁
      simp only [kr, kDann]
      simp only [RufMaschineG.weltVon] at hax
      rw [hax]
      rfl
  | dannBindAxiomOptElseGrund _ _ l Γ Λ Λ' e a args he hr hp hd hgd err rest k ρ hhead σ₁ hs₁ σ₂ r hax neu hneu hΛ =>
      kstart
      subst hs₁
      simp only [kr, kDann]
      simp only [RufMaschineG.weltVon] at hax
      rw [hax]
      rfl

theorem schrittK_von_g6 (P : Programm D) (O : Orakel D) (passes : Nat)
    {M M' : RufMaschineG D} {f : Faden} (hs : RufSchrittG6 P O passes M f M') :
    kSchrittK P O passes (M.faeden f).kern M.speicher = some ((M'.faeden f).kern, M'.speicher) := by
  cases hs with
  | endeBindAxiomElseOk l Γ Λ τ a args he hr hw hg hd hgd err rest ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      kstart
      subst hs₁
      simp only [kr, kEnde]
      simp only [RufMaschineG.weltVon] at hax
      rw [hax]
      rfl
  | endeBindAxiomElseGrund l Γ Λ τ a args he hr hw hg hd hgd err rest ρ hhead σ₁ hs₁ σ₂ r hax neu hneu hΛ =>
      kstart
      subst hs₁
      simp only [kr, kEnde]
      simp only [RufMaschineG.weltVon] at hax
      rw [hax]
      rfl
  | endeBindAxiomOptElseOk l Γ Λ e a args he hr hp hd hgd err rest ρ hhead σ₁ hs₁ σ₂ v hax neu hneu hΛ =>
      kstart
      subst hs₁
      simp only [kr, kEnde]
      simp only [RufMaschineG.weltVon] at hax
      rw [hax]
      rfl
  | endeBindAxiomOptElseGrund l Γ Λ e a args he hr hp hd hgd err rest ρ hhead σ₁ hs₁ σ₂ r hax neu hneu hΛ =>
      kstart
      subst hs₁
      simp only [kr, kEnde]
      simp only [RufMaschineG.weltVon] at hax
      rw [hax]
      rfl

theorem schrittK_von_g7 (P : Programm D) (O : Orakel D) (passes : Nat)
    {M M' : RufMaschineG D} {f : Faden} (hs : RufSchrittG7 P O passes M f M') :
    kSchrittK P O passes (M.faeden f).kern M.speicher = some ((M'.faeden f).kern, M'.speicher) := by
  cases hs with
  | dannVerbrauch l Γ Λ Λ'' t member edge inv bound mass body rest k ρ hhead =>
      kstart
      rfl
  | verbrauchWeiter l Γ Λ t member edge inv bound mass body rest k ρ hhead
      σ₁ hs₁ hw σ₂ hs₂ v hv σ₃ hs₃ m hm neu hneu hΛ =>
      kstart
      subst hm hs₃ hs₂ hs₁
      simp only [kr]
      simp only [RufMaschineG.weltVon] at hw hv
      rw [if_pos hw, hv]
      rfl
  | verbrauchLeer l Γ Λ t member edge inv bound mass body rest k ρ hhead
      σ₁ hs₁ hw σ₂ hs₂ hleer hkein neu hneu hΛ =>
      kstart
      subst hs₂ hs₁
      simp only [kr]
      simp only [RufMaschineG.weltVon] at hw hleer hkein
      rw [if_pos hw, hleer, if_pos hkein]
      rfl
  | verbrauchFort l Γ Λ t member edge inv bound mass body rest vor k i ρ hhead
      σ₁ hs₁ m' hm' hfall neu hneu hΛ =>
      kstart
      subst hm' hs₁
      simp only [kr]
      simp only [RufMaschineG.weltVon] at hfall
      rw [if_pos hfall]
      rfl
  | dannLeaveVerbrauch l Γ Λ t member edge inv bound mass body rest vor k restb i ρ
      hleave hhead σ' ρ' neu hstep hneu hkein σm hsm m' hm' hfall σ₁ hs₁ hw
      neu₁ hneu₁ hΛ =>
      kstart
      simp only [execStmt, RufMaschineG.weltVon] at hstep
      cases hstep
      subst hm' hs₁ hsm
      simp only [kr, kDann, kDannCons, GEntfaltbar, Stmt.istBlatt,
        Bool.false_eq_true, ↓reduceIte, kAusDann, execStmt, kLeave, Env.tail]
      rw [if_pos hfall, if_pos hw]
      rfl
  | dannNextVerbrauch l Γ Λ t member edge inv bound mass body rest vor k restb i ρ
      hnext hhead σ' ρ' neu hstep hneu hkein σm hsm m' hm' hfall neum hneum hΛ =>
      kstart
      simp only [execStmt, RufMaschineG.weltVon] at hstep
      cases hstep
      subst hm' hsm
      simp only [kr, kDann, kDannCons, GEntfaltbar, Stmt.istBlatt,
        Bool.false_eq_true, ↓reduceIte, kAusDann, execStmt, kNext, Env.tail]
      rw [if_pos hfall]
      rfl

theorem schrittK_von (P : Programm D) (O : Orakel D) (passes : Nat)
    {M M' : RufMaschineG D} {f : Faden} (hs : RufSchrittG P O passes M f M') :
    kSchrittK P O passes (M.faeden f).kern M.speicher = some ((M'.faeden f).kern, M'.speicher) := by
  cases hs with
  | g1 hs => exact schrittK_von_g1 (P := P) (O := O) (passes := passes) (hs := hs)
  | g2 hs => exact schrittK_von_g2 (P := P) (O := O) (passes := passes) (hs := hs)
  | g3 hs => exact schrittK_von_g3 (P := P) (O := O) (passes := passes) (hs := hs)
  | g4 hs => exact schrittK_von_g4 (P := P) (O := O) (passes := passes) (hs := hs)
  | g5 hs => exact schrittK_von_g5 (P := P) (O := O) (passes := passes) (hs := hs)
  | g6 hs => exact schrittK_von_g6 (P := P) (O := O) (passes := passes) (hs := hs)
  | g7 hs => exact schrittK_von_g7 (P := P) (O := O) (passes := passes) (hs := hs)

end Gabbro.Grammatik
