module
public import Grammatik.Nichtinterferenz.LokalSchritt.Teil1Basis
import all Grammatik.Nichtinterferenz.LokalSchritt.Teil1Basis

public import Grammatik.Nichtinterferenz.Lokal

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}
section Schritt

variable {S T : D.Tab ⊕ D.Glob → Bool} {Ax AxT : D.Ax → Bool}

theorem kLeave_rel (hST : ∀ c, S c = true → T c = true) (st : List (KRahmen D)) (f : D.Fn)
    (rho : Env D (D.params f)) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (k : GRest D (vertragVon D f) l Γ Λ) (hk : k.nR S Ax) (hl : l = true) {σ τ : World D}
    (h : WRel T σ τ) (ρ : Env D Γ) :
    KRel T (kLeave st f rho k hl σ ρ) (kLeave st f rho k hl τ ρ) := by
  cases k with
  | travRest t inv body is k =>
      simp only [GRest.nR] at hk
      simp only [kLeave]
      rw [(h.lese _ inv.orte).eval inv (alle_von hST hk.1) ρ.tail]
      exact KRel.ite (fun _ => KRel.lokal _ _ _ _ _ (h.lese _ _).1 (h.lese _ _).2)
        (fun _ => KRel.none_l _)
  | wiederRest n bis body ueber k => exact KRel.lokal _ _ _ _ _ h.1 h.2
  | ewigRest a n inv body k => exact KRel.lokal _ _ _ _ _ h.1 h.2
  | dann b k => exact KRel.lokal _ _ _ _ _ h.1 h.2
  | schrumpf k => exact KRel.lokal _ _ _ _ _ h.1 h.2
  | frei L k => exact KRel.lokal _ _ _ _ _ (by rw [h.1]) h.2
  | abbruch k => exact KRel.lokal _ _ _ _ _ h.1 h.2
  | _ => exact KRel.none_l _

theorem kNext_rel (st : List (KRahmen D)) (f : D.Fn)
    (rho : Env D (D.params f)) {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (k : GRest D (vertragVon D f) l Γ Λ) (hl : l = true) {σ τ : World D}
    (h : WRel T σ τ) (ρ : Env D Γ) :
    KRel T (kNext st f rho k hl σ ρ) (kNext st f rho k hl τ ρ) := by
  cases k with
  | travRest t inv body is k => exact KRel.lokal _ _ _ _ _ h.1 h.2
  | wiederRest n bis body ueber k => exact KRel.lokal _ _ _ _ _ h.1 h.2
  | ewigRest a n inv body k => exact KRel.lokal _ _ _ _ _ h.1 h.2
  | dann b k => exact KRel.lokal _ _ _ _ _ h.1 h.2
  | schrumpf k => exact KRel.lokal _ _ _ _ _ h.1 h.2
  | frei L k => exact KRel.lokal _ _ _ _ _ (by rw [h.1]) h.2
  | abbruch k => exact KRel.lokal _ _ _ _ _ h.1 h.2
  | _ => exact KRel.none_l _

theorem kAusDann_rel (hST : ∀ c, S c = true → T c = true) (st : List (KRahmen D)) (f : D.Fn)
    (rho : Env D (D.params f)) {l : Bool} {Γ : Ctx} {Λ' Λ'' : List (Res D)}
    (rest : Block D (vertragVon D f) l Γ Λ' Λ'') (k : GRest D (vertragVon D f) l Γ Λ'')
    (hk : k.nR S Ax) {o₁ o₂ : Ausgang (vertragVon D f) l Γ} (h : AusRel T o₁ o₂) :
    KRel T (kAusDann st f rho rest k o₁) (kAusDann st f rho rest k o₂) := by
  cases o₁ <;> cases o₂ <;> simp only [AusRel] at h
  · obtain ⟨hw, rfl⟩ := h; exact KRel.lokal _ _ _ _ _ hw.1 hw.2
  · obtain ⟨hw, rfl⟩ := h; exact kPop_rel st f hw _
  · obtain ⟨hw, rfl⟩ := h
    simp only [kAusDann]
    rw [hw.1]
    exact kPopGrund_rel st f _ hw.2 _
  · obtain ⟨hw, rfl⟩ := h; exact kLeave_rel hST st f rho k hk _ hw _
  · obtain ⟨hw, rfl⟩ := h; exact kNext_rel st f rho k _ hw _
  · exact KRel.none_l _
  · exact KRel.none_l _

theorem kAusEnde_rel (st : List (KRahmen D)) (f : D.Fn)
    (rho : Env D (D.params f)) {l : Bool} {Γ : Ctx} {Λ' : List (Res D)}
    (rest : Endblock D (vertragVon D f) l Γ Λ') {o₁ o₂ : Ausgang (vertragVon D f) l Γ}
    (h : AusRel T o₁ o₂) :
    KRel T (kAusEnde st f rho rest o₁) (kAusEnde st f rho rest o₂) := by
  cases o₁ <;> cases o₂ <;> simp only [AusRel] at h
  · obtain ⟨hw, rfl⟩ := h; exact KRel.lokal _ _ _ _ _ hw.1 hw.2
  · obtain ⟨hw, rfl⟩ := h; exact kPop_rel st f hw _
  · obtain ⟨hw, rfl⟩ := h
    simp only [kAusEnde]
    rw [hw.1]
    exact kPopGrund_rel st f _ hw.2 _
  · exact KRel.none_l _
  · exact KRel.none_l _
  · exact KRel.none_l _
  · exact KRel.none_l _

theorem zahl_ext {lo hi : Int} {a b : Zahl lo hi} (h : a.n = b.n) : a = b := by
  cases a
  cases b
  simp only at h
  subst h
  rfl

theorem KRel.lokalEnv (st : List (KRahmen D)) (f : D.Fn) (rho : Env D (D.params f)) {l : Bool}
    {Γ : Ctx} {Λ : List (Res D)} {ρ₁ ρ₂ : Env D Γ} (hρ : ρ₁ = ρ₂)
    (r : GRest D (vertragVon D f) l Γ Λ) {s₁ s₂ : List (Ereignis D)} {m₁ m₂ : Speicher D}
    (hs : s₁ = s₂) (hm : SpeicherGleich T m₁ m₂) :
    KRel T (kLokal st f rho ρ₁ r s₁ m₁) (kLokal st f rho ρ₂ r s₂ m₂) := by
  subst hρ
  exact KRel.lokal _ _ _ _ _ hs hm

theorem KRel.dite' {c₁ c₂ : Prop} [Decidable c₁] [Decidable c₂] (hc : c₁ ↔ c₂)
    {x₁ : c₁ → KErg D} {x₂ : c₂ → KErg D} {y₁ : ¬c₁ → KErg D} {y₂ : ¬c₂ → KErg D}
    (h1 : ∀ h₁ h₂, KRel T (x₁ h₁) (x₂ h₂)) (h2 : ∀ h₁ h₂, KRel T (y₁ h₁) (y₂ h₂)) :
    KRel T (dite c₁ x₁ y₁) (dite c₂ x₂ y₂) := by
  by_cases h : c₁
  · rw [dif_pos h, dif_pos (hc.mp h)]; exact h1 _ _
  · rw [dif_neg h, dif_neg (fun h' => h (hc.mpr h'))]; exact h2 _ _

theorem KRel.dite {c : Prop} [Decidable c] {x₁ x₂ : c → KErg D} {y₁ y₂ : ¬c → KErg D}
    (h1 : ∀ h, KRel T (x₁ h) (x₂ h)) (h2 : ∀ h, KRel T (y₁ h) (y₂ h)) :
    KRel T (dite c x₁ y₁) (dite c x₂ y₂) := by
  by_cases hc : c
  · rw [dif_pos hc, dif_pos hc]; exact h1 hc
  · rw [dif_neg hc, dif_neg hc]; exact h2 hc

variable (hST : ∀ c, S c = true → T c = true) (hAx : ∀ a, Ax a = true → AxT a = true)
  (P : Programm D) (O : Orakel D) (passes : Nat)
  (st : List (KRahmen D)) (f : D.Fn) (rho : Env D (D.params f)) (spur : List (Ereignis D))
  {sp₁ sp₂ : Speicher D}
include hST

theorem kRufEnde_rel (hsp : SpeicherGleich T sp₁ sp₂) {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (ρ : Env D Γ) (s : Stmt D (vertragVon D f) l Γ Λ Λ')
    (rest : Endblock D (vertragVon D f) l Γ Λ') (hs : nS S Ax s = true) :
    KRel T (kRufEnde P st f rho spur sp₁ ρ s rest) (kRufEnde P st f rho spur sp₂ ρ s rest) := by
  have hW := WRel.welt hsp spur
  cases s with
  | call g args hp hr =>
      simp only [nS] at hs
      simp only [kRufEnde]
      rw [(hW.lese Λ args.orte).evalArgs args (alle_von hST hs) ρ]
      exact KRel.push _ _ _ _ _ _ _ _ rfl hsp
  | callInd p args hp hr =>
      simp only [nS, Bool.and_eq_true] at hs
      simp only [kRufEnde]
      have h1 := hW.lese Λ (p.orte ++ args.orte)
      rw [h1.eval p (alle_von hST hs.1) ρ, h1.evalArgs args (alle_von hST hs.2) ρ]
      generalize eval _ p _ ρ = x
      obtain ⟨g, hg⟩ := x
      exact KRel.push _ _ _ _ _ _ _ _ rfl hsp
  | _ => exact KRel.none_l _

theorem kRufDann_rel (hsp : SpeicherGleich T sp₁ sp₂) {l : Bool} {Γ : Ctx}
    {Λ Λ' Λ'' : List (Res D)} (ρ : Env D Γ) (s : Stmt D (vertragVon D f) l Γ Λ Λ')
    (rest : Block D (vertragVon D f) l Γ Λ' Λ'') (k : GRest D (vertragVon D f) l Γ Λ'')
    (hs : nS S Ax s = true) :
    KRel T (kRufDann P st f rho spur sp₁ ρ s rest k) (kRufDann P st f rho spur sp₂ ρ s rest k) := by
  have hW := WRel.welt hsp spur
  cases s with
  | call g args hp hr =>
      simp only [nS] at hs
      simp only [kRufDann]
      rw [(hW.lese Λ args.orte).evalArgs args (alle_von hST hs) ρ]
      exact KRel.push _ _ _ _ _ _ _ _ rfl hsp
  | callInd p args hp hr =>
      simp only [nS, Bool.and_eq_true] at hs
      simp only [kRufDann]
      have h1 := hW.lese Λ (p.orte ++ args.orte)
      rw [h1.eval p (alle_von hST hs.1) ρ, h1.evalArgs args (alle_von hST hs.2) ρ]
      generalize eval _ p _ ρ = x
      obtain ⟨g, hg⟩ := x
      exact KRel.push _ _ _ _ _ _ _ _ rfl hsp
  | _ => exact KRel.none_l _

theorem kEntf_rel (hsp : SpeicherGleich T sp₁ sp₂) {l : Bool} {Γ : Ctx}
    {Λ Λ' Λ'' : List (Res D)} (ρ : Env D Γ) (s : Stmt D (vertragVon D f) l Γ Λ Λ')
    (rest : Block D (vertragVon D f) l Γ Λ' Λ'') (k : GRest D (vertragVon D f) l Γ Λ'')
    (hs : nS S Ax s = true) :
    KRel T (kEntf passes st f rho spur sp₁ ρ s rest k) (kEntf passes st f rho spur sp₂ ρ s rest k) := by
  have hW := WRel.welt hsp spur
  cases s with
  | ite c t e =>
      simp only [nS, Bool.and_eq_true] at hs
      simp only [kEntf]
      rw [(hW.lese Λ c.orte).eval c (alle_von hST hs.1.1) ρ]
      exact KRel.ite (fun _ => KRel.lokal _ _ _ _ _ rfl hsp) (fun _ => KRel.lokal _ _ _ _ _ rfl hsp)
  | onOption o p a =>
      simp only [nS, Bool.and_eq_true] at hs
      simp only [kEntf]
      rw [(hW.lese Λ o.orte).eval o (alle_von hST hs.1.1) ρ]
      generalize eval _ o _ ρ = x
      cases x with
      | none => exact KRel.lokal _ _ _ _ _ rfl hsp
      | some v => exact KRel.lokal _ _ _ _ _ rfl hsp
  | onTag v arms =>
      simp only [nS, Bool.and_eq_true] at hs
      simp only [kEntf]
      rw [(hW.lese Λ v.orte).eval v (alle_von hST hs.1) ρ]
      generalize armWahlG arms _ = x
      rcases x with ⟨_ | ⟨lo, hi⟩, b, nutz⟩
      · exact KRel.lokal _ _ _ _ _ rfl hsp
      · exact KRel.lokal _ _ _ _ _ rfl hsp
  | onWhy r arms =>
      simp only [nS, Bool.and_eq_true] at hs
      simp only [kEntf]
      rw [(hW.lese Λ r.orte).eval r (alle_von hST hs.1) ρ]
      exact KRel.lokal _ _ _ _ _ rfl hsp
  | locks L hr body => exact KRel.lokal _ _ _ _ _ rfl hsp
  | breaking i body => exact KRel.lokal _ _ _ _ _ rfl hsp
  | traverse t inv body => exact KRel.lokal _ _ _ _ _ rfl hsp
  | retry n bis body ueber => exact KRel.lokal _ _ _ _ _ rfl hsp
  | forever a inv body => exact KRel.lokal _ _ _ _ _ rfl hsp
  | _ => exact KRel.none_l _

include hAx in
theorem kDannCons_rel (hO : OrakelTreu T AxT O) (hsp : SpeicherGleich T sp₁ sp₂) {l : Bool}
    {Γ : Ctx} {Λ Λ' Λ'' : List (Res D)} (ρ : Env D Γ) (s : Stmt D (vertragVon D f) l Γ Λ Λ')
    (rest : Block D (vertragVon D f) l Γ Λ' Λ'') (k : GRest D (vertragVon D f) l Γ Λ'')
    (hs : nS S Ax s = true) (hk : k.nR S Ax) :
    KRel T (kDannCons P O passes st f rho spur sp₁ ρ s rest k)
      (kDannCons P O passes st f rho spur sp₂ ρ s rest k) := by
  unfold kDannCons
  by_cases h1 : GEntfaltbar s = true
  · rw [if_pos h1, if_pos h1]
    exact kEntf_rel hST passes st f rho spur hsp ρ s rest k hs
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : s.istBlatt = true
    · rw [if_pos h2, if_pos h2]
      exact kAusDann_rel hST st f rho rest k hk
        (blatt_rel O passes hST hAx hO s h2 hs (WRel.welt hsp spur) ρ)
    · rw [if_neg h2, if_neg h2]
      exact kRufDann_rel hST P st f rho spur hsp ρ s rest k hs

include hAx in
theorem kEndeCons_rel (hO : OrakelTreu T AxT O) (hsp : SpeicherGleich T sp₁ sp₂) {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} (ρ : Env D Γ) (s : Stmt D (vertragVon D f) l Γ Λ Λ')
    (rest : Endblock D (vertragVon D f) l Γ Λ') (hs : nS S Ax s = true) :
    KRel T (kEndeCons P O passes st f rho spur sp₁ ρ s rest)
      (kEndeCons P O passes st f rho spur sp₂ ρ s rest) := by
  unfold kEndeCons
  by_cases h1 : GEntfaltbar s = true
  · rw [if_pos h1, if_pos h1]
    exact KRel.lokal _ _ _ _ _ rfl hsp
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : s.istBlatt = true
    · rw [if_pos h2, if_pos h2]
      exact kAusEnde_rel st f rho rest
        (blatt_rel O passes hST hAx hO s h2 hs (WRel.welt hsp spur) ρ)
    · rw [if_neg h2, if_neg h2]
      exact kRufEnde_rel hST P st f rho spur hsp ρ s rest hs

include hAx in
theorem kEnde_rel (hO : OrakelTreu T AxT O) (hsp : SpeicherGleich T sp₁ sp₂) {l : Bool}
    {Γ : Ctx} {Λ : List (Res D)} (ρ : Env D Γ) (e : Endblock D (vertragVon D f) l Γ Λ)
    (he : nE S Ax e = true) :
    KRel T (kEnde P O passes st f rho spur sp₁ ρ e) (kEnde P O passes st f rho spur sp₂ ρ e) := by
  have hW := WRel.welt hsp spur
  cases e with
  | cons s rest =>
      simp only [nE, Bool.and_eq_true] at he
      exact kEndeCons_rel hST hAx P O passes st f rho spur hO hsp ρ s rest he.1
  | bind e rest =>
      simp only [nE, Bool.and_eq_true] at he
      simp only [kEnde]
      rw [(hW.lese Λ e.orte).eval e (alle_von hST he.1) ρ]
      exact KRel.lokal _ _ _ _ _ rfl hsp
  | bindCall g args he' hp hr rest =>
      simp only [kEnde]
      split
      · exact KRel.lokal _ _ _ _ _ rfl hsp
      · exact KRel.none_l _
  | bindCallElse g args he' hp hr err rest =>
      simp only [kEnde]
      split
      · exact KRel.lokal _ _ _ _ _ rfl hsp
      · exact KRel.none_l _
  | bindAxiom a args he' hw hg hd hgd rest =>
      simp only [nE, Bool.and_eq_true] at he
      have h1 := hW.lese Λ args.orte
      obtain ⟨e1, e2⟩ := axiomAntwort_rel O hO (hAx a he.1.1) h1
        (evalArgs ((sp₂.welt spur).lese Λ args.orte) args ((sp₂.welt spur).lese Λ args.orte) ρ)
      simp only [kEnde]
      rw [h1.evalArgs args (alle_von hST he.1.2) ρ]
      revert e1 e2
      generalize axiomAntwort O a ((sp₁.welt spur).lese Λ args.orte) _ = p₁
      generalize axiomAntwort O a ((sp₂.welt spur).lese Λ args.orte) _ = p₂
      rintro e1 e2
      obtain ⟨w1, r1⟩ := p₁
      obtain ⟨w2, r2⟩ := p₂
      simp only at e1 e2 ⊢
      subst e1
      cases r1 with
      | none => exact KRel.none_l _
      | some v => exact KRel.lokal _ _ _ _ _ e2.1 e2.2
  | bindAxiomElse a args he' hr hw hg hd hgd err rest =>
      simp only [nE, Bool.and_eq_true] at he
      have h1 := hW.lese Λ args.orte
      obtain ⟨e1, e2⟩ := axiomAntwortSonst_rel O hO (hAx a he.1.1.1) h1
        (evalArgs ((sp₂.welt spur).lese Λ args.orte) args ((sp₂.welt spur).lese Λ args.orte) ρ)
      simp only [kEnde]
      rw [h1.evalArgs args (alle_von hST he.1.1.2) ρ]
      revert e1 e2
      generalize axiomAntwortSonst O a ((sp₁.welt spur).lese Λ args.orte) _ = p₁
      generalize axiomAntwortSonst O a ((sp₂.welt spur).lese Λ args.orte) _ = p₂
      rintro e1 e2
      obtain ⟨w1, r1⟩ := p₁
      obtain ⟨w2, r2⟩ := p₂
      simp only at e1 e2 ⊢
      subst e1
      rcases r1 with _ | v | r
      · exact KRel.none_l _
      · exact KRel.lokal _ _ _ _ _ e2.1 e2.2
      · exact KRel.lokal _ _ _ _ _ e2.1 e2.2
  | regRead r hk rest =>
      simp only [kEnde]
      split
      · exact KRel.lokal _ _ _ _ _ rfl hsp
      · exact KRel.none_l _
  | regReadElse r hk z sonst rest =>
      simp only [kEnde]
      split
      · exact KRel.lokal _ _ _ _ _ rfl hsp
      · exact KRel.none_l _
  | awaits g pl hp hL hat rest =>
      simp only [kEnde]
      split
      · exact KRel.lokal _ _ _ _ _ rfl hsp
      · exact KRel.none_l _
  | bindCallInd p args he' hp hr rest =>
      simp only [kEnde]
      split
      · exact KRel.lokal _ _ _ _ _ rfl hsp
      · exact KRel.none_l _
  | narrow e lo' hi' sonst rest =>
      simp only [kEnde]
      split
      · exact KRel.lokal _ _ _ _ _ rfl hsp
      · exact KRel.none_l _
  | exchange g neu hw hL rest =>
      simp only [kEnde]
      split
      · exact KRel.lokal _ _ _ _ _ rfl hsp
      · exact KRel.none_l _
  | ite c t e =>
      simp only [kEnde]
      split
      · exact KRel.lokal _ _ _ _ _ rfl hsp
      · exact KRel.none_l _
  | ret e _ =>
      simp only [nE] at he
      simp only [kEnde]
      rw [(hW.lese Λ e.orte).evalErg e (alle_von hST he) ρ]
      exact kPop_rel st f (hW.lese Λ e.orte) _
  | retWhy r _ => exact kPopGrund_rel st f spur hsp r
  | leave _ => exact KRel.none_l _
  | next _ => exact KRel.none_l _

end Schritt
end Gabbro.Grammatik
