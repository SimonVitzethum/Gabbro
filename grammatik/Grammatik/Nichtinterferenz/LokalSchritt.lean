/-
  File:      Grammatik/Nichtinterferenz/LokalSchritt.lean
  Subject:   THE STEP OF ONE THREAD IS LOCAL, RELATIONALLY (`schrittK_rel`).

  One ghost-free thread state `k`, two memories that agree on a carrier set
  `T`; the head residue of `k` reads only inside `S ⊆ T` and calls only
  axioms the oracle answers faithfully on `T`. Then the two steps
  `kSchrittK k sp₁` and `kSchrittK k sp₂`, if both exist, end in the SAME
  ghost-free state and in memories that again agree on `T`.

  This is step consistency for one thread, stated over the function of
  `Schritt.lean` -- one case analysis over the residue, no pairing of two
  derivations. Device register reads use register locality (`RegLokal`):
  the device carriers of a register the head reads lie in `S`.
-/
import Grammatik.Nichtinterferenz.Lokal

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- Two step results that agree: both absent, or (if both present) the
    same ghost-free state and memories agreeing on `T`. -/
def KRel (T : D.Tab ⊕ D.Glob → Bool) (x y : KErg D) : Prop :=
  ∀ a b, x = some a → y = some b → a.1 = b.1 ∧ SpeicherGleich T a.2 b.2

section Rel

variable {T : D.Tab ⊕ D.Glob → Bool}

theorem KRel.none_l (y : KErg D) : KRel T none y := fun _ _ h _ => by cases h

theorem KRel.none_r (x : KErg D) : KRel T x none := fun _ _ _ h => by cases h

theorem KRel.lokal (st : List (KRahmen D)) (f : D.Fn) (rho : Env D (D.params f)) {l : Bool}
    {Γ : Ctx} {Λ : List (Res D)} (ρ : Env D Γ) (r : GRest D (vertragVon D f) l Γ Λ)
    {s₁ s₂ : List (Ereignis D)} {m₁ m₂ : Speicher D} (hs : s₁ = s₂)
    (hm : SpeicherGleich T m₁ m₂) :
    KRel T (kLokal st f rho ρ r s₁ m₁) (kLokal st f rho ρ r s₂ m₂) := by
  intro a b ha hb
  simp only [kLokal, Option.some.injEq] at ha hb
  subst ha hb hs
  exact ⟨rfl, hm⟩

theorem KRel.push (P : Programm D) (st : List (KRahmen D)) (f : D.Fn) (rho : Env D (D.params f))
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (ρ : Env D Γ) (rc : GRest D (vertragVon D f) l Γ Λ)
    (g : D.Fn) (rhog : Env D (D.params g)) {s₁ s₂ : List (Ereignis D)} {m₁ m₂ : Speicher D}
    (hs : s₁ = s₂) (hm : SpeicherGleich T m₁ m₂) :
    KRel T (kPush P st f rho ρ rc g rhog s₁ m₁) (kPush P st f rho ρ rc g rhog s₂ m₂) := by
  intro a b ha hb
  simp only [kPush, Option.some.injEq] at ha hb
  subst ha hb hs
  exact ⟨rfl, hm⟩

theorem KRel.ite {c : Prop} [Decidable c] {x₁ x₂ y₁ y₂ : KErg D} (h1 : c → KRel T x₁ x₂)
    (h2 : ¬c → KRel T y₁ y₂) : KRel T (if c then x₁ else y₁) (if c then x₂ else y₂) := by
  by_cases hc : c
  · rw [if_pos hc, if_pos hc]; exact h1 hc
  · rw [if_neg hc, if_neg hc]; exact h2 hc

theorem kBinde_rel (f : D.Fn) (rst : List (KRahmen D)) (c : KRahmen D) {σ τ : World D}
    (h : WRel T σ τ) (v : ErgVal D (vertragVon D f).erg) :
    KRel T (kBinde f rst c σ v) (kBinde f rst c τ v) := by
  obtain ⟨cf, crho, ⟨l, Γ, Λ, ρc, r⟩⟩ := c
  cases r with
  | wartet restb k =>
      simp only [kBinde]
      split
      · intro a b ha hb
        simp only [Option.some.injEq] at ha hb
        subst ha hb
        exact ⟨by simp [h.1], h.2⟩
      · exact KRel.none_l _
  | wartetSonst n err restb k =>
      simp only [kBinde]
      split
      · intro a b ha hb
        simp only [Option.some.injEq] at ha hb
        subst ha hb
        exact ⟨by simp [h.1], h.2⟩
      · exact KRel.none_l _
  | _ => exact KRel.none_l _

theorem kPop_rel (st : List (KRahmen D)) (f : D.Fn) {σ τ : World D} (h : WRel T σ τ)
    (v : ErgVal D (vertragVon D f).erg) : KRel T (kPop st f σ v) (kPop st f τ v) := by
  cases st with
  | nil => exact KRel.none_l _
  | cons c rst =>
      simp only [kPop]
      refine KRel.ite (fun _ => kBinde_rel f rst c h v) (fun _ => ?_)
      intro a b ha hb
      simp only [Option.some.injEq] at ha hb
      subst ha hb
      exact ⟨by simp [h.1], h.2⟩

theorem kPopGrund_rel (st : List (KRahmen D)) (f : D.Fn) (spur : List (Ereignis D))
    {m₁ m₂ : Speicher D} (hm : SpeicherGleich T m₁ m₂) (r : Fin (vertragVon D f).gruende) :
    KRel T (kPopGrund st f spur m₁ r) (kPopGrund st f spur m₂ r) := by
  cases st with
  | nil => exact KRel.none_l _
  | cons c rst =>
      obtain ⟨cf, crho, ⟨l, Γ, Λ, ρc, rr⟩⟩ := c
      cases rr with
      | wartetSonst n err restb k =>
          simp only [kPopGrund]
          split
          · intro a b ha hb
            simp only [Option.some.injEq] at ha hb
            subst ha hb
            exact ⟨rfl, hm⟩
          · exact KRel.none_l _
      | _ => exact KRel.none_l _

end Rel

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
  | onGrund r arms =>
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
  | ret e _ =>
      simp only [nE] at he
      simp only [kEnde]
      rw [(hW.lese Λ e.orte).evalErg e (alle_von hST he) ρ]
      exact kPop_rel st f (hW.lese Λ e.orte) _
  | retGrund r _ => exact kPopGrund_rel st f spur hsp r
  | leave _ => exact KRel.none_l _
  | next _ => exact KRel.none_l _

include hAx in
theorem kDann_rel (hO : OrakelTreu T AxT O) (hRL : RegLokal O) (hsp : SpeicherGleich T sp₁ sp₂)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} (ρ : Env D Γ)
    (b : Block D (vertragVon D f) l Γ Λ Λ') (k : GRest D (vertragVon D f) l Γ Λ')
    (hb : nB S Ax b = true) (hk : k.nR S Ax) :
    KRel T (kDann P O passes st f rho spur sp₁ ρ b k) (kDann P O passes st f rho spur sp₂ ρ b k) := by
  have hW := WRel.welt hsp spur
  cases b with
  | nil => exact KRel.lokal _ _ _ _ _ rfl hsp
  | cons s rest =>
      simp only [nB, Bool.and_eq_true] at hb
      exact kDannCons_rel hST hAx P O passes st f rho spur hO hsp ρ s rest k hb.1 hk
  | bind e rest =>
      simp only [nB, Bool.and_eq_true] at hb
      simp only [kDann]
      rw [(hW.lese Λ e.orte).eval e (alle_von hST hb.1) ρ]
      exact KRel.lokal _ _ _ _ _ rfl hsp
  | bindCall g args he hp hr rest =>
      simp only [nB, Bool.and_eq_true] at hb
      simp only [kDann]
      rw [(hW.lese Λ args.orte).evalArgs args (alle_von hST hb.1) ρ]
      exact KRel.push _ _ _ _ _ _ _ _ rfl hsp
  | bindCallInd p args he hp hr rest =>
      simp only [nB, Bool.and_eq_true] at hb
      simp only [kDann]
      have h1 := hW.lese Λ (p.orte ++ args.orte)
      rw [h1.eval p (alle_von hST hb.1.1) ρ, h1.evalArgs args (alle_von hST hb.1.2) ρ]
      generalize eval _ p _ ρ = x
      obtain ⟨g, hg⟩ := x
      exact KRel.push _ _ _ _ _ _ _ _ rfl hsp
  | bindCallElse g args he hp hr err rest =>
      simp only [nB, Bool.and_eq_true] at hb
      simp only [kDann]
      rw [(hW.lese Λ args.orte).evalArgs args (alle_von hST hb.1.1) ρ]
      exact KRel.push _ _ _ _ _ _ _ _ rfl hsp
  | bindAxiom a args he hw hg hd hgd rest =>
      simp only [nB, Bool.and_eq_true] at hb
      have h1 := hW.lese Λ args.orte
      obtain ⟨e1, e2⟩ := axiomAntwort_rel O hO (hAx a hb.1.1) h1
        (evalArgs ((sp₂.welt spur).lese Λ args.orte) args ((sp₂.welt spur).lese Λ args.orte) ρ)
      simp only [kDann]
      rw [h1.evalArgs args (alle_von hST hb.1.2) ρ]
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
  | regLies r hk' rest =>
      simp only [nB, Bool.and_eq_true] at hb
      simp only [kDann]
      rw [hRL.1 r _ _ (gleichAuf_von_sg (σ := sp₁.welt spur) (τ := sp₂.welt spur) hsp
        (alle_von hST hb.1))]
      generalize einpassen _ (D.rtyp r) _ = x
      cases x with
      | none => exact KRel.none_l _
      | some v => exact KRel.ite (fun _ => KRel.lokal _ _ _ _ _ rfl hsp) (fun _ => KRel.none_l _)
  | regLiesElse r hk' zusage sonst rest =>
      simp only [nB, Bool.and_eq_true] at hb
      simp only [kDann]
      rw [hRL.1 r _ _ (gleichAuf_von_sg (σ := sp₁.welt spur) (τ := sp₂.welt spur) hsp
        (alle_von hST hb.1.1.1))]
      generalize einpassen _ (D.rtyp r) _ = x
      cases x with
      | none => exact KRel.none_l _
      | some v =>
          simp only
          rw [(hW.lese Λ zusage.orte).eval zusage (alle_von hST hb.1.1.2) (.cons v ρ)]
          exact KRel.ite (fun _ => KRel.lokal _ _ _ _ _ rfl hsp)
            (fun _ => KRel.lokal _ _ _ _ _ rfl hsp)
  | awaits g payload hp hL rest =>
      simp only [nB, Bool.and_eq_true] at hb
      simp only [kDann]
      rw [hRL.2 g _ _ (gleichAuf_von_sg (σ := sp₁.welt spur) (τ := sp₂.welt spur) hsp
        (by simp [hST _ hb.1]))]
      have hg : ((sp₁.welt spur).lese Λ [.inr g]).globs g =
          ((sp₂.welt spur).lese Λ [.inr g]).globs g := hsp (.inr g) (hST _ hb.1)
      rw [hg]
      exact KRel.ite (fun _ => KRel.lokal _ _ _ _ _ rfl hsp) (fun _ => KRel.none_l _)
  | exchange g neuE hw hL rest =>
      simp only [nB, Bool.and_eq_true] at hb
      have h1 := hW.lese Λ (.inr g :: neuE.orte)
      have hg : ((sp₁.welt spur).lese Λ (.inr g :: neuE.orte)).globs g =
          ((sp₂.welt spur).lese Λ (.inr g :: neuE.orte)).globs g := hsp (.inr g) (hST _ hb.1.1)
      simp only [kDann]
      rw [hg, h1.eval neuE (alle_von hST hb.1.2) _]
      exact KRel.lokal _ _ _ _ _ (h1.schreibGlob g Λ _).1 (h1.schreibGlob g Λ _).2
  | narrow e lo' hi' sonst rest =>
      simp only [nB, Bool.and_eq_true] at hb
      have he' := (hW.lese Λ e.orte).eval e (alle_von hST hb.1.1) ρ
      have hn := congrArg Zahl.n he'
      simp only [kDann]
      refine KRel.dite' (by rw [hn]) (fun h₁ h₂ => KRel.lokalEnv _ _ _ ?_ _ rfl hsp)
        (fun _ _ => KRel.lokal _ _ _ _ _ rfl hsp)
      congr 1
      exact zahl_ext hn
  | pruefung c sonst rest =>
      simp only [nB, Bool.and_eq_true] at hb
      simp only [kDann]
      rw [(hW.lese Λ c.orte).eval c (alle_von hST hb.1.1) ρ]
      exact KRel.ite (fun _ => KRel.lokal _ _ _ _ _ rfl hsp)
        (fun _ => KRel.lokal _ _ _ _ _ rfl hsp)
  | gleit op a b lo hi rest =>
      simp only [nB, Bool.and_eq_true] at hb
      simp only [kDann]
      have h1 := hW.lese Λ (a.orte ++ b.orte)
      rw [h1.eval a (alle_von hST hb.1.1) ρ, h1.eval b (alle_von hST hb.1.2) ρ]
      generalize gleitPasst lo hi _ = x
      cases x with
      | none => exact KRel.none_l _
      | some v => exact KRel.lokal _ _ _ _ _ rfl hsp
  | gleitLit q lo hi rest =>
      simp only [kDann]
      generalize gleitPasst lo hi _ = x
      cases x with
      | none => exact KRel.none_l _
      | some v => exact KRel.lokal _ _ _ _ _ rfl hsp
  | gleitVon e lo hi rest =>
      simp only [nB, Bool.and_eq_true] at hb
      simp only [kDann]
      rw [(hW.lese Λ e.orte).eval e (alle_von hST hb.1) ρ]
      generalize gleitPasst lo hi _ = x
      cases x with
      | none => exact KRel.none_l _
      | some v => exact KRel.lokal _ _ _ _ _ rfl hsp
  | gleitNarrow e lo hi sonst rest =>
      simp only [nB, Bool.and_eq_true] at hb
      simp only [kDann]
      rw [(hW.lese Λ e.orte).eval e (alle_von hST hb.1.1) ρ]
      generalize gleitPasst lo hi _ = x
      cases x with
      | none => exact KRel.lokal _ _ _ _ _ rfl hsp
      | some v => exact KRel.lokal _ _ _ _ _ rfl hsp

include hAx in
theorem kr_rel (hO : OrakelTreu T AxT O) (hRL : RegLokal O) (hsp : SpeicherGleich T sp₁ sp₂)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (ρ : Env D Γ)
    (r : GRest D (vertragVon D f) l Γ Λ) (hr : r.nR S Ax) :
    KRel T (kr P O passes st f rho spur sp₁ ρ r) (kr P O passes st f rho spur sp₂ ρ r) := by
  have hW := WRel.welt hsp spur
  cases r with
  | ende e => exact kEnde_rel hST hAx P O passes st f rho spur hO hsp ρ e hr
  | dann b k => exact kDann_rel hST hAx P O passes st f rho spur hO hRL hsp ρ b k hr.1 hr.2
  | schrumpf k =>
      cases ρ
      exact KRel.lokal _ _ _ _ _ rfl hsp
  | frei L k => exact KRel.lokal _ _ _ _ _ rfl hsp
  | trav t inv body ks k =>
      simp only [GRest.nR] at hr
      cases ks with
      | nil =>
          simp only [kr]
          rw [(hW.lese Λ inv.orte).eval inv (alle_von hST hr.1) ρ]
          exact KRel.ite (fun _ => KRel.lokal _ _ _ _ _ rfl hsp) (fun _ => KRel.none_l _)
      | cons i is =>
          simp only [kr]
          rw [(hW.lese Λ inv.orte).eval inv (alle_von hST hr.1) ρ]
          exact KRel.ite (fun _ => KRel.lokal _ _ _ _ _ rfl hsp) (fun _ => KRel.none_l _)
  | travRest t inv body is k =>
      cases ρ
      exact KRel.lokal _ _ _ _ _ rfl hsp
  | wieder n bis body ueber k =>
      simp only [GRest.nR] at hr
      cases n with
      | zero => exact KRel.lokal _ _ _ _ _ rfl hsp
      | succ n =>
          simp only [kr]
          rw [(hW.lese Λ bis.orte).eval bis (alle_von hST hr.1) ρ]
          exact KRel.ite (fun _ => KRel.lokal _ _ _ _ _ rfl hsp)
            (fun _ => KRel.lokal _ _ _ _ _ rfl hsp)
  | wiederRest n bis body ueber k => exact KRel.lokal _ _ _ _ _ rfl hsp
  | ewig a n inv body k =>
      simp only [GRest.nR] at hr
      cases n with
      | zero => exact KRel.none_l _
      | succ n =>
          simp only [kr]
          rw [(hW.lese Λ inv.orte).eval inv (alle_von hST hr.1) ρ]
          exact KRel.ite (fun _ => KRel.lokal _ _ _ _ _ rfl hsp) (fun _ => KRel.none_l _)
  | ewigRest a n inv body k => exact KRel.lokal _ _ _ _ _ rfl hsp
  | wartet b k => exact KRel.none_l _
  | wartetSonst n err b k => exact KRel.none_l _
  | abbruch k => exact KRel.none_l _

end Schritt

/-- **Step consistency for one thread, over the ghost-free state
    (`schrittK_rel`).** The head residue of `k` passes the flow check for
    `S` and `Ax`; `S ⊆ T`, `Ax ⊆ AxT`, the oracle is faithful on `T` for
    `AxT`, registers are local. Two memories that agree on `T`: the two
    steps, if both exist, give the same ghost-free state and memories that
    agree on `T`. -/
theorem schrittK_rel {S T : D.Tab ⊕ D.Glob → Bool} {Ax AxT : D.Ax → Bool}
    (hST : ∀ c, S c = true → T c = true) (hAx : ∀ a, Ax a = true → AxT a = true)
    (P : Programm D) (O : Orakel D) (passes : Nat) (hO : OrakelTreu T AxT O) (hRL : RegLokal O)
    (k : KFaden D) (hk : k.kopf.rest.2.2.2.2.nR S Ax) {sp₁ sp₂ : Speicher D}
    (hsp : SpeicherGleich T sp₁ sp₂) :
    KRel T (kSchrittK P O passes k sp₁) (kSchrittK P O passes k sp₂) :=
  kr_rel hST hAx P O passes k.stapel k.kopf.f k.kopf.rho k.spur hO hRL hsp _ _ hk

end Gabbro.Grammatik
