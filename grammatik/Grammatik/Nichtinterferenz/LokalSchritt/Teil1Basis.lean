module

public import Grammatik.Nichtinterferenz.Lokal

@[expose] public section



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

/-- Two `Option` matches with equal discriminants agree when every `some`
    arm agrees and the `none` arms agree. Used for the deterministic
    consuming choice (`verbrauchWahl`), whose discriminant is a pure
    function of low-equivalent member/edge reads. -/
theorem KRel.opt {α : Type} {x₁ x₂ : Option α} (hx : x₁ = x₂)
    {A₁ A₂ : α → KErg D} {B₁ B₂ : KErg D}
    (hs : ∀ v, KRel T (A₁ v) (A₂ v)) (hn : KRel T B₁ B₂) :
    KRel T (match x₁ with | some v => A₁ v | none => B₁)
      (match x₂ with | some v => A₂ v | none => B₂) := by
  subst hx
  cases x₂ with
  | some v => exact hs v
  | none => exact hn

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
        exact ⟨by simp only [h.1], h.2⟩
      · exact KRel.none_l _
  | wartetSonst n err restb k =>
      simp only [kBinde]
      split
      · intro a b ha hb
        simp only [Option.some.injEq] at ha hb
        subst ha hb
        exact ⟨by simp only [h.1], h.2⟩
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
      exact ⟨by simp only [h.1], h.2⟩

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

end Gabbro.Grammatik
