module

public import Grammatik.Logik.Fortschritt.KostenG.T1.Scoped

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-- Both answer channels resume a suspended caller without increasing its
    potential or introducing a callee absent from its saved source. -/
private theorem antwortRestG_kosten {V : Vertrag D} (g : D.Fn)
    (a : ErgVal D (vertragVon D g).erg ⊕ Fin (vertragVon D g).gruende)
    (x y : Σ l : Bool, Σ Γ : Ctx, Σ Λ : List (Res D), Env D Γ × GRest D V l Γ Λ)
    (ha : antwortRestG g a x = some y) (pa : Nat)
    (c : D.Fn → Nat) (Z : D.Fn → Bool) (ZS : Nat → Bool) (EW : Bool) :
    (rufeR Z ZS EW x.2.2.2.2 = true → rufeR Z ZS EW y.2.2.2.2 = true) ∧
      potRest c pa y.2.2.2.2 ≤ potRest c pa x.2.2.2.2 := by
  obtain ⟨l, Γ, Λ, ρ, r⟩ := x
  cases a with
  | inl v =>
      cases r with
      | wartet b k | wartetSonst _ _ b k =>
          simp only [antwortRestG] at ha
          split at ha
          · simp only [Option.some.injEq] at ha
            subst y
            simp only [rufeR, potRest, Bool.and_eq_true]
            exact ⟨by simp_all, by omega⟩
          · cases ha
      | _ =>
          simp only [antwortRestG, Option.some.injEq] at ha
          subst y
          exact ⟨id, Nat.le_refl _⟩
  | inr grund =>
      cases r with
      | wartetSonst n err b k =>
          simp only [antwortRestG] at ha
          split at ha
          · simp only [Option.some.injEq] at ha
            subst y
            simp only [rufeR, potRest, rufeB_alsBlock, kostenBlock_alsBlock, Bool.and_eq_true]
            exact ⟨fun h => ⟨h.1.1, h.2⟩, by omega⟩
          · cases ha
      | _ => simp only [antwortRestG, reduceCtorEq] at ha

/-- Delivery either completes a zero-potential root, or pops and resumes
    a caller under the caller's own cost table. -/
theorem rufAntwortG_kosten {z z' : RufFadenG D} {vor σ : World D}
    {a : ErgVal D (vertragVon D z.kopf.f).erg ⊕ Fin (vertragVon D z.kopf.f).gruende}
    (ha : rufAntwortG z vor σ a = some z') (pa : Nat) :
    (z'.stapel = z.stapel ∧ ∀ (c : D.Fn → Nat) (Z : D.Fn → Bool)
      (ZS : Nat → Bool) (EW : Bool),
      rufeR Z ZS EW z'.kopf.rest.2.2.2.2 = true ∧ potRest c pa z'.kopf.rest.2.2.2.2 = 0) ∨
    (∃ (caller : RufRahmenG D) (rst : List (RufRahmenG D)),
      z.stapel = caller :: rst ∧ z'.stapel = rst ∧
      ∀ (c : D.Fn → Nat) (Z : D.Fn → Bool) (ZS : Nat → Bool) (EW : Bool),
        (rufeR Z ZS EW caller.rest.2.2.2.2 = true →
          rufeR Z ZS EW z'.kopf.rest.2.2.2.2 = true) ∧
        potRest c pa z'.kopf.rest.2.2.2.2 ≤ potRest c pa caller.rest.2.2.2.2) := by
  cases hst : z.stapel with
  | nil =>
      simp only [rufAntwortG, hst, Option.some.injEq] at ha
      subst z'
      exact Or.inl ⟨rfl, fun _ _ _ _ => ⟨rfl, rfl⟩⟩
  | cons caller rst =>
      obtain ⟨r, hr⟩ : ∃ r, antwortRestG z.kopf.f a caller.rest = some r := by
        cases hr : antwortRestG z.kopf.f a caller.rest with
        | none => simp [rufAntwortG, hst, hr] at ha
        | some r => exact ⟨r, rfl⟩
      simp [rufAntwortG, hst, hr] at ha
      subst z'
      exact Or.inr ⟨caller, rst, rfl, rfl,
        fun c Z ZS EW => antwortRestG_kosten _ _ _ _ hr pa c Z ZS EW⟩

end Gabbro.Grammatik
