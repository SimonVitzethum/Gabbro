/- Subject: Literal, concatenation and truncation of short string values. -/
import Stage0.Senke.Ausdruck.Aggregat.Wort

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {Λ : List (Res D)} {Γ : Ctx}
variable {σ₀ σ : World D} {fp : Runner.W} {K d top : Nat} {W : Runner.Mem → Prop}
variable {ρ : Env D Γ} {c : List II} {m : Runner.Mem} {pc : Runner.W}

theorem strLit_ok {n : Nat} (bs : List (Zahl 0 255)) (hb : bs.length ≤ n)
    (h : lowE L (Γ := Γ) (Λ := Λ) (.strLit bs hb) d = some (c, top))
    (hK : top ≤ K) (hp : Pre L m pc fp K d c ρ W) :
    Ok m pc fp K d c (Enc L (.str n) (eval σ₀ (Expr.strLit (Λ := Λ) bs hb) σ ρ)) := by
  simp only [lowE_eqs] at h
  split at h
  · next hn =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have := strN_range bs
    exact (const_ok hp (lit32_nat (by omega)) (by omega)).mono fun w hw =>
      ⟨hn, by simpa only [eval, BitVec.ofInt_natCast] using hw⟩
  · cases h

theorem strCat_ok {n q : Nat} (s : Expr D Γ Λ (.str n)) (t : Expr D Γ Λ (.str q))
    (ihs : ∀ ca ta, lowE L s d = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W → Ok m pc fp K d ca (Enc L (.str n) (eval σ₀ s σ ρ)))
    (iht : ∀ ca ta, lowE L t d = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W → Ok m pc fp K d ca (Enc L (.str q) (eval σ₀ t σ ρ)))
    (h : lowE L (.strCat s t) d = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W) :
    Ok m pc fp K d c (Enc L (.str (n + q)) (eval σ₀ (.strCat s t) σ ρ)) := by
  simp only [lowE_eqs] at h
  split at h
  · next hn =>
    split at h
    · next hz =>
      have hs : (eval σ₀ s σ ρ).1 = [] := List.eq_nil_of_length_eq_zero (by have := (eval σ₀ s σ ρ).2; omega)
      exact (iht c top h hK m pc hp).mono fun w hw => by
        exact ⟨hn, by simpa [eval, strCatW, hs] using hw.2⟩
    · next hz =>
      have ht : (eval σ₀ t σ ρ).1 = [] := List.eq_nil_of_length_eq_zero (by have := (eval σ₀ t σ ρ).2; omega)
      exact (ihs c top h hK m pc hp).mono fun w hw => by
        exact ⟨hn, by simpa [eval, strCatW, ht] using hw.2⟩
  · cases h

theorem strWeit_ok {n : Nat} (q : Nat) (s : Expr D Γ Λ (.str n))
    (ih : ∀ ca ta, lowE L s d = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W → Ok m pc fp K d ca (Enc L (.str n) (eval σ₀ s σ ρ)))
    (h : lowE L (.strWeit q s) d = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W) :
    Ok m pc fp K d c (Enc L (.str q) (eval σ₀ (.strWeit q s) σ ρ)) := by
  simp only [lowE_eqs] at h
  split at h
  · next hn =>
    split at h
    · next hz =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact (const_ok hp (by decide) (by omega)).mono fun w hw => by
        exact ⟨hn.2, by simpa [eval, strWeitW, hz, strN] using hw⟩
    · next hz =>
      have hlen : (eval σ₀ s σ ρ).1.length ≤ q := by have := (eval σ₀ s σ ρ).2; omega
      exact (ih c top h hK m pc hp).mono fun w hw =>
        ⟨hn.2, by simpa [eval, strWeitW, List.take_of_length_le hlen] using hw.2⟩
  · cases h
end Gabbro.Stage0.Senke
