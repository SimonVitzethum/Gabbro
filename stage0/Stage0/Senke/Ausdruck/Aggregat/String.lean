/- Subject: Literal, concatenation and truncation of short string values. -/
import Stage0.Senke.Ausdruck.Aggregat.Wort
import Stage0.Senke.Ausdruck.Aggregat.Materialize
import Stage0.Senke.Ausdruck.Aggregat.Scalar

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat} {Λ : List (Res D)} {Γ : Ctx}
variable {σ₀ σ : World D} {fp : Runner.W} {K d top : Nat} {W : Runner.Mem → Prop}
variable {ρ : Env D Γ} {c : List II} {m : Runner.Mem} {pc : Runner.W}

theorem strCat_ok {n q : Nat} (s : Expr D Γ Λ (.str n)) (t : Expr D Γ Λ (.str q))
    (ihs : ∀ ca ta, lowE L (reserved := reserved) s d = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W reserved → ValueOk L m pc fp K d ca (.str n) (eval σ₀ s σ ρ))
    (iht : ∀ ca ta, lowE L (reserved := reserved) t d = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W reserved → ValueOk L m pc fp K d ca (.str q) (eval σ₀ t σ ρ))
    (h : lowE L (reserved := reserved) (.strCat s t) d = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c (.str (n + q)) (eval σ₀ (.strCat s t) σ ρ) := by
  simp only [lowE_eqs] at h
  split at h
  · next hn =>
    refine Ok.value ?_ (by simp only [valueWords, if_pos hn])
    split at h
    · next hz =>
      have hs : (eval σ₀ s σ ρ).1 = [] := List.eq_nil_of_length_eq_zero (by have := (eval σ₀ s σ ρ).2; omega)
      exact ((iht c top h hK m pc hp).word (by change q ≤ 1; omega)).mono fun w hw => by
        exact ⟨hn, by simpa [eval, strCatW, hs] using hw.2⟩
    · next hz =>
      have ht : (eval σ₀ t σ ρ).1 = [] := List.eq_nil_of_length_eq_zero (by have := (eval σ₀ t σ ρ).2; omega)
      exact ((ihs c top h hK m pc hp).word (by change n ≤ 1; omega)).mono fun w hw => by
        exact ⟨hn, by simpa [eval, strCatW, ht] using hw.2⟩
  · cases h

theorem strWeit_ok {n : Nat} (q : Nat) (s : Expr D Γ Λ (.str n))
    (ih : ∀ ca ta, lowE L (reserved := reserved) s d = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W reserved → ValueOk L m pc fp K d ca (.str n) (eval σ₀ s σ ρ))
    (h : lowE L (reserved := reserved) (.strWeit q s) d = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c (.str q) (eval σ₀ (.strWeit q s) σ ρ) := by
  simp only [lowE_eqs] at h
  split at h
  · next hn =>
    refine Ok.value ?_ (by simp only [valueWords, if_pos hn.2])
    split at h
    · next hz =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact (const_ok hp (by decide) (by omega)).mono fun w hw => by
        exact ⟨hn.2, by simpa [eval, strWeitW, hz, strN] using hw⟩
    · next hz =>
      have hlen : (eval σ₀ s σ ρ).1.length ≤ q := by have := (eval σ₀ s σ ρ).2; omega
      exact ((ih c top h hK m pc hp).word hn.1).mono fun w hw =>
        ⟨hn.2, by simpa [eval, strWeitW, List.take_of_length_le hlen] using hw.2⟩
  · cases h
end Gabbro.Stage0.Senke
