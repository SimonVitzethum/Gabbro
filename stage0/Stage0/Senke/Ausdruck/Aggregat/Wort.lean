/- Subject: One shared composition rule for operations on lowered word values. -/
import Stage0.Senke.Ausdruck.Wenn

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat}

theorem wordL_ok {fp : Runner.W} {K d top o : Nat} {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc : Runner.W} {a b : Option (List II × Nat)} {c : List II}
    {Pa Pb P : Runner.W → Prop} {g : Runner.W → Runner.W → Option Runner.W}
    (h : wordL o d a b = some (c, top)) (hK : top ≤ K)
    (iha : ∀ ca ta, a = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W reserved → Ok m pc fp K d ca Pa)
    (ihb : ∀ cb tb, b = some (cb, tb) → tb ≤ K → ∀ m pc,
      Pre L m pc fp K (d + 1) cb ρ W reserved → Ok m pc fp K (d + 1) cb Pb)
    (hg : ∀ wa wb, Pa wa → Pb wb → ∃ r, g wa wb = some r ∧ P r)
    (hop : op o = bin g) (ho : o < 256) (hp : Pre L m pc fp K d c ρ W reserved) :
    Ok m pc fp K d c P := by
  simp only [wordL, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨⟨ca, ta⟩, ha, ⟨cb, tb⟩, hb, hc⟩ := h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hc
  exact bin_ok (iha ca ta ha (by omega)) (ihb cb tb hb (by omega)) hg hop ho (by omega) hp

/-- Apply a word operation against a literal, retaining a single operand's induction hypothesis. -/
theorem wordK_ok {fp : Runner.W} {K d top o : Nat} {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {m : Runner.Mem} {pc : Runner.W} {a : Option (List II × Nat)} {c : List II}
    {Pa P : Runner.W → Prop} {g : Runner.W → Runner.W → Option Runner.W} {k : Int}
    (h : wordK o d a k = some (c, top)) (hK : top ≤ K) (hk : lit32 k = true)
    (ih : ∀ ca ta, a = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W reserved → Ok m pc fp K d ca Pa)
    (hg : ∀ wa, Pa wa → ∃ r, g wa (BitVec.ofInt 64 k) = some r ∧ P r)
    (hop : op o = bin g) (ho : o < 256) (hp : Pre L m pc fp K d c ρ W reserved) :
    Ok m pc fp K d c P := by
  refine wordL_ok h hK ih (Pb := fun w => w = BitVec.ofInt 64 k) ?_ ?_ hop ho hp
  · intro cb tb hb htb m pc hp
    cases hb
    exact const_ok hp hk (by omega)
  · intro wa wb ha hb
    subst wb
    exact hg wa ha
end Gabbro.Stage0.Senke
