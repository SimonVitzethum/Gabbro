/- Subject: The option-presence test, kept outside the main expression recursion. -/
import Stage0.Senke.Ausdruck.Lesen
namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration}

theorem istSome_ok {L : Lay D} {Λ : List (Res D)} {Γ : Ctx} {n : Int}
    (e : Expr D Γ Λ (.opt n)) {σ₀ σ : World D} {fp : Runner.W} {K d top : Nat}
    {W : Runner.Mem → Prop} {ρ : Env D Γ} {c : List II} {m : Runner.Mem} {pc : Runner.W}
    (ih : ∀ ce te, lowE L e d = some (ce, te) → te ≤ K → ∀ m pc,
      Pre L m pc fp K d ce ρ W → Ok m pc fp K d ce (Enc L (.opt n) (eval σ₀ e σ ρ)))
    (h : lowE L (.istSome e) d = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W) : Ok m pc fp K d c (Enc L .bool (eval σ₀ (.istSome e) σ ρ)) := by
    simp only [lowE_eqs] at h
    split at h
    · next hn =>
      simp only [decide_eq_true_eq] at hn
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨⟨ce, te⟩, he, hc⟩ := h
      simp only [bin2, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      have := lowE_top e d ce te he
      refine bin_ok (cb := [ci 1 (d + 1) 1 0])
        (Pa := fun w => w = if (eval σ₀ e σ ρ).isSome = false then 1 else 0)
        (fun m pc hp => bin_ok (fun m pc hp => ih ce te he (by omega) m pc hp)
          (fun m pc hp => const_ok hp (by decide) (by omega))
          (g := fun x y => some (Runner.IR.bool (x == y))) (fun we wm pe pm => ⟨_, rfl, by
            simp only [Enc] at pe
            rw [pe, pm, bool_word]
            cases hv : eval σ₀ e σ ρ with
            | none => simp [optN]
            | some k =>
              have := k.lo_le; have := k.le_hi
              have hne : k.n ≠ -1 := by omega
              have hb : (BitVec.ofInt 64 (optN (some k)) == BitVec.ofInt 64 (-1)) = false := by
                simp only [optN]
                rw [beq_in (by omega) (by decide)]
                simp [hne]
              simp only [hb, Option.isSome_some, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]⟩) rfl (by decide) (by omega) hp)
        (fun m pc hp => const_ok hp (by decide) (by omega))
        (g := fun x y => some (x ^^^ y)) ?_ rfl (by decide) (by omega) hp
      intro wa wb pa pb
      refine ⟨_, rfl, ?_⟩
      simp only [Enc, eval] at ⊢
      rw [pa, pb]
      by_cases hs : (eval σ₀ e σ ρ).isSome = true
      · simp only [hs, wahr?, Bool.true_eq_false, ↓reduceIte]; decide
      · simp only [Bool.not_eq_true] at hs
        simp only [hs, wahr?, Bool.false_eq_true, ↓reduceIte]; decide
    · cases h

end Gabbro.Stage0.Senke
