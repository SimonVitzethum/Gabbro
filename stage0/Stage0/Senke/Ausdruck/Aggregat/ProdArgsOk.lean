/- Sequential product arguments preserve prior fields and their canonical encoding. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.Array
public import Stage0.Senke.Ausdruck.Aggregat.ProdArgs
public import Stage0.Senke.Ausdruck.Aggregat.Product
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {Γ : Ctx} {Λ : List (Res D)}
variable {σ₀ σ : World D} {fp : Runner.W} {K reserved : Nat}
variable {W : Runner.Mem → Prop} {ρ : Env D Γ}

/-- Each field hypothesis is reusable at the offset selected by the traversal. -/
theorem prodArgs_ok
    (field : ∀ {τ} (e : Expr D Γ Λ τ) d ca ta,
      lowE L (reserved := reserved) e d = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W reserved →
        ValueOk L m pc fp K d ca τ (eval σ₀ e σ ρ)) :
    ∀ {fs} (args : Args D Γ Λ fs) d c top,
      prodArgsL (lowE L (reserved := reserved)) args d = some (c, top) → top ≤ K →
      ∀ m pc, Pre L m pc fp K d c ρ W reserved →
      Executes m pc fp K d c (fun m' =>
        ProdValid L fs (evalProd σ₀ args σ ρ) ∧
        WordsAt m' fp d (encodeProductFields L fs (evalProd σ₀ args σ ρ)))
  | _, .nil, d, c, top, h, hK, m, pc, hp => by
    simp only [prodArgsL, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨m, ?_, Agree.refl _ _ _ _, trivial, ?_⟩
    · simpa using (Star.refl ⟨pc, fp⟩ m)
    · simp [WordsAt, encodeProductFields]
  | _, @Args.cons _ _ _ τ fs e rest, d, c, top, h, hK, m, pc, hp => by
    simp only [prodArgsL, bind, Option.bind_eq_some_iff, pure,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨ce, te⟩, he, ⟨cr, tr⟩, hr, rfl, rfl⟩ := h
    have headTop := lowE_top e d ce te he
    obtain ⟨m1, run1, changed1, head⟩ := field e d ce te he (by omega) m pc hp.left
    have next := hp.next changed1 (by omega : d ≤ d + valueWords τ) (by omega)
    obtain ⟨m2, run2, changed2, valid, words⟩ :=
      prodArgs_ok field rest (d + valueWords τ) cr tr hr (by omega) m1 _ next
    have kept := head.agree changed2 (hp.frame.agree changed1) (Nat.le_refl _) (by omega)
    refine ⟨m2, ?_, changed1.trans (changed2.mono (by omega)), ⟨kept.1, valid⟩, ?_⟩
    · simpa only [List.length_append, pc_add] using run1.trans run2
    · rw [encodeProductFields_cons, wordsAt_append]
      exact ⟨kept.2, by simpa only [evalProd, ProdVal.tl, encodeWords_length] using words⟩
end Gabbro.Stage0.Senke
