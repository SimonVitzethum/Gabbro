/- Sequential product arguments preserve prior fields and their canonical encoding. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.Array
public import Stage0.Senke.Ausdruck.Aggregat.ProdArgs
public import Stage0.Senke.Ausdruck.Aggregat.Product
@[expose] public section

variable {currentOld : Bool}

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {Γ : Ctx} {Λ : List (Res D)}
variable {σ₀ σ : World D} {fp : Runner.W} {K reserved : Nat}
variable {W : Runner.Mem → Prop} {ρ : Env D Γ}

/-- Field correctness follows the concrete argument spine, so callers can prove it
    by mutual structural recursion with expression correctness. -/
def ProdFieldsOk (L : Lay D) (σ₀ σ : World D) (fp : Runner.W) (K reserved : Nat)
    (W : Runner.Mem → Prop) (ρ : Env D Γ) : {fs : List Ty} → Args D Γ Λ fs → Prop
  | _, .nil => True
  | _, @Args.cons _ _ _ τ _ e rest =>
    (∀ d ca ta, lowE (currentOld := currentOld) L (reserved := reserved) e d = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W reserved →
        ValueOk L m pc fp K d ca τ (eval σ₀ e σ ρ)) ∧
    ProdFieldsOk L σ₀ σ fp K reserved W ρ rest

/-- Each field hypothesis is reusable at the offset selected by the traversal. -/
theorem prodArgs_ok :
    ∀ {fs} (args : Args D Γ Λ fs), ProdFieldsOk (currentOld := currentOld) L σ₀ σ fp K reserved W ρ args → ∀ d c top,
      prodArgsL (lowE (currentOld := currentOld) L (reserved := reserved)) args d = some (c, top) → top ≤ K →
      ∀ m pc, Pre L m pc fp K d c ρ W reserved →
      Executes m pc fp K d c (fun m' =>
        ProdValid L fs (evalProd σ₀ args σ ρ) ∧
        WordsAt m' fp d (encodeProductFields L fs (evalProd σ₀ args σ ρ)))
  | _, .nil, _, d, c, top, h, hK, m, pc, hp => by
    simp only [prodArgsL, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨m, ?_, Agree.refl _ _ _ _, trivial, ?_⟩
    · simpa using (Star.refl ⟨pc, fp⟩ m)
    · simp [WordsAt, encodeProductFields]
  | _, @Args.cons _ _ _ τ fs e rest, field, d, c, top, h, hK, m, pc, hp => by
    simp only [prodArgsL, bind, Option.bind_eq_some_iff, pure,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨ce, te⟩, he, ⟨cr, tr⟩, hr, rfl, rfl⟩ := h
    have tailTop := prodArgsL_top (lowE (currentOld := currentOld) L (reserved := reserved)) rest _ cr tr hr
    obtain ⟨m1, run1, changed1, head⟩ := field.1 d ce te he (by omega) m pc hp.left
    have next := hp.next changed1 (by omega : d ≤ d + valueWords τ) (by omega)
    obtain ⟨m2, run2, changed2, valid, words⟩ :=
      prodArgs_ok rest field.2 (d + valueWords τ) cr tr hr (by omega) m1 _ next
    have kept := head.agree changed2 (hp.frame.agree changed1) (Nat.le_refl _) (by omega)
    refine ⟨m2, ?_, changed1.trans (changed2.mono (by omega)), ⟨kept.1, valid⟩, ?_⟩
    · simpa only [List.length_append, pc_add] using run1.trans run2
    · rw [encodeProductFields_cons, wordsAt_append]
      exact ⟨kept.2, by simpa only [evalProd, ProdVal.tl, encodeWords_length] using words⟩

/-- Nonempty products already occupy their field span; empty products write zero. -/
theorem prod_ok {name : Nat} {fs : List Ty} (args : Args D Γ Λ fs)
    (fields : ProdFieldsOk (currentOld := currentOld) L σ₀ σ fp K reserved W ρ args)
    {d top : Nat} {c : List II} {m : Runner.Mem} {pc : Runner.W}
    (h : prodL d (prodArgsL (lowE (currentOld := currentOld) L (reserved := reserved)) args d) = some (c, top))
    (hK : top ≤ K) (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c (.prod name fs) (evalProd σ₀ args σ ρ) := by
  simp only [prodL, bind, Option.bind_eq_some_iff, pure,
    Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨code, bound⟩, lower, rfl, rfl⟩ := h
  cases args with
  | nil =>
    simp only [prodArgsL, Option.some.injEq, Prod.mk.injEq] at lower
    obtain ⟨rfl, rfl⟩ := lower
    simp only [if_pos (rfl : d = d)] at hp ⊢
    obtain ⟨m', run, changed, w, read, encoded⟩ := const_ok hp (by decide) (by omega)
    refine ⟨m', run, changed, trivial, ?_⟩
    have zero : w = 0 := by simpa using encoded
    subst w
    erw [encodeWords_prod]; simp only [encodeProduct, if_pos rfl]
    intro i hi
    have index : i = 0 := by simpa using hi
    subst i
    simpa using read
  | cons e tail =>
    rename_i τ rest
    have span := prodArgsL_top (lowE (currentOld := currentOld) L (reserved := reserved)) (.cons e tail) d code bound lower
    have positive := productWords_pos_of_ne_nil (by simp : τ :: rest ≠ [])
    have nonempty : bound ≠ d := by omega
    simp only [if_neg nonempty] at hp ⊢
    exact (prodArgs_ok (.cons e tail) fields d code bound lower (by omega) m pc hp).mono
      (fun _ result => by
        simp only [ValueAt, ValueValid]
        erw [encodeWords_prod]
        simpa only [encodeProduct, if_neg (by simp : τ :: rest ≠ [])] using result)
end Gabbro.Stage0.Senke
