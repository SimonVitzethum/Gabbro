/- Correctness of finite universal and existential Boolean folds. -/
import Stage0.Senke.Ausdruck.Quant.Bind
import Stage0.Senke.Ausdruck.Quant.Indices

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat}

def quantVal (all : Bool) {α : Type} (xs : List α) (p : α → Bool) : Bool :=
  if all then xs.all p else xs.any p

theorem quantC_ok {fp : Runner.W} {K d : Nat} {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    (all : Bool) (count : Int) (cb : List II) (p : Zahl 0 (count - 1) → Bool)
    (hc : count.toNat < 2 ^ 31) (hd : d + 3 < K)
    (ih : ∀ k m pc, Pre L m pc fp K (d + 3) cb (Env.cons (show Wert D (.index count) from k) ρ) W reserved →
      Ok m pc fp K (d + 3) cb (fun w => w = if p k then 1 else 0)) :
    ∀ n j, j + n ≤ count.toNat → ∀ m pc,
      Pre L m pc fp K d (quantC all (frei Γ reserved) d cb j n) ρ W reserved →
      Ok m pc fp K d (quantC all (frei Γ reserved) d cb j n) (fun w => w = if quantVal all (idxAb count j n) p then 1 else 0)
  | 0, j, _, m, pc, hp => by
    simp only [quantC, idxAb_zero, quantVal, List.all_nil, List.any_nil] at hp ⊢
    cases all <;> exact const_ok hp (by decide) (by omega)
  | n + 1, j, hj, m, pc, hp => by
    obtain ⟨x, hx, hxs⟩ := idxAb_succ count j n (by omega)
    have hp' : Pre L m pc fp K d
        (quantC all (frei Γ reserved) d cb (j + 1) n ++ quantBindC (frei Γ reserved) (d + 1) j cb ++
          [ci (if all then 8 else 9) d d (d + 1)]) ρ W reserved := hp
    have hctx := hp.ctx
    have hbind : ∀ m pc, Pre L m pc fp K (d + 1) (quantBindC (frei Γ reserved) (d + 1) j cb) ρ W reserved →
        Ok m pc fp K (d + 1) (quantBindC (frei Γ reserved) (d + 1) j cb) (fun w => w = if p x then 1 else 0) := by
      intro m pc hp
      have hp'' : Pre L m pc fp K (d + 1) (quantBindC (frei Γ reserved) (d + 1) x.n cb) ρ W reserved := by rw [hx]; exact hp
      have hh := quantBind_ok (n := count) (k := x) (by rw [hx]; exact lit32_nat (by omega))
        (by omega) (by omega) hp'' (by simpa [Nat.add_assoc] using ih x)
      rw [← hx]
      exact hh
    refine bin_ok (quantC_ok all count cb p hc hd ih n (j + 1) (by omega)) hbind
      (g := fun a b => some (if all then a &&& b else a ||| b)) ?_ ?_ ?_ (by omega) hp'
    · intro a b ha hb
      refine ⟨_, rfl, ?_⟩
      rw [ha, hb, hxs]
      cases all <;> simp only [quantVal, Bool.false_eq_true, ite_false, ite_true, List.all_cons, List.any_cons]
      · rw [or_word, Bool.or_comm]
      · rw [and_word, Bool.and_comm]
    · cases all <;> rfl
    · cases all <;> decide

theorem quantL_ok {fp : Runner.W} {K d : Nat} {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc : Runner.W} {c : List II} {top : Nat}
    (all : Bool) (count : Int) (body : Option (List II × Nat)) (p : Zahl 0 (count - 1) → Bool)
    (h : quantL all (frei Γ reserved) d count body = some (c, top)) (hK : top ≤ K)
    (ih : ∀ cb tb, body = some (cb, tb) → tb ≤ K → ∀ k m pc,
      Pre L m pc fp K (d + 3) cb (Env.cons (show Wert D (.index count) from k) ρ) W reserved →
      Ok m pc fp K (d + 3) cb (fun w => w = if p k then 1 else 0))
    (hp : Pre L m pc fp K d c ρ W reserved) :
    Ok m pc fp K d c (fun w => w = if quantVal all (alleIndizes count) p then 1 else 0) := by
  simp only [quantL] at h
  split at h
  · next hz =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have he : alleIndizes count = [] := by simp [alleIndizes, hz]
      simp only [he, quantVal, List.all_nil, List.any_nil]
      cases all <;> exact const_ok hp (by decide) (by omega)
  · simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨cb, tb⟩, hb, h⟩ := h
    split at h
    · next hlen =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [alleIndizes_ab]
        exact quantC_ok all count cb p hlen.1 (by omega) (ih cb tb hb (by omega)) _ 0 (by omega) m pc hp
    · cases h

end Gabbro.Stage0.Senke
