/- Count preservation, including the accumulator and index bounds. -/
module
public import Stage0.Senke.Ausdruck.Quant.Satz
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat}

/-- The mathematical accumulator is a natural count, before word encoding. -/
def countVal {α : Type} (xs : List α) (p : α → Bool) : Nat := (xs.filter p).length

theorem countVal_cons {α : Type} (x : α) (xs : List α) (p : α → Bool) :
    countVal (x :: xs) p = countVal xs p + (if p x then 1 else 0) := by
  cases hx : p x <;> simp [countVal, hx]

theorem countVal_idxAb_bound (count j n : Nat)
    (p : Zahl 0 ((count : Int) - 1) → Bool) (h : j + n ≤ count) :
    countVal (idxAb (count : Int) j n) p ≤ n ∧
      j + countVal (idxAb (count : Int) j n) p ≤ count := by
  have filtered := List.length_filter_le p (idxAb (count : Int) j n)
  have indices : (idxAb (count : Int) j n).length ≤ n := by
    unfold idxAb
    have bound := List.length_filterMap_le
      (fun (k : Nat) => if h : (k : Int) ≤ (count : Int) - 1 then
        some (show Zahl 0 ((count : Int) - 1) from ⟨k, by omega, h⟩) else none)
      (List.range' j n)
    simpa only [List.length_range'] using bound
  unfold countVal
  omega

theorem countC_ok {fp : Runner.W} {K d : Nat} {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    (count : Nat) (cb : List II) (p : Zahl 0 ((count : Int) - 1) → Bool)
    (hc : count < 2 ^ 31) (hd : d + 3 < K)
    (ih : ∀ k m pc, Pre L m pc fp K (d + 3) cb
      (Env.cons (show Wert D (.index (count : Int)) from k) ρ) W reserved →
      Ok m pc fp K (d + 3) cb (fun w => w = if p k then 1 else 0)) :
    ∀ n j, j + n ≤ count → ∀ m pc,
      Pre L m pc fp K d (countC (frei Γ reserved) d cb j n) ρ W reserved →
      Ok m pc fp K d (countC (frei Γ reserved) d cb j n)
        (fun w => w = BitVec.ofNat 64 (countVal (idxAb (count : Int) j n) p))
  | 0, j, _, m, pc, hp => by
    simp only [countC, idxAb_zero, countVal, List.filter_nil, List.length_nil] at hp ⊢
    exact const_ok hp (by decide) (by omega)
  | n + 1, j, hj, m, pc, hp => by
    obtain ⟨x, hx, hxs⟩ := idxAb_succ (count : Int) j n (by omega)
    have hp' : Pre L m pc fp K d
        (countC (frei Γ reserved) d cb (j + 1) n ++
          quantBindC (frei Γ reserved) (d + 1) j cb ++ [ci 3 d d (d + 1)]) ρ W reserved := hp
    have hctx := hp.ctx
    have hbind : ∀ m pc, Pre L m pc fp K (d + 1)
        (quantBindC (frei Γ reserved) (d + 1) j cb) ρ W reserved →
        Ok m pc fp K (d + 1) (quantBindC (frei Γ reserved) (d + 1) j cb)
          (fun w => w = if p x then 1 else 0) := by
      intro m pc hp
      have hp'' : Pre L m pc fp K (d + 1)
          (quantBindC (frei Γ reserved) (d + 1) x.n cb) ρ W reserved := by rw [hx]; exact hp
      have hh := quantBind_ok (n := (count : Int)) (k := x)
        (integerWords_word (by omega) (by omega)) (by rw [hx]; exact lit32_nat (by omega))
        (by omega) (by omega) hp'' (by simpa [Nat.add_assoc] using ih x)
      rw [← hx]
      exact hh
    have bounds := countVal_idxAb_bound count (j + 1) n p (by omega)
    have noOverflow : countVal (idxAb (count : Int) (j + 1) n) p + 1 < 2 ^ 64 := by omega
    refine bin_ok (countC_ok count cb p hc hd ih n (j + 1) (by omega)) hbind
      (g := fun a b => some (a + b)) ?_ rfl (by decide) (by omega) hp'
    intro a b ha hb
    refine ⟨_, rfl, ?_⟩
    rw [ha, hb, hxs, countVal_cons]
    cases px : p x <;> simp [px, BitVec.ofNat_add]

theorem countL_ok {fp : Runner.W} {K d : Nat} {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc : Runner.W} {c : List II} {top : Nat}
    (n : Nat) (body : Option (List II × Nat)) (p : Zahl 0 ((n : Int) - 1) → Bool)
    (h : countL (frei Γ reserved) d n body = some (c, top)) (hK : top ≤ K)
    (ih : ∀ cb tb, body = some (cb, tb) → tb ≤ K → ∀ k m pc,
      Pre L m pc fp K (d + 3) cb (Env.cons (show Wert D (.index (n : Int)) from k) ρ) W reserved →
      Ok m pc fp K (d + 3) cb (fun w => w = if p k then 1 else 0))
    (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c (.int 0 (n : Int)) (zaehleWahr n p) := by
  have bounds := countL_bounds h
  refine Ok.value ?_ (integerWords_word (by decide) (by omega))
  change Ok m pc fp K d c (fun w => w = BitVec.ofInt 64 (zaehleWahr n p).n)
  simp only [zaehleWahr, BitVec.ofInt_natCast]
  simp only [countL] at h
  split at h
  · next zero =>
    subst n
    obtain ⟨rfl, rfl⟩ := Option.some.inj h
    simp only [alleIndizes, Int.toNat_zero, List.range_zero, List.filterMap_nil,
      List.filter_nil, List.length_nil]
    exact const_ok hp (by decide) (by omega)
  · simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨cb, tb⟩, hb, h⟩ := h
    split at h
    · next budget =>
      obtain ⟨rfl, rfl⟩ := Option.some.inj h
      rw [alleIndizes_ab, Int.toNat_natCast]
      exact countC_ok n cb p budget.1 (by omega) (ih cb tb hb (by omega)) n 0 (by omega) m pc hp
    · cases h

end Gabbro.Stage0.Senke
