/- Subject: The option-presence test, kept outside the main expression recursion. -/
module
public import Stage0.Senke.Ausdruck.Lesen
public import Stage0.Senke.Ausdruck.Aggregat.Scalar
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {reserved : Nat}

/-- Small options share their complete index word; larger options put a tag
    before the same complete integer encoding used everywhere else. -/
theorem some_ok {L : Lay D} {Λ : List (Res D)} {Γ : Ctx} {n : Int}
    (e : Expr D Γ Λ (.index n)) {σ₀ σ : World D} {fp : Runner.W} {K d top : Nat}
    {W : Runner.Mem → Prop} {ρ : Env D Γ} {c : List II} {m : Runner.Mem} {pc : Runner.W}
    (ih : ∀ d ca ta, lowE L e d reserved = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K d ca ρ W reserved → ValueOk L m pc fp K d ca (.index n) (eval σ₀ e σ ρ))
    (h : lowE L (.some e) d reserved = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c (.opt n) (eval σ₀ (.some e) σ ρ) := by
  simp only [lowE_eqs] at h
  split at h
  · next short =>
    obtain ⟨m', run, changed, value⟩ := ih d c top h hK m pc hp
    have width : integerWords 0 (n - 1) = 1 := integerWords_unsigned (by decide) (by omega)
    refine ⟨m', run, changed, trivial, ?_⟩
    simpa only [encodeWords, width, integerEncoding, if_pos short, eval, optN] using value.2
  · next long =>
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨ce, te⟩, he, rfl, rfl⟩ := h
    have childTop := lowE_top e (d + 1) ce te he
    obtain ⟨m1, run1, changed1, w, read1, equal⟩ := const_ok hp.left (by decide) (by omega)
    subst w
    have next := hp.next changed1 (Nat.le_succ d) (by omega)
    obtain ⟨m2, run2, changed2, value⟩ := ih (d + 1) ce te he
      (Nat.le_trans (Nat.le_max_left _ _) hK) m1 _ next
    refine ⟨m2, ?_, changed1.trans (changed2.mono (Nat.le_succ d)), trivial, ?_⟩
    · simpa only [List.length_append, pc_add] using run1.trans run2
    · change WordsAt m2 fp d (encodeWords L (.opt n) (some (eval σ₀ e σ ρ)))
      simp only [encodeWords, if_neg long]
      rw [show (1 : Runner.W) :: integerEncoding (integerWords 0 (n - 1)) (eval σ₀ e σ ρ).n =
        [1] ++ integerEncoding (integerWords 0 (n - 1)) (eval σ₀ e σ ρ).n from rfl,
        wordsAt_append]
      constructor
      · intro i hi
        have zero : i = 0 := by simpa using hi
        subst i
        rw [agree_rd_low changed2 next.frame.room (by omega) (by omega)]
        exact read1
      · exact value.2

theorem istSome_ok {L : Lay D} {Λ : List (Res D)} {Γ : Ctx} {n : Int}
    (e : Expr D Γ Λ (.opt n)) {σ₀ σ : World D} {fp : Runner.W} {K d top : Nat}
    {W : Runner.Mem → Prop} {ρ : Env D Γ} {c : List II} {m : Runner.Mem} {pc : Runner.W}
    (ih : ∀ ce te, lowE L e d reserved = some (ce, te) → te ≤ K → ∀ m pc,
      Pre L m pc fp K d ce ρ W reserved → ValueOk L m pc fp K d ce (.opt n) (eval σ₀ e σ ρ))
    (h : lowE L (.istSome e) d reserved = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) : ValueOk L m pc fp K d c .bool (eval σ₀ (.istSome e) σ ρ) := by
    refine Ok.value ?_ rfl
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
        (fun m pc hp => bin_ok (fun m pc hp => (ih ce te he (by omega) m pc hp).word hn)
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
