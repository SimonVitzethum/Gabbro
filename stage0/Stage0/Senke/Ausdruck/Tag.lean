/-
  File:      stage0/Stage0/Senke/Ausdruck/Tag.lean
  Subject:   An injective word representation for tagged values: tag + 256 * payload offset.
-/
import Stage0.Senke.Ausdruck.Top

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR
variable {D : Deklaration} {L : Lay D}

theorem sumOff_lt {cs : List (Option (Int × Int))} (h : sumFits cs = true)
    (i : Fin cs.length) (v : Nutzlast (cs.get i)) : sumOff (cs.get i) v < 2 ^ 56 := by
  simp only [sumFits, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  have hc := h.2 _ (List.get_mem cs i)
  generalize cs.get i = c at v hc ⊢
  cases c with
  | none => simp [sumOff]
  | some p =>
    rcases p with ⟨lo, hi⟩
    simp only [decide_eq_true_eq] at hc
    have := v.lo_le; have := v.le_hi
    simp only [sumOff]
    omega

theorem sumN_lt {cs : List (Option (Int × Int))} (h : sumFits cs = true)
    (v : Wert D (.sum cs)) : sumN v < 2 ^ 64 := by
  have := sumOff_lt h v.1 v.2
  have hi := v.1.isLt
  have hl : cs.length ≤ 256 := by
    simp only [sumFits, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1
  simp only [sumN]
  omega

theorem sumN_tag {cs : List (Option (Int × Int))} (h : sumFits cs = true)
    (v : Wert D (.sum cs)) : sumN v % 256 = v.1.val := by
  have hl : cs.length ≤ 256 := by
    simp only [sumFits, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1
  have := v.1.isLt
  simp only [sumN]
  omega

theorem sumN_off {cs : List (Option (Int × Int))} (h : sumFits cs = true)
    (v : Wert D (.sum cs)) : sumN v / 256 = sumOff (cs.get v.1) v.2 := by
  have hl : cs.length ≤ 256 := by
    simp only [sumFits, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1
  have := v.1.isLt
  simp only [sumN]
  omega

theorem sumOff_inj (c : Option (Int × Int)) (a b : Nutzlast c) (h : sumOff c a = sumOff c b) : a = b := by
  cases c with
  | none => cases a; cases b; rfl
  | some p =>
    rcases p with ⟨lo, hi⟩
    have := a.lo_le; have := b.lo_le
    have hn : a.n = b.n := by simp only [sumOff] at h; omega
    cases a; cases b; cases hn; rfl

theorem encSum_inj {cs : List (Option (Int × Int))} {a b : Wert D (.sum cs)} {w : Runner.W}
    (ha : Enc L (.sum cs) a w) (hb : Enc L (.sum cs) b w) : a = b := by
  have hn : sumN a = sumN b := by
    have hw := congrArg BitVec.toNat (ha.2.symm.trans hb.2)
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (sumN_lt ha.1 a),
      Nat.mod_eq_of_lt (sumN_lt hb.1 b)] at hw
    exact hw
  have hi : a.1 = b.1 := Fin.ext (by rw [← sumN_tag ha.1 a, ← sumN_tag hb.1 b, hn])
  rcases a with ⟨i, a⟩; rcases b with ⟨j, b⟩
  cases hi
  congr 1
  apply sumOff_inj
  have := congrArg (· / 256) hn
  rw [sumN_off (D := D) ha.1 ⟨i, a⟩, sumN_off (D := D) hb.1 ⟨i, b⟩] at this
  exact this

theorem sumWord_tag {cs : List (Option (Int × Int))} (h : sumFits cs = true)
    (v : Wert D (.sum cs)) : BitVec.ofNat 64 (sumN v) &&& 255 = BitVec.ofNat 64 v.1.val := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (sumN_lt h v)]
  change sumN v &&& (2 ^ 8 - 1) = v.1.val % 2 ^ 64
  rw [Nat.and_two_pow_sub_one_eq_mod, sumN_tag (D := D) h v]
  have := v.1.isLt
  have hl : cs.length ≤ 256 := by
    simp only [sumFits, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1
  omega

theorem sumWord_off {cs : List (Option (Int × Int))} (h : sumFits cs = true)
    (v : Wert D (.sum cs)) : BitVec.ofNat 64 (sumN v) >>> 8 = BitVec.ofNat 64 (sumOff (cs.get v.1) v.2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (sumN_lt h v),
    Nat.shiftRight_eq_div_pow]
  change sumN v / 256 = sumOff (cs.get v.1) v.2 % 2 ^ 64
  rw [sumN_off (D := D) h v, Nat.mod_eq_of_lt (by have := sumOff_lt h v.1 v.2; omega)]

theorem sumWord_payload {cs : List (Option (Int × Int))} (h : sumFits cs = true)
    (i : Fin cs.length) {lo hi : Int} (hc : cs.get i = some (lo, hi)) (v : Nutzlast (cs.get i)) :
    (BitVec.ofNat 64 (sumN (D := D) ⟨i, v⟩) >>> 8) + BitVec.ofInt 64 lo =
      BitVec.ofInt 64 (hc ▸ v).n := by
  rw [sumWord_off (D := D) h ⟨i, v⟩]
  change BitVec.ofNat 64 (sumOff (cs.get i) v) + BitVec.ofInt 64 lo = BitVec.ofInt 64 (hc ▸ v).n
  generalize he : cs.get i = c at v hc ⊢
  subst hc
  simp only [sumOff]
  have hv := v.lo_le
  rw [← BitVec.ofInt_natCast, ← BitVec.ofInt_add]
  congr 1
  omega

/-- Both a bare arm and a nonzero, negative payload have different words. -/
theorem encSum_inj_zeuge :
    let cs := [none, some (-7, 13)]
    let a : Wert D (.sum cs) := ⟨⟨1, by decide⟩, ⟨-2, by decide, by decide⟩⟩
    Enc L (.sum cs) a (1281 : Runner.W) ∧
      (∀ b, Enc L (.sum cs) b (1281 : Runner.W) → b = a) := by
  dsimp
  have h : Enc L (.sum [none, some (-7, 13)])
      (D := D) ⟨⟨1, by decide⟩, ⟨-2, by decide, by decide⟩⟩ 1281 := by constructor <;> rfl
  exact ⟨h, fun _ hb => encSum_inj hb h⟩

set_option maxRecDepth 2048 in
/-- Accept both exact limits and refuse the first tag count or payload width beyond them. -/
theorem sumFits_zeuge :
    sumFits (List.replicate 256 none) = true ∧
    sumFits (List.replicate 257 none) = false ∧
    sumFits [some (0, 2 ^ 56 - 1)] = true ∧
    sumFits [some (0, 2 ^ 56)] = false := by decide

section
variable [Kern]
/-- Construct a sum word from its payload expression, using wrapping word arithmetic. -/
theorem packSum_ok {m : Runner.Mem} {pc fp : Runner.W} {K d tag : Nat} {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {lo hi : Int} {v : Zahl lo hi} {ce : List II × Nat}
    (hl : lit32 lo = true) (htag : tag < 256) (hK : d + 2 ≤ K)
    (ih : ∀ m pc, Pre L m pc fp K d ce.1 ρ W → Ok m pc fp K d ce.1 (Enc (D := D) L (.int lo hi) v))
    (hp : Pre L m pc fp K d (packSum d lo tag ce).1 ρ W) :
    Ok m pc fp K d (packSum d lo tag ce).1
      (fun w => w = BitVec.ofNat 64 (tag + 256 * sumOff (some (lo, hi)) v)) := by
  simp only [packSum, bin2] at hp ⊢
  refine bin_ok (Pa := fun w => w = BitVec.ofInt 64 ((v.n - lo) * 256))
    (fun m pc hp => bin_ok (Pa := fun w => w = BitVec.ofInt 64 (v.n - lo))
      (fun m pc hp => bin_ok ih (fun m pc hp => const_ok hp hl (by omega))
        (g := fun a b => some (a - b))
        (fun a b ha hb => ⟨_, rfl, by rw [ha, hb, ← ofInt_sub']⟩) rfl (by decide) (by omega) hp)
      (fun m pc hp => const_ok hp (by decide) (by omega)) (g := fun a b => some (a * b))
      (fun a b ha hb => ⟨_, rfl, by rw [ha, hb, ← BitVec.ofInt_mul]⟩) rfl (by decide) (by omega) hp)
    (fun m pc hp => const_ok hp (lit32_nat (by omega)) (by omega)) (g := fun a b => some (a + b))
    (fun a b ha hb => ⟨_, rfl, ?_⟩) rfl (by decide) (by omega) hp
  rw [ha, hb, ← BitVec.ofInt_add, ← BitVec.ofInt_natCast]
  congr 1
  have := v.lo_le
  simp only [sumOff]
  omega
end

end Gabbro.Stage0.Senke
