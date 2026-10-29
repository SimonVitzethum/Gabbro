/- Shared signed-key comparisons for float expressions and range checks. -/
import Stage0.Senke.Ausdruck.Gleit.Code

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
variable [Kern] {D : Deklaration} {L : Lay D}

theorem floatKeyL_room {d top : Nat} {a b : Option (List II × Nat)} {c : List II}
    (h : floatKeyL d a b = some (c, top)) : d + 5 ≤ top := by
  cases a with
  | none => cases h
  | some a => cases b with
    | none => cases h
    | some b => exact (floatKeyL_top h).1

theorem floatCmpL_ok {fp : Runner.W} {K d ta tb top : Nat} {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {a b c : List II} {x y : Int} (le : Bool)
    (h : floatCmpL le d (some (a, ta)) (some (b, tb)) = some (c, top))
    (hx : -2^63 ≤ x ∧ x < 2^63) (hy : -2^63 ≤ y ∧ y < 2^63) (hd : d+2 ≤ K)
    (ha : ∀ m pc, Pre L m pc fp K d a ρ W → Ok m pc fp K d a (· = BitVec.ofInt 64 x))
    (hb : ∀ m pc, Pre L m pc fp K (d+1) b ρ W → Ok m pc fp K (d+1) b (· = BitVec.ofInt 64 y))
    {m : Runner.Mem} {pc : Runner.W} (hp : Pre L m pc fp K d c ρ W) :
    Ok m pc fp K d c (· = Runner.IR.bool (if le then !decide (x < y) else decide (x < y))) := by
  cases le <;> simp only [floatCmpL, bind, Option.bind_some, pure, Bool.false_eq_true,
    ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h ⊢
  · obtain ⟨rfl, rfl⟩ := h
    exact bin_ok ha hb (fun a b ha hb => ⟨_, rfl, by rw [ha, hb, slt_in hx hy]⟩)
      (g := fun a b => some (Runner.IR.bool (a.slt b))) rfl (by decide) (by omega) hp
  · obtain ⟨rfl, rfl⟩ := h
    apply bin_ok (g := fun a b => some (a ^^^ b))
      (Pa := fun w => w = Runner.IR.bool (decide (x < y)))
      (Pb := fun w => w = BitVec.ofInt 64 1) ?_
      (fun _ _ hp => const_ok hp (by decide) (by omega)) ?_ rfl (by decide) (by omega) hp
    · intro m pc hp
      exact bin_ok ha hb (fun a b ha hb => ⟨_, rfl, by rw [ha, hb, slt_in hx hy]⟩)
        (g := fun a b => some (Runner.IR.bool (a.slt b))) rfl (by decide) (by omega) hp
    · intro a b ha hb
      refine ⟨_, rfl, ?_⟩
      rw [ha, hb, bool_word, not_word, ← bool_word]

end Gabbro.Stage0.Senke
