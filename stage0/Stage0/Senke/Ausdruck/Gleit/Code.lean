/- Correct integer-only code templates for binary64 ordering. -/
import Stage0.Senke.Ausdruck.Gleit.Schluessel

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat}

/-- A template consumes the two ordinary expression proofs; it adds no semantic assumption. -/
theorem floatKeyL_ok {fp : Runner.W} {K d ta tb top : Nat} {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {a b c : List II} {x : GFloat}
    (h : floatKeyL d (some (a, ta)) (some (b, tb)) = some (c, top)) (hK : top ≤ K)
    (ha : ∀ m pc, Pre L m pc fp K d a ρ W reserved → Ok m pc fp K d a (fun w => Gleitkomma.wf Gleitkomma.f64 x ∧
      w = BitVec.ofNat 64 (Gleitkomma.zuBits Gleitkomma.f64 x)))
    (hb : ∀ m pc, Pre L m pc fp K (d+3) b ρ W reserved → Ok m pc fp K (d+3) b (fun w => Gleitkomma.wf Gleitkomma.f64 x ∧
      w = BitVec.ofNat 64 (Gleitkomma.zuBits Gleitkomma.f64 x)))
    {m : Runner.Mem} {pc : Runner.W} (hp : Pre L m pc fp K d c ρ W reserved) :
    Ok m pc fp K d c (fun w => Gleitkomma.wf Gleitkomma.f64 x ∧ w = BitVec.ofInt 64 (floatKey x)) := by
  have ht := floatKeyL_top h
  simp only [floatKeyL, bind, Option.bind_some, pure, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  let raw : Runner.W := BitVec.ofNat 64 (Gleitkomma.zuBits Gleitkomma.f64 x)
  apply bin_ok (g := fun x y => some (x * y))
    (Pa := fun w => Gleitkomma.wf Gleitkomma.f64 x ∧ w = ((raw <<< 1) >>> 1))
    (Pb := fun w => w = 1 - 2 * Runner.IR.bool (raw.slt 0)) ?_ ?_ ?_ rfl (by decide) (by omega) hp
  · intro m pc hp
    apply bin_ok (g := fun x y => some (x >>> (y.toNat % 64)))
      (Pa := fun w => Gleitkomma.wf Gleitkomma.f64 x ∧ w = raw <<< 1)
      (Pb := fun w => w = BitVec.ofInt 64 1) ?_ ?_ ?_ rfl (by decide) (by omega) hp
    · intro m pc hp
      exact bin_ok ha (fun _ _ hp => const_ok hp (by decide) (by omega))
        (fun x y hx hy => ⟨_, rfl, hx.1, by rw [hx.2, hy]; rfl⟩)
        (g := fun x y => some (x <<< (y.toNat % 64))) rfl (by decide) (by omega) hp
    · intro m pc hp
      exact const_ok hp (by decide) (by omega)
    · intro x y hx hy
      exact ⟨_, rfl, hx.1, by rw [hx.2, hy]; rfl⟩
  · intro m pc hp
    apply bin_ok (g := fun x y => some (x - y))
      (Pa := fun w => w = BitVec.ofInt 64 1)
      (Pb := fun w => w = 2 * Runner.IR.bool (raw.slt 0))
      (fun _ _ hp => const_ok hp (by decide) (by omega)) ?_ ?_ rfl (by decide) (by omega) hp
    · intro m pc hp
      apply bin_ok (g := fun x y => some (x * y))
        (Pa := fun w => w = BitVec.ofInt 64 2)
        (Pb := fun w => w = Runner.IR.bool (raw.slt 0))
        (fun _ _ hp => const_ok hp (by decide) (by omega)) ?_ ?_ rfl (by decide) (by omega) hp
      · intro m pc hp
        exact bin_ok hb (fun _ _ hp => const_ok hp (by decide) (by omega))
          (fun x y hx hy => ⟨_, rfl, by rw [hx.2, hy]; rfl⟩)
          (g := fun x y => some (Runner.IR.bool (x.slt y))) rfl (by decide) (by omega) hp
      · intro x y hx hy
        exact ⟨_, rfl, by rw [hx, hy]; rfl⟩
    · intro x y hx hy
      exact ⟨_, rfl, by rw [hx, hy]; rfl⟩
  · intro x y hx hy
    refine ⟨_, rfl, hx.1, ?_⟩
    rw [hx.2, hy]
    exact float_key_word hx.1

end Gabbro.Stage0.Senke
