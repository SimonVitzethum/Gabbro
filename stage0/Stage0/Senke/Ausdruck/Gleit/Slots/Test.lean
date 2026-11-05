/- Source narrowing uses the same native range guard as computed binders. -/
module
public import Stage0.Senke.Gleit.Native.Range
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat}

theorem floatRangeL_room {d top : Nat} {lo hi : Int × Int}
    {e : Nat → Option (List II × Nat)} {c : List II}
    (h : floatRangeL d lo hi e = some (c, top)) : d + 7 ≤ top := by
  simp only [floatRangeL, Option.map_eq_some_iff] at h
  obtain ⟨⟨body, ceiling⟩, hb, he⟩ := h
  cases he
  omega

theorem floatRangeL_ok {fp : Runner.W} {K d top : Nat} {Γ : Ctx} {Λ : List (Res D)}
    {ρ : Env D Γ} {W : Runner.Mem → Prop} (σ₀ σ : World D) {l1 h1 lo hi : Int × Int}
    (e : Expr D Γ Λ (.fl l1 h1)) {c : List II}
    (ih : ∀ d c top, lowE L e (reserved := reserved) d = some (c, top) → top ≤ K →
      ∀ m pc, Pre L m pc fp K d c ρ W reserved →
        Ok m pc fp K d c (Enc L (.fl l1 h1) (eval σ₀ e σ ρ)))
    (h : floatRangeL d lo hi (lowE L e (reserved := reserved)) = some (c, top)) (hK : top ≤ K)
    {m : Runner.Mem} {pc : Runner.W} (hp : Pre L m pc fp K d c ρ W reserved) :
    Ok m pc fp K d c (· = Runner.IR.bool (floatRangeReject lo hi (eval σ₀ e σ ρ).x)) := by
  exact nativeFloatRangeL_at_ok lo hi (eval σ₀ e σ ρ).x
    (fun j code ceiling hc ht m pc pre => (ih j code ceiling hc ht m pc pre).mono
      (fun w hw => by rw [show w = (eval σ₀ e σ ρ).x.hwToBits.toBitVec from hw]; exact nativeFloat_read_word _))
    h hK hp

end Gabbro.Stage0.Senke
