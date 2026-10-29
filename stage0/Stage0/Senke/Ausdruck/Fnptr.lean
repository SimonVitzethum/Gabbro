/-
  Subject: Function references are the code addresses carried by the layout.
-/
import Stage0.Senke.Ausdruck.Top

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat}

/-- Loading a function reference preserves its signature witness and emits its code address. -/
theorem fnref_ok {Λ : List (Res D)} {Γ : Ctx} {f : D.Fn} {n : Nat} {hf : D.passt f n = true}
    {d top K : Nat} {c : List II} {m : Runner.Mem} {pc fp : Runner.W} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} (σ₀ σ : World D)
    (h : lowE L (Expr.fnref f n hf : Expr D Γ Λ (.fnptr n)) d reserved = some (c, top))
    (hK : top ≤ K) (hp : Pre L m pc fp K d c ρ W reserved) :
    Ok m pc fp K d c (Enc L (.fnptr n) (eval σ₀ (Λ := Λ) (.fnref f n hf) σ ρ)) := by
  simp only [lowE_eqs] at h
  split at h
  · next haddr =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact (const_ok hp haddr (by omega)).mono fun w hw => by
      simpa only [Enc, eval, BitVec.ofInt_natCast] using hw
  · cases h

end Gabbro.Stage0.Senke
