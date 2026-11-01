/- Complete variable lowering uses the shared frame transport. -/
import Stage0.Senke.Ausdruck.Aggregat.FrameCopy

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

/-- The actual variable emitter returns the complete canonical value, at every
    declared width. In particular no singleton-array premise is involved. -/
theorem var_value_ok {reserved : Nat} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (x : Var Γ τ) {m : Runner.Mem} {pc fp : Runner.W} {K d top : Nat}
    {code : List II} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    (lower : lowE L (reserved := reserved) (Λ := Λ) (.var x) d = some (code, top))
    (fits : top ≤ K) (pre : Pre L m pc fp K d code ρ W reserved) :
    ValueOk L m pc fp K d code τ (ρ.get x) := by
  simp only [lowE_eqs, Option.some.injEq, Prod.mk.injEq] at lower
  obtain ⟨rfl, rfl⟩ := lower
  have bound := variableOffset_bound x
  have placed : vslot x reserved + valueWords τ ≤ frei Γ reserved := by
    unfold vslot frei
    omega
  have ctx := pre.ctx
  obtain ⟨m', run, changed, value⟩ := copyValue_run pre.frame pre.small fits
    (by omega) (Or.inr (by have := pre.ctx; omega)) pre.code
    (by simpa only [copyWords_length] using pre.far) (pre.env τ x)
  refine ⟨m', by simpa only [copyWords_length] using run, ?_, value⟩
  exact ⟨changed.rd, changed.wr, fun a ha => changed.b a (by
    intro ⟨lower, upper⟩
    apply ha
    exact ⟨lower, by unfold inSlots at *; omega⟩)⟩


end Gabbro.Stage0.Senke
