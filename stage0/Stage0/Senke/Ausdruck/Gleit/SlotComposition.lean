/- Composition from an actual child execution and slot read. -/
import Stage0.Senke.Ausdruck.Gleit.Skalieren

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

/-- Compose an actual zero-producing child execution with the explicit-slot
    continuation, preserving the caller's reserved environment prefix. -/
theorem computedFloatOfL_zero_ok (F : Gleitkomma.Format)
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {m : Runner.Mem} {pc fp : Runner.W} {K d top reserved : Nat}
    {child : Nat → Option (List II × Nat)} {code : List II}
    (hc : computedFloatOfL F d child = some (code, top))
    (hp : Pre L m pc fp K d code ρ W reserved)
    (hk : d + 5 < K)
    (childRun : ∀ ce, child d = some ce →
      Ok m pc fp K d ce.1 (· = 0)) :
    Ok m pc fp K d code (· = 0) := by
  simp only [computedFloatOfL, bind, Option.bind_eq_some_iff, pure,
    Option.some.injEq] at hc
  obtain ⟨ce, he, ca, ha, hc⟩ := hc
  cases hc
  apply slotContinuation hp (by omega) (childRun ce he)
  intro m' w pre read hw
  subst w
  exact floatOfIntContinuationL_zero_ok F ha pre hk read

#print axioms computedFloatOfL_zero_ok

end Gabbro.Stage0.Senke
