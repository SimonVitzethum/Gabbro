/- Computed integer hooks share the scalar and complete-magnitude continuations. -/
module
public import Stage0.Senke.Ausdruck.Gleit.Wide.Code
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

/-- Signed-word intervals retain the established short path. Every other
    binary64 interval uses its complete magnitude and the shared IEEE packer.
    Binary32 is an auxiliary hook; source `floatOf` always requests binary64. -/
def computedFloatOfE (L : Lay D) {Γ : Ctx} {Λ : List (Res D)}
    {lo hi : Int} (F : Gleitkomma.Format) (e : Expr D Γ Λ (.int lo hi))
    (d : Nat) (reserved : Nat := 0) : Option (List II × Nat) :=
  if F ∈ [Gleitkomma.f32, Gleitkomma.f64] ∧ -2^63 ≤ lo ∧ hi < 2^63 then
    computedFloatOfL F d (fun j => lowE L e j reserved)
  else if F = Gleitkomma.f64 then wideComputedFloatOfE L e d reserved
  else none

/-- The actual emitting branch reserves a result slot on every interval. -/
theorem computedFloatOfE_bounds {Γ : Ctx} {Λ : List (Res D)}
    {lo hi : Int} {F : Gleitkomma.Format} {e : Expr D Γ Λ (.int lo hi)}
    {d reserved top : Nat} {code : List II}
    (hc : computedFloatOfE L F e d reserved = some (code, top)) : d < top := by
  unfold computedFloatOfE at hc
  split at hc
  · simp only [computedFloatOfL, bind, Option.bind_eq_some_iff, pure,
      Option.some.injEq] at hc
    obtain ⟨ce, he, ca, ha, hc⟩ := hc
    cases hc
    obtain ⟨assembly, assemblyOk, _⟩ := floatOfIntContinuationL_parts F d ha
    have bound := floatOfIntAssemblyL_ceiling assemblyOk
    omega
  · split at hc
    · exact wideComputedFloatOfE_top hc
    · cases hc

/-- All generated field expressions consume the ordinary `lowE_ok` theorem.
    This is the same world/layout contract as the block's expression rule,
    with the reservation and complete memory footprint preserved throughout. -/
theorem computedFloatOfE_ok {Γ : Ctx} {Λ : List (Res D)}
    {lo hi : Int} {F : Gleitkomma.Format} {e : Expr D Γ Λ (.int lo hi)}
    {ρ : Env D Γ} {W : Runner.Mem → Prop} {σ₀ σ : World D}
    {m : Runner.Mem} {pc fp : Runner.W} {K d top reserved : Nat} {code : List II}
    (hc : computedFloatOfE L F e d reserved = some (code, top))
    (hp : Pre L m pc fp K d code ρ W reserved) (ht : top ≤ K)
    (lay : LayIn L) (same : σ₀ = σ) (world : ∀ m, W m → WeltAt m L σ) :
    Ok m pc fp K d code
      (· = BitVec.ofNat 64 (Gleitkomma.zuBits F
        (Gleitkomma.ofInt F (eval σ₀ e σ ρ).n))) := by
  unfold computedFloatOfE at hc
  split at hc
  · next guard =>
    have parts := hc
    simp only [computedFloatOfL, bind, Option.bind_eq_some_iff, pure,
      Option.some.injEq] at parts
    obtain ⟨ce, he, ca, ha, equal⟩ := parts
    apply computedFloatOfL_ok F guard.1 (eval σ₀ e σ ρ)
      guard.2.1 guard.2.2 hc hp ht
    intro child emitted
    have childEq : child = ce := Option.some.inj (emitted.symm.trans he)
    subst child
    cases equal
    exact (lowE_ok (same := fun _ => same) σ₀ σ world lay e d ce.1 ce.2 he
      (by omega) m pc ρ hp.left).word trivial
  · split at hc
    · next format =>
      subst F
      exact wideComputedFloatOfE_ok e same lay world reserved hc ht m pc hp
    · cases hc

#print axioms computedFloatOfE_ok
end Gabbro.Stage0.Senke
