/- Computed integer hooks share the scalar and complete-magnitude continuations. -/
module
public import Stage0.Senke.Ausdruck.Gleit.Wide.Values
public import Stage0.Senke.Ausdruck.Gleit.Slots.SlotBasics
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gleitkomma Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

/-- Small runtime values reuse the scalar conversion. Large values retain
    three guard bits plus sticky and use the shared nearest-even packer.
    The source interval determines storage only, never admissibility. -/
def wideComputedFloatOfE (L : Lay D) {Γ : Ctx} {Λ : List (Res D)}
    {lo hi : Int} (e : Expr D Γ Λ (.int lo hi)) (d : Nat) (reserved : Nat := 0) :
    Option (List II × Nat) :=
  let w := WideFloat.width lo hi
  let field := fun {a b : Int} (t : Expr D Γ Λ (.int a b)) j => lowE L t j reserved
  let flag := fun j => lowE L (.lt (WideFloat.magnitude w e) (.lit (2 ^ 55))) j reserved
  let sign := fun j => lowE L (.lt e (.lit 0)) j reserved
  let small := fun j => computedFloatOfL f64 j (field (WideFloat.small e))
  let large := fun j => routineRoundPackL j sign (field (WideFloat.index w e))
    (field (WideFloat.guard w e))
  routineChooseL d flag small large

theorem wideComputedFloatOfE_top {L : Lay D} {Γ : Ctx} {Λ : List (Res D)}
    {lo hi : Int} {e : Expr D Γ Λ (.int lo hi)} {d reserved top : Nat} {c : List II}
    (h : wideComputedFloatOfE L e d reserved = some (c, top)) : d < top := by
  simp only [wideComputedFloatOfE, routineChooseL, bind, Option.bind_eq_some_iff,
    pure, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨cc, tt⟩, _, _, rfl⟩ := h
  omega


/-- The theorem uses the ordinary expression simulation at each synthesized
    field. Every fallback in the typed normalization is accounted for by its
    value lemma; the complete integer is never reduced to its first limb. -/
theorem wideComputedFloatOfE_ok {Γ : Ctx} {Λ : List (Res D)}
    {lo hi : Int} (e : Expr D Γ Λ (.int lo hi))
    {σ₀ σ : World D} (same : σ₀ = σ) (lay : LayIn L)
    {ρ : Env D Γ} {W : Runner.Mem → Prop} (world : ∀ m, W m → WeltAt m L σ)
    (reserved : Nat) :
    WordCode (L := L) ρ W (fun d => wideComputedFloatOfE L e d reserved)
      (BitVec.ofNat 64 (zuBits f64 (ofInt f64 (eval σ₀ e σ ρ).n))) reserved := by
  let w := WideFloat.width lo hi
  let z := (eval σ₀ e σ ρ).n
  have bound : (z.natAbs : Int) ≤ WideFloat.upper w := WideFloat.magnitude_bound _
  have mag := WideFloat.magnitude_value (σ₀ := σ₀) (σ := σ) (ρ := ρ) (e := e) bound
  have condition : WordCode (L := L) ρ W _ _ reserved := WideFloat.boolean
    (.lt (WideFloat.magnitude w e) (.lit (2 ^ 55))) lay same world reserved
  change WordCode (L := L) ρ W _
    (Runner.IR.bool (decide ((eval σ₀ (WideFloat.magnitude w e) σ ρ).n < (2 : Int) ^ 55))) reserved at condition
  rw [mag] at condition
  have sign : WordCode (L := L) ρ W _ _ reserved :=
    WideFloat.boolean (.lt e (.lit 0)) lay same world reserved
  change WordCode (L := L) ρ W _ (Runner.IR.bool (decide (z < 0))) reserved at sign
  have small : decide ((z.natAbs : Int) < 2 ^ 55) = true →
      WordCode (L := L) ρ W
        (fun j => computedFloatOfL f64 j (fun d => lowE L (WideFloat.small e) d reserved))
        (BitVec.ofNat 64 (zuBits f64 (ofInt f64 z))) reserved := by
    intro flag fp K d c top emitted fits m pc pre
    have smallBound : z.natAbs < 2 ^ 55 := by
      have comparison : (z.natAbs : Int) < 2 ^ 55 := of_decide_eq_true flag
      exact_mod_cast comparison
    have narrow : (eval σ₀ (WideFloat.small e) σ ρ).n = z :=
      WideFloat.small_value (σ₀ := σ₀) (σ := σ) (ρ := ρ) (e := e) smallBound
    rw [← narrow]
    apply computedFloatOfL_ok f64 (by simp) (eval σ₀ (WideFloat.small e) σ ρ)
      (by decide) (by decide) emitted pre fits
    intro ce child
    have childTop : ce.2 ≤ K := by
      simp only [computedFloatOfL, bind, Option.bind_eq_some_iff, pure,
        Option.some.injEq] at emitted
      obtain ⟨ce', he', ca, ha, eq⟩ := emitted
      have eqChild := Option.some.inj (child.symm.trans he')
      cases eqChild
      cases eq
      omega
    have childPre : Pre L m pc fp K d ce.1 ρ W reserved := by
      simp only [computedFloatOfL, bind, Option.bind_eq_some_iff, pure,
        Option.some.injEq] at emitted
      obtain ⟨ce', he', ca, ha, eq⟩ := emitted
      have eqChild := Option.some.inj (child.symm.trans he')
      cases eqChild
      cases eq
      exact pre.left
    exact (lowE_ok (same := fun _ => same) σ₀ σ world lay (WideFloat.small e)
      d ce.1 ce.2 child childTop m pc ρ childPre).word trivial
  have large : decide ((z.natAbs : Int) < 2 ^ 55) = false →
      WordCode (L := L) ρ W
        (fun j => routineRoundPackL j (fun d => lowE L (.lt e (.lit 0)) d reserved)
          (fun d => lowE L (WideFloat.index w e) d reserved)
          (fun d => lowE L (WideFloat.guard w e) d reserved))
        (BitVec.ofNat 64 (zuBits f64 (ofInt f64 z))) reserved := by
    intro flag fp K d code top emitted fits m pc pre
    have big : 2 ^ 55 ≤ z.natAbs := by
      have : ¬ (z.natAbs : Int) < 2 ^ 55 := by simpa using flag
      omega
    have iv := WideFloat.index_value (σ₀ := σ₀) (σ := σ) (ρ := ρ) (e := e) bound big
    have gv := WideFloat.guard_value (σ₀ := σ₀) (σ := σ) (ρ := ρ) (e := e) bound (by omega)
    have index : WordCode (L := L) ρ W _ _ reserved :=
      WideFloat.word (WideFloat.index w e) (by decide) lay same world reserved
    have guard : WordCode (L := L) ρ W _ _ reserved :=
      WideFloat.word (WideFloat.guard w e) (by decide) lay same world reserved
    rw [iv, BitVec.ofInt_natCast] at index
    rw [gv, BitVec.ofInt_natCast] at guard
    rw [← integerFloat_round z big]
    exact routineRoundPackL_ok sign index guard
      (fp := fp) (K := K) (d := d) (c := code) (top := top) emitted fits m pc pre
  intro fp K d code top emitted fits m pc pre
  have result := routineChooseL_ok condition small large
    (fp := fp) (K := K) (d := d) (c := code) (top := top) emitted fits m pc pre
  simpa only [wideComputedFloatOfE, ite_self] using result

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
#print axioms wideComputedFloatOfE_ok
end Gabbro.Stage0.Senke
