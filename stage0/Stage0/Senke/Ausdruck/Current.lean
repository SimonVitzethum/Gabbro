/- Ordinary old reads use the current world; ensures fallback must keep them disabled. -/
module
public import Stage0.Senke.Ausdruck.Lesen
public import Stage0.Senke.Welt.Spans.CellStore
public import Stage0.Senke.Welt.Spans.Read
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat} {currentOld : Bool}
variable {W : Runner.Mem → Prop}

/-- The checked integer index and complete-value column read share one conversion proof. -/
theorem slotValueC_index_ok {Γ : Ctx} {t : D.Tab} {f : D.Feld t}
    {σ : World D} (index : Zahl 0 (D.count t - 1))
    {fp pc : Runner.W} {K d top : Nat} {code : List II} {child : List II × Nat}
    {m : Runner.Mem} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    (made : slotValueC L t f d child = some (code, top)) (fits : top ≤ K)
    (layout : LayIn L) (world : ∀ m, W m → WeltAt m L σ)
    (ih : ∀ m pc, Pre L m pc fp K (d + valueWords (D.typ t f)) child.1 ρ W reserved →
      Ok m pc fp K (d + valueWords (D.typ t f)) child.1
        (Enc L (.index (D.count t)) index))
    (pre : Pre L m pc fp K d code ρ W reserved) :
    ValueOk L m pc fp K d code (D.typ t f) (σ.slots t index.n f) := by
  have bound : ((index.n.toNat : Nat) : Int) < D.count t := by
    have := index.lo_le
    have := index.le_hi
    omega
  have toWord : BitVec.ofInt 64 index.n = BitVec.ofNat 64 index.n.toNat := by
    rw [← BitVec.ofInt_natCast, Int.toNat_of_nonneg index.lo_le]
  have result := slotValueC_ok (idx := index.n.toNat) made fits (L.bounded bound) layout
    (fun m pc hp => (ih m pc hp).mono fun w hw => by
      simp only [Enc] at hw
      rw [hw, toWord]) world pre
  rw [Int.toNat_of_nonneg index.lo_le] at result
  exact result

/-- Raw G admits old in ordinary expressions. Its snapshot equals the current world there;
    it is not the distinct function-entry snapshot used by ensures. -/
theorem oldGlobal_ok {Λ : List (Res D)} {Γ : Ctx} (σ₀ σ : World D)
    (world : ∀ m, W m → WeltAt m L σ) (g : D.Glob) (access : gdarf D g Λ)
    {fp pc : Runner.W} {K d top : Nat} {code : List II} {m : Runner.Mem} {ρ : Env D Γ}
    (same : currentOld = true → σ₀ = σ)
    (made : lowE (currentOld := currentOld) L (.oldG g access) d reserved = some (code, top))
    (fits : top ≤ K) (pre : Pre L m pc fp K d code ρ W reserved) :
    ValueOk L m pc fp K d code (D.gtyp g) (eval σ₀ (.oldG g access) σ ρ) := by
  simp only [lowE_eqs] at made
  split at made
  · next enabled =>
    have equal := same enabled
    subst σ₀
    exact globalValueC_ok made fits world pre
  · cases made

/-- An old slot read evaluates its index in the same current world as every ordinary slot read. -/
theorem oldSlot_ok {Λ : List (Res D)} {Γ : Ctx} (σ₀ σ : World D)
    (world : ∀ m, W m → WeltAt m L σ) (layout : LayIn L)
    (t : D.Tab) (f : D.Feld t) (i : Expr D Γ Λ (.index (D.count t))) (access : darf D t Λ)
    {fp pc : Runner.W} {K d top : Nat} {code : List II} {m : Runner.Mem} {ρ : Env D Γ}
    (same : currentOld = true → σ₀ = σ)
    (ih : ∀ ci ti, lowE (currentOld := currentOld) L i
        (d + valueWords (D.typ t f)) reserved = some (ci, ti) → ti ≤ K → ∀ m pc,
      Pre L m pc fp K (d + valueWords (D.typ t f)) ci ρ W reserved →
        ValueOk L m pc fp K (d + valueWords (D.typ t f)) ci (.index (D.count t)) (eval σ₀ i σ ρ))
    (made : lowE (currentOld := currentOld) L (.oldS t f i access) d reserved = some (code, top))
    (fits : top ≤ K) (pre : Pre L m pc fp K d code ρ W reserved) :
    ValueOk L m pc fp K d code (D.typ t f) (eval σ₀ (.oldS t f i access) σ ρ) := by
  simp only [lowE_eqs] at made
  split at made
  · next enabled =>
    have equal := same enabled
    subst σ₀
    simp only [bind, Option.bind_eq_some_iff] at made
    obtain ⟨⟨ci, ti⟩, lower, made⟩ := made
    have tops := slotValueC_top made
    exact slotValueC_index_ok (eval σ i σ ρ) made fits layout world
      (fun m pc hp => (ih ci ti lower (by have := tops.1; omega) m pc hp).word trivial) pre
  · cases made

end Gabbro.Stage0.Senke
