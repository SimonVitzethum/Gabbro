/- Runtime selection from a saved column uses one result span and two scratch words. -/
module
public import Stage0.Senke.Ausdruck.Old.Column
public import Stage0.Senke.Ausdruck.Quant.Selection
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable {D : Deklaration} {L : Lay D}

def entryColumnL (τ : Ty) (base d : Nat) (index : Option (List II × Nat)) :
    Option (List II × Nat) := do
  let ci ← index
  let ptr := d + valueWords τ
  pure (ci.1 ++ selectFrameSpan (valueWords τ) base d ptr (ptr + 1), max ci.2 (ptr + 2))

theorem entryColumnL_top {τ : Ty} {base d top : Nat} {index : Option (List II × Nat)}
    {code : List II} (emitted : entryColumnL τ base d index = some (code, top)) : d < top := by
  simp only [entryColumnL, bind, Option.bind_eq_some_iff, pure, Option.some.injEq,
    Prod.mk.injEq] at emitted
  obtain ⟨⟨ci, ti⟩, _, rfl, rfl⟩ := emitted
  omega

/-- A complete immutable snapshot can be selected upwards into fresh expression storage.
    The index is evaluated before the pointer arithmetic, under the usual expression contract. -/
theorem entryColumnL_ok [Kern] {τ : Ty} {n : Int} (k : Zahl 0 (n - 1)) (v : Wert D τ)
    {Γ : Ctx} {ρ : Env D Γ} {fp : Runner.W} {K base d reserved : Nat}
    {W : Runner.Mem → Prop} {index : Option (List II × Nat)} {code : List II} {top : Nat}
    (bounds : base + n.toNat * valueWords τ ≤ frei Γ reserved)
    (literal : 8 * valueWords τ < 2 ^ 31)
    (saved : ∀ {m}, EnvAt L m fp ρ reserved →
      ValueAt L m fp (base + k.n.toNat * valueWords τ) τ v)
    (child : ∀ ci ti, index = some (ci, ti) → ti ≤ K → ∀ m pc,
      Pre L m pc fp K (d + valueWords τ) ci ρ W reserved →
        ValueOk L m pc fp K (d + valueWords τ) ci (.index n) k)
    (emitted : entryColumnL τ base d index = some (code, top)) (fits : top ≤ K)
    (m : Runner.Mem) (pc : Runner.W) (pre : Pre L m pc fp K d code ρ W reserved) :
    ValueOk L m pc fp K d code τ v := by
  simp only [entryColumnL, bind, Option.bind_eq_some_iff, pure, Option.some.injEq,
    Prod.mk.injEq] at emitted
  obtain ⟨⟨ci, ti⟩, hi, rfl, rfl⟩ := emitted
  let ptr := d + valueWords τ
  have idxPre : Pre L m pc fp K ptr ci ρ W reserved :=
    { pre.left with ctx := by have := pre.ctx; dsimp only [ptr]; omega }
  obtain ⟨m1, run1, changed1, indexValue⟩ := child ci ti hi (by omega) m pc idxPre
  have tail := pre.next (d' := ptr) (changed1.mono (by omega))
    (by dsimp only [ptr]; omega) (by omega : d ≤ K)
  have input := saved tail.env
  obtain ⟨word, read, encoded⟩ := ValueAt.word (.index n) k trivial indexValue
  change word = BitVec.ofInt 64 k.n at encoded
  subst word
  have indexWord : m1.rd64 (slot fp (BitVec.ofNat 64 ptr)) = some (BitVec.ofNat 64 k.n.toNat) := by
    simpa only [← BitVec.ofInt_natCast, Int.toNat_of_nonneg k.lo_le] using read
  have selectedBound : base + (k.n.toNat + 1) * valueWords τ ≤ d := by
    have range : k.n.toNat + 1 ≤ n.toNat := by have := k.lo_le; have := k.le_hi; omega
    have size := Nat.mul_le_mul_right (valueWords τ) range
    have := pre.ctx
    omega
  obtain ⟨m2, run2, changed2, result⟩ := selectFrameSpan_checked_ok
    (by dsimp only [ptr]; omega) (Or.inr selectedBound) (Nat.le_refl ptr)
    (by omega) (by omega) literal indexWord input tail
  refine ⟨m2, ?_, (changed1.mono (by omega)).trans changed2, result⟩
  simpa only [List.length_append, pc_add] using run1.trans run2

end Gabbro.Stage0.Senke
