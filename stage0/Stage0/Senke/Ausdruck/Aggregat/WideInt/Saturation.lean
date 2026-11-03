/- Composition of exact wide addition, signed comparison and clamp with Zahl.addS. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.WideInt.Eng
public import Stage0.Senke.Ausdruck.Aggregat.WideInt.Ring
public import Stage0.Senke.Ausdruck.Aggregat.Materialize
public import Stage0.Senke.Ausdruck.Wenn
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat}

theorem intConstL_ok {lo hi : Int} (v : Zahl lo hi)
    {fp pc : Runner.W} {K d top : Nat} {c : List II} {m : Runner.Mem}
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    (h : intConstL lo hi v.n d = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c (.int lo hi) v :=
  constValue_ok (τ := .int lo hi) v trivial (by erw [encodeWords_int]; exact h) hK hp

theorem saturatingAddL_ok {lo hi : Int} (x y : Zahl lo hi)
    {fa fb : Nat → Option (List II × Nat)} {fp : Runner.W} {K d top : Nat} {c : List II}
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop} {m : Runner.Mem} {pc : Runner.W}
    (iha : ∀ q ca ta, fa q = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K q ca ρ W reserved → ValueOk L m pc fp K q ca (.int lo hi) x)
    (ihb : ∀ q cb tb, fb q = some (cb, tb) → tb ≤ K → ∀ m pc,
      Pre L m pc fp K q cb ρ W reserved → ValueOk L m pc fp K q cb (.int lo hi) y)
    (h : saturatingAddL lo hi d fa fb = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c (.int lo hi) (Zahl.addS x y) := by
  have inhabited : lo ≤ hi := by have := x.lo_le; have := x.le_hi; omega
  let low : Zahl lo hi := ⟨lo, by omega, inhabited⟩
  let high : Zahl lo hi := ⟨hi, inhabited, by omega⟩
  let bound : Zahl lo lo := ⟨lo, by omega, by omega⟩
  let fallback : Zahl lo hi := if (Zahl.add x y).n < lo then low else high
  have sum_ok : ∀ q cc tt,
      wideAddL lo hi lo hi (lo + lo) (hi + hi) q fa fb = some (cc, tt) → tt ≤ K →
      ∀ m pc, Pre L m pc fp K q cc ρ W reserved →
        ValueOk L m pc fp K q cc (.int (lo + lo) (hi + hi)) (Zahl.add x y) := by
    intro q cc tt emitted fits m pc pre
    exact wideAdd_ok x y (iha q) (ihb _) emitted fits pre
  unfold saturatingAddL at h
  apply wideEng_ok (Zahl.add x y) fallback (Zahl.addS x y)
    (fun inside => addS_exakt_wenn_passt x y inside.1 inside.2) ?_ (sum_ok d) ?_ h hK hp
  · intro outside
    apply Zahl.ext_n
    rw [Zahl.addS_n x y inhabited]
    dsimp only [fallback, low, high]
    split <;> simp only [Zahl.add] at * <;> omega
  · intro cb tb emitted fits m pc pre
    simp only [wennL, bind, Option.bind_eq_some_iff] at emitted
    obtain ⟨⟨cc, tc⟩, cond, ⟨ca, ta⟩, left, ⟨ce, te⟩, right, emitted⟩ := emitted
    split at emitted
    · next budget =>
      obtain ⟨rfl, rfl⟩ := Option.some.inj emitted
      have positive := intConstL_top left
      refine wenn_ok (bc := decide ((Zahl.add x y).n < lo)) pre budget (by omega) ?_ ?_ ?_
      · intro pre
        exact (wideLt_ok (Zahl.add x y) bound (sum_ok d)
          (fun cc tt hc ht m pc hp => intConstL_ok bound hc ht hp)
          cond (by omega) pre).word trivial
      · intro below m pc pre
        have below : (Zahl.add x y).n < lo := of_decide_eq_true below
        have r := intConstL_ok low left (by omega) pre
        simp only [fallback, if_pos below]
        exact r
      · intro above m pc pre
        have above : ¬ (Zahl.add x y).n < lo := by simpa only [decide_eq_false_iff_not] using above
        have r := intConstL_ok high right (by omega) pre
        simp only [fallback, if_neg above]
        exact r
    · cases emitted

end Gabbro.Stage0.Senke
