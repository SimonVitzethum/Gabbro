/- Emission proofs recover the actual body and targets used by forever lowering. -/
import Stage0.Senke.Anweisung.Faelle.Schleifen.Counter

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR

@[simp] theorem foreverCode_length (counter one scratch budget : Nat) (cc cb : List II) :
    (foreverCode counter one scratch budget cc cb).length = cc.length + cb.length + 13 := by
  simp [foreverCode, foreverCounterInit, foreverCounter, stopC, sysC]
  omega

theorem foreverC_budget {counter one scratch budget : Nat} {inv : List II × Nat}
    {body : Int × Int → Option (List II × Nat)} {code : List II} {top : Nat}
    (h : foreverC counter one scratch budget inv body = some (code, top)) :
    budget < 2 ^ 31 ∧ budget < 2 ^ 64 := by
  unfold foreverC at h
  split at h
  · omega
  · simp at h

theorem foreverC_refuses_budget (counter one scratch budget : Nat) (inv : List II × Nat)
    (body : Int × Int → Option (List II × Nat)) (h : 2 ^ 31 ≤ budget) :
    foreverC counter one scratch budget inv body = none := by
  simp [foreverC, show ¬budget < 2 ^ 31 by omega]

/-- Recover the actual candidate and its targets from successful emission. This
    is the body premise needed by the mutual soundness induction, with no trusted
    assertion about candidate lengths or jump relocation. -/
theorem foreverC_actual {counter one scratch budget : Nat} {inv : List II × Nat}
    {body : Int × Int → Option (List II × Nat)} {code : List II} {top : Nat}
    (h : foreverC counter one scratch budget inv body = some (code, top)) :
    ∃ cb tb, body (foreverTargets inv.1.length cb.length) = some (cb, tb) ∧
      code = foreverCode counter one scratch budget inv.1 cb ∧
      inv.2 ≤ top ∧ tb ≤ top ∧ counter + 1 ≤ top ∧ one + 1 ≤ top ∧ scratch + 8 ≤ top := by
  unfold foreverC at h
  split at h
  · simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨probe, hp, actual, ha, h⟩ := h
    split at h
    · rename_i same
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨actual.1, actual.2, ?_, rfl, ?_⟩
      · simpa only [same] using ha
      · omega
    · simp at h
  · simp at h

/-- Offsets in instruction units: the backedge and budget stop lie beyond the
    full invariant/body fragment. These are the addresses consumed by Runtime. -/
theorem forever_offsets (i b : Nat) :
    2 + i + 1 + b + 1 + 3 = i + b + 7 ∧
    2 + i + 1 + b + 1 + 3 + 1 = i + b + 8 ∧
    (16 * (i + b + 7 : Nat) : Int) + (foreverTargets i b).2 = 64 ∧
    (foreverTargets i b).1 = 64 + 16 * 4 := by
  simp [foreverTargets]
  omega

/-- The runtime contract measures exits from the backedge, whereas the
    candidate producer measures them from the body end, four instructions earlier. -/
theorem forever_runtime_targets (i b : Nat) :
    exPlus (64, -(16 * (i + b + 7 : Nat) : Int)) 4 = foreverTargets i b := by
  simp only [exPlus, foreverTargets, Prod.mk.injEq]
  constructor <;> push_cast <;> omega

/-- Budget changes instruction data only, including the zero-fuel case. -/
theorem foreverC_zeuge :
    (foreverC 9 10 13 0 ([], 14) (fun _ => some ([], 14))).isSome = true ∧
    (foreverC 9 10 13 1 ([], 14) (fun _ => some ([], 14))).isSome = true ∧
    (foreverC 9 10 13 2 ([], 14) (fun _ => some ([], 14))).isSome = true ∧
    foreverC 9 10 13 (2 ^ 31) ([], 14) (fun _ => some ([], 14)) = none ∧
    (foreverCode 9 10 13 0 [] []).length = 13 := by decide

/-- The largest positive signed immediate is accepted; an unstable candidate
    length is rejected even when its first probe succeeded. -/
theorem foreverC_refusal_zeuge :
    (foreverC 9 10 13 (2 ^ 31 - 1) ([], 14)
      (fun _ => some ([], 14))).isSome = true ∧
    foreverC 9 10 13 2 ([], 14)
      (fun targets => if targets.1 = 0 then some ([], 14)
        else some ([ci 2 13 12 0], 14)) = none := by decide

end Gabbro.Stage0.Senke
