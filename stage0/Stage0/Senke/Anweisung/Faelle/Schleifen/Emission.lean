/- Concrete constant-size forever control. Kept off the lowering hook until the
   complete statement simulation transports initialization and both exit edges. -/
import Stage0.Senke.Anweisung.Faelle.Schleifen.Counter

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR

/-- Body exits relative to the end of the body. Leave skips both stops and the
    backedge; next jumps directly to the counter header. -/
def foreverTargets (invariant body : Nat) : Int × Int :=
  (128, -(16 * (invariant + body + 3 : Nat) : Int))

/-- The header starts after the two initialization instructions. False invariants
    stop with 104; exhausted fuel stops with 111 before evaluating the invariant. -/
def foreverCode (counter one scratch budget : Nat) (cc cb : List II) : List II :=
  foreverCounterInit counter budget ++ [ci 1 one 1 0] ++
    foreverCounter counter one (16 * (cc.length + cb.length + 8)) ++
    cc ++ [ci 19 scratch (16 * (cb.length + 2)) 0] ++ cb ++
    [ci 18 64 0 0] ++ stopC 104 scratch ++
    [ci 18 (-(16 * (cc.length + cb.length + 7 : Nat) : Int)) 0 0] ++
    stopC 111 scratch

/-- Signed instruction immediates bound the semantic budget more tightly than
    the runtime counter word. Check before invoking the body candidate producer.
    The first candidate measures length only; the second uses actual targets.
    Refuse if its length changes, rather than trusting a relocation assumption. -/
def foreverC (counter one scratch budget : Nat) (inv : List II × Nat)
    (body : Int × Int → Option (List II × Nat)) : Option (List II × Nat) := do
  if budget < 2 ^ 31 then
    let probe ← body (0, 0)
    let actual ← body (foreverTargets inv.1.length probe.1.length)
    if actual.1.length = probe.1.length then
      pure (foreverCode counter one scratch budget inv.1 actual.1,
        max inv.2 (max actual.2 (max (counter + 1) (max (one + 1) (scratch + 8)))))
    else none
  else none

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

/-- Budget changes instruction data only, including the zero-fuel case. -/
theorem foreverC_zeuge :
    (foreverC 9 10 13 0 ([], 14) (fun _ => some ([], 14))).isSome = true ∧
    (foreverC 9 10 13 1 ([], 14) (fun _ => some ([], 14))).isSome = true ∧
    (foreverC 9 10 13 2 ([], 14) (fun _ => some ([], 14))).isSome = true ∧
    foreverC 9 10 13 (2 ^ 31) ([], 14) (fun _ => some ([], 14)) = none ∧
    (foreverCode 9 10 13 0 [] []).length = 13 := by decide

end Gabbro.Stage0.Senke
