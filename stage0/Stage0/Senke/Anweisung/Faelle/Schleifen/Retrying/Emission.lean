/- Exact constant-size retry accounting and recovery of the actual body. -/
module
public import Stage0.Senke.Anweisung.Faelle.Schleifen.Code
@[expose] public section

namespace Gabbro.Stage0.Senke
open Runner.IR

@[simp] theorem retryHeader_length (counter one scratch : Nat) (cc cb cu : List II) :
    (retryHeader counter one scratch cc cb cu).length = cc.length + cb.length + cu.length + 5 := by
  simp only [retryHeader, retryTest, foreverCounter, List.length_append,
    List.length_cons, List.length_nil]
  omega

@[simp] theorem retryCode_length (counter one scratch budget : Nat) (cc cb cu : List II) :
    (retryCode counter one scratch budget cc cb cu).length = cc.length + cb.length + cu.length + 7 := by
  simp only [retryCode, foreverCounterInit, retryHeader_length, List.length_append,
    List.length_cons, List.length_nil]
  omega

/-- Normalize the condition's skip distance once for all code-slice proofs. -/
theorem retryHeader_eq (counter one scratch : Nat) (cc cb cu : List II) :
    retryHeader counter one scratch cc cb cu =
      cc ++ ([ci 19 scratch 32 0,
        ci 18 (16 * (cb.length + cu.length + 4)) 0 0,
        ci 19 counter (16 * (cb.length + 3)) 0, ci 4 counter counter one] ++
        (cb ++ ([ci 18 (-(16 * (cc.length + cb.length + 4 : Nat) : Int)) 0 0] ++ cu))) := by
  have count : (foreverCounter counter one (16 * (cb.length + 3)) ++
      (cb ++ ([ci 18 (-(16 * (cc.length + cb.length + 4 : Nat) : Int)) 0 0] ++ cu))).length =
      cb.length + cu.length + 3 := by
    simp only [foreverCounter, List.length_append, List.length_cons, List.length_nil]
    omega
  unfold retryHeader retryTest
  rw [count]
  have offset : (16 : Int) * ((cb.length + cu.length + 3 : Nat) + 1) =
      16 * (cb.length + cu.length + 4) := by omega
  rw [offset]
  rfl

/-- Every recovered top accounts for all three code fragments and both control
    slots. Image and jump bounds depend only on code lengths, never the fuel. -/
theorem retryC_actual {counter one scratch budget : Nat} {cc cu : List II × Nat}
    {body : Int × Int → Option (List II × Nat)} {code : List II} {top : Nat}
    (h : retryC counter one scratch budget cc cu body = some (code, top)) :
    ∃ cb tb, body (retryTargets cc.1.length cb.length cu.1.length) = some (cb, tb) ∧
      code = retryCode counter one scratch budget cc.1 cb cu.1 ∧
      cc.2 ≤ top ∧ tb ≤ top ∧ cu.2 ≤ top ∧ counter + 1 ≤ top ∧ one + 1 ≤ top ∧
      scratch + 1 ≤ top ∧ budget < 2 ^ 31 ∧
      16 * (cc.1.length + cb.length + cu.1.length + 7) < 2 ^ 31 := by
  unfold retryC at h
  split at h
  · rename_i fuel
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨probe, _, actual, lowered, out⟩ := h
    split at out
    · rename_i sized
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at out
      obtain ⟨rfl, rfl⟩ := out
      refine ⟨actual.1, actual.2, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, fuel, sized.2⟩
      · simpa only [sized.1] using lowered
      all_goals omega
    · cases out
  · cases h

/-- Signed backward and forward displacements all fit under the one image gate. -/
theorem retry_displacements (c b u : Nat) (small : 16 * (c + b + u + 7) < 2 ^ 31) :
    lit32 (16 * (b + u + 4 : Nat)) = true ∧
    lit32 (16 * (b + 3 : Nat)) = true ∧
    lit32 (-(16 * (c + b + 4 : Nat) : Int)) = true := by
  simp only [lit32, Bool.and_eq_true_iff, decide_eq_true_eq]
  omega

/-- Large semantic bounds do not enlarge either the body or the header. -/
theorem retry_size_zeuge :
    (retryCode 4 5 6 16 [ci 1 6 0 0] [] []).length =
      (retryCode 4 5 6 2560 [ci 1 6 0 0] [] []).length ∧
    (retryC 4 5 6 2560 ([ci 1 6 0 0], 7) ([], 7)
      (fun _ => some ([], 7))).isSome = true := by decide

end Gabbro.Stage0.Senke
