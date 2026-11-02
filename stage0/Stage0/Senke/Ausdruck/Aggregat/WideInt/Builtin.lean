/- Generic C13 arithmetic preservation through exact operations and the full-width mask. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.WideInt.Mask
public import Stage0.Senke.Ausdruck.Aggregat.WideInt.Shift
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option linter.unusedSectionVars false
variable [Kern] {D : Deklaration} {L : Lay D} {reserved : Nat}

theorem intBuiltin2L_ok {τ1 τ2 τ : Ty} (op : IntBuiltin [τ1, τ2] τ)
    (x : Wert D τ1) (y : Wert D τ2)
    {fa fb : Nat → Option (List II × Nat)} {fp : Runner.W} {K d top : Nat} {c : List II}
    {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop} {m : Runner.Mem} {pc : Runner.W}
    (iha : ∀ q ca ta, fa q = some (ca, ta) → ta ≤ K → ∀ m pc,
      Pre L m pc fp K q ca ρ W reserved → ValueOk L m pc fp K q ca τ1 x)
    (ihb : ∀ q cb tb, fb q = some (cb, tb) → tb ≤ K → ∀ m pc,
      Pre L m pc fp K q cb ρ W reserved → ValueOk L m pc fp K q cb τ2 y)
    (h : intBuiltin2L op d fa fb = some (c, top)) (hK : top ≤ K)
    (hp : Pre L m pc fp K d c ρ W reserved) :
    ValueOk L m pc fp K d c τ (evalIntBuiltin2 op x y) := by
  cases op with
  | addW w =>
    apply wrapL_ok w (Zahl.add x y) (by have := x.lo_le; have := y.lo_le; change 0 ≤ x.n + y.n; omega)
      (Zahl.addW w x y) rfl ?_ h hK hp
    intro ce te emitted fits m pc pre
    exact wideAdd_ok x y (iha d) (ihb _) emitted fits pre
  | subW w =>
    let modulus := (2 : Int) ^ (w + 1)
    let constant : Zahl modulus modulus := ⟨modulus, by omega, by omega⟩
    let sum := Zahl.add (Zahl.sub x y) constant
    have nonnegative : 0 ≤ sum.n := by
      have hx := x.lo_le
      have hy := y.le_hi
      change 0 ≤ (x.n - y.n) + modulus
      dsimp only [modulus]
      omega
    apply wrapL_ok w sum nonnegative (Zahl.subW w x y) ?_ ?_ h hK hp
    · change (x.n - y.n) % modulus = ((x.n - y.n) + modulus) % modulus
      rw [Int.add_emod_right]
    · intro ce te emitted fits m pc pre
      apply wideAdd_ok (Zahl.sub x y) constant ?_
        (fun cc tt hc ht m pc hp => intConstL_ok constant hc ht hp) emitted fits pre
      intro cc tt hc ht m pc hp
      exact wideSub_ok x y (iha d) (ihb _) hc ht hp
  | mulW w =>
    apply wrapL_ok w (Zahl.mul x y) (Int.mul_nonneg x.lo_le y.lo_le)
      (Zahl.mulW w x y) rfl ?_ h hK hp
    intro ce te emitted fits m pc pre
    exact wideMul_ok x y (iha d) (ihb _) emitted fits pre
  | shlW w =>
    have inputBound : (2 : Int) ^ (w + 1) - 1 < 2 ^ (w + 1) := by omega
    have shiftBound : (w : Int) < ((w + 1 : Nat) : Int) := by omega
    let shifted := Zahl.shl (w + 1) inputBound shiftBound (by decide) (by decide) x y
    apply wrapL_ok w shifted shifted.lo_le (Zahl.shlW w x y) rfl ?_ h hK hp
    intro ce te emitted fits m pc pre
    exact wideShl_ok (w + 1) inputBound shiftBound (by decide) (by decide) x y
      (iha d) (ihb _) emitted fits pre
  | addS lo hi => exact saturatingAddL_ok x y iha ihb h hK hp
  | rotl w => simp only [intBuiltin2L] at h; cases h
  | rotr w => simp only [intBuiltin2L] at h; cases h

end Gabbro.Stage0.Senke
