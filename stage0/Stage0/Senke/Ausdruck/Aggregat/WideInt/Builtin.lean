/- Generic C13 arithmetic preservation through exact operations and the full-width mask. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.WideInt.Mask
public import Stage0.Senke.Ausdruck.Aggregat.WideInt.Shift
public import Stage0.Senke.Ausdruck.Aggregat.WideInt.BitBuiltin.Sound
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
    let u := (2 : Int) ^ (w + 1) - 1
    let source := fun q => wideAddL 0 u 0 u (0 + 0) (u + u) q fa fb
    change wrapL w (0 + 0) (u + u) d source = some (c, top) at h
    erw [show evalIntBuiltin2 (D := D) (.addW w) x y = Zahl.addW w x y from rfl]
    apply wrapL_ok (fe := source) (d := d) w (Zahl.add x y)
      (by have := x.lo_le; have := y.lo_le; change 0 ≤ x.n + y.n; omega)
      (Zahl.addW w x y) rfl ?_ h hK hp
    intro ce te emitted fits m pc pre
    exact wideAdd_ok (fa := fa) (fb := fb) x y (iha d) (ihb _) emitted fits pre
  | subW w =>
    let modulus := (2 : Int) ^ (w + 1)
    let u := modulus - 1
    let constant : Zahl modulus modulus := ⟨modulus, by omega, by omega⟩
    let sum := Zahl.add (Zahl.sub x y) constant
    let difference := fun q => wideSubL 0 u 0 u (0 - u) (u - 0) q fa fb
    let source := fun q => wideAddL (0 - u) (u - 0) modulus modulus
      ((0 - u) + modulus) ((u - 0) + modulus) q difference (intConstL modulus modulus modulus)
    change wrapL w ((0 - u) + modulus) ((u - 0) + modulus) d source = some (c, top) at h
    erw [show evalIntBuiltin2 (D := D) (.subW w) x y = Zahl.subW w x y from rfl]
    have nonnegative : 0 ≤ sum.n := by
      have hx := x.lo_le
      have hy := y.le_hi
      change 0 ≤ (x.n - y.n) + modulus
      dsimp only [modulus]
      omega
    apply wrapL_ok (fe := source) (d := d) w sum nonnegative (Zahl.subW w x y) ?_ ?_ h hK hp
    · change (x.n - y.n) % modulus = ((x.n - y.n) + modulus) % modulus
      rw [Int.add_emod_right]
    · intro ce te emitted fits m pc pre
      apply wideAdd_ok (fa := difference) (fb := intConstL modulus modulus modulus)
        (Zahl.sub x y) constant ?_
        (fun cc tt hc ht m pc hp => intConstL_ok constant hc ht hp) emitted fits pre
      intro cc tt hc ht m pc hp
      exact wideSub_ok (fa := fa) (fb := fb) x y (iha d) (ihb _) hc ht hp
  | mulW w =>
    let u := (2 : Int) ^ (w + 1) - 1
    let lo := imin (imin (0 * 0) (0 * u)) (imin (u * 0) (u * u))
    let hi := imax (imax (0 * 0) (0 * u)) (imax (u * 0) (u * u))
    let source := fun q => wideMulL 0 u 0 u lo hi q fa fb
    change wrapL w lo hi d source = some (c, top) at h
    erw [show evalIntBuiltin2 (D := D) (.mulW w) x y = Zahl.mulW w x y from rfl]
    apply wrapL_ok (fe := source) (d := d) w (Zahl.mul x y) (Int.mul_nonneg x.lo_le y.lo_le)
      (Zahl.mulW w x y) rfl ?_ h hK hp
    intro ce te emitted fits m pc pre
    exact wideMul_ok (fa := fa) (fb := fb) x y (iha d) (ihb _) emitted fits pre
  | shlW w =>
    have inputBound : (2 : Int) ^ (w + 1) - 1 < 2 ^ (w + 1) := by omega
    have shiftBound : (w : Int) < ((w + 1 : Nat) : Int) := by omega
    let shifted := Zahl.shl (w + 1) inputBound shiftBound (by decide) (by decide) x y
    let u := (2 : Int) ^ (w + 1) - 1
    let source := fun q => wideShlL 0 u 0 (w : Int) 0 (u * 2 ^ w) q fa fb
    change wrapL w 0 (u * 2 ^ w) d source = some (c, top) at h
    erw [show evalIntBuiltin2 (D := D) (.shlW w) x y = Zahl.shlW w x y from rfl]
    apply wrapL_ok (fe := source) (d := d) w shifted shifted.lo_le (Zahl.shlW w x y) rfl ?_ h hK hp
    intro ce te emitted fits m pc pre
    exact wideShl_ok (fa := fa) (fb := fb) (w + 1) inputBound shiftBound (by decide) (by decide) x y
      (iha d) (ihb _) emitted fits pre
  | addS lo hi => exact saturatingAddL_ok x y iha ihb h hK hp
  | rotl w => exact BitBuiltin.rotate_ok false w x y iha ihb d c top h hK m pc hp
  | rotr w => exact BitBuiltin.rotate_ok true w x y iha ihb d c top h hK m pc hp

end Gabbro.Stage0.Senke
