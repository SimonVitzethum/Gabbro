/- Exact W-bit rotate composition, including the shift-by-W internal zero case. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.WideInt.BitBuiltin.Composition
@[expose] public section

namespace Gabbro.Stage0.Senke.BitBuiltin
open Gabbro.Grammatik Runner.IR
set_option linter.unusedSectionVars false

theorem shift_mod_field (W s x : Nat) (amount : s ≤ W) :
    (x * 2 ^ s) % 2 ^ W = (x % 2 ^ (W - s)) * 2 ^ s := by
  have widths : W - s + s = W := by omega
  calc
    (x * 2 ^ s) % 2 ^ W = (x * 2 ^ s) % (2 ^ (W - s) * 2 ^ s) := by
      rw [← Nat.pow_add, widths]
    _ = (x % 2 ^ (W - s)) * 2 ^ s := Nat.mul_mod_mul_right _ _ _

variable [Kern] {D : Deklaration} {L : Lay D} {fp : Runner.W} {K reserved : Nat}
  {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
local notation "Runs" => Produces L fp K ρ W reserved

theorem rotate_ok (right : Bool) (w : Nat) (x : Zahl 0 ((2 : Int) ^ (w + 1) - 1))
    (s : Zahl 0 (w : Int)) {fa fb : Emitter}
    (ia : Runs fa (.int 0 ((2 : Int) ^ (w + 1) - 1)) x)
    (ib : Runs fb (.int 0 (w : Int)) s) :
    Runs (rotate right w fa fb) (.int 0 ((2 : Int) ^ (w + 1) - 1))
      (if right then Zahl.rotr w x s else Zahl.rotl w x s) := by
  let u := (2 : Int) ^ (w + 1) - 1
  let full : Zahl 0 (w + 1 : Nat) := ⟨(w + 1 : Nat), by omega, by omega⟩
  let widened : Zahl 0 (w + 1 : Nat) := ⟨s.n, s.lo_le, by have := s.le_hi; omega⟩
  let complement : Zahl 0 (w + 1 : Nat) :=
    ⟨(w + 1 : Nat) - s.n, by have := s.le_hi; omega, by have := s.lo_le; omega⟩
  let fwide := cast 0 (w : Int) 0 (w + 1 : Nat) fb
  let fcomp := sub (w + 1 : Nat) (w : Int) (w + 1 : Nat)
    (constant (w + 1 : Nat) (w + 1 : Nat)) fb
  have wideCode : Runs fwide (.int 0 (w + 1 : Nat)) widened := cast_ok s widened rfl ib
  have compCode : Runs fcomp (.int 0 (w + 1 : Nat)) complement :=
    sub_ok full s complement rfl (constant_ok full) ib
  let left := if right then complement else widened
  let rcount := if right then widened else complement
  let fl := if right then fcomp else fwide
  let fr := if right then fwide else fcomp
  have leftCode : Runs fl (.int 0 (w + 1 : Nat)) left := by cases right <;> assumption
  have rightCode : Runs fr (.int 0 (w + 1 : Nat)) rcount := by cases right <;> assumption
  have inputBound : u < (2 : Int) ^ (w + 2) := field_bound w
  let shifted := Zahl.shl (w + 2) inputBound (by omega) (by decide) (by decide) x left
  let high := Zahl.shr (w + 2) inputBound (by omega) (by decide) (by decide) x rcount
  let low := natural u ((x.n.toNat * 2 ^ left.n.toNat) % 2 ^ (w + 1)) (by
    have h := Nat.mod_lt (x.n.toNat * 2 ^ left.n.toNat) (Nat.pow_pos (by decide) : 0 < 2 ^ (w + 1))
    have cast : ((2 ^ (w + 1) : Nat) : Int) = (2 : Int) ^ (w + 1) := by
      simp only [Int.natCast_pow, Int.cast_ofNat_Int]
    dsimp only [u]
    omega)
  have shiftValue : shifted.n = ((x.n.toNat * 2 ^ left.n.toNat : Nat) : Int) := by
    change x.n * 2 ^ left.n.toNat = _
    rw [Int.natCast_mul, Int.natCast_pow, Int.cast_ofNat_Int, Int.toNat_of_nonneg x.lo_le]
  have highValue : high.n = ((x.n.toNat / 2 ^ rcount.n.toNat : Nat) : Int) := by
    change x.n / 2 ^ rcount.n.toNat = _
    rw [Int.natCast_ediv, Int.natCast_pow, Int.cast_ofNat_Int, Int.toNat_of_nonneg x.lo_le]
  have lowCode : Runs (mask (u * 2 ^ (w + 1)) (w + 1) (shl u (w + 1) fa fl)) (.int 0 u) low :=
    mask_ok (w + 1) shifted low (by
      change _ = ((shifted.n.toNat % 2 ^ (w + 1) : Nat) : Int)
      rw [shiftValue, Int.toNat_natCast]
      rfl)
      (shl_ok (w + 2) (w + 1) inputBound (by omega) x left shifted shiftValue ia leftCode)
  have highCode : Runs (shr u (w + 1) fa fr) (.int 0 u) high :=
    shr_ok (w + 2) (w + 1) inputBound (by omega) x rcount high highValue ia rightCode
  have amount := zahlAmt_le w s
  have wideNat : widened.n.toNat = s.n.toNat := rfl
  have compNat : complement.n.toNat = w + 1 - s.n.toNat := by
    have := Int.toNat_of_nonneg s.lo_le
    dsimp only [complement]
    omega
  apply add_ok low high _ ?_ lowCode highCode
  rw [show low.n = ((x.n.toNat * 2 ^ left.n.toNat) % 2 ^ (w + 1) : Nat) from rfl, highValue]
  cases right with
  | false =>
    change (rotln w s.n.toNat x.n.toNat : Int) =
      (((x.n.toNat * 2 ^ widened.n.toNat) % 2 ^ (w + 1) : Nat) : Int) +
        ((x.n.toNat / 2 ^ complement.n.toNat : Nat) : Int)
    rw [wideNat, compNat, shift_mod_field (w + 1) s.n.toNat x.n.toNat (by omega)]
    simp only [rotln, Int.natCast_add]
  | true =>
    change (rotrn w s.n.toNat x.n.toNat : Int) =
      (((x.n.toNat * 2 ^ complement.n.toNat) % 2 ^ (w + 1) : Nat) : Int) +
        ((x.n.toNat / 2 ^ widened.n.toNat : Nat) : Int)
    rw [wideNat, compNat, shift_mod_field (w + 1) (w + 1 - s.n.toNat) x.n.toNat (by omega),
      show w + 1 - (w + 1 - s.n.toNat) = s.n.toNat by omega]
    simp only [rotrn, Int.natCast_add]

end Gabbro.Stage0.Senke.BitBuiltin
