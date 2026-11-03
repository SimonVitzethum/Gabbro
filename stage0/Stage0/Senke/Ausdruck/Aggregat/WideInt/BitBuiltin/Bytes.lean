/- One byte-reversal fold for bswap16, bswap32 and bswap64. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.WideInt.BitBuiltin.Composition
@[expose] public section

namespace Gabbro.Stage0.Senke.BitBuiltin
open Gabbro.Grammatik Runner.IR
set_option linter.unusedSectionVars false

/-- Proof-level packet value of the emitted shift/mask/add fold. -/
def reverseNat : Nat → Nat → Nat
  | 0, _ => 0
  | bytes + 1, x => (x % 256) * 256 ^ bytes + reverseNat bytes (x / 256)

theorem reverseNat_lt (bytes x : Nat) : reverseNat bytes x < 256 ^ bytes := by
  induction bytes generalizing x with
  | zero => simp only [reverseNat, Nat.pow_zero]; decide
  | succ bytes ih =>
    have digit := Nat.mod_lt x (by decide : 0 < 256)
    have rest := ih (x / 256)
    have step := Nat.mul_le_mul_right (256 ^ bytes) (show x % 256 + 1 ≤ 256 by omega)
    rw [Nat.add_mul, Nat.one_mul] at step
    simp only [reverseNat, Nat.pow_succ]
    omega

def reverseValue {hi : Int} (bytes : Nat) (x : Zahl 0 hi) : Zahl 0 ((256 : Int) ^ bytes - 1) :=
  natural ((256 : Int) ^ bytes - 1) (reverseNat bytes x.n.toNat) (by
    have := reverseNat_lt bytes x.n.toNat
    have cast : ((256 ^ bytes : Nat) : Int) = (256 : Int) ^ bytes := by
      simp only [Int.natCast_pow, Int.cast_ofNat_Int]
    omega)

theorem pow_byte (bytes : Nat) : (2 : Nat) ^ (8 * bytes) = 256 ^ bytes := by
  rw [Nat.pow_mul]

theorem reverseNat_bswap16 (x : Nat) : reverseNat 2 x = bswap16n x := by
  simp [reverseNat, bswap16n, byteOf, Nat.div_div_eq_div_mul, Nat.add_assoc]

theorem reverseNat_bswap32 (x : Nat) : reverseNat 4 x = bswap32n x := by
  simp [reverseNat, bswap32n, byteOf, Nat.div_div_eq_div_mul, Nat.add_assoc]

theorem reverseNat_bswap64 (x : Nat) : reverseNat 8 x = bswap64n x := by
  simp [reverseNat, bswap64n, byteOf, Nat.div_div_eq_div_mul, Nat.add_assoc]

variable [Kern] {D : Deklaration} {L : Lay D} {fp : Runner.W} {K reserved : Nat}
  {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
local notation "Runs" => Produces L fp K ρ W reserved

theorem reverseBytes_ok {hi : Int} (width : Nat) (bound : hi < (2 : Int) ^ width)
    (room : 8 < width) (bytes : Nat) (x : Zahl 0 hi) {fa : Emitter}
    (ia : Runs fa (.int 0 hi) x) :
    Runs (reverseBytes hi bytes fa) (.int 0 ((256 : Int) ^ bytes - 1)) (reverseValue bytes x) := by
  induction bytes generalizing x fa with
  | zero =>
    change Runs (constant 0 0) (.int 0 0) (⟨0, by decide, by decide⟩ : Zahl 0 0)
    exact constant_ok (⟨0, by decide, by decide⟩ : Zahl 0 0)
  | succ bytes ih =>
    let eight : Zahl 0 8 := ⟨8, by decide, by decide⟩
    let next : Zahl 0 hi := natural hi (x.n.toNat / 256) (by
      have := Nat.div_le_self x.n.toNat 256
      have := Int.toNat_of_nonneg x.lo_le
      have := x.le_hi
      omega)
    let byte : Zahl 0 255 := natural 255 (x.n.toNat % 256) (by
      have := Nat.mod_lt x.n.toNat (by decide : 0 < 256); omega)
    have nextCode : Runs (shr hi 8 fa (constant 8 8)) (.int 0 hi) next :=
      shr_ok width 8 bound room x eight next rfl ia (constant_ok eight)
    have byteCode : Runs (mask hi 8 fa) (.int 0 255) byte := mask_ok 8 x byte rfl ia
    let amount : Zahl 0 (8 * bytes : Nat) := ⟨(8 * bytes : Nat), by omega, by omega⟩
    have byteBound : (255 : Int) < 2 ^ (8 * bytes + 9) := by
      have mono : (2 : Int) ^ 8 ≤ 2 ^ (8 * bytes + 9) := by
        exact_mod_cast Nat.pow_le_pow_right (by decide : 0 < 2) (show 8 ≤ 8 * bytes + 9 by omega)
      omega
    let shifted := Zahl.shl (8 * bytes + 9) byteBound (by omega) (by decide) (by decide) byte amount
    have shiftedValue : shifted.n = ((x.n.toNat % 256 * 2 ^ (8 * bytes) : Nat) : Int) := by
      change ((x.n.toNat % 256 : Nat) : Int) * 2 ^ (8 * bytes) = _
      rw [Int.natCast_mul, Int.natCast_pow, Int.cast_ofNat_Int]
    have shiftedCode : Runs
        (shl 255 (8 * bytes) (mask hi 8 fa) (constant (8 * bytes : Nat) (8 * bytes : Nat)))
        (.int 0 (255 * 2 ^ (8 * bytes))) shifted :=
      shl_ok (8 * bytes + 9) (8 * bytes) byteBound (by omega) byte amount shifted shiftedValue
        byteCode (constant_ok amount)
    exact add_ok shifted (reverseValue bytes next) (reverseValue (bytes + 1) x)
      (by simp only [reverseValue, natural, reverseNat, next, Int.toNat_natCast,
        shiftedValue, pow_byte, Int.natCast_add]) shiftedCode (ih next nextCode)

end Gabbro.Stage0.Senke.BitBuiltin
