/- Round the three guard bits and pack the binary64 result in integer IR. -/
module
public import Stage0.Senke.Gleit.Normal.Exact
public import Stage0.Senke.Gleit.Pack
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Gleitkomma Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

/-- The normalized word still has three guard bits. Integer rounding uses
    the complete low remainder, including any sticky bit from alignment. -/
def routineRoundMagnitudeWord (a : Runner.W) : Runner.W :=
  BitVec.ofNat 64 (rundeInt (a.toNat / 8) (a.toNat % 8) 8)

def routineRoundMagnitudeL (d : Nat) (a : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  floatRoundShiftL d a (fun j => some ([ci 1 j 3 0], j + 1))

{reserved : Nat} {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a : Nat → Option (List II × Nat)} {av : Runner.W}
    (ha : WordCode (L := L) (reserved := reserved) ρ W a av) :
    WordCode (L := L) (reserved := reserved) ρ W (fun d => routineRoundMagnitudeL d a) (routineRoundMagnitudeWord av) :=
  floatRoundShiftL_ok ha (WordCode.const 3 (by decide)) (by decide : 3 < 63)

/-- The rounded hidden-bit carry changes both significand and exponent.
    Exponent overflow is selected before packing a normal or subnormal. -/
def routineRoundPackWord (sign index magnitude : Runner.W) : Runner.W :=
  let q := routineRoundMagnitudeWord magnitude
  let carry := Runner.IR.bool (q == BitVec.ofNat 64 (2 ^ 53))
  let exponent := index + carry
  let significand := q >>> (carry.toNat % 64)
  if exponent.ult 2047 then
    if significand.ult (BitVec.ofNat 64 (2 ^ 52)) then packWord sign 0 significand
    else packWord sign exponent (significand - BitVec.ofNat 64 (2 ^ 52))
  else packWord sign 2047 0

def routineRoundPackL (d : Nat) (sign index magnitude : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  let q := fun j => routineRoundMagnitudeL j magnitude
  let hidden := fun j => some (konstWL 4 (2 ^ 52) j)
  let carry := fun j => wordL 14 j (q j) (some (konstWL 4 (2 ^ 53) (j + 1)))
  let exponent := fun j => wordL 3 j (index j) (carry (j + 1))
  let sig := fun j => wordL 12 j (q j) (carry (j + 1))
  let zero := fun j => some ([ci 1 j 0 0], j + 1)
  let maxExp := fun j => some ([ci 1 j 2047 0], j + 1)
  let subnormal := fun j => packL j sign zero sig
  let normal := fun j => packL j sign exponent
    (fun k => wordL 4 k (sig k) (hidden (k + 1)))
  let finite := fun j => routineChooseL j (fun k => routineLessL k sig hidden) subnormal normal
  routineChooseL d (fun j => routineLessL j exponent maxExp) finite
    (fun j => packL j sign maxExp zero)

/-- Every branch is an existing checked word fragment. This theorem covers
    the emitted integer routine; canonical IEEE identification is separate. -/
{reserved : Nat} {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {sign index magnitude : Nat → Option (List II × Nat)} {sv ev mv : Runner.W}
    (hs : WordCode (L := L) (reserved := reserved) ρ W sign sv)
    (he : WordCode (L := L) (reserved := reserved) ρ W index ev)
    (hm : WordCode (L := L) (reserved := reserved) ρ W magnitude mv) :
    WordCode (L := L) (reserved := reserved) ρ W (fun d => routineRoundPackL d sign index magnitude)
      (routineRoundPackWord sv ev mv) := by
  have q := routineRoundMagnitudeL_ok hm
  have hidden := WordCode.konst (L := L) (ρ := ρ) (W := W) (2 ^ 52) (by decide)
  have carry := WordCode.bin q (WordCode.konst (2 ^ 53) (by decide))
    (g := fun x y => some (Runner.IR.bool (x == y))) rfl rfl (by decide : 14 < 256)
  have exponent := WordCode.bin he carry
    (g := fun x y => some (x + y)) rfl rfl (by decide : 3 < 256)
  have sig := WordCode.bin q carry
    (g := fun x y => some (x >>> (y.toNat % 64))) rfl rfl (by decide : 12 < 256)
  have zero := WordCode.const (L := L) (ρ := ρ) (W := W) 0 (by decide)
  have maxExp := WordCode.const (L := L) (ρ := ρ) (W := W) 2047 (by decide)
  have subnormal := packL_ok hs zero sig
  have fraction := WordCode.bin sig hidden
    (g := fun x y => some (x - y)) rfl rfl (by decide : 4 < 256)
  have normal := packL_ok hs exponent fraction
  have finite := routineChooseL_ok (routineLessL_ok sig hidden) (fun _ => subnormal) (fun _ => normal)
  exact routineChooseL_ok (routineLessL_ok exponent maxExp) (fun _ => finite)
    (fun _ => packL_ok hs maxExp zero)

theorem routineRoundPackWord_zeuge :
    routineRoundPackWord 0 1023 (BitVec.ofNat 64 (2 ^ 55)) = BitVec.ofNat 64 4607182418800017408 ∧
    routineRoundPackWord 0 1 16 = 2 ∧
    routineRoundPackWord 0 2046 (BitVec.ofNat 64 (2 ^ 56 - 1)) = BitVec.ofNat 64 9218868437227405312 ∧
    routineRoundPackWord 1 1023 (BitVec.ofNat 64 (2 ^ 55 + 4)) = BitVec.ofNat 64 13830554455654793216 := by
  decide +kernel

#print axioms routineRoundMagnitudeL_ok
#print axioms routineRoundPackL_ok
#print axioms routineRoundPackWord_zeuge
end Gabbro.Stage0.Senke
