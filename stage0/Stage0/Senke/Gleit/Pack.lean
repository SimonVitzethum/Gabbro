/- Normalization and packing for software binary64 addition
    (`Block.float`, `op = .add`).

    The exact magnitude sum is below `2^54` on this path (two significands
    below `2^53`), so normalization is one conditional bit, not a leading-one
    search: `softNormK` shifts by one exactly past `2^53`, and `softNormQ/R/Den`
    feed the round decision of `Round.lean` (`softFormR_lt`, `softDen_bound`,
    `softNormQ_bound`). A rounded `2^53` carries to `2^52` at the next exponent
    (`softCarry`/`softCarryExp`, value preserved by `softCarry_halves` and
    `softCarry_exact`). `softPack` is the bit pattern (sign, biased exponent,
    fraction) with `softPack_model` against the kernel encoder `gToU64`, and
    `packL` builds it as Stage-0 IR from existing integer opcodes only
    (`shl` 11, `or` 9 via `wordL`/`wordK`) with its `WordCode` correctness
    lemma. The biased exponent arrives formed (unbiased plus bias); subnormal
    left-shifts and the carry branch select in the composition. -/
module
public import Grammatik.Bausteine.Gleitkomma.GleitkommaBits
public import Stage0.Senke.Ausdruck.Aggregat.Hilfena
public import Stage0.Senke.Ausdruck.Gleit.Komposition
public import Stage0.Senke.Gleit.Add
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik
open Gleitkomma
open Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

/-- Normalization shift: one bit down exactly past `2^53` (the exact sum is
    below `2^54`, so no leading-one search is needed on this path). -/
def softNormK (S : Nat) : Nat := if S < 2 ^ 53 then 0 else 1

/-- Common denominator after normalization. -/
def softNormDen (S : Nat) : Nat := 2 ^ softNormK S

/-- Normalized quotient feeding the round decision. -/
def softNormQ (S : Nat) : Nat := S / 2 ^ softNormK S

/-- Remainder feeding the round decision. -/
def softNormR (S : Nat) : Nat := S % 2 ^ softNormK S

/-- The denominator is one or two: far below the signed-word bound the round
    fragment needs, on every input. -/
theorem softDen_bound (S : Nat) : 2 ^ softNormK S < 2 ^ 63 := by
  unfold softNormK
  split <;> decide

/-- The remainder is below the denominator, on every input. -/
theorem softFormR_lt (S : Nat) : S % 2 ^ softNormK S < 2 ^ softNormK S := by
  have hpos : 0 < 2 ^ softNormK S := by
    unfold softNormK
    split <;> decide
  exact Nat.mod_lt _ hpos

/-- The normalized quotient fits 53 bits whenever the exact sum fits 54
    (two significands below `2^53`, the add path's bound). -/
theorem softNormQ_bound (S : Nat) (hS : S < 2 ^ 54) :
    S / 2 ^ softNormK S < 2 ^ 53 := by
  have h54 : (2 : Nat) ^ 54 = 2 * 2 ^ 53 := by decide
  unfold softNormK
  split
  · simp_all
  · show S / 2 < 2 ^ 53
    omega

/-- Carry adjust: a rounded `2^53` is `2^52` at the next exponent. -/
def softCarry (q : Nat) : Nat := if q = 2 ^ 53 then 2 ^ 52 else q

def softCarryExp (e q : Nat) : Nat := if q = 2 ^ 53 then e + 1 else e

/-- Doubling the significand halves the exponent step: the carry keeps the
    exact value. -/
theorem softCarry_halves (e : Nat) : 2 ^ 53 * 2 ^ e = 2 ^ 52 * 2 ^ (e + 1) := by
  rw [show (53 : Nat) = 52 + 1 from rfl, Nat.pow_succ, Nat.pow_succ, mul_assoc,
    mul_comm (2 : Nat) (2 ^ e)]

/-- The carry adjust preserves the exact value on every input. -/
theorem softCarry_exact (q e : Nat) :
    softCarry q * 2 ^ softCarryExp e q = q * 2 ^ e := by
  have hc : (2 : Nat) ^ 53 = 2 ^ 53 := rfl
  by_cases h : q = 2 ^ 53
  · subst h
    unfold softCarry softCarryExp
    repeat rw [if_pos hc]
    exact (softCarry_halves e).symm
  · unfold softCarry softCarryExp
    repeat rw [if_neg h]

/-- Bit pattern: sign, biased exponent, fraction. The biased exponent arrives
    formed (unbiased plus bias); the significand carries its hidden one. -/
def softPack (s : Bool) (bexp frac : Nat) : UInt64 :=
  UInt64.ofNat ((if s then 1 else 0) * 2 ^ 63 + bexp * 2 ^ 52 + frac)

/-- Packing is exactly the kernel encoder on every triple. -/
theorem softPack_model (s : Bool) (bexp frac : Nat) :
    gToU64 ⟨s, bexp, frac⟩ = softPack s bexp frac := by
  have e11 : Format.ebits f64 = 11 := by decide
  have f52 : Format.fracBits f64 = 52 := by decide
  have hsg : (⟨s, bexp, frac⟩ : GBits f64).sign = s := rfl
  have hbe : (⟨s, bexp, frac⟩ : GBits f64).bexp = bexp := rfl
  have hfr : (⟨s, bexp, frac⟩ : GBits f64).frac = frac := rfl
  have h63 : (2 : Nat) ^ (11 + 52) = 2 ^ 63 := by decide
  unfold gToU64 softPack
  rw [zuBits_zerlegt, e11, f52, hsg, hbe, hfr, h63]

/-- Packed word: sign at 63, biased exponent at 52, fraction in the low bits.
    Shift amounts are written as the runner sees them. Fields arrive in range;
    no masking is folded in. -/
def packWord (s e f : Runner.W) : Runner.W :=
  ((s <<< ((BitVec.ofInt 64 63).toNat % 64)) |||
    (e <<< ((BitVec.ofInt 64 52).toNat % 64))) ||| f

/-- `pack = (sign << 63) | (bexp << 52) | frac` as IR (opcodes 11 then 9).
    The shifts complete below their use, so no scratch is clobbered. -/
def packL (d : Nat) (s e f : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  wordL 9 d
    (wordL 9 d (wordK 11 d (s d) 63) (wordK 11 (d + 1) (e (d + 1)) 52))
    (f (d + 1))

/-- Compositional IR simulation for packing. -/
theorem packL_ok {reserved : Nat} {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {s e f : Nat → Option (List II × Nat)} {sv ev fv : Runner.W}
    (hs : WordCode (L := L) (reserved := reserved) ρ W s sv) (he : WordCode (L := L) (reserved := reserved) ρ W e ev)
    (hf : WordCode (L := L) (reserved := reserved) ρ W f fv) :
    WordCode (L := L) (reserved := reserved) ρ W (fun d => packL d s e f) (packWord sv ev fv) := by
  have hc63 : lit32 (63 : Int) = true := by decide
  have hc52 : lit32 (52 : Int) = true := by decide
  have shS : WordCode (L := L) (reserved := reserved) ρ W _ _ := WordCode.bin hs (WordCode.const 63 hc63)
    (g := fun x y => some (x <<< (y.toNat % 64))) rfl rfl (by decide : 11 < 256)
  have shE : WordCode (L := L) (reserved := reserved) ρ W _ _ := WordCode.bin he (WordCode.const 52 hc52)
    (g := fun x y => some (x <<< (y.toNat % 64))) rfl rfl (by decide : 11 < 256)
  have hi : WordCode (L := L) (reserved := reserved) ρ W _ _ := WordCode.bin shS shE
    (g := fun x y => some (x ||| y)) rfl rfl (by decide : 9 < 256)
  have result : WordCode (L := L) (reserved := reserved) ρ W _ _ := WordCode.bin hi hf
    (g := fun x y => some (x ||| y)) rfl rfl (by decide : 9 < 256)
  intro fp K d c top h hK m pc hp
  simpa only [packL, packWord, BitVec.ofInt_ofNat, BitVec.ofNat_eq_ofNat] using
    result (fp := fp) (K := K) (d := d) (c := c) (top := top) h hK m pc hp

/-- Joint fixtures: `1.0`, `-0.0` and `+inf` pack to their bit patterns, and
    the word pack agrees on closed inputs. -/
theorem pack_zeuge :
    softPack false 1023 0 = 4607182418800017408 ∧
    softPack true 0 0 = 9223372036854775808 ∧
    softPack false 2047 0 = 9218868437227405312 ∧
    packWord 1 (BitVec.ofNat 64 1023) (BitVec.ofNat 64 0) =
      BitVec.ofNat 64 4607182418800017408 := by
  decide +kernel

/-- Packing on closed inputs computes and emits. -/
theorem packL_ok_zeuge {Γ : Ctx} (ρ : Env D Γ) (W : Runner.Mem → Prop) :
    WordCode (L := L) ρ W (fun d => packL d
      (fun j => some (konstWL 4 1 j))
      (fun j => some (konstWL 4 1023 j))
      (fun j => some (konstWL 4 0 j)))
      (BitVec.ofNat 64 4607182418800017408) ∧
    (packL 8 (fun j => some (konstWL 4 1 j))
      (fun j => some (konstWL 4 1023 j))
      (fun j => some (konstWL 4 0 j))).isSome = true := by
  constructor
  · intro fp K d c top h hK m pc hp
    have result : WordCode (L := L) ρ W _ _ := packL_ok
      (WordCode.konst 1 (by decide)) (WordCode.konst 1023 (by decide))
      (WordCode.konst 0 (by decide))
    have hx : packWord (BitVec.ofNat 64 1) (BitVec.ofNat 64 1023)
        (BitVec.ofNat 64 0) = BitVec.ofNat 64 4607182418800017408 := by decide
    rw [hx] at result
    exact result h hK m pc hp
  · decide +kernel

#print axioms softDen_bound
#print axioms softFormR_lt
#print axioms softNormQ_bound
#print axioms softCarry_halves
#print axioms softCarry_exact
#print axioms softPack_model
#print axioms packL_ok
#print axioms pack_zeuge
#print axioms packL_ok_zeuge

end Gabbro.Stage0.Senke
