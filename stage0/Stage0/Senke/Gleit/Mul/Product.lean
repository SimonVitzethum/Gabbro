/- Reuse the wide-integer 64 x 64 -> 128 multiplication for softfloat.
   Four 32-bit partial products supply the high limb; ordinary multiplication
   supplies the low limb. The runner needs no new instruction or float opcode. -/
module
public import Stage0.Senke.Ausdruck.Arithmetik.Wide.Multiply.MulWord
public import Stage0.Senke.Gleit.RoutineBranch
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

/-- High multiplication, using exactly the partial-product formula already
    proved for wide integers. All intermediate operations are existing IR. -/
def softMulHighL (d : Nat) (a b : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  let mask := fun j => some (konstWL 4 (2 ^ 32 - 1) j)
  let ah := fun j => wordK 12 j (a j) 32
  let al := fun j => wordL 8 j (a j) (mask (j + 1))
  let bh := fun j => wordK 12 j (b j) 32
  let bl := fun j => wordL 8 j (b j) (mask (j + 1))
  let p0 := fun j => wordL 5 j (al j) (bl (j + 1))
  let p1 := fun j => wordL 5 j (ah j) (bl (j + 1))
  let p2 := fun j => wordL 5 j (al j) (bh (j + 1))
  let p3 := fun j => wordL 5 j (ah j) (bh (j + 1))
  let mid0 := fun j => wordL 3 j (wordK 12 j (p0 j) 32)
    (wordL 8 (j + 1) (p1 (j + 1)) (mask (j + 2)))
  let mid := fun j => wordL 3 j (mid0 j)
    (wordL 8 (j + 1) (p2 (j + 1)) (mask (j + 2)))
  let hi0 := fun j => wordL 3 j (p3 j) (wordK 12 (j + 1) (p1 (j + 1)) 32)
  let hi1 := fun j => wordL 3 j (hi0 j) (wordK 12 (j + 1) (p2 (j + 1)) 32)
  wordL 3 d (hi1 d) (wordK 12 (d + 1) (mid (d + 1)) 32)

/-- Composition certifies the actual emitted high-multiply instructions.
    The natural-number identification is the existing `mulHiW_toNat`. -/
theorem softMulHighL_word {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a b : Nat → Option (List II × Nat)} {av bv : Runner.W}
    (ha : WordCode (L := L) ρ W a av) (hb : WordCode (L := L) ρ W b bv) :
    WordCode (L := L) ρ W (fun d => softMulHighL d a b) (mulHiW av bv) := by
  have mask : WordCode (L := L) ρ W _ _ := WordCode.konst (L := L) (ρ := ρ) (W := W) (2 ^ 32 - 1) (by decide)
  have count : WordCode (L := L) ρ W _ _ := WordCode.const (L := L) (ρ := ρ) (W := W) 32 (by decide)
  have ah : WordCode (L := L) ρ W _ _ := WordCode.bin ha count (g := fun x y => some (x >>> (y.toNat % 64)))
    rfl rfl (by decide : 12 < 256)
  have al : WordCode (L := L) ρ W _ _ := WordCode.bin ha mask (g := fun x y => some (x &&& y))
    rfl rfl (by decide : 8 < 256)
  have bh : WordCode (L := L) ρ W _ _ := WordCode.bin hb count (g := fun x y => some (x >>> (y.toNat % 64)))
    rfl rfl (by decide : 12 < 256)
  have bl : WordCode (L := L) ρ W _ _ := WordCode.bin hb mask (g := fun x y => some (x &&& y))
    rfl rfl (by decide : 8 < 256)
  have p0 : WordCode (L := L) ρ W _ _ := WordCode.bin al bl (g := fun x y => some (x * y))
    rfl rfl (by decide : 5 < 256)
  have p1 : WordCode (L := L) ρ W _ _ := WordCode.bin ah bl (g := fun x y => some (x * y))
    rfl rfl (by decide : 5 < 256)
  have p2 : WordCode (L := L) ρ W _ _ := WordCode.bin al bh (g := fun x y => some (x * y))
    rfl rfl (by decide : 5 < 256)
  have p3 : WordCode (L := L) ρ W _ _ := WordCode.bin ah bh (g := fun x y => some (x * y))
    rfl rfl (by decide : 5 < 256)
  have p0h : WordCode (L := L) ρ W _ _ := WordCode.bin p0 count (g := fun x y => some (x >>> (y.toNat % 64)))
    rfl rfl (by decide : 12 < 256)
  have p1l : WordCode (L := L) ρ W _ _ := WordCode.bin p1 mask (g := fun x y => some (x &&& y))
    rfl rfl (by decide : 8 < 256)
  have p2l : WordCode (L := L) ρ W _ _ := WordCode.bin p2 mask (g := fun x y => some (x &&& y))
    rfl rfl (by decide : 8 < 256)
  have mid0 : WordCode (L := L) ρ W _ _ := WordCode.bin p0h p1l (g := fun x y => some (x + y))
    rfl rfl (by decide : 3 < 256)
  have mid : WordCode (L := L) ρ W _ _ := WordCode.bin mid0 p2l (g := fun x y => some (x + y))
    rfl rfl (by decide : 3 < 256)
  have p1h : WordCode (L := L) ρ W _ _ := WordCode.bin p1 count (g := fun x y => some (x >>> (y.toNat % 64)))
    rfl rfl (by decide : 12 < 256)
  have p2h : WordCode (L := L) ρ W _ _ := WordCode.bin p2 count (g := fun x y => some (x >>> (y.toNat % 64)))
    rfl rfl (by decide : 12 < 256)
  have midh : WordCode (L := L) ρ W _ _ := WordCode.bin mid count (g := fun x y => some (x >>> (y.toNat % 64)))
    rfl rfl (by decide : 12 < 256)
  have hi0 : WordCode (L := L) ρ W _ _ := WordCode.bin p3 p1h (g := fun x y => some (x + y))
    rfl rfl (by decide : 3 < 256)
  have hi1 : WordCode (L := L) ρ W _ _ := WordCode.bin hi0 p2h (g := fun x y => some (x + y))
    rfl rfl (by decide : 3 < 256)
  have result : WordCode (L := L) ρ W _ _ :=
    WordCode.bin hi1 midh (g := fun x y => some (x + y))
      rfl rfl (by decide : 3 < 256)
  intro fp K d c top h hK m pc hp
  have h32 : (32#64).toNat % 64 = 32 := by decide
  simpa only [mulHiW, m32, BitVec.ofInt_ofNat, h32] using
    result (fp := fp) (K := K) (d := d) (c := c) (top := top) h hK m pc hp

/-- Both limbs identify one untruncated product, for arbitrary input words.
    This equation also rules out silently discarding the top 42 product bits. -/
theorem softMulProduct_limbs (a b : Runner.W) :
    (a * b).toNat + (mulHiW a b).toNat * 2 ^ 64 = a.toNat * b.toNat := by
  rw [BitVec.toNat_mul, mulHiW_toNat]
  exact Nat.mod_add_div' _ _

/-- The high-limb emitter exposes the same exact quotient as the generic
    integer routine. This is independent of any floating-point bound. -/
theorem softMulHighL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a b : Nat → Option (List II × Nat)} {av bv : Runner.W}
    (ha : WordCode (L := L) ρ W a av) (hb : WordCode (L := L) ρ W b bv) :
    WordCode (L := L) ρ W (fun d => softMulHighL d a b)
      (BitVec.ofNat 64 (av.toNat * bv.toNat / 2 ^ 64)) := by
  have exactWord : mulHiW av bv = BitVec.ofNat 64 (av.toNat * bv.toNat / 2 ^ 64) := by
    rw [← mulHiW_toNat]
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [← exactWord]
  have result : WordCode (L := L) ρ W _ _ := softMulHighL_word ha hb
  intro fp K d c top h hK m pc hp
  exact result (fp := fp) (K := K) (d := d) (c := c) (top := top) h hK m pc hp

/-- A maximal binary64 significand really occupies both limbs; two maximal
    machine words additionally exercise every carry of the general formula. -/
theorem softMulProduct_limbs_zeuge :
    (BitVec.ofNat 64 (2 ^ 53 - 1) * BitVec.ofNat 64 (2 ^ 53 - 1)).toNat =
      2 ^ 64 - 2 ^ 54 + 1 ∧
    (mulHiW (BitVec.ofNat 64 (2 ^ 53 - 1)) (BitVec.ofNat 64 (2 ^ 53 - 1))).toNat =
      2 ^ 42 - 1 ∧
    (mulHiW (BitVec.ofNat 64 (2 ^ 64 - 1)) (BitVec.ofNat 64 (2 ^ 64 - 1))).toNat =
      2 ^ 64 - 2 := by
  decide +kernel

#print axioms softMulHighL_word
#print axioms softMulProduct_limbs
#print axioms softMulHighL_ok
#print axioms softMulProduct_limbs_zeuge
end Gabbro.Stage0.Senke
