/- Shared integer-only extraction of IEEE fields for arithmetic dispatch. -/
import Stage0.Senke.Ausdruck.Arithmetik.Vorzeichen

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem

/-- A single extraction mechanism serves sign, exponent and fraction fields. -/
def floatFieldWord (w : Runner.W) (offset width : Nat) : Runner.W :=
  (w >>> offset) &&& BitVec.ofNat 64 (2^width - 1)

/-- The integer mechanism extracts the mathematical binary field. -/
theorem floatFieldWord_model (w : Runner.W) (offset width : Nat)
    (hm : 2^width - 1 < 2^64) :
    (floatFieldWord w offset width).toNat = w.toNat / 2^offset % 2^width := by
  simp only [floatFieldWord, BitVec.toNat_and, BitVec.toNat_ushiftRight,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow]

/-- The packed input decodes through the existing canonical inverse. -/
theorem floatFieldWord_canonical (a : GFloat) (ha : Gleitkomma.wf Gleitkomma.f64 a) :
    let w := BitVec.ofNat 64 (Gleitkomma.zuBits Gleitkomma.f64 a)
    (floatFieldWord w 0 52).toNat = a.frac ∧
    (floatFieldWord w 52 11).toNat = a.bexp := by
  have inv := Gleitkomma.ausBits_zuBits _ Gleitkomma.f64_dicht a ha
  have bound := Gleitkomma.zuBits_lt _ Gleitkomma.f64_dicht a ha
  have hw : Gleitkomma.f64.ebits + Gleitkomma.f64.fracBits + 1 = 64 := by decide
  rw [hw] at bound
  have hf := congrArg (fun x : GFloat => x.frac) inv
  have he := congrArg (fun x : GFloat => x.bexp) inv
  change Gleitkomma.zuBits Gleitkomma.f64 a % 2^52 = a.frac at hf
  change Gleitkomma.zuBits Gleitkomma.f64 a / 2^52 % 2^11 = a.bexp at he
  dsimp only
  rw [floatFieldWord_model _ 0 52 (by decide), floatFieldWord_model _ 52 11 (by decide)]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound, Nat.pow_zero, Nat.div_one]
  exact ⟨hf, he⟩

/-- Offset is an immediate and must fit the runner's shift-count convention.
    Width is materialised as an arbitrary-word mask, with no signed division. -/
def floatFieldL (offset width d : Nat) (e : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  if offset < 64 then
    wordL 8 d (wordL 12 d (e d) (some ([ci 1 ((d + 1 : Nat) : Int) offset 0], d + 2)))
      (some (konstWL 4 (2^width - 1) (d + 1)))
  else none

/-- Exact cost of the shared extraction after the input producer. -/
theorem floatFieldL_shape (offset width d : Nat) (ho : offset < 64)
    (e : Nat → Option (List II × Nat)) (code : List II) (top : Nat)
    (he : e d = some (code, top)) :
    ∃ output, floatFieldL offset width d e = some (output, max top (d + 3)) ∧
      output.length = code.length + 20 := by
  simp [floatFieldL, ho, wordL, he, konstWL, bin2, Nat.max_assoc,
    Nat.max_eq_left (show d + 2 ≤ d + 3 by omega)]

/-- A signed NaN jointly satisfies the canonical inverse and both field
    bridges, exercising the high input bit and a nonzero payload. -/
theorem floatFieldWord_canonical_zeuge :
    let a : GFloat := ⟨true, 2047, 9⟩
    Gleitkomma.wf Gleitkomma.f64 a ∧
    (floatFieldWord (BitVec.ofNat 64 (Gleitkomma.zuBits _ a)) 0 52).toNat = 9 ∧
    (floatFieldWord (BitVec.ofNat 64 (Gleitkomma.zuBits _ a)) 52 11).toNat = 2047 := by
  decide +kernel

variable [Kern] {D : Deklaration} {L : Lay D}

/-- Generic code simulation carries the producer's full frame agreement. -/
theorem floatFieldL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {e : Nat → Option (List II × Nat)} {w : Runner.W}
    (offset width : Nat) (ho : offset < 64) (hm : 2^width - 1 < 2^64)
    (he : WordCode (L := L) ρ W e w) :
    WordCode (L := L) ρ W (fun d => floatFieldL offset width d e)
      (floatFieldWord w offset width) := by
  have shift : WordCode (L := L) ρ W
      (fun d => wordL 12 d (e d) (some ([ci 1 ((d + 1 : Nat) : Int) offset 0], d + 2)))
      (w >>> offset) := by
    have hg : (some (w >>> ((BitVec.ofInt 64 offset).toNat % 64)) : Option Runner.W) =
        some (w >>> offset) := by
      have heq : (BitVec.ofInt 64 offset).toNat = offset := by
        rw [BitVec.ofInt_natCast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      rw [heq, Nat.mod_eq_of_lt ho]
    intro fp K d c top h hK m pc hp
    exact WordCode.bin he (WordCode.const offset (lit32_nat (by omega)))
      (g := fun a b => some (a >>> (b.toNat % 64))) hg rfl (by decide : 12 < 256)
      h hK m pc hp
  have result : WordCode (L := L) ρ W
      (fun d => wordL 8 d (wordL 12 d (e d) (some ([ci 1 ((d + 1 : Nat) : Int) offset 0], d + 2)))
        (some (konstWL 4 (2^width - 1) (d + 1)))) (floatFieldWord w offset width) :=
    WordCode.bin shift (WordCode.konst (2^width - 1) hm)
      (g := fun a b => some (a &&& b)) rfl rfl (by decide : 8 < 256)
  intro fp K d c top h hK m pc hp
  simp only [floatFieldL, ho, ↓reduceIte] at h
  exact result h hK m pc hp

#print axioms floatFieldWord_canonical
#print axioms floatFieldL_ok
end Gabbro.Stage0.Senke
