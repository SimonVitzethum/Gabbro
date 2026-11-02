module
public import Stage0.Senke.Ausdruck.Gleit.Skalieren.Teil2a

public import Stage0.Senke.Ausdruck.Gleit.RundCode
public import Stage0.Senke.Ausdruck.Gleit.Schieben
public import Stage0.Senke.Ausdruck.Gleit.Exponent
public import Stage0.Senke.Ausdruck.Gleit.Betrag
public import Stage0.Senke.Ausdruck.Gleit.Skalieren.Teil1

@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}


/-- The emitted magnitude/exponent prefix computes the canonical exponent directly
    from a nonzero signed input, with the range needed by normal packing. -/
theorem floatOfIntAssemblyL_prefix {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {input : Nat → Option (List II × Nat)}
    (z : Int) (hz : -2^63 ≤ z ∧ z < 2^63) (hn : z ≠ 0)
    (hi : WordCode (L := L) ρ W input (BitVec.ofInt 64 z)) :
    WordCode (L := L) ρ W
      (fun d => floatExponentL d (fun j => floatMagnitudeL j input))
      (BitVec.ofInt 64 (Gleitkomma.findeExp z.natAbs 1)) ∧
    (0 ≤ Gleitkomma.findeExp z.natAbs 1 ∧
      Gleitkomma.findeExp z.natAbs 1 ≤ 63) := by
  have hm := floatOfIntAssembly_magnitude_bound z hz
  have hnabs : z.natAbs ≠ 0 := by omega
  have hu := Gleitkomma.bitlen_obere z.natAbs
  have hl := Gleitkomma.bitlen_untere z.natAbs hnabs
  have hb : 0 < Gleitkomma.bitlen z.natAbs := by
    by_cases h : Gleitkomma.bitlen z.natAbs = 0
    · have he : Gleitkomma.bitlen z.natAbs = 0 := h
      simp [he] at hu
      omega
    · omega
  have hp : 2 ^ (Gleitkomma.bitlen z.natAbs - 1) ≤ z.natAbs := by
    have he : Gleitkomma.bitlen z.natAbs =
        (Gleitkomma.bitlen z.natAbs - 1) + 1 := by omega
    rw [he, Nat.pow_succ] at hl
    omega
  have he : Gleitkomma.bitlen z.natAbs - 1 ≤ 63 :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (by omega)
  constructor
  · have hc : WordCode (L := L) ρ W
        (fun d => floatExponentL d (fun j => floatMagnitudeL j input))
        (BitVec.ofInt 64 (Gleitkomma.findeExp
          (floatMagnitudeWord (BitVec.ofInt 64 z)).toNat 1)) :=
      floatExponentL_canonical (floatMagnitudeL_ok hi)
      (show (floatMagnitudeWord (BitVec.ofInt 64 z)).toNat ≠ 0 by rw [hm.1]; exact hnabs)
    rw [hm.1] at hc
    intro fp K d c top h ht m pc hp
    exact hc h ht m pc hp
  · rw [findeExp_integer_nonzero z.natAbs hnabs]
    omega

/-- The actual post-prefix comparison, including both operand temporary ranges.
    Its signed comparison operands are the canonical exponent and fraction width. -/
theorem floatOfIntAssemblyL_compare {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {input : Nat → Option (List II × Nat)}
    (z : Int) (hz : -2^63 ≤ z ∧ z < 2^63) (hn : z ≠ 0)
    (hi : WordCode (L := L) ρ W input (BitVec.ofInt 64 z)) (p : Nat) (hp : p - 1 < 2^64) :
    WordCode (L := L) ρ W
      (fun d => wordL 13 d
        (floatExponentL d (fun j => floatMagnitudeL j input))
        (some (konstWL 4 (p - 1) (d + 1))))
      (Runner.IR.bool ((BitVec.ofInt 64 (Gleitkomma.findeExp z.natAbs 1)).toInt <
        (BitVec.ofNat 64 (p - 1)).toInt)) := by
  have result : WordCode (L := L) ρ W _ _ := WordCode.bin (floatOfIntAssemblyL_prefix z hz hn hi).1
    (WordCode.konst (p - 1) hp)
    (g := fun a b => some (Runner.IR.bool (a.toInt < b.toInt)))
    rfl rfl (by decide : 13 < 256)
  intro fp K d c top h ht m pc hp
  exact result h ht m pc hp

/-- Canonical exponent bounds discharge the signed machine comparison.
    Equality belongs to the right branch, including its zero shift. -/
theorem floatOfIntAssemblyL_compare_canonical {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {input : Nat → Option (List II × Nat)}
    (z : Int) (hz : -2^63 ≤ z ∧ z < 2^63) (hn : z ≠ 0)
    (hi : WordCode (L := L) ρ W input (BitVec.ofInt 64 z))
    (p : Nat) (hp : p - 1 < 2^63) :
    WordCode (L := L) ρ W
      (fun d => wordL 13 d
        (floatExponentL d (fun j => floatMagnitudeL j input))
        (some (konstWL 4 (p - 1) (d + 1))))
      (Runner.IR.bool (Gleitkomma.findeExp z.natAbs 1 < (p - 1 : Nat))) := by
  have he := (floatOfIntAssemblyL_prefix z hz hn hi).2
  have ha : (BitVec.ofInt 64 (Gleitkomma.findeExp z.natAbs 1)).toInt =
      Gleitkomma.findeExp z.natAbs 1 := toInt_ofInt_in (by omega) (by omega)
  have hb : (BitVec.ofNat 64 (p - 1)).toInt = (p - 1 : Nat) := by
    change (BitVec.ofInt 64 ((p - 1 : Nat) : Int)).toInt = _
    exact toInt_ofInt_in (by omega) (by omega)
  intro fp K d c top h ht m pc hpre
  have result := floatOfIntAssemblyL_compare z hz hn hi p (by omega) h ht m pc hpre
  simpa only [ha, hb] using result

/-- The actual comparison selects the right branch also at equality (shift zero).
    Its execution and frame follow from the canonical signed-input prefix. -/
theorem floatOfIntAssemblyL_right_compare {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {input : Nat → Option (List II × Nat)}
    (z : Int) (hz : -2^63 ≤ z ∧ z < 2^63) (hn : z ≠ 0)
    (hi : WordCode (L := L) ρ W input (BitVec.ofInt 64 z))
    (p : Nat) (hp : p - 1 < 2^63)
    (hr : ((p - 1 : Nat) : Int) ≤ Gleitkomma.findeExp z.natAbs 1) :
    WordCode (L := L) ρ W
      (fun d => wordL 13 d
        (floatExponentL d (fun j => floatMagnitudeL j input))
        (some (konstWL 4 (p - 1) (d + 1)))) 0 := by
  have hnot : ¬ Gleitkomma.findeExp z.natAbs 1 < ((p - 1 : Nat) : Int) := by omega
  intro fp K d c top hc ht m pc pre
  have result := floatOfIntAssemblyL_compare_canonical z hz hn hi p hp hc ht m pc pre
  simpa [Runner.IR.bool, hnot] using result

/-- Entry into the actual emitted left scale branch. The comparison prefix runs
    before the branch and its temporary writes satisfy the ordinary frame rule. -/
theorem floatOfIntAssemblyL_left_entry {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {input : Nat → Option (List II × Nat)}
    (z : Int) (hz : -2^63 ≤ z ∧ z < 2^63) (hn : z ≠ 0)
    (hi : WordCode (L := L) ρ W input (BitVec.ofInt 64 z))
    (p : Nat) (hb : p - 1 < 2^64)
    (hlt : (BitVec.ofInt 64 (Gleitkomma.findeExp z.natAbs 1)).toInt <
      (BitVec.ofNat 64 (p - 1)).toInt)
    {m : Runner.Mem} {pc fp : Runner.W} {K d top : Nat}
    {cc ca cb : List II} {tc : Nat}
    (hc : wordL 13 d
      (floatExponentL d (fun j => floatMagnitudeL j input))
      (some (konstWL 4 (p - 1) (d + 1))) = some (cc, tc))
    (hemit : floatOfIntScaleL p d input = some (wennC d cc ca cb, top))
    (ht : tc ≤ K) (hd : d < K)
    (hp : Pre L m pc fp K d (wennC d cc ca cb) ρ W 0) :
    ∃ m', Star ⟨pc, fp⟩ m
      ⟨pc + BitVec.ofNat 64 (16 * (cc.length + 1)), fp⟩ m' ∧
      Agree fp d K m m' ∧
      m'.rd64 (slot fp (BitVec.ofNat 64 d)) = some 1 := by
  apply wenn_taken_entry hp hd
  intro m pc hp
  have h := floatOfIntAssemblyL_compare z hz hn hi p hb hc ht m pc hp
  simpa only [Runner.IR.bool, decide_eq_true hlt, ite_true] using h

/-- The actual scale conditional executes its comparison, left subtraction and
    shift, and end jump; Ok includes the complete temporary frame. -/
theorem floatOfIntScaleL_left {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {input : Nat → Option (List II × Nat)}
    (z : Int) (hz : -2^63 ≤ z ∧ z < 2^63) (hn : z ≠ 0)
    (hi : WordCode (L := L) ρ W input (BitVec.ofInt 64 z))
    (p : Nat) (hp1 : 1 ≤ p) (hpb : p - 1 < 64)
    (hlt : Gleitkomma.findeExp z.natAbs 1 < (p - 1 : Nat))
    {m : Runner.Mem} {pc fp : Runner.W} {K d top : Nat} {c : List II}
    (hc : floatOfIntScaleL p d input = some (c, top))
    (ht : top ≤ K) (hd : d < K)
    (hpre : Pre L m pc fp K d c ρ W 0) :
    Ok m pc fp K d c
      (fun w => w = BitVec.ofNat 64
        (Gleitkomma.normQ p (Gleitkomma.findeExp z.natAbs 1) z.natAbs 1)) := by
  have he := floatOfIntAssemblyL_prefix z hz hn hi
  have hm : WordCode (L := L) ρ W (fun j => floatMagnitudeL j input)
      (floatMagnitudeWord (BitVec.ofInt 64 z)) := floatMagnitudeL_ok hi
  have hk : WordCode (L := L) ρ W
      (fun j => wordL 4 j (some (konstWL 4 (p - 1) j))
        (floatExponentL (j + 1) (fun k => floatMagnitudeL k input)))
      (BitVec.ofNat 64 (((p : Int) - 1) - Gleitkomma.findeExp z.natAbs 1).toNat) := by
    have hs : BitVec.ofNat 64 (p - 1) -
        BitVec.ofInt 64 (Gleitkomma.findeExp z.natAbs 1) =
        BitVec.ofNat 64 (((p : Int) - 1) - Gleitkomma.findeExp z.natAbs 1).toNat := by
      have ee : Gleitkomma.findeExp z.natAbs 1 =
          (Gleitkomma.findeExp z.natAbs 1).toNat := by omega
      rw [ee, BitVec.ofInt_natCast]
      rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]
      congr 1
      omega
    rw [← hs]
    intro fp K d c top h ht m pc pre
    exact WordCode.bin (WordCode.konst (p - 1) (by omega)) he.1
      (o := 4) (g := fun a b => some (a - b)) rfl rfl (by decide) h ht m pc pre
  have hl : WordCode (L := L) ρ W _ _ := floatLeftShiftL_normQ_precision (p := p) hm hk
    (by omega) (by omega)
  have mag := (floatOfIntAssembly_magnitude_bound z hz).1
  exact wennL_ok hc ht hd (bc := true)
    (fun _ _ h t m pc pre => by
      have r := floatOfIntAssemblyL_compare_canonical z hz hn hi p (by omega) h t m pc pre
      simpa [Runner.IR.bool, hlt] using r)
    (fun _ _ _ h t m pc pre => by
      simpa only [Ok, Executes, mag] using hl h t m pc pre)
    (by intro h; cases h) hpre

/-- The actual right scale executes subtraction, nearest-even rounding and jumps. -/
theorem floatOfIntScaleL_right {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {input : Nat → Option (List II × Nat)}
    (z : Int) (hz : -2^63 ≤ z ∧ z < 2^63) (hn : z ≠ 0)
    (hi : WordCode (L := L) ρ W input (BitVec.ofInt 64 z))
    (p : Nat) (hp : 2 ≤ p) (hb : p - 1 < 64)
    (hr : ((p - 1 : Nat) : Int) ≤ Gleitkomma.findeExp z.natAbs 1)
    {m : Runner.Mem} {pc fp : Runner.W} {K d top : Nat} {c : List II}
    (hc : floatOfIntScaleL p d input = some (c, top))
    (ht : top ≤ K) (hd : d < K)
    (pre : Pre L m pc fp K d c ρ W 0) :
    Ok m pc fp K d c (fun w => w = BitVec.ofNat 64
      (Gleitkomma.normQ p (Gleitkomma.findeExp z.natAbs 1) z.natAbs 1)) := by
  have he := floatOfIntAssemblyL_prefix z hz hn hi
  have hs : (Gleitkomma.findeExp z.natAbs 1 - ((p : Int) - 1)).toNat < 63 := by
    have bounds := he.2
    omega
  have hk : WordCode (L := L) ρ W
      (fun j => wordL 4 j
        (floatExponentL j (fun k => floatMagnitudeL k input))
        (some (konstWL 4 (p - 1) (j + 1))))
      (BitVec.ofNat 64 (Gleitkomma.findeExp z.natAbs 1 - ((p : Int) - 1)).toNat) := by
    have eq : BitVec.ofInt 64 (Gleitkomma.findeExp z.natAbs 1) -
        BitVec.ofNat 64 (p - 1) =
        BitVec.ofNat 64 (Gleitkomma.findeExp z.natAbs 1 - ((p : Int) - 1)).toNat := by
      have ee : Gleitkomma.findeExp z.natAbs 1 =
          (Gleitkomma.findeExp z.natAbs 1).toNat := by omega
      rw [ee, BitVec.ofInt_natCast]
      rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]
      congr 1
      omega
    rw [← eq]
    intro fp K d c top h ht m pc pre
    exact WordCode.bin he.1 (WordCode.konst (p - 1) (by omega))
      (o := 4) (g := fun a b => some (a - b)) rfl rfl (by decide) h ht m pc pre
  have round : WordCode (L := L) ρ W _ _ := floatRoundShiftL_normQ_precision (p := p)
    (floatMagnitudeL_ok hi) hk (by omega) hs
  exact wennL_ok hc ht hd (bc := false)
    (fun _ _ h t m pc pre => floatOfIntAssemblyL_right_compare z hz hn hi p (by omega) hr h t m pc pre)
    (by intro h; cases h)
    (fun _ _ _ h t m pc pre => by
      simpa only [Ok, Executes, (floatOfIntAssembly_magnitude_bound z hz).1] using round h t m pc pre) pre

/-- Actual sign instructions derive their contribution from the signed input. -/
theorem floatOfIntSignL_ok {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {input : Nat → Option (List II × Nat)}
    (z : Int) (hz : -2^63 ≤ z ∧ z < 2^63)
    (hi : WordCode (L := L) ρ W input (BitVec.ofInt 64 z))
    (signBit : Nat) (hb : signBit < 2^64) :
    WordCode (L := L) ρ W
      (fun j => wordL 5 j (wordK 13 j (input j) 0)
        (some (konstWL 4 signBit (j + 1))))
      (BitVec.ofNat 64 (if z < 0 then signBit else 0)) := by
  have hs : WordCode (L := L) ρ W _ _ := WordCode.bin hi
    (WordCode.const 0 (by decide))
    (g := fun a b => some (Runner.IR.bool (a.slt b))) rfl rfl (by decide : 13 < 256)
  have ht : WordCode (L := L) ρ W _ _ := WordCode.bin hs (WordCode.konst signBit hb)
    (g := fun a b => some (a * b)) rfl rfl (by decide : 5 < 256)
  have hz' : (BitVec.ofInt 64 z).toInt = z := toInt_ofInt_in hz.1 hz.2
  intro fp K d c top hc hK m pc hp
  have result := ht hc hK m pc hp
  split <;> rename_i hsign
  · simpa [BitVec.slt, hz', Runner.IR.bool, hsign] using result
  · simpa [BitVec.slt, hz', Runner.IR.bool, hsign] using result

end Gabbro.Stage0.Senke
