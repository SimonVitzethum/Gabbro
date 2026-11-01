module

public import Stage0.Senke.Ausdruck.Gleit.RundCode
public import Stage0.Senke.Ausdruck.Gleit.Schieben
public import Stage0.Senke.Ausdruck.Gleit.Exponent
public import Stage0.Senke.Ausdruck.Gleit.Betrag
public import Stage0.Senke.Ausdruck.Gleit.Skalieren.Teil1

@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

/-- Both signs and formats jointly exercise a halfway integer that carries. -/
theorem floatPackCarryL_rundeBruchKern_zeuge {Γ : Ctx} (ρ : Env D Γ)
    (W : Runner.Mem → Prop) :
    ∀ F ∈ [Gleitkomma.f32, Gleitkomma.f64], ∀ sign : Bool,
      let n := 2^(F.p + 1) - 1
      let E : Int := F.p
      let lit := fun n d => some (konstWL 4 n d)
      Gleitkomma.normQ F.p E n 1 = 2 * 2^F.fracBits ∧
      WordCode (L := L) ρ W
        (fun dst => floatPackCarryL dst
          (lit (if sign then 2^(F.ebits + F.fracBits) else 0))
          (lit (E - F.emin + 1).toNat)
          (lit (Gleitkomma.normQ F.p E n 1)) (2^F.fracBits))
        (BitVec.ofNat 64 (Gleitkomma.zuBits F
          (Gleitkomma.rundeBruchKern F sign n 1 E))) := by
  intro F hF sign
  have hb : 1 ≤ F.p ∧ F.fracBits = F.p - 1 ∧
      F.emin ≤ (F.p : Int) ∧ (F.p : Int) < F.emax ∧
      2 * 2^F.fracBits < 2^64 ∧ F.bexpMax ≤ 2^64 ∧
      (0 < ((F.p : Int) - F.emin + 1).toNat ∧
        ((F.p : Int) - F.emin + 1).toNat + 1 < F.bexpMax) ∧
      Gleitkomma.normQ F.p (F.p : Int) (2^(F.p + 1) - 1) 1 = 2 * 2^F.fracBits ∧
      (if sign then 2^(F.ebits + F.fracBits) else 0) < 2^64 ∧
      ((F.p : Int) - F.emin + 1).toNat < 2^64 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
    rcases hF with rfl | rfl <;> cases sign <;> decide +kernel
  refine ⟨hb.2.2.2.2.2.2.2.1, ?_⟩
  apply floatPackCarryL_rundeBruchKern
  · exact WordCode.konst _ hb.2.2.2.2.2.2.2.2.1
  · exact WordCode.konst _ hb.2.2.2.2.2.2.2.2.2
  · apply WordCode.konst
    rw [hb.2.2.2.2.2.2.2.1]
    exact hb.2.2.2.2.1
  · exact hb.1
  · exact hb.2.1
  · exact hb.2.2.1
  · exact hb.2.2.2.1
  · exact hb.2.2.2.2.1
  · exact hb.2.2.2.2.2.1
  · exact hb.2.2.2.2.2.2.1
  · rw [hb.2.2.2.2.2.2.2.1]
    constructor <;> omega


 theorem floatPackCarry_nat_zeuge :
    (Runner.IR.bool (BitVec.ofNat 64 16 == BitVec.ofNat 64 16)).toNat = 1 ∧
    (Runner.IR.bool (BitVec.ofNat 64 15 == BitVec.ofNat 64 16)).toNat = 0 := by
  decide +kernel

/-- The zero path emits positive zero, including signed integer zero. -/
def floatPackZeroL (d : Nat) : Option (List II × Nat) :=
  some (konstWL 4 0 d)

theorem floatPackZeroL_ok {Γ : Ctx} (ρ : Env D Γ) (W : Runner.Mem → Prop) :
    WordCode (L := L) ρ W floatPackZeroL (BitVec.ofNat 64 0) :=
  WordCode.konst 0 (by decide)

/-- Signed integer zero has positive sign in the canonical G conversion. -/
theorem floatPackZeroL_canonical {Γ : Ctx} (ρ : Env D Γ) (W : Runner.Mem → Prop)
    (F : Gleitkomma.Format) :
    WordCode (L := L) ρ W floatPackZeroL
      (BitVec.ofNat 64 (Gleitkomma.zuBits F (Gleitkomma.ofInt F 0))) := by
  have hz : Gleitkomma.ofInt F 0 = ⟨false, 0, 0⟩ := by
    change Gleitkomma.rundeBruchBei F false 0 1 = _
    exact normalize_integer_zero F false
  rw [hz]
  simp only [Gleitkomma.zuBits, Bool.false_eq_true, ite_false, Nat.zero_mul, Nat.zero_add]
  change WordCode (L := L) ρ W floatPackZeroL (BitVec.ofNat 64 0)
  intro fp K d c top h hK m pc hp
  exact floatPackZeroL_ok (L := L) ρ W h hK m pc hp

/-- Both formats jointly witness emitted code and canonical signed conversion. -/
theorem floatPackZeroL_canonical_zeuge {Γ : Ctx} (ρ : Env D Γ)
    (W : Runner.Mem → Prop) :
    ∀ F ∈ [Gleitkomma.f32, Gleitkomma.f64],
      (floatPackZeroL 8).isSome = true ∧
      WordCode (L := L) ρ W floatPackZeroL
        (BitVec.ofNat 64 (Gleitkomma.zuBits F (Gleitkomma.ofInt F 0))) := by
  intro F _
  exact ⟨by decide, floatPackZeroL_canonical ρ W F⟩

/-- The scale branch shared by the actual integer assembly and its entry proof. -/
def floatOfIntScaleL (p d : Nat) (input : Nat → Option (List II × Nat)) :=
  let magnitude := fun j => floatMagnitudeL j input
  let exponent := fun j => floatExponentL j magnitude
  let threshold := fun j => some (konstWL 4 (p - 1) j)
  wennL d (wordL 13 d (exponent d) (threshold (d + 1)))
    (wordL 11 d (magnitude d)
      (wordL 4 (d + 1) (threshold (d + 1)) (exponent (d + 2))))
    (floatRoundShiftL d magnitude
      (fun j => wordL 4 j (exponent j) (threshold (j + 1))))

/-- Integer conversion candidate, kept off lowE until full simulation is proved.
    Binary combinators reserve d and evaluate the right operand at d+1.
    Branches share d; pure inputs are recomputed in separate temporary ranges. -/
def floatOfIntAssemblyL (p bias signBit : Nat) (d : Nat)
    (input : Nat → Option (List II × Nat)) : Option (List II × Nat) :=
  let magnitude := fun j => floatMagnitudeL j input
  let exponent := fun j => floatExponentL j magnitude
  let scale := fun j => floatOfIntScaleL p j input
  let sign := fun j => wordL 5 j (wordK 13 j (input j) 0)
    (some (konstWL 4 signBit (j + 1)))
  let biased := fun j => wordL 3 j (exponent j)
    (some (konstWL 4 bias (j + 1)))
  wennL d (wordK 14 d (magnitude d) 0) (floatPackZeroL d)
    (floatPackCarryL d sign biased scale (2^(p - 1)))

/-- The emitted zero branch alone reserves the assembly destination. -/
theorem floatOfIntAssemblyL_ceiling {p bias signBit d : Nat}
    {input : Nat → Option (List II × Nat)} {out : List II × Nat}
    (h : floatOfIntAssemblyL p bias signBit d input = some out) :
    d + 1 ≤ out.2 := by
  simp only [floatOfIntAssemblyL, wennL, floatPackZeroL, bind,
    Option.bind_eq_some_iff] at h
  obtain ⟨cc, hc, ca, ha, cb, hb, h⟩ := h
  split at h
  · cases h
    simp only [Option.some.injEq] at ha
    subst ca
    simp only [konstWL, bin2] at *
    omega
  · contradiction

/-- The signed input interval bounds the unsigned magnitude, including minInt. -/
theorem floatOfIntAssembly_magnitude_bound (z : Int)
    (hz : -2^63 ≤ z ∧ z < 2^63) :
    (floatMagnitudeWord (BitVec.ofInt 64 z)).toNat = z.natAbs ∧
      z.natAbs ≤ 2^63 := by
  have hb : z.natAbs ≤ 2^63 := by
    omega
  rw [floatMagnitudeWord_model z hz, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show z.natAbs < 2^64 by omega)]
  exact ⟨rfl, hb⟩

/-- Both IEEE formats keep every signed-word exponent and scaling count in range.
    These bounds include minInt and do not assume a precomputed exponent. -/
theorem floatOfIntAssembly_scale_bounds (F : Gleitkomma.Format)
    (hF : F ∈ [Gleitkomma.f32, Gleitkomma.f64]) (E : Int)
    (hE : 0 ≤ E ∧ E ≤ 63) :
    F.emin ≤ E ∧ E < (F.emax : Int) ∧
    (E - ((F.p : Int) - 1)).toNat < 63 ∧
    (((F.p : Int) - 1) - E).toNat < 64 ∧
    (0 < (E - F.emin + 1).toNat ∧
      (E - F.emin + 1).toNat + 1 < F.bexpMax) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
  rcases hF with rfl | rfl <;>
    simp only [Gleitkomma.f32, Gleitkomma.f64, Gleitkomma.Format.emin,
      Gleitkomma.Format.emax, Gleitkomma.Format.bexpMax] <;> omega

/-- The actual assembled zero branch includes magnitude computation and the jump.
    The generic branch rule preserves the frame and validates emitted offsets. -/
theorem floatOfIntAssemblyL_zero {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {input : Nat → Option (List II × Nat)}
    (hi : WordCode (L := L) ρ W input (BitVec.ofInt 64 0))
    (p bias signBit : Nat) :
    WordCode (L := L) ρ W (fun d => floatOfIntAssemblyL p bias signBit d input)
      (BitVec.ofNat 64 0) := by
  have hm : WordCode (L := L) ρ W (fun d => floatMagnitudeL d input) (floatMagnitudeWord (BitVec.ofInt 64 0)) := floatMagnitudeL_ok hi
  have hc : WordCode (L := L) ρ W
      (fun d => wordK 14 d (floatMagnitudeL d input) 0) 1 := by
    intro fp K d c top h ht m pc hp
    exact wordK_ok h ht (by decide) (fun _ _ he ht => hm he ht)
      (g := fun a b => some (Runner.IR.bool (a == b)))
      (fun a ha => by subst a; exact ⟨1, by decide, rfl⟩)
      rfl (by decide) hp
  intro fp K d c top h ht m pc hp
  have hd : d < K := by
    have hh := h
    simp only [floatOfIntAssemblyL, wennL, bind, Option.bind_eq_some_iff] at hh
    obtain ⟨⟨cc, tc⟩, _, ⟨ca, ta⟩, ha, ⟨cb, tb⟩, _, hh⟩ := hh
    simp only [floatPackZeroL, Option.some.injEq, Prod.mk.injEq] at ha
    cases ha
    split at hh
    · cases hh; simp only [konstWL, bin2] at ht; omega
    · contradiction
  exact wennL_ok h ht hd (bc := true)
    (fun _ _ he ht => hc he ht)
    (fun _ _ _ he ht => floatPackZeroL_ok ρ W he ht)
    (by intro h; cases h) hp

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
