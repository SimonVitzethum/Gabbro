module

public import Stage0.Senke.Ausdruck.Gleit.RundCode
public import Stage0.Senke.Ausdruck.Gleit.Schieben
public import Stage0.Senke.Ausdruck.Gleit.Exponent
public import Stage0.Senke.Ausdruck.Gleit.Betrag
public import Stage0.Senke.Ausdruck.Gleit.Skalieren.Teil2

@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

theorem floatOfIntLeftPackL_ok {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {input : Nat → Option (List II × Nat)}
    (z : Int) (hz : -2^63 ≤ z ∧ z < 2^63) (hn : z ≠ 0)
    (hi : WordCode (L := L) ρ W input (BitVec.ofInt 64 z))
    (p bias signBit : Nat) (hp : 1 ≤ p) (hpb : p - 1 < 63)
    (hb : bias < 2^64) (hsb : signBit < 2^64)
    (hlt : Gleitkomma.findeExp z.natAbs 1 < (p - 1 : Nat)) :
    let ev := BitVec.ofInt 64 (Gleitkomma.findeExp z.natAbs 1) + BitVec.ofNat 64 bias
    let qv := BitVec.ofNat 64
      (Gleitkomma.normQ p (Gleitkomma.findeExp z.natAbs 1) z.natAbs 1)
    let unit := 2^(p - 1)
    let carry := Runner.IR.bool (qv == BitVec.ofNat 64 (2 * unit))
    WordCode (L := L) ρ W (fun d => floatPackCarryL d
      (fun j => wordL 5 j (wordK 13 j (input j) 0)
        (some (konstWL 4 signBit (j + 1))))
      (fun j => wordL 3 j (floatExponentL j (fun k => floatMagnitudeL k input))
        (some (konstWL 4 bias (j + 1))))
      (fun j => floatOfIntScaleL p j input) unit)
      (BitVec.ofNat 64 (if z < 0 then signBit else 0) +
        (ev + carry) * BitVec.ofNat 64 unit +
        ((qv >>> (carry.toNat % 64)) - BitVec.ofNat 64 unit)) := by
  have he : WordCode (L := L) ρ W _ _ := WordCode.bin (floatOfIntAssemblyL_prefix z hz hn hi).1
    (WordCode.konst bias hb) (g := fun a b => some (a + b))
    rfl rfl (by decide : 3 < 256)
  have hq : WordCode (L := L) ρ W (fun j => floatOfIntScaleL p j input)
      (BitVec.ofNat 64 (Gleitkomma.normQ p (Gleitkomma.findeExp z.natAbs 1) z.natAbs 1)) := by
    intro fp K d c top hc ht m pc pre
    exact floatOfIntScaleL_left z hz hn hi p hp (by omega) hlt hc ht
      (by
        have hh := hc
        simp only [floatOfIntScaleL, wennL, bind, Option.bind_eq_some_iff] at hh
        obtain ⟨⟨cc, tc⟩, _, ⟨ca, ta⟩, ha, ⟨cb, tb⟩, _, hh⟩ := hh
        simp only [wordL, bin2, bind, Option.bind_eq_some_iff] at ha
        obtain ⟨a, _, b, _, ha⟩ := ha
        cases ha
        split at hh
        · cases hh; omega
        · contradiction) pre
  apply floatPackCarryL_ok (floatOfIntSignL_ok z hz hi signBit hsb) he hq
  have hpow : 2^(p - 1) < 2^63 := Nat.pow_lt_pow_right (by decide) hpb
  omega

/-- Connected execution of the actual signed right scaling and packing instructions.
    The result is stated at word level; canonical field bounds are a separate obligation. -/
theorem floatOfIntRightPackL_ok {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {input : Nat → Option (List II × Nat)}
    (z : Int) (hz : -2^63 ≤ z ∧ z < 2^63) (hn : z ≠ 0)
    (hi : WordCode (L := L) ρ W input (BitVec.ofInt 64 z))
    (p bias signBit : Nat) (hp : 2 ≤ p) (hpb : p - 1 < 63)
    (hb : bias < 2^64) (hsb : signBit < 2^64)
    (hr : ((p - 1 : Nat) : Int) ≤ Gleitkomma.findeExp z.natAbs 1) :
    let ev := BitVec.ofInt 64 (Gleitkomma.findeExp z.natAbs 1) + BitVec.ofNat 64 bias
    let qv := BitVec.ofNat 64
      (Gleitkomma.normQ p (Gleitkomma.findeExp z.natAbs 1) z.natAbs 1)
    let unit := 2^(p - 1)
    let carry := Runner.IR.bool (qv == BitVec.ofNat 64 (2 * unit))
    WordCode (L := L) ρ W (fun d => floatPackCarryL d
      (fun j => wordL 5 j (wordK 13 j (input j) 0)
        (some (konstWL 4 signBit (j + 1))))
      (fun j => wordL 3 j (floatExponentL j (fun k => floatMagnitudeL k input))
        (some (konstWL 4 bias (j + 1))))
      (fun j => floatOfIntScaleL p j input) unit)
      (BitVec.ofNat 64 (if z < 0 then signBit else 0) +
        (ev + carry) * BitVec.ofNat 64 unit +
        ((qv >>> (carry.toNat % 64)) - BitVec.ofNat 64 unit)) := by
  have he : WordCode (L := L) ρ W _ _ := WordCode.bin (floatOfIntAssemblyL_prefix z hz hn hi).1
    (WordCode.konst bias hb) (g := fun a b => some (a + b))
    rfl rfl (by decide : 3 < 256)
  have hq : WordCode (L := L) ρ W (fun j => floatOfIntScaleL p j input)
      (BitVec.ofNat 64 (Gleitkomma.normQ p (Gleitkomma.findeExp z.natAbs 1) z.natAbs 1)) := by
    intro fp K d c top hc ht m pc pre
    exact floatOfIntScaleL_right z hz hn hi p hp (by omega) hr hc ht
      (by
        have hh := hc
        simp only [floatOfIntScaleL, wennL, bind, Option.bind_eq_some_iff] at hh
        obtain ⟨⟨cc, tc⟩, _, ⟨ca, ta⟩, ha, ⟨cb, tb⟩, _, hh⟩ := hh
        simp only [wordL, bin2, bind, Option.bind_eq_some_iff] at ha
        obtain ⟨a, _, b, _, ha⟩ := ha
        cases ha
        split at hh
        · cases hh; omega
        · contradiction) pre
  apply floatPackCarryL_ok (floatOfIntSignL_ok z hz hi signBit hsb) he hq
  have hpow : 2^(p - 1) < 2^63 := Nat.pow_lt_pow_right (by decide) hpb
  omega

/-- Signed input execution supplies the canonical normal exponent field bounds. -/
theorem floatOfIntAssemblyL_normal_exponent {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {input : Nat → Option (List II × Nat)}
    (z : Int) (hz : -2^63 ≤ z ∧ z < 2^63) (hn : z ≠ 0)
    (hi : WordCode (L := L) ρ W input (BitVec.ofInt 64 z))
    (F : Gleitkomma.Format) (hF : F ∈ [Gleitkomma.f32, Gleitkomma.f64]) :
    let E := Gleitkomma.findeExp z.natAbs 1
    F.emin ≤ E ∧ E < (F.emax : Int) ∧
      0 < (E - F.emin + 1).toNat ∧
      (E - F.emin + 1).toNat + 1 < F.bexpMax := by
  have h := floatOfIntAssembly_scale_bounds F hF _
    (floatOfIntAssemblyL_prefix z hz hn hi).2
  exact ⟨h.1, h.2.1, h.2.2.2.2⟩

/-- Integer left normalization derives both significand bounds from the input. -/
theorem floatOfInt_left_significand_bounds (n p : Nat) (hn : n ≠ 0)
    (hlt : Gleitkomma.findeExp n 1 < (p - 1 : Nat)) :
    2^(p - 1) ≤ Gleitkomma.normQ p (Gleitkomma.findeExp n 1) n 1 ∧
    Gleitkomma.normQ p (Gleitkomma.findeExp n 1) n 1 < 2^p := by
  have he := findeExp_integer_nonzero n hn
  have hu := Gleitkomma.bitlen_obere n
  have hl := Gleitkomma.bitlen_untere n hn
  have hb : 0 < Gleitkomma.bitlen n := by
    cases h : Gleitkomma.bitlen n with
    | zero => simp [h] at hu; omega
    | succ k => omega
  have hp : 1 ≤ p := by omega
  rw [floatNormQ_left p _ n (by omega)]
  have hs : ((p : Int) - 1 - Gleitkomma.findeExp n 1).toNat =
      p - Gleitkomma.bitlen n := by omega
  rw [hs]
  have hsum : Gleitkomma.bitlen n + (p - Gleitkomma.bitlen n) = p := by omega
  have hsum' : (Gleitkomma.bitlen n - 1) + (p - Gleitkomma.bitlen n) = p - 1 := by omega
  have hlo : 2^(Gleitkomma.bitlen n - 1) ≤ n := by
    have hh : Gleitkomma.bitlen n = (Gleitkomma.bitlen n - 1) + 1 := by omega
    rw [hh, Nat.pow_succ] at hl
    omega
  constructor
  · calc
      2^(p - 1) = 2^(Gleitkomma.bitlen n - 1) * 2^(p - Gleitkomma.bitlen n) := by rw [← Nat.pow_add, hsum']
      _ ≤ n * 2^(p - Gleitkomma.bitlen n) := Nat.mul_le_mul_right _ hlo
  · calc
      n * 2^(p - Gleitkomma.bitlen n) < 2^Gleitkomma.bitlen n * 2^(p - Gleitkomma.bitlen n) := Nat.mul_lt_mul_of_pos_right hu (Nat.pow_pos (by decide))
      _ = 2^p := by rw [← Nat.pow_add, hsum]

/-- Canonical integer conversion on the left path has no carry or rounding loss. -/
theorem floatOfInt_left_canonical (F : Gleitkomma.Format) (z : Int)
    (hn : z ≠ 0) (hp : 1 ≤ F.p)
    (hlo : F.emin ≤ Gleitkomma.findeExp z.natAbs 1)
    (hhi : Gleitkomma.findeExp z.natAbs 1 < (F.emax : Int))
    (hlt : Gleitkomma.findeExp z.natAbs 1 < (F.p - 1 : Nat)) :
    Gleitkomma.ofInt F z =
      ⟨decide (z < 0), (Gleitkomma.findeExp z.natAbs 1 - F.emin + 1).toNat,
        Gleitkomma.normQ F.p (Gleitkomma.findeExp z.natAbs 1) z.natAbs 1 -
          2^(F.p - 1)⟩ := by
  have ha : z.natAbs ≠ 0 := by omega
  have hq := floatOfInt_left_significand_bounds z.natAbs F.p ha hlt
  simp only [Gleitkomma.ofInt, Gleitkomma.rundeExakt, Gleitkomma.exaktBruch,
    Int.le_refl, ↓reduceIte, Int.toNat_zero, Nat.pow_zero, Int.natCast_one, Int.mul_one,
    Gleitkomma.rundeBruch, Gleitkomma.rundeBruchBei, Nat.one_ne_zero, ha]
  rw [floatPackCarry_rundeBruchKern F _ _ _ _ hp hlo hhi, if_pos hq.2]

/-- The actual left packer returns the canonical integer-conversion bits. -/
theorem floatOfIntLeftPackL_ofInt {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {input : Nat → Option (List II × Nat)}
    (F : Gleitkomma.Format) (z : Int)
    (hz : -2^63 ≤ z ∧ z < 2^63) (hn : z ≠ 0)
    (hi : WordCode (L := L) ρ W input (BitVec.ofInt 64 z))
    (hp : 1 ≤ F.p) (hpb : F.p - 1 < 63)
    (hfrac : F.fracBits = F.p - 1)
    (bias : Nat) (hb : bias < 2^64)
    (hsb : 2^(F.ebits + F.fracBits) < 2^64)
    (hu : 2 * 2^F.fracBits < 2^64) (hm : F.bexpMax ≤ 2^64)
    (hlo : F.emin ≤ Gleitkomma.findeExp z.natAbs 1)
    (hhi : Gleitkomma.findeExp z.natAbs 1 < (F.emax : Int))
    (he : 0 < (Gleitkomma.findeExp z.natAbs 1 - F.emin + 1).toNat ∧
      (Gleitkomma.findeExp z.natAbs 1 - F.emin + 1).toNat + 1 < F.bexpMax)
    (heb : BitVec.ofInt 64 (Gleitkomma.findeExp z.natAbs 1) + BitVec.ofNat 64 bias =
      BitVec.ofNat 64 (Gleitkomma.findeExp z.natAbs 1 - F.emin + 1).toNat)
    (hlt : Gleitkomma.findeExp z.natAbs 1 < (F.p - 1 : Nat)) :
    WordCode (L := L) ρ W (fun d => floatPackCarryL d
      (fun j => wordL 5 j (wordK 13 j (input j) 0)
        (some (konstWL 4 (2^(F.ebits + F.fracBits)) (j + 1))))
      (fun j => wordL 3 j (floatExponentL j (fun k => floatMagnitudeL k input))
        (some (konstWL 4 bias (j + 1))))
      (fun j => floatOfIntScaleL F.p j input) (2^(F.p - 1)))
      (BitVec.ofNat 64 (Gleitkomma.zuBits F (Gleitkomma.ofInt F z))) := by
  have hq := floatOfInt_left_significand_bounds z.natAbs F.p (by omega) hlt
  have poweq : 2 * 2^(F.p - 1) = 2^F.p := by
    rw [Nat.mul_comm, ← Nat.pow_succ]
    congr 1
    omega
  have pack := floatPackCarry_canonical F (decide (z < 0))
    (Gleitkomma.findeExp z.natAbs 1 - F.emin + 1).toNat
    (Gleitkomma.normQ F.p (Gleitkomma.findeExp z.natAbs 1) z.natAbs 1)
    hu hm he (by rw [hfrac, poweq]; exact ⟨hq.1, Nat.le_of_lt hq.2⟩)
  have hncarry : Gleitkomma.normQ F.p (Gleitkomma.findeExp z.natAbs 1) z.natAbs 1 ≠
      2 * 2^F.fracBits := by rw [hfrac, poweq]; omega
  simp only [hncarry, ↓reduceIte, Nat.add_zero] at pack
  rw [floatOfInt_left_canonical F z hn hp hlo hhi hlt]
  rw [hfrac] at pack
  rw [← pack]
  intro fp K d c top hc ht m pc pre
  simpa only [decide_eq_true_eq, heb, hfrac] using
    floatOfIntLeftPackL_ok z hz hn hi F.p bias (2^(F.ebits + F.fracBits)) hp hpb hb hsb hlt hc ht m pc pre

/-- Canonical right normalization includes the zero-shift boundary. -/
theorem floatOfInt_right_significand_bounds (n p : Nat) (hn : n ≠ 0)
    (hp : 1 ≤ p) (hr : ((p - 1 : Nat) : Int) ≤ Gleitkomma.findeExp n 1) :
    2^(p - 1) ≤ Gleitkomma.normQ p (Gleitkomma.findeExp n 1) n 1 ∧
    Gleitkomma.normQ p (Gleitkomma.findeExp n 1) n 1 ≤ 2 * 2^(p - 1) := by
  have he := findeExp_integer_nonzero n hn
  have hu := Gleitkomma.bitlen_obere n
  have hl := Gleitkomma.bitlen_untere n hn
  have hb : 0 < Gleitkomma.bitlen n := by
    cases h : Gleitkomma.bitlen n with
    | zero => simp [h] at hu; omega
    | succ k => omega
  let k := Gleitkomma.bitlen n - p
  have hs : (Gleitkomma.findeExp n 1 - ((p : Int) - 1)).toNat = k := by
    dsimp [k]; omega
  have hlo : 2^(p - 1) * 2^k ≤ n := by
    rw [← Nat.pow_add]
    have hx : p - 1 + k + 1 = Gleitkomma.bitlen n := by dsimp [k]; omega
    rw [← hx, Nat.pow_succ] at hl
    omega
  have hupper : n < (2 * 2^(p - 1)) * 2^k := by
    have hx : p - 1 + k + 1 = Gleitkomma.bitlen n := by dsimp [k]; omega
    calc
      n < 2^Gleitkomma.bitlen n := hu
      _ = (2 * 2^(p - 1)) * 2^k := by rw [← hx, Nat.pow_succ, Nat.pow_add]; ac_rfl
  rw [floatNormQ_shift p _ n (by omega), hs]
  have hd : 0 < 2^k := Nat.pow_pos (by decide)
  have hlowq : 2^(p - 1) ≤ n / 2^k := (Nat.le_div_iff_mul_le hd).2 hlo
  have hhighq : n / 2^k < 2 * 2^(p - 1) := (Nat.div_lt_iff_lt_mul hd).2 hupper
  unfold Gleitkomma.rundeInt
  split <;> (try split) <;> (try split) <;> omega

/-- The actual right packer, given rounded-significand bounds, returns the canonical integer-conversion bits. -/
theorem floatOfIntRightPackL_ofInt {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {input : Nat → Option (List II × Nat)}
    (F : Gleitkomma.Format) (z : Int)
    (hz : -2^63 ≤ z ∧ z < 2^63) (hn : z ≠ 0)
    (hi : WordCode (L := L) ρ W input (BitVec.ofInt 64 z))
    (hp : 2 ≤ F.p) (hpb : F.p - 1 < 63)
    (hfrac : F.fracBits = F.p - 1)
    (bias : Nat) (hb : bias < 2^64)
    (hsb : 2^(F.ebits + F.fracBits) < 2^64)
    (hu : 2 * 2^F.fracBits < 2^64) (hm : F.bexpMax ≤ 2^64)
    (hlo : F.emin ≤ Gleitkomma.findeExp z.natAbs 1)
    (hhi : Gleitkomma.findeExp z.natAbs 1 < (F.emax : Int))
    (he : 0 < (Gleitkomma.findeExp z.natAbs 1 - F.emin + 1).toNat ∧
      (Gleitkomma.findeExp z.natAbs 1 - F.emin + 1).toNat + 1 < F.bexpMax)
    (heb : BitVec.ofInt 64 (Gleitkomma.findeExp z.natAbs 1) + BitVec.ofNat 64 bias =
      BitVec.ofNat 64 (Gleitkomma.findeExp z.natAbs 1 - F.emin + 1).toNat)
    (hr : ((F.p - 1 : Nat) : Int) ≤ Gleitkomma.findeExp z.natAbs 1) :
    WordCode (L := L) ρ W (fun d => floatPackCarryL d
      (fun j => wordL 5 j (wordK 13 j (input j) 0)
        (some (konstWL 4 (2^(F.ebits + F.fracBits)) (j + 1))))
      (fun j => wordL 3 j (floatExponentL j (fun k => floatMagnitudeL k input))
        (some (konstWL 4 bias (j + 1))))
      (fun j => floatOfIntScaleL F.p j input) (2^(F.p - 1)))
      (BitVec.ofNat 64 (Gleitkomma.zuBits F (Gleitkomma.ofInt F z))) := by
  have ha : z.natAbs ≠ 0 := by omega
  have hq := floatOfInt_right_significand_bounds z.natAbs F.p ha (by omega) hr
  rw [← hfrac] at hq
  have canonical : Gleitkomma.ofInt F z = Gleitkomma.rundeBruchKern F
      (decide (z < 0)) z.natAbs 1 (Gleitkomma.findeExp z.natAbs 1) := by
    simp [Gleitkomma.ofInt, Gleitkomma.rundeExakt, Gleitkomma.exaktBruch,
      Gleitkomma.rundeBruch, Gleitkomma.rundeBruchBei, ha]
  rw [canonical, floatPackCarry_fields F _ _ _ _ (by omega) hfrac hlo hhi hq.2]
  have pack := floatPackCarry_canonical F (decide (z < 0))
    (Gleitkomma.findeExp z.natAbs 1 - F.emin + 1).toNat
    (Gleitkomma.normQ F.p (Gleitkomma.findeExp z.natAbs 1) z.natAbs 1)
    hu hm he hq
  rw [hfrac] at pack
  rw [hfrac, ← pack]
  intro fp K d c top hc ht m pc pre
  simpa only [decide_eq_true_eq, heb, hfrac] using
    floatOfIntRightPackL_ok z hz hn hi F.p bias (2^(F.ebits + F.fracBits)) hp hpb hb hsb hr hc ht m pc pre

/-- Supported formats discharge the static premises of the actual left packer. -/
theorem floatOfIntLeftPack_format (F : Gleitkomma.Format)
    (hF : F ∈ [Gleitkomma.f32, Gleitkomma.f64]) :
    1 ≤ F.p ∧ F.p - 1 < 63 ∧ F.fracBits = F.p - 1 ∧
    2^(F.ebits + F.fracBits) < 2^64 ∧
    2 * 2^F.fracBits < 2^64 ∧ F.bexpMax ≤ 2^64 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
  rcases hF with rfl | rfl <;> decide

/-- Actual signed-input exponent bounds determine the encoded bias field. -/
theorem floatOfIntAssemblyL_bias {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {input : Nat → Option (List II × Nat)}
    (F : Gleitkomma.Format) (hF : F ∈ [Gleitkomma.f32, Gleitkomma.f64])
    (z : Int) (hz : -2^63 ≤ z ∧ z < 2^63) (hn : z ≠ 0)
    (hi : WordCode (L := L) ρ W input (BitVec.ofInt 64 z)) :
    BitVec.ofInt 64 (Gleitkomma.findeExp z.natAbs 1) + BitVec.ofNat 64 F.bias =
      BitVec.ofNat 64 (Gleitkomma.findeExp z.natAbs 1 - F.emin + 1).toNat := by
  have he := (floatOfIntAssemblyL_prefix z hz hn hi).2
  have hn : Gleitkomma.findeExp z.natAbs 1 =
      ((Gleitkomma.findeExp z.natAbs 1).toNat : Int) := by omega
  rw [hn, BitVec.ofInt_natCast, ← BitVec.ofNat_add]
  congr 1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
  rcases hF with rfl | rfl <;>
    simp only [Gleitkomma.Format.bias, Gleitkomma.Format.emax,
      Gleitkomma.Format.emin, Gleitkomma.f32, Gleitkomma.f64] <;> omega

/-- The complete outer assembly executes canonical signed integer conversion on
    the strict left path, deriving all format and packing premises. -/
theorem floatOfIntAssemblyL_left_ofInt {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {input : Nat → Option (List II × Nat)}
    (F : Gleitkomma.Format) (hF : F ∈ [Gleitkomma.f32, Gleitkomma.f64])
    (z : Int) (hz : -2^63 ≤ z ∧ z < 2^63) (hn : z ≠ 0)
    (hi : WordCode (L := L) ρ W input (BitVec.ofInt 64 z))
    (hlt : Gleitkomma.findeExp z.natAbs 1 < (F.p - 1 : Nat)) :
    WordCode (L := L) ρ W
      (fun d => floatOfIntAssemblyL F.p F.bias (2^(F.ebits + F.fracBits)) d input)
      (BitVec.ofNat 64 (Gleitkomma.zuBits F (Gleitkomma.ofInt F z))) := by
  obtain ⟨hp, hpb, hf, hs, hu, hm⟩ := floatOfIntLeftPack_format F hF
  obtain ⟨hlo, hhi, he⟩ := floatOfIntAssemblyL_normal_exponent z hz hn hi F hF
  have hb : F.bias < 2^64 := by
    rcases (show F = Gleitkomma.f32 ∨ F = Gleitkomma.f64 by simpa using hF) with rfl | rfl <;> decide
  have pack : WordCode (L := L) ρ W _ _ := floatOfIntLeftPackL_ofInt F z hz hn hi hp hpb hf F.bias hb hs hu hm hlo hhi he
    (floatOfIntAssemblyL_bias F hF z hz hn hi) hlt
  have mag : WordCode (L := L) ρ W _ _ := floatMagnitudeL_ok hi
  have nz : floatMagnitudeWord (BitVec.ofInt 64 z) ≠ 0 := by
    intro h
    have hh := (floatOfIntAssembly_magnitude_bound z hz).1
    rw [h] at hh
    simp at hh
    omega
  have cond : WordCode (L := L) ρ W
      (fun d => wordK 14 d (floatMagnitudeL d input) 0) 0 := by
    intro fp K d c top h ht m pc pre
    exact wordK_ok h ht (by decide) (fun _ _ he ht => mag he ht)
      (g := fun a b => some (Runner.IR.bool (a == b)))
      (fun a ha => by subst a; exact ⟨0, by simpa [Runner.IR.bool] using nz, rfl⟩)
      rfl (by decide) pre
  intro fp K d c top h ht m pc pre
  have hd : d < K := by
    have hh := h
    simp only [floatOfIntAssemblyL, wennL, bind, Option.bind_eq_some_iff] at hh
    obtain ⟨⟨cc, tc⟩, _, ⟨ca, ta⟩, ha, ⟨cb, tb⟩, _, hh⟩ := hh
    simp only [floatPackZeroL, Option.some.injEq, Prod.mk.injEq] at ha
    cases ha
    split at hh
    · cases hh; simp only [konstWL, bin2] at ht; omega
    · contradiction
  exact wennL_ok h ht hd (bc := false)
    (fun _ _ he ht => cond he ht)
    (by intro h; cases h)
    (fun _ _ _ he ht => pack he ht) pre

/-- The complete outer assembly executes canonical signed integer conversion on
    the right path, deriving all format and packing premises. -/
theorem floatOfIntAssemblyL_right_ofInt {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {input : Nat → Option (List II × Nat)}
    (F : Gleitkomma.Format) (hF : F ∈ [Gleitkomma.f32, Gleitkomma.f64])
    (z : Int) (hz : -2^63 ≤ z ∧ z < 2^63) (hn : z ≠ 0)
    (hi : WordCode (L := L) ρ W input (BitVec.ofInt 64 z))
    (hr : ((F.p - 1 : Nat) : Int) ≤ Gleitkomma.findeExp z.natAbs 1) :
    WordCode (L := L) ρ W
      (fun d => floatOfIntAssemblyL F.p F.bias (2^(F.ebits + F.fracBits)) d input)
      (BitVec.ofNat 64 (Gleitkomma.zuBits F (Gleitkomma.ofInt F z))) := by
  obtain ⟨hp, hpb, hf, hs, hu, hm⟩ := floatOfIntLeftPack_format F hF
  obtain ⟨hlo, hhi, he⟩ := floatOfIntAssemblyL_normal_exponent z hz hn hi F hF
  have hb : F.bias < 2^64 := by
    rcases (show F = Gleitkomma.f32 ∨ F = Gleitkomma.f64 by simpa using hF) with rfl | rfl <;> decide
  have hp2 : 2 ≤ F.p := by
    rcases (show F = Gleitkomma.f32 ∨ F = Gleitkomma.f64 by simpa using hF) with rfl | rfl <;> decide
  have pack : WordCode (L := L) ρ W _ _ := floatOfIntRightPackL_ofInt F z hz hn hi hp2 hpb hf F.bias hb hs hu hm hlo hhi he
    (floatOfIntAssemblyL_bias F hF z hz hn hi) hr
  have mag : WordCode (L := L) ρ W _ _ := floatMagnitudeL_ok hi
  have nz : floatMagnitudeWord (BitVec.ofInt 64 z) ≠ 0 := by
    intro h
    have hh := (floatOfIntAssembly_magnitude_bound z hz).1
    rw [h] at hh
    simp at hh
    omega
  have cond : WordCode (L := L) ρ W
      (fun d => wordK 14 d (floatMagnitudeL d input) 0) 0 := by
    intro fp K d c top h ht m pc pre
    exact wordK_ok h ht (by decide) (fun _ _ he ht => mag he ht)
      (g := fun a b => some (Runner.IR.bool (a == b)))
      (fun a ha => by subst a; exact ⟨0, by simpa [Runner.IR.bool] using nz, rfl⟩)
      rfl (by decide) pre
  intro fp K d c top h ht m pc pre
  have hd : d < K := by
    have hh := h
    simp only [floatOfIntAssemblyL, wennL, bind, Option.bind_eq_some_iff] at hh
    obtain ⟨⟨cc, tc⟩, _, ⟨ca, ta⟩, ha, ⟨cb, tb⟩, _, hh⟩ := hh
    simp only [floatPackZeroL, Option.some.injEq, Prod.mk.injEq] at ha
    cases ha
    split at hh
    · cases hh; simp only [konstWL, bin2] at ht; omega
    · contradiction
  exact wennL_ok h ht hd (bc := false)
    (fun _ _ he ht => cond he ht)
    (by intro h; cases h)
    (fun _ _ _ he ht => pack he ht) pre

/-- Four joint fixtures discharge every outer-left premise and execute the
    emitted assembly with the canonical conversion result. -/
theorem floatOfIntAssemblyL_left_ofInt_zeuge {Γ : Ctx} (ρ : Env D Γ)
    (W : Runner.Mem → Prop) :
    ∀ F ∈ [Gleitkomma.f32, Gleitkomma.f64], ∀ z ∈ ([37, -37] : List Int),
      F ∈ [Gleitkomma.f32, Gleitkomma.f64] ∧
      (-2^63 ≤ z ∧ z < 2^63) ∧ z ≠ 0 ∧
      Gleitkomma.findeExp z.natAbs 1 < (F.p - 1 : Nat) ∧
      WordCode (L := L) ρ W
        (fun d => some (konstWL 4 (BitVec.ofInt 64 z).toNat d)) (BitVec.ofInt 64 z) ∧
      WordCode (L := L) ρ W
        (fun d => floatOfIntAssemblyL F.p F.bias (2^(F.ebits + F.fracBits)) d
          (fun j => some (konstWL 4 (BitVec.ofInt 64 z).toNat j)))
        (BitVec.ofNat 64 (Gleitkomma.zuBits F (Gleitkomma.ofInt F z))) := by
  intro F hF z hz
  have bounds : -2^63 ≤ z ∧ z < 2^63 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl <;> decide
  have nonzero : z ≠ 0 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl <;> decide
  have left : Gleitkomma.findeExp z.natAbs 1 < (F.p - 1 : Nat) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz hF
    rcases hF with rfl | rfl <;> rcases hz with rfl | rfl <;> decide +kernel
  have input : WordCode (L := L) ρ W
      (fun d => some (konstWL 4 (BitVec.ofInt 64 z).toNat d)) (BitVec.ofInt 64 z) := by
    have h : WordCode (L := L) ρ W
        (fun d => some (konstWL 4 (BitVec.ofInt 64 z).toNat d))
        (BitVec.ofNat 64 (BitVec.ofInt 64 z).toNat) := WordCode.konst (L := L) (ρ := ρ) (W := W)
      (BitVec.ofInt 64 z).toNat (BitVec.isLt _)
    have eq : BitVec.ofNat 64 (BitVec.ofInt 64 z).toNat = BitVec.ofInt 64 z := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl <;> decide
    rw [eq] at h
    intro fp K d c top hc ht m pc pre
    exact h hc ht m pc pre
  exact ⟨hF, bounds, nonzero, left, input,
    floatOfIntAssemblyL_left_ofInt F hF z bounds nonzero input left⟩

/-- Joint minimum-integer, tie, carry and shift-zero fixtures discharge every outer-right premise and execute the
    emitted assembly with the canonical conversion result. -/
end Gabbro.Stage0.Senke
