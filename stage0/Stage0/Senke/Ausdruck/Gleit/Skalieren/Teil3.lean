module
public import Stage0.Senke.Ausdruck.Gleit.Skalieren.Teil3a

public import Stage0.Senke.Ausdruck.Gleit.RundCode
public import Stage0.Senke.Ausdruck.Gleit.Schieben
public import Stage0.Senke.Ausdruck.Gleit.Exponent
public import Stage0.Senke.Ausdruck.Gleit.Betrag
public import Stage0.Senke.Ausdruck.Gleit.Skalieren.Teil2

@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

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

end Gabbro.Stage0.Senke
