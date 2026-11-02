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
end Gabbro.Stage0.Senke
