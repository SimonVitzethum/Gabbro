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
theorem floatFieldWord_canonical (F : Gleitkomma.Format)
    (hd : F.dicht) (hw : F.ebits + F.fracBits + 1 ≤ 64)
    (a : Gleitkomma.GBits F) (ha : Gleitkomma.wf F a) :
    let w := BitVec.ofNat 64 (Gleitkomma.zuBits F a)
    (floatFieldWord w 0 F.fracBits).toNat = a.frac ∧
    (floatFieldWord w F.fracBits F.ebits).toNat = a.bexp := by
  have inv := Gleitkomma.ausBits_zuBits F hd a ha
  have bound := Gleitkomma.zuBits_lt F hd a ha
  have powBound : 2^(F.ebits + F.fracBits + 1) ≤ (2^64 : Nat) :=
    Nat.pow_le_pow_right (by decide) hw
  have bound64 : Gleitkomma.zuBits F a < 2^64 := by omega
  have fracBound : 2^F.fracBits - 1 < (2^64 : Nat) := by
    have h := Nat.pow_le_pow_right (by decide : 1 ≤ 2)
      (show F.fracBits ≤ 64 by omega)
    have hp : 0 < (2^F.fracBits : Nat) := Nat.pow_pos (by decide)
    omega
  have expBound : 2^F.ebits - 1 < (2^64 : Nat) := by
    have h := Nat.pow_le_pow_right (by decide : 1 ≤ 2)
      (show F.ebits ≤ 64 by omega)
    have hp : 0 < (2^F.ebits : Nat) := Nat.pow_pos (by decide)
    omega
  have hf := congrArg (fun x : Gleitkomma.GBits F => x.frac) inv
  have he := congrArg (fun x : Gleitkomma.GBits F => x.bexp) inv
  change Gleitkomma.zuBits F a % 2^F.fracBits = a.frac at hf
  change Gleitkomma.zuBits F a / 2^F.fracBits % 2^F.ebits = a.bexp at he
  dsimp only
  rw [floatFieldWord_model _ 0 F.fracBits fracBound,
    floatFieldWord_model _ F.fracBits F.ebits expBound]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound64, Nat.pow_zero, Nat.div_one]
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

/-- Executed input decoding for every well-formed packed operand in a dense
    format fitting a runner word. Both fields retain the producer's frame. -/
theorem floatFieldL_canonical {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    (F : Gleitkomma.Format) (hd : F.dicht)
    (hw : F.ebits + F.fracBits + 1 ≤ 64)
    (a : Gleitkomma.GBits F) (ha : Gleitkomma.wf F a)
    {e : Nat → Option (List II × Nat)}
    (he : WordCode (L := L) ρ W e (BitVec.ofNat 64 (Gleitkomma.zuBits F a))) :
    WordCode (L := L) ρ W (fun d => floatFieldL 0 F.fracBits d e)
      (BitVec.ofNat 64 a.frac) ∧
    WordCode (L := L) ρ W (fun d => floatFieldL F.fracBits F.ebits d e)
      (BitVec.ofNat 64 a.bexp) := by
  obtain ⟨hf, hx⟩ := floatFieldWord_canonical F hd hw a ha
  have fm : 2^F.fracBits - 1 < (2^64 : Nat) := by
    have h := Nat.pow_le_pow_right (by decide : 1 ≤ 2)
      (show F.fracBits ≤ 64 by omega)
    have hp : 0 < (2^F.fracBits : Nat) := Nat.pow_pos (by decide)
    omega
  have em : 2^F.ebits - 1 < (2^64 : Nat) := by
    have h := Nat.pow_le_pow_right (by decide : 1 ≤ 2)
      (show F.ebits ≤ 64 by omega)
    have hp : 0 < (2^F.ebits : Nat) := Nat.pow_pos (by decide)
    omega
  have ff : WordCode (L := L) ρ W (fun d => floatFieldL 0 F.fracBits d e)
      (floatFieldWord (BitVec.ofNat 64 (Gleitkomma.zuBits F a)) 0 F.fracBits) :=
    floatFieldL_ok 0 F.fracBits (by decide) fm he
  have fe : WordCode (L := L) ρ W (fun d => floatFieldL F.fracBits F.ebits d e)
      (floatFieldWord (BitVec.ofNat 64 (Gleitkomma.zuBits F a)) F.fracBits F.ebits) :=
    floatFieldL_ok F.fracBits F.ebits (by omega) em he
  have hf' := congrArg (BitVec.ofNat 64) hf
  have hx' := congrArg (BitVec.ofNat 64) hx
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hf' hx'
  rw [hf'] at ff
  rw [hx'] at fe
  exact ⟨ff, fe⟩

/-- Alignment uses exponent one for both subnormals and zero. This is an
    internal scale index, not a change to the canonical exact value of zero. -/
def floatScaleIndexL (F : Gleitkomma.Format) (d : Nat)
    (e : Nat → Option (List II × Nat)) : Option (List II × Nat) :=
  wordL 3 d (floatFieldL F.fracBits F.ebits d e)
    (wordL 14 (d+1) (floatFieldL F.fracBits F.ebits (d+1) e)
      (some ([ci 1 (d+2) 0 0], d+3)))

/-- The emitted scale index is derived entirely from the packed operand.
    This holds for all well-formed words, hence every finite f32/f64 input,
    without requiring a caller-supplied exponent or excluding large gaps. -/
theorem floatScaleIndexL_canonical {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} (F : Gleitkomma.Format) (hd : F.dicht)
    (hw : F.ebits + F.fracBits + 1 ≤ 64)
    (a : Gleitkomma.GBits F) (ha : Gleitkomma.wf F a)
    {e : Nat → Option (List II × Nat)}
    (he : WordCode (L := L) ρ W e (BitVec.ofNat 64 (Gleitkomma.zuBits F a))) :
    WordCode (L := L) ρ W (fun d => floatScaleIndexL F d e)
      (BitVec.ofNat 64 (max a.bexp 1)) := by
  have fe : WordCode (L := L) ρ W (fun d => floatFieldL F.fracBits F.ebits d e)
      (BitVec.ofNat 64 a.bexp) := (floatFieldL_canonical F hd hw a ha he).2
  have c0 : WordCode (L := L) ρ W _ _ := WordCode.const (L := L) (ρ := ρ) (W := W) 0 (by decide)
  have zero : WordCode (L := L) ρ W _ _ := WordCode.bin fe c0
    (g := fun a b => some (Runner.IR.bool (a == b)))
    rfl rfl (by decide : 14 < 256)
  have sum : WordCode (L := L) ρ W _ _ := WordCode.bin fe zero (g := fun a b => some (a + b))
    rfl rfl (by decide : 3 < 256)
  have bound : a.bexp < 2^64 := by
    have h := ha.1
    have p := Nat.pow_le_pow_right (by decide : 1 ≤ 2)
      (show F.ebits ≤ 64 by omega)
    have dense := hd
    unfold Gleitkomma.Format.dicht at dense
    omega
  have ez : (BitVec.ofNat 64 a.bexp == 0) = decide (a.bexp = 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
    simp
  have result : BitVec.ofNat 64 a.bexp +
      Runner.IR.bool (BitVec.ofNat 64 a.bexp == 0) =
      BitVec.ofNat 64 (max a.bexp 1) := by
    rw [ez]
    by_cases hz : a.bexp = 0
    · simp [hz, Runner.IR.bool]
    · have hpos : 1 ≤ a.bexp := by omega
      simp [hz, Runner.IR.bool, Nat.max_eq_left hpos]
  intro fp K d c top h hK m pc hp
  have out : Ok m pc fp K d c (fun x => x = BitVec.ofNat 64 a.bexp +
      Runner.IR.bool (BitVec.ofNat 64 a.bexp == 0)) := sum h hK m pc hp
  rw [result] at out
  exact out

#print axioms floatScaleIndexL_canonical

omit [Kern] in
/-- Both supported formats jointly exercise zero, least subnormal, least
    normal and greatest finite inputs through the common decoder. -/
theorem floatFieldWord_formats_zeuge :
    ∀ F ∈ [Gleitkomma.f32, Gleitkomma.f64],
      F.dicht ∧ F.ebits + F.fracBits + 1 ≤ 64 ∧
      ∀ a ∈ ([⟨true, 0, 0⟩, ⟨false, 0, 1⟩, ⟨false, 1, 0⟩,
        ⟨true, F.bexpMax - 1, 2^F.fracBits - 1⟩] : List (Gleitkomma.GBits F)),
        Gleitkomma.wf F a ∧
        (floatFieldWord (BitVec.ofNat 64 (Gleitkomma.zuBits F a)) 0 F.fracBits).toNat = a.frac ∧
        (floatFieldWord (BitVec.ofNat 64 (Gleitkomma.zuBits F a)) F.fracBits F.ebits).toNat = a.bexp := by
  simp only [List.mem_cons, List.mem_singleton, forall_eq_or_imp, forall_eq, Gleitkomma.Format.dicht]
  decide +kernel

#print axioms floatFieldWord_formats_zeuge
#print axioms floatFieldL_canonical
#print axioms floatFieldWord_canonical
#print axioms floatFieldL_ok
end Gabbro.Stage0.Senke
