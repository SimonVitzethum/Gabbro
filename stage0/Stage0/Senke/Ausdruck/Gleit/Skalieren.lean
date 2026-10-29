/- Quotient/remainder scaling followed by G's nearest-even rounding. -/
import Stage0.Senke.Ausdruck.Gleit.RundCode
import Stage0.Senke.Ausdruck.Gleit.Schieben
import Stage0.Senke.Ausdruck.Gleit.Exponent

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

/-- Round an unsigned magnitude after a binary right shift. The full remainder
    is kept until the shared nearest-even decision; inputs must be pure. -/
def floatRoundShiftL (d : Nat) (a k : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  let q := fun d => floatShiftQuotL d a k
  let back := fun d => wordL 11 d (q d) (k (d + 1))
  let rem := fun d => wordL 4 d (a d) (back (d + 1))
  let den := fun d => wordL 11 d (some ([ci 1 d 1 0], d + 1)) (k (d + 1))
  floatRoundL d q rem den

theorem floatShiftRemainderWord_model (a : Runner.W) (k : Nat) :
    a - ((a >>> k) <<< k) = BitVec.ofNat 64 (a.toNat % 2^k) := by
  have back := floatShiftBackWord_toNat a k
  have hle : ((a >>> k) <<< k) ≤ a := by
    rw [BitVec.le_def, back]
    exact Nat.div_mul_le_self _ _
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le hle, back, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) a.isLt)]
  exact Nat.mod_eq_sub_div_mul.symm

/-- Every unsigned input is allowed. The count bound makes the denominator a
    positive signed word, as required by floatRoundL's proved comparison. -/
theorem floatRoundShiftL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a k : Nat → Option (List II × Nat)} {av : Runner.W} {s : Nat}
    (ha : WordCode (L := L) ρ W a av)
    (hk : WordCode (L := L) ρ W k (BitVec.ofNat 64 s)) (hs : s < 63) :
    WordCode (L := L) ρ W (fun d => floatRoundShiftL d a k)
      (BitVec.ofNat 64 (Gleitkomma.rundeInt (av.toNat / 2^s) (av.toNat % 2^s) (2^s))) := by
  have hkn : (BitVec.ofNat 64 s).toNat = s := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hm : s % 64 = s := Nat.mod_eq_of_lt (by omega)
  have hqv : av >>> s = BitVec.ofNat 64 (av.toNat / 2^s) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) av.isLt)]
  have hdv : (BitVec.ofInt 64 1) <<< s = BitVec.ofNat 64 (2^s) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have q : WordCode (L := L) ρ W _ _ := floatShiftQuotL_ok ha hk
  have back : WordCode (L := L) ρ W _ _ := WordCode.bin q hk
    (g := fun a b => some (a <<< (b.toNat % 64))) rfl rfl (by decide : 11 < 256)
  have rem : WordCode (L := L) ρ W _ _ := WordCode.bin ha back
    (g := fun a b => some (a - b)) rfl rfl (by decide : 4 < 256)
  have den : WordCode (L := L) ρ W _ _ := WordCode.bin
    (WordCode.const 1 (by decide)) hk (g := fun a b => some (a <<< (b.toNat % 64)))
    rfl rfl (by decide : 11 < 256)
  intro fp K d c top h hK m pc hp
  exact floatRoundL_ok (av.toNat / 2^s) (av.toNat % 2^s) (2^s)
    (Nat.mod_lt _ (Nat.pow_pos (by decide)))
    ((Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mpr hs)
    (fun he ht m pc hp => (q he ht m pc hp).mono fun w hw => by
      simpa only [hkn, hqv] using hw)
    (fun he ht m pc hp => (rem he ht m pc hp).mono fun w hw => by
      simpa only [hkn, hm, floatShiftRemainderWord_model] using hw)
    (fun he ht m pc hp => (den he ht m pc hp).mono fun w hw => by
      simpa only [hkn, hm, hdv] using hw)
    h hK hp

/-- The normal-path scaling of G, when the exponent requires a right shift. -/
theorem floatNormQ_shift (p : Nat) (E : Int) (n : Nat) (he : (p : Int) - 1 ≤ E) :
    Gleitkomma.normQ p E n 1 =
      Gleitkomma.rundeInt (n / 2^(E - ((p : Int) - 1)).toNat)
        (n % 2^(E - ((p : Int) - 1)).toNat) (2^(E - ((p : Int) - 1)).toNat) := by
  by_cases hz : E = (p : Int) - 1
  · subst E
    simp [Gleitkomma.normQ, Gleitkomma.normQD]
  · have hn : ¬0 ≤ (p : Int) - 1 - E := by omega
    simp only [Gleitkomma.normQ, Gleitkomma.normQD, hn, ↓reduceIte, Nat.one_mul]

/-- Integer magnitudes requiring left scaling have no discarded bits. -/
theorem floatNormQ_left (p : Nat) (E : Int) (n : Nat)
    (he : E ≤ (p : Int) - 1) :
    Gleitkomma.normQ p E n 1 = n * 2^((p : Int) - 1 - E).toNat := by
  have hs : 0 ≤ (p : Int) - 1 - E := by omega
  simp [Gleitkomma.normQ, Gleitkomma.normQD, hs, he, Gleitkomma.rundeInt, Nat.mod_one]

/-- Actual left-shift IR agrees with G's integer normalization. -/
theorem floatLeftShiftL_normQ {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a k : Nat → Option (List II × Nat)} {av : Runner.W} {E : Int}
    (ha : WordCode (L := L) ρ W a av)
    (hk : WordCode (L := L) ρ W k (BitVec.ofNat 64 (52 - E).toNat))
    (he : E ≤ 52) (hs : (52 - E).toNat < 64) :
    WordCode (L := L) ρ W (fun d => wordL 11 d (a d) (k (d + 1)))
      (BitVec.ofNat 64 (Gleitkomma.normQ 53 E av.toNat 1)) := by
  have result : WordCode (L := L) ρ W _ _ := WordCode.bin ha hk
    (g := fun a b => some (a <<< (b.toNat % 64))) rfl rfl (by decide : 11 < 256)
  have hv : av <<< ((BitVec.ofNat 64 (52 - E).toNat).toNat % 64) =
      BitVec.ofNat 64 (Gleitkomma.normQ 53 E av.toNat 1) := by
    rw [floatNormQ_left 53 E av.toNat (by simpa using he)]
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt (show (52 - E).toNat < 2^64 by omega)]
  intro fp K d c top h hK m pc hp
  exact (result h hK m pc hp).mono fun w hw => hw.trans hv

/-- This component already agrees with G's normal significand computation;
    exponent selection and packing are still separate obligations. -/
theorem floatRoundShiftL_normQ {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a k : Nat → Option (List II × Nat)} {av : Runner.W} {E : Int}
    (ha : WordCode (L := L) ρ W a av)
    (hk : WordCode (L := L) ρ W k (BitVec.ofNat 64 (E - 52).toNat))
    (he : 52 ≤ E) (hs : (E - 52).toNat < 63) :
    WordCode (L := L) ρ W (fun d => floatRoundShiftL d a k)
      (BitVec.ofNat 64 (Gleitkomma.normQ 53 E av.toNat 1)) := by
  intro fp K d c top h hK m pc hp
  rw [floatNormQ_shift 53 E av.toNat (by simpa using he)]
  exact floatRoundShiftL_ok ha hk hs h hK m pc hp

/-- Rounding can carry out of the retained significand; it is not truncated. -/
theorem floatRoundShiftL_ok_zeuge {Γ : Ctx} (ρ : Env D Γ) (W : Runner.Mem → Prop) :
    WordCode (L := L) ρ W (fun d => floatRoundShiftL d
      (fun j => some (konstWL 4 (2^64 - 1) j))
      (fun j => some (konstWL 4 11 j))) (BitVec.ofNat 64 (2^53)) ∧
    (floatRoundShiftL 8 (fun j => some (konstWL 4 (2^64 - 1) j))
      (fun j => some (konstWL 4 11 j))).isSome = true := by
  constructor
  · intro fp K d c top h hK m pc hp
    have result : WordCode (L := L) ρ W _ _ := floatRoundShiftL_ok
      (WordCode.konst (2^64 - 1) (by decide)) (WordCode.konst 11 (by decide)) (by decide)
    have hx : BitVec.ofNat 64
        (Gleitkomma.rundeInt ((BitVec.ofNat 64 (2^64 - 1)).toNat / 2^11)
          ((BitVec.ofNat 64 (2^64 - 1)).toNat % 2^11) (2^11)) =
        BitVec.ofNat 64 (2^53) := by decide +kernel
    rw [hx] at result
    exact result h hK m pc hp
  · decide +kernel

theorem floatRoundShiftL_normQ_zeuge {Γ : Ctx} (ρ : Env D Γ) (W : Runner.Mem → Prop) :
    WordCode (L := L) ρ W (fun d => floatRoundShiftL d
      (fun j => some (konstWL 4 (2^53 + 3) j))
      (fun j => some (konstWL 4 1 j))) (BitVec.ofNat 64 (2^52 + 2)) ∧
    (floatRoundShiftL 8 (fun j => some (konstWL 4 (2^53 + 3) j))
      (fun j => some (konstWL 4 1 j))).isSome = true := by
  constructor
  · intro fp K d c top h hK m pc hp
    have result : WordCode (L := L) ρ W _ _ := floatRoundShiftL_normQ (E := 53)
      (WordCode.konst (2^53 + 3) (by decide)) (WordCode.konst 1 (by decide))
      (by decide) (by decide)
    have hx : BitVec.ofNat 64
        (Gleitkomma.normQ 53 53 (BitVec.ofNat 64 (2^53 + 3)).toNat 1) =
        BitVec.ofNat 64 (2^52 + 2) := by decide +kernel
    rw [hx] at result
    exact result h hK m pc hp
  · decide +kernel

/-- Pack a normal rounded significand. The caller supplies the already biased
    exponent and the sign contribution (zero or the format's sign bit). -/
def floatPackNormalL (d : Nat) (s e q : Nat → Option (List II × Nat))
    (unit : Nat) : Option (List II × Nat) :=
  let k := fun j => some (konstWL 4 unit j)
  let fraction := fun j => wordL 4 j (q j) (k (j + 1))
  let exponent := fun j => wordL 5 j (e j) (k (j + 1))
  let upper := fun j => wordL 3 j (s j) (exponent (j + 1))
  wordL 3 d (upper d) (fraction (d + 1))

/-- Generic simulation, using only the existing integer IR operations. -/
theorem floatPackNormalL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {s e q : Nat → Option (List II × Nat)} {sv ev qv : Runner.W}
    (hs : WordCode (L := L) ρ W s sv) (he : WordCode (L := L) ρ W e ev)
    (hq : WordCode (L := L) ρ W q qv) (unit : Nat) (hu : unit < 2^64) :
    WordCode (L := L) ρ W (fun d => floatPackNormalL d s e q unit)
      (sv + ev * BitVec.ofNat 64 unit + (qv - BitVec.ofNat 64 unit)) := by
  have hk : WordCode (L := L) ρ W _ _ := WordCode.konst (L := L) (ρ := ρ) (W := W) unit hu
  have hf : WordCode (L := L) ρ W _ _ := WordCode.bin hq hk (g := fun a b => some (a - b)) rfl rfl (by decide : 4 < 256)
  have hx : WordCode (L := L) ρ W _ _ := WordCode.bin he hk (g := fun a b => some (a * b)) rfl rfl (by decide : 5 < 256)
  have ht : WordCode (L := L) ρ W _ _ := WordCode.bin hs hx (g := fun a b => some (a + b)) rfl rfl (by decide : 3 < 256)
  intro fp K d c top h hK m pc hp
  exact (WordCode.bin ht hf (g := fun a b => some (a + b)) rfl rfl (by decide : 3 < 256)) h hK m pc hp

/-- Correspondence to the model's canonical encoder on normal field bounds.
    The rounded significand includes its implicit leading bit; no carry is allowed. -/
theorem floatPackNormal_canonical (F : Gleitkomma.Format) (sign : Bool) (e q : Nat)
    (hu : 2^F.fracBits < 2^64) (he : 0 < e ∧ e < F.bexpMax)
    (hq : 2^F.fracBits ≤ q ∧ q < 2^(F.fracBits + 1)) :
    BitVec.ofNat 64 (if sign then 2^(F.ebits + F.fracBits) else 0) +
      BitVec.ofNat 64 e * BitVec.ofNat 64 (2^F.fracBits) +
      (BitVec.ofNat 64 q - BitVec.ofNat 64 (2^F.fracBits)) =
    BitVec.ofNat 64 (Gleitkomma.zuBits F ⟨sign, e, q - 2^F.fracBits⟩) := by
  rw [← BitVec.ofNat_mul, BitVec.ofNat_sub_ofNat_of_le q _ hu hq.1, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
  rfl

/-- Joint sign and field-boundary fixtures for both supported IEEE formats. -/
theorem floatPackNormal_zeuge {Γ : Ctx} (ρ : Env D Γ) (W : Runner.Mem → Prop) :
    ∀ F ∈ [Gleitkomma.f32, Gleitkomma.f64], ∀ sign : Bool,
    ∀ e ∈ [1, F.bexpMax - 1], ∀ q ∈ [2^F.fracBits, 2^(F.fracBits + 1) - 1],
      let signWord := if sign then 2^(F.ebits + F.fracBits) else 0
      let lit := fun n d => some (konstWL 4 n d)
      (0 < e ∧ e < F.bexpMax) ∧
      (2^F.fracBits ≤ q ∧ q < 2^(F.fracBits + 1)) ∧
      WordCode (L := L) ρ W
        (fun d => floatPackNormalL d (lit signWord) (lit e) (lit q) (2^F.fracBits))
        (BitVec.ofNat 64 (Gleitkomma.zuBits F ⟨sign, e, q - 2^F.fracBits⟩)) := by
  intro F hF sign e he q hq
  have bounds : 2^F.fracBits < 2^64 ∧
      (if sign then 2^(F.ebits + F.fracBits) else 0) < 2^64 ∧
      e < 2^64 ∧ q < 2^64 ∧ (0 < e ∧ e < F.bexpMax) ∧
      (2^F.fracBits ≤ q ∧ q < 2^(F.fracBits + 1)) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hF he hq
    rcases hF with rfl | rfl <;>
      rcases he with rfl | rfl <;> rcases hq with rfl | rfl <;>
      cases sign <;> decide +kernel
  refine ⟨bounds.2.2.2.2.1, bounds.2.2.2.2.2, ?_⟩
  intro fp K d c top h hK m pc hp
  have result : WordCode (L := L) ρ W _ _ := floatPackNormalL_ok
    (WordCode.konst _ bounds.2.1) (WordCode.konst _ bounds.2.2.1)
    (WordCode.konst _ bounds.2.2.2.1) _ bounds.1
  rw [floatPackNormal_canonical F sign e q bounds.1 bounds.2.2.2.2.1 bounds.2.2.2.2.2] at result
  exact result h hK m pc hp

/-- Renormalize a rounded significand at the carry boundary using integer IR.
    Equality produces the shift count and the exponent increment. -/
def floatPackCarryL (d : Nat) (s e q : Nat → Option (List II × Nat))
    (unit : Nat) : Option (List II × Nat) :=
  let limit := fun j => some (konstWL 4 (2 * unit) j)
  let carry := fun j => wordL 14 j (q j) (limit (j + 1))
  let exponent := fun j => wordL 3 j (e j) (carry (j + 1))
  let significand := fun j => wordL 12 j (q j) (carry (j + 1))
  floatPackNormalL d s exponent significand unit

theorem floatPackCarryL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {s e q : Nat → Option (List II × Nat)} {sv ev qv : Runner.W}
    (hs : WordCode (L := L) ρ W s sv) (he : WordCode (L := L) ρ W e ev)
    (hq : WordCode (L := L) ρ W q qv) (unit : Nat) (hu : 2 * unit < 2^64) :
    let carry := Runner.IR.bool (qv == BitVec.ofNat 64 (2 * unit))
    WordCode (L := L) ρ W (fun d => floatPackCarryL d s e q unit)
      (sv + (ev + carry) * BitVec.ofNat 64 unit +
        ((qv >>> (carry.toNat % 64)) - BitVec.ofNat 64 unit)) := by
  have hc : WordCode (L := L) ρ W _ _ := WordCode.bin hq
    (WordCode.konst (2 * unit) hu)
    (g := fun a b => some (Runner.IR.bool (a == b))) rfl rfl (by decide : 14 < 256)
  have hx : WordCode (L := L) ρ W _ _ := WordCode.bin he hc
    (g := fun a b => some (a + b)) rfl rfl (by decide : 3 < 256)
  have hq' : WordCode (L := L) ρ W _ _ := WordCode.bin hq hc
    (g := fun a b => some (a >>> (b.toNat % 64))) rfl rfl (by decide : 12 < 256)
  dsimp only
  intro fp K d c top h hK m pc hp
  exact floatPackNormalL_ok hs hx hq' unit (by omega) h hK m pc hp

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

end Gabbro.Stage0.Senke
