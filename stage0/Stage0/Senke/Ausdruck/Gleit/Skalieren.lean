/- Quotient/remainder scaling followed by G's nearest-even rounding. -/
import Stage0.Senke.Ausdruck.Gleit.RundCode
import Stage0.Senke.Ausdruck.Gleit.Schieben
import Stage0.Senke.Ausdruck.Gleit.Exponent
import Stage0.Senke.Ausdruck.Gleit.Betrag

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
theorem floatLeftShiftL_normQ_precision {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a k : Nat → Option (List II × Nat)} {av : Runner.W} {E : Int} {p : Nat}
    (ha : WordCode (L := L) ρ W a av)
    (hk : WordCode (L := L) ρ W k (BitVec.ofNat 64 (((p : Int) - 1) - E).toNat))
    (he : E ≤ ((p : Int) - 1)) (hs : (((p : Int) - 1) - E).toNat < 64) :
    WordCode (L := L) ρ W (fun d => wordL 11 d (a d) (k (d + 1)))
      (BitVec.ofNat 64 (Gleitkomma.normQ p E av.toNat 1)) := by
  have result : WordCode (L := L) ρ W _ _ := WordCode.bin ha hk
    (g := fun a b => some (a <<< (b.toNat % 64))) rfl rfl (by decide : 11 < 256)
  have hv : av <<< ((BitVec.ofNat 64 (((p : Int) - 1) - E).toNat).toNat % 64) =
      BitVec.ofNat 64 (Gleitkomma.normQ p E av.toNat 1) := by
    rw [floatNormQ_left p E av.toNat (by simpa using he)]
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt (show (((p : Int) - 1) - E).toNat < 2^64 by omega)]
  intro fp K d c top h hK m pc hp
  exact (result h hK m pc hp).mono fun w hw => hw.trans hv

/-- This component already agrees with G's normal significand computation;
    exponent selection and packing are still separate obligations. -/
theorem floatRoundShiftL_normQ_precision {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a k : Nat → Option (List II × Nat)} {av : Runner.W} {E : Int} {p : Nat}
    (ha : WordCode (L := L) ρ W a av)
    (hk : WordCode (L := L) ρ W k (BitVec.ofNat 64 (E - ((p : Int) - 1)).toNat))
    (he : ((p : Int) - 1) ≤ E) (hs : (E - ((p : Int) - 1)).toNat < 63) :
    WordCode (L := L) ρ W (fun d => floatRoundShiftL d a k)
      (BitVec.ofNat 64 (Gleitkomma.normQ p E av.toNat 1)) := by
  intro fp K d c top h hK m pc hp
  rw [floatNormQ_shift p E av.toNat (by simpa using he)]
  exact floatRoundShiftL_ok ha hk hs h hK m pc hp

/-- Actual left-shift IR agrees with G's integer normalization. -/
theorem floatLeftShiftL_normQ {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a k : Nat → Option (List II × Nat)} {av : Runner.W} {E : Int}
    (ha : WordCode (L := L) ρ W a av)
    (hk : WordCode (L := L) ρ W k (BitVec.ofNat 64 (52 - E).toNat))
    (he : E ≤ 52) (hs : (52 - E).toNat < 64) :
    WordCode (L := L) ρ W (fun d => wordL 11 d (a d) (k (d + 1)))
      (BitVec.ofNat 64 (Gleitkomma.normQ 53 E av.toNat 1)) := by
  exact floatLeftShiftL_normQ_precision (p := 53) ha hk he hs

/-- This component already agrees with G's normal significand computation;
    exponent selection and packing are still separate obligations. -/
theorem floatRoundShiftL_normQ {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a k : Nat → Option (List II × Nat)} {av : Runner.W} {E : Int}
    (ha : WordCode (L := L) ρ W a av)
    (hk : WordCode (L := L) ρ W k (BitVec.ofNat 64 (E - 52).toNat))
    (he : 52 ≤ E) (hs : (E - 52).toNat < 63) :
    WordCode (L := L) ρ W (fun d => floatRoundShiftL d a k)
      (BitVec.ofNat 64 (Gleitkomma.normQ 53 E av.toNat 1)) := by
  exact floatRoundShiftL_normQ_precision (p := 53) ha hk he hs

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

/-- Transfer the actual carry comparison and shift to natural fields. -/
theorem floatPackCarry_nat (q u : Nat) (hu : 2*u < 2^64)
    (hq : u ≤ q ∧ q ≤ 2*u) :
    let c := Runner.IR.bool (BitVec.ofNat 64 q == BitVec.ofNat 64 (2*u))
    c.toNat = (if q = 2*u then 1 else 0) ∧
    (BitVec.ofNat 64 q >>> (c.toNat % 64)).toNat =
      (if q = 2*u then u else q) := by
  have hq64 : q < 2^64 := by omega
  have eqv : (BitVec.ofNat 64 q == BitVec.ofNat 64 (2*u)) = decide (q = 2*u) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hq64, Nat.mod_eq_of_lt hu]
  dsimp only
  rw [eqv]
  by_cases h : q = 2*u
  · subst q
    simp [Runner.IR.bool, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt hu, Nat.mul_div_cancel_left]
  · simp [h, Runner.IR.bool, BitVec.toNat_ushiftRight,
      Nat.mod_eq_of_lt hq64]

/-- The packing expression uses the natural renormalized significand. -/
theorem floatPackCarry_word (q u : Nat) (hu : 2*u < 2^64)
    (hq : u ≤ q ∧ q ≤ 2*u) :
    let c := Runner.IR.bool (BitVec.ofNat 64 q == BitVec.ofNat 64 (2*u))
    (BitVec.ofNat 64 q >>> (c.toNat % 64)) - BitVec.ofNat 64 u =
      BitVec.ofNat 64 (if q = 2*u then u else q) - BitVec.ofNat 64 u := by
  have bridge := (floatPackCarry_nat q u hu hq).2
  have hb : (if q = 2*u then u else q) < 2^64 := by split <;> omega
  have hw : (BitVec.ofNat 64 q >>>
      ((Runner.IR.bool (BitVec.ofNat 64 q == BitVec.ofNat 64 (2*u))).toNat % 64)) =
      BitVec.ofNat 64 (if q = 2*u then u else q) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
    exact bridge
  dsimp only
  rw [hw]

/-- Renormalization preserves the normal field interval, including carry. -/
theorem floatPackCarry_bounds (q u e max : Nat) (hu : 0 < u)
    (hq : u ≤ q ∧ q ≤ 2*u) (he : 0 < e ∧ e + 1 < max) :
    (0 < e + (if q = 2*u then 1 else 0) ∧
      e + (if q = 2*u then 1 else 0) < max) ∧
    (u ≤ (if q = 2*u then u else q) ∧
      (if q = 2*u then u else q) < 2*u) := by
  split <;> omega

/-- Real exponent bounds exclude machine-word wrap after carry addition. -/
theorem floatPackCarry_exponent (q u e max : Nat) (hu : 2*u < 2^64)
    (hq : u ≤ q ∧ q ≤ 2*u) (he : e + 1 < max) (hm : max ≤ 2^64) :
    let c := Runner.IR.bool (BitVec.ofNat 64 q == BitVec.ofNat 64 (2*u))
    (BitVec.ofNat 64 e + c).toNat = e + (if q = 2*u then 1 else 0) := by
  have hc := (floatPackCarry_nat q u hu hq).1
  have he64 : e < 2^64 := by omega
  have hn : e + (if q = 2*u then 1 else 0) < 2^64 := by split <;> omega
  dsimp only at hc ⊢
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt he64, hc,
    Nat.mod_eq_of_lt hn]

/-- The actual carry packing expression equals canonical normalized fields. -/
theorem floatPackCarry_canonical (F : Gleitkomma.Format) (sign : Bool) (e q : Nat)
    (hu : 2 * 2^F.fracBits < 2^64) (hm : F.bexpMax ≤ 2^64)
    (he : 0 < e ∧ e + 1 < F.bexpMax)
    (hq : 2^F.fracBits ≤ q ∧ q ≤ 2 * 2^F.fracBits) :
    let c := Runner.IR.bool (BitVec.ofNat 64 q == BitVec.ofNat 64 (2 * 2^F.fracBits))
    BitVec.ofNat 64 (if sign then 2^(F.ebits + F.fracBits) else 0) +
      (BitVec.ofNat 64 e + c) * BitVec.ofNat 64 (2^F.fracBits) +
      ((BitVec.ofNat 64 q >>> (c.toNat % 64)) - BitVec.ofNat 64 (2^F.fracBits)) =
    BitVec.ofNat 64 (Gleitkomma.zuBits F
      ⟨sign, e + (if q = 2 * 2^F.fracBits then 1 else 0),
        (if q = 2 * 2^F.fracBits then 2^F.fracBits else q) - 2^F.fracBits⟩) := by
  have hb := floatPackCarry_bounds q (2^F.fracBits) e F.bexpMax
    (Nat.pow_pos (by decide)) hq he
  have hx : BitVec.ofNat 64 e +
      Runner.IR.bool (BitVec.ofNat 64 q == BitVec.ofNat 64 (2 * 2^F.fracBits)) =
      BitVec.ofNat 64 (e + (if q = 2 * 2^F.fracBits then 1 else 0)) := by
    apply BitVec.eq_of_toNat_eq
    rw [floatPackCarry_exponent q _ e F.bexpMax hu hq he.2 hm,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  dsimp only
  rw [hx, floatPackCarry_word q _ hu hq]
  apply floatPackNormal_canonical F sign _ _ (by omega) hb.1
  simpa [Nat.pow_succ, Nat.mul_comm] using hb.2

/-- The normal branch of the actual rounding kernel, before field packing. -/
theorem floatPackCarry_rundeBruchKern (F : Gleitkomma.Format) (sign : Bool)
    (n d : Nat) (E : Int) (hp : 1 ≤ F.p)
    (hlo : F.emin ≤ E) (hhi : E < (F.emax : Int)) :
    Gleitkomma.rundeBruchKern F sign n d E =
      if Gleitkomma.normQ F.p E n d < 2^F.p then
        ⟨sign, (E - F.emin + 1).toNat,
          Gleitkomma.normQ F.p E n d - 2^(F.p - 1)⟩
      else ⟨sign, (E - F.emin + 2).toNat, 0⟩ := by
  have hn : ¬ E < F.emin - (F.p : Int) := by omega
  unfold Gleitkomma.rundeBruchKern
  rw [if_neg (by omega), if_neg hn, if_pos hlo]
  split
  · rfl
  · rfl

/-- Actual emitted carry IR simulates canonical normalized G fields. -/
theorem floatPackCarryL_canonical {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {s ex qcode : Nat → Option (List II × Nat)}
    (F : Gleitkomma.Format) (sign : Bool) (e q : Nat)
    (hs : WordCode (L := L) ρ W s
      (BitVec.ofNat 64 (if sign then 2^(F.ebits + F.fracBits) else 0)))
    (hecode : WordCode (L := L) ρ W ex (BitVec.ofNat 64 e))
    (hqcode : WordCode (L := L) ρ W qcode (BitVec.ofNat 64 q))
    (hu : 2 * 2^F.fracBits < 2^64) (hm : F.bexpMax ≤ 2^64)
    (he : 0 < e ∧ e + 1 < F.bexpMax)
    (hq : 2^F.fracBits ≤ q ∧ q ≤ 2 * 2^F.fracBits) :
    WordCode (L := L) ρ W (fun d => floatPackCarryL d s ex qcode (2^F.fracBits))
      (BitVec.ofNat 64 (Gleitkomma.zuBits F
        ⟨sign, e + (if q = 2 * 2^F.fracBits then 1 else 0),
          (if q = 2 * 2^F.fracBits then 2^F.fracBits else q) - 2^F.fracBits⟩)) := by
  rw [← floatPackCarry_canonical F sign e q hu hm he hq]
  intro fp K d c top h hK m pc hp
  exact floatPackCarryL_ok hs hecode hqcode (2^F.fracBits) hu h hK m pc hp

/-- Actual normal rounding outputs are exactly the carry packer's fields. -/
theorem floatPackCarry_fields (F : Gleitkomma.Format) (sign : Bool)
    (n d : Nat) (E : Int) (hp : 1 ≤ F.p) (hf : F.fracBits = F.p - 1)
    (hlo : F.emin ≤ E) (hhi : E < (F.emax : Int))
    (hq : Gleitkomma.normQ F.p E n d ≤ 2 * 2^F.fracBits) :
    Gleitkomma.rundeBruchKern F sign n d E =
      ⟨sign, (E - F.emin + 1).toNat +
          (if Gleitkomma.normQ F.p E n d = 2 * 2^F.fracBits then 1 else 0),
        (if Gleitkomma.normQ F.p E n d = 2 * 2^F.fracBits
          then 2^F.fracBits else Gleitkomma.normQ F.p E n d) - 2^F.fracBits⟩ := by
  have hpow : 2^F.p = 2 * 2^F.fracBits := by
    have he : F.p = F.fracBits + 1 := by omega
    rw [he, Nat.pow_succ]
    omega
  rw [floatPackCarry_rundeBruchKern F sign n d E hp hlo hhi, hpow]
  by_cases hc : Gleitkomma.normQ F.p E n d = 2 * 2^F.fracBits
  · simp only [hc, Nat.lt_irrefl, ↓reduceIte, Nat.sub_self]
    congr 1
    omega
  · have hl : Gleitkomma.normQ F.p E n d < 2 * 2^F.fracBits := by omega
    simp only [hl, hc, ↓reduceIte, Nat.add_zero]
    rw [hf]


/-- The emitted carry fragment returns the actual canonical rounding-kernel bits. -/
theorem floatPackCarryL_rundeBruchKern {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {s ex qcode : Nat → Option (List II × Nat)}
    (F : Gleitkomma.Format) (sign : Bool) (n d : Nat) (E : Int)
    (hs : WordCode (L := L) ρ W s
      (BitVec.ofNat 64 (if sign then 2^(F.ebits + F.fracBits) else 0)))
    (hecode : WordCode (L := L) ρ W ex (BitVec.ofNat 64 (E - F.emin + 1).toNat))
    (hqcode : WordCode (L := L) ρ W qcode
      (BitVec.ofNat 64 (Gleitkomma.normQ F.p E n d)))
    (hp : 1 ≤ F.p) (hf : F.fracBits = F.p - 1)
    (hlo : F.emin ≤ E) (hhi : E < (F.emax : Int))
    (hu : 2 * 2^F.fracBits < 2^64) (hm : F.bexpMax ≤ 2^64)
    (he : 0 < (E - F.emin + 1).toNat ∧
      (E - F.emin + 1).toNat + 1 < F.bexpMax)
    (hq : 2^F.fracBits ≤ Gleitkomma.normQ F.p E n d ∧
      Gleitkomma.normQ F.p E n d ≤ 2 * 2^F.fracBits) :
    WordCode (L := L) ρ W (fun dst => floatPackCarryL dst s ex qcode (2^F.fracBits))
      (BitVec.ofNat 64 (Gleitkomma.zuBits F (Gleitkomma.rundeBruchKern F sign n d E))) := by
  rw [floatPackCarry_fields F sign n d E hp hf hlo hhi hq.2]
  exact floatPackCarryL_canonical F sign _ _ hs hecode hqcode hu hm he hq


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
      simpa only [mag] using hl h t m pc pre)
    (by intro h; cases h) hpre

/-- The actual right scale executes subtraction, nearest-even rounding and jumps. -/
theorem floatOfIntScaleL_right {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} {input : Nat → Option (List II × Nat)}
    (z : Int) (hz : -2^63 ≤ z ∧ z < 2^63) (hn : z ≠ 0)
    (hi : WordCode (L := L) ρ W input (BitVec.ofInt 64 z))
    (p : Nat) (hp : 1 ≤ p) (hb : p - 1 < 64)
    (hr : ((p - 1 : Nat) : Int) ≤ Gleitkomma.findeExp z.natAbs 1)
    (hs : (Gleitkomma.findeExp z.natAbs 1 - ((p : Int) - 1)).toNat < 63)
    {m : Runner.Mem} {pc fp : Runner.W} {K d top : Nat} {c : List II}
    (hc : floatOfIntScaleL p d input = some (c, top))
    (ht : top ≤ K) (hd : d < K)
    (pre : Pre L m pc fp K d c ρ W 0) :
    Ok m pc fp K d c (fun w => w = BitVec.ofNat 64
      (Gleitkomma.normQ p (Gleitkomma.findeExp z.natAbs 1) z.natAbs 1)) := by
  have he := floatOfIntAssemblyL_prefix z hz hn hi
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
      simpa only [(floatOfIntAssembly_magnitude_bound z hz).1] using round h t m pc pre) pre

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

/-- Connected execution of the actual signed left scaling and packing instructions.
    The result is stated at word level; canonical field bounds are a separate obligation. -/
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

#print axioms floatOfIntAssemblyL_left_ofInt
#print axioms floatOfIntAssemblyL_left_ofInt_zeuge

end Gabbro.Stage0.Senke
