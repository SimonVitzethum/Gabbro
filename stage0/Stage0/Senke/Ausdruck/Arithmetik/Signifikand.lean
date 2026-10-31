/- Connected finite operand decoding using only integer S0 instructions.
   The hidden bit is absent at exponent zero, including signed zero. -/
import Stage0.Senke.Ausdruck.Arithmetik.Felder

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem

/-- The signed coefficient before exponent alignment. Specials are dispatched
    by the caller; decoding itself is total on all input words. -/
def floatCoefficientWord (w : Runner.W) : Runner.W :=
  (1 - 2 * floatFieldWord w 63 1) *
    (floatFieldWord w 0 52 +
      (1 - Runner.IR.bool (floatFieldWord w 52 11 == 0)) * BitVec.ofNat 64 (2^52))

/-- One compositional integer fragment, shared by addition and subtraction.
    The producer is pure and may be reread at arbitrary temporary bases. -/
def floatCoefficientL (d : Nat) (e : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  let c := fun (n : Int) (d : Nat) => some ([ci 1 d n 0], d + 1)
  let sign := fun d => wordL 4 d (c 1 d)
    (wordL 5 (d + 1) (c 2 (d + 1)) (floatFieldL 63 1 (d + 2) e))
  let hidden := fun d => wordL 5 d
    (wordL 4 d (c 1 d)
      (wordL 14 (d + 1) (floatFieldL 52 11 (d + 1) e) (c 0 (d + 2))))
    (some (konstWL 4 (2^52) (d + 1)))
  wordL 5 d (sign d)
    (wordL 3 (d + 1) (floatFieldL 0 52 (d + 1) e) (hidden (d + 2)))

/-- Canonical integer coefficient, with no hidden bit for subnormals. -/
def floatCoefficient (a : GFloat) : Int :=
  (if a.sign then -1 else 1) *
    ((a.frac : Int) + if a.bexp = 0 then 0 else (2^52 : Int))

/-- The connected word arithmetic agrees with the canonical decoded fields. -/
theorem floatCoefficientWord_canonical (a : GFloat)
    (ha : Gleitkomma.wf Gleitkomma.f64 a) :
    floatCoefficientWord (BitVec.ofNat 64 (Gleitkomma.zuBits _ a)) =
      BitVec.ofInt 64 (floatCoefficient a) := by
  let w := BitVec.ofNat 64 (Gleitkomma.zuBits Gleitkomma.f64 a)
  obtain ⟨hf, he⟩ := floatFieldWord_canonical Gleitkomma.f64 Gleitkomma.f64_dicht (by decide) a ha
  change (floatFieldWord _ 0 52).toNat = a.frac at hf
  change (floatFieldWord _ 52 11).toNat = a.bexp at he
  have hs : (floatFieldWord w 63 1).toNat = if a.sign then 1 else 0 := by
    have inv := congrArg (fun x : GFloat => x.sign)
      (Gleitkomma.ausBits_zuBits _ Gleitkomma.f64_dicht a ha)
    have bound := Gleitkomma.zuBits_lt _ Gleitkomma.f64_dicht a ha
    change Gleitkomma.zuBits Gleitkomma.f64 a < 2^64 at bound
    rw [floatFieldWord_model _ 63 1 (by decide)]
    simp only [w, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
    change (Gleitkomma.zuBits Gleitkomma.f64 a / 2^63 % 2 == 1) = a.sign at inv
    have small := Nat.mod_lt (Gleitkomma.zuBits Gleitkomma.f64 a / 2^63) (by decide : 0 < 2)
    cases hsign : a.sign <;> simp only [hsign, Bool.false_eq_true, ↓reduceIte]
    · have hn : Gleitkomma.zuBits Gleitkomma.f64 a / 2^63 % 2 ≠ 1 := by simpa [hsign] using inv
      omega
    · have hn : Gleitkomma.zuBits Gleitkomma.f64 a / 2^63 % 2 = 1 := by simpa [hsign] using inv
      exact hn
  have wf : floatFieldWord w 0 52 = BitVec.ofNat 64 a.frac := by
    rw [← hf]; simp [w]
  have we : floatFieldWord w 52 11 = BitVec.ofNat 64 a.bexp := by
    rw [← he]; simp [w]
  have ws : floatFieldWord w 63 1 = BitVec.ofNat 64 (if a.sign then 1 else 0) := by
    rw [← hs]; simp
  have ez : (BitVec.ofNat 64 a.bexp == 0) = decide (a.bexp = 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, BitVec.toNat_ofNat]
    have hb : a.bexp < 2^64 := by have := ha.1; change a.bexp ≤ 2047 at this; omega
    rw [Nat.mod_eq_of_lt hb]; rfl
  change floatCoefficientWord w = _
  unfold floatCoefficientWord
  rw [wf, we, ws, ez]
  cases hsign : a.sign <;> by_cases hz : a.bexp = 0 <;>
    simp [floatCoefficient, hsign, hz, Runner.IR.bool, BitVec.ofInt_neg, BitVec.ofInt_mul, BitVec.ofInt_add,
      BitVec.ofInt_natCast] <;>
      change (-1 : Runner.W) * _ = -_ <;> rw [BitVec.neg_mul] <;> exact congrArg Neg.neg (BitVec.one_mul _)

/-- The source dyadic exponent is computed from the encoded operand. Signed
    zero keeps the canonical exponent zero; subnormals use the minimum scale.
    No correctness premise about an internal exponent is needed. -/
theorem floatCoefficient_exact_scale (a : GFloat) (h : a.bexp ≠ 2047) :
    Gleitkomma.wertExakt Gleitkomma.f64 a = some ⟨floatCoefficient a,
      if a.bexp = 0 then (if a.frac = 0 then 0 else -1074)
      else (a.bexp : Int) - 1023 - 52⟩ := by
  by_cases hz : a.bexp = 0
  · by_cases hf : a.frac = 0 <;>
      simp [Gleitkomma.wertExakt, Gleitkomma.klasse, Gleitkomma.f64,
        Gleitkomma.Format.bexpMax, Gleitkomma.Format.bias, Gleitkomma.Format.emin,
        floatCoefficient, hz, hf]
  · simp [Gleitkomma.wertExakt, Gleitkomma.klasse, Gleitkomma.f64,
      Gleitkomma.Format.bexpMax, Gleitkomma.Format.bias, Gleitkomma.Format.emin,
      floatCoefficient, hz, h, Int.add_comm]

/-- Bounds on the actual source scale follow from the encoded finite input,
    including zero. The upper endpoint is 2046 - 1023 - 52; the lower
    endpoint is shared by subnormals and the least normal exponent. These
    bounds do not yet identify a normalization temporary with the source scale. -/
theorem floatCoefficient_exact_bounds (a : GFloat)
    (ha : Gleitkomma.wf Gleitkomma.f64 a) (h : a.bexp ≠ 2047) :
    ∃ e, Gleitkomma.wertExakt Gleitkomma.f64 a = some ⟨floatCoefficient a, e⟩ ∧
      -1074 ≤ e ∧ e ≤ 971 := by
  refine ⟨_, floatCoefficient_exact_scale a h, ?_⟩
  have hb := ha.1
  change a.bexp ≤ 2047 at hb
  split
  · split <;> decide
  · change (-1074 : Int) ≤ (a.bexp : Int) - 1023 - 52 ∧
      (a.bexp : Int) - 1023 - 52 ≤ (971 : Int)
    omega

/-- Link to the exact finite operand semantics, including zero and subnormal
    coefficients. -/
theorem floatCoefficient_exact (a : GFloat) (h : a.bexp ≠ 2047) :
    ∃ e, Gleitkomma.wertExakt Gleitkomma.f64 a = some ⟨floatCoefficient a, e⟩ :=
  ⟨_, floatCoefficient_exact_scale a h⟩

/-- Joint source-scale fixtures: signed zero, least subnormal, least normal,
    and greatest finite exponent, with both signs. -/
theorem floatCoefficient_exact_scale_zeuge :
    ∀ a ∈ ([⟨true, 0, 0⟩, ⟨false, 0, 1⟩, ⟨false, 1, 0⟩,
      ⟨true, 2046, 2^52-1⟩] : List GFloat),
      Gleitkomma.wf Gleitkomma.f64 a ∧ a.bexp ≠ 2047 ∧
      ∃ e, Gleitkomma.wertExakt Gleitkomma.f64 a = some ⟨floatCoefficient a, e⟩ ∧
        -1074 ≤ e ∧ e ≤ 971 := by
  intro a ha
  have valid : Gleitkomma.wf Gleitkomma.f64 a ∧ a.bexp ≠ 2047 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with h | h | h | h <;> subst a <;> decide
  exact ⟨valid.1, valid.2, floatCoefficient_exact_bounds a valid.1 valid.2⟩

#print axioms floatCoefficient_exact_scale
#print axioms floatCoefficient_exact_bounds
#print axioms floatCoefficient_exact_scale_zeuge

/-- Exact emitted instruction count and temporary ceiling. Rereading the
    pure input costs three producer executions; no unbounded loop is hidden. -/
theorem floatCoefficientL_shape (d t n : Nat)
    (e : Nat → Option (List II × Nat)) (code : Nat → List II)
    (he : ∀ k, e k = some (code k, k + t))
    (hl : ∀ k, (code k).length = n) :
    ∃ output, floatCoefficientL d e =
      some (output, max (d + t + 3) (d + 6)) ∧ output.length = 3*n + 88 := by
  simp [floatCoefficientL, floatFieldL, wordL, he, konstWL, bin2, hl,
    Nat.max_assoc]
  refine ⟨_, ⟨rfl, ?_⟩, ?_⟩
  · omega
  · simp [hl]; omega

variable [Kern] {D : Deklaration} {L : Lay D}

/-- Simulation of the actual connected fragment for every input producer,
    arbitrary frame, footprint and temporary base through WordCode/Ok. -/
theorem floatCoefficientL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {e : Nat → Option (List II × Nat)} {w : Runner.W}
    (he : WordCode (L := L) ρ W e w) :
    WordCode (L := L) ρ W (fun d => floatCoefficientL d e) (floatCoefficientWord w) := by
  have c0 : WordCode (L := L) ρ W _ _ := WordCode.const (L := L) (ρ := ρ) (W := W) 0 (by decide)
  have c1 : WordCode (L := L) ρ W _ _ := WordCode.const (L := L) (ρ := ρ) (W := W) 1 (by decide)
  have c2 : WordCode (L := L) ρ W _ _ := WordCode.const (L := L) (ρ := ρ) (W := W) 2 (by decide)
  have fs : WordCode (L := L) ρ W _ _ := floatFieldL_ok 63 1 (by decide) (by decide) he
  have fe : WordCode (L := L) ρ W _ _ := floatFieldL_ok 52 11 (by decide) (by decide) he
  have ff : WordCode (L := L) ρ W _ _ := floatFieldL_ok 0 52 (by decide) (by decide) he
  have twice : WordCode (L := L) ρ W _ _ := WordCode.bin c2 fs (g := fun a b => some (a * b)) rfl rfl (by decide : 5 < 256)
  have sign : WordCode (L := L) ρ W _ _ := WordCode.bin c1 twice (g := fun a b => some (a - b)) rfl rfl (by decide : 4 < 256)
  have zero : WordCode (L := L) ρ W _ _ := WordCode.bin fe c0 (g := fun a b => some (Runner.IR.bool (a == b)))
    rfl rfl (by decide : 14 < 256)
  have normal : WordCode (L := L) ρ W _ _ := WordCode.bin c1 zero (g := fun a b => some (a - b)) rfl rfl (by decide : 4 < 256)
  have hidden : WordCode (L := L) ρ W _ _ := WordCode.bin normal (WordCode.konst (2^52) (by decide))
    (g := fun a b => some (a * b)) rfl rfl (by decide : 5 < 256)
  have magnitude : WordCode (L := L) ρ W _ _ := WordCode.bin ff hidden (g := fun a b => some (a + b))
    rfl rfl (by decide : 3 < 256)
  intro fp K d c top h hK m pc hp
  exact WordCode.bin sign magnitude (g := fun a b => some (a * b))
    rfl rfl (by decide : 5 < 256) h hK m pc hp

end Gabbro.Stage0.Senke
