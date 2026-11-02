/- Shared integer-only extraction of IEEE fields for arithmetic dispatch. -/
module
public import Stage0.Senke.Ausdruck.Arithmetik.Feldera
public import Stage0.Senke.Ausdruck.Arithmetik.Vorzeichen
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem

variable [Kern] {D : Deklaration} {L : Lay D}
/-- Compare the decoded alignment indices, using the runner's signed comparison.
    Dense formats leave a sign bit above the exponent, so these indices are positive. -/
def floatScaleOrderL (F : Gleitkomma.Format) (d : Nat)
    (a b : Nat → Option (List II × Nat)) : Option (List II × Nat) :=
  wordL 13 d (floatScaleIndexL F d a) (floatScaleIndexL F (d+1) b)

/-- Absolute alignment distance from the same two input producers. The comparison
    selects the sign of the modular subtraction before multiplication. -/
def floatScaleDistanceL (F : Gleitkomma.Format) (d : Nat)
    (a b : Nat → Option (List II × Nat)) : Option (List II × Nat) :=
  wordL 5 d
    (wordL 4 d (floatScaleIndexL F d a) (floatScaleIndexL F (d+1) b))
    (wordL 4 (d+1) (some ([ci 1 (d+1) 1 0], d+2))
      (wordL 5 (d+2) (some ([ci 1 (d+2) 2 0], d+3))
        (floatScaleOrderL F (d+3) a b)))

/-- Both the actual ordering and the actual subtraction are derived from packed
    operands. There is no assumed internal exponent, ordering or distance. -/
theorem floatScaleDistanceL_canonical {Γ : Ctx} {ρ : Env D Γ}
    {W : Runner.Mem → Prop} (F : Gleitkomma.Format) (hd : F.dicht)
    (hw : F.ebits + F.fracBits + 1 ≤ 64)
    (a b : Gleitkomma.GBits F) (ha : Gleitkomma.wf F a) (hb : Gleitkomma.wf F b)
    {ea eb : Nat → Option (List II × Nat)}
    (hea : WordCode (L := L) ρ W ea (BitVec.ofNat 64 (Gleitkomma.zuBits F a)))
    (heb : WordCode (L := L) ρ W eb (BitVec.ofNat 64 (Gleitkomma.zuBits F b))) :
    WordCode (L := L) ρ W (fun d => floatScaleOrderL F d ea eb)
      (Runner.IR.bool (decide (max a.bexp 1 < max b.bexp 1))) ∧
    WordCode (L := L) ρ W (fun d => floatScaleDistanceL F d ea eb)
      (BitVec.ofNat 64 (max a.bexp 1 - max b.bexp 1 +
        (max b.bexp 1 - max a.bexp 1))) := by
  let x := max a.bexp 1
  let y := max b.bexp 1
  have bounds (v : Gleitkomma.GBits F) (hv : Gleitkomma.wf F v) :
      (max v.bexp 1 : Int) < 2^63 := by
    have p := Nat.pow_le_pow_right (by decide : 1 ≤ 2)
      (show F.ebits ≤ 63 by omega)
    have h := hv.1
    unfold Gleitkomma.Format.dicht at hd
    omega
  have bx := bounds a ha
  have by' := bounds b hb
  have ax : WordCode (L := L) ρ W (fun d => floatScaleIndexL F d ea) (BitVec.ofNat 64 x) := floatScaleIndexL_canonical F hd hw a ha hea
  have ay : WordCode (L := L) ρ W (fun d => floatScaleIndexL F d eb) (BitVec.ofNat 64 y) := floatScaleIndexL_canonical F hd hw b hb heb
  have cmp : Runner.IR.bool ((BitVec.ofNat 64 x).slt (BitVec.ofNat 64 y)) =
      Runner.IR.bool (decide (x < y)) := by
    change Runner.IR.bool ((BitVec.ofInt 64 (x : Int)).slt (BitVec.ofInt 64 (y : Int))) = _
    rw [slt_in (by dsimp [x]; constructor <;> omega)
      (by dsimp [y]; constructor <;> omega)]
    simp
  have order : WordCode (L := L) ρ W (fun d => floatScaleOrderL F d ea eb)
      (Runner.IR.bool (decide (x < y))) := by
    have r : WordCode (L := L) ρ W _ _ := WordCode.bin ax ay (g := fun a b => some (Runner.IR.bool (a.slt b)))
      rfl rfl (by decide : 13 < 256)
    intro fp K d c top h hK m pc hp
    exact (r h hK m pc hp).mono fun w h => h.trans cmp
  have delta : WordCode (L := L) ρ W _ _ := WordCode.bin ax ay (g := fun a b => some (a-b))
    rfl rfl (by decide : 4 < 256)
  have twice : WordCode (L := L) ρ W _ _ := WordCode.bin (WordCode.const (L := L) (ρ := ρ) (W := W) 2 (by decide))
    order (g := fun a b => some (a*b)) rfl rfl (by decide : 5 < 256)
  have sign : WordCode (L := L) ρ W _ _ := WordCode.bin (WordCode.const (L := L) (ρ := ρ) (W := W) 1 (by decide))
    twice (g := fun a b => some (a-b)) rfl rfl (by decide : 4 < 256)
  have result : WordCode (L := L) ρ W _ _ := WordCode.bin delta sign (g := fun a b => some (a*b))
    rfl rfl (by decide : 5 < 256)
  refine ⟨order, ?_⟩
  intro fp K d c top h hK m pc hp
  apply (result h hK m pc hp).mono
  intro w heq
  rw [heq]
  change (BitVec.ofNat 64 x - BitVec.ofNat 64 y) *
    (1 - 2 * Runner.IR.bool (decide (x < y))) = BitVec.ofNat 64 (x-y+(y-x))
  by_cases hxy : x < y
  · have hnat : x-y=0 := by omega
    simp only [hxy, decide_true, Runner.IR.bool, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.mul_one, hnat,
      Nat.zero_add]
    have hz : BitVec.ofNat 64 1 - BitVec.ofNat 64 2 = -(BitVec.ofNat 64 1) := by decide
    rw [hz, BitVec.mul_neg, BitVec.mul_one, BitVec.neg_sub, BitVec.add_comm,
      ← BitVec.sub_eq_add_neg,
      BitVec.ofNat_sub_ofNat_of_le (w := 64) y x (by dsimp [x] at bx; omega) (by omega)]
  · have hnat : y-x=0 := by omega
    simp only [hxy, decide_false, Runner.IR.bool, Bool.false_eq_true, ↓reduceIte, BitVec.ofNat_eq_ofNat,
      BitVec.mul_zero, BitVec.sub_zero, BitVec.mul_one, hnat, Nat.add_zero]
    exact BitVec.ofNat_sub_ofNat_of_le (w := 64) x y (by dsimp [y] at by'; omega) (by omega)

/-- Extract the sign from the canonical packed operand, sharing the field decoder. -/
theorem floatSignL_canonical {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    (F : Gleitkomma.Format) (hd : F.dicht) (hw : F.ebits + F.fracBits + 1 ≤ 64)
    (a : Gleitkomma.GBits F) (ha : Gleitkomma.wf F a)
    {e : Nat → Option (List II × Nat)}
    (he : WordCode (L := L) ρ W e (BitVec.ofNat 64 (Gleitkomma.zuBits F a))) :
    WordCode (L := L) ρ W (fun d => floatFieldL (F.ebits+F.fracBits) 1 d e)
      (Runner.IR.bool a.sign) := by
  have bound := Gleitkomma.zuBits_lt F hd a ha
  have p := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hw
  have bound64 : Gleitkomma.zuBits F a < 2^64 := by omega
  have inv := congrArg (fun x : Gleitkomma.GBits F => x.sign)
    (Gleitkomma.ausBits_zuBits F hd a ha)
  change (Gleitkomma.zuBits F a / 2^(F.ebits+F.fracBits) % 2 == 1) = a.sign at inv
  have small := Nat.mod_lt (Gleitkomma.zuBits F a / 2^(F.ebits+F.fracBits))
    (by decide : 0 < 2)
  have field : floatFieldWord (BitVec.ofNat 64 (Gleitkomma.zuBits F a))
      (F.ebits+F.fracBits) 1 = Runner.IR.bool a.sign := by
    apply BitVec.eq_of_toNat_eq
    rw [floatFieldWord_model _ _ 1 (by decide)]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound64]
    cases hs : a.sign
    · have hn : Gleitkomma.zuBits F a / 2^(F.ebits+F.fracBits) % 2 ≠ 1 := by
        simpa [hs] using inv
      simp [Runner.IR.bool]
      omega
    · have hn : Gleitkomma.zuBits F a / 2^(F.ebits+F.fracBits) % 2 = 1 := by
        simpa [hs] using inv
      simpa [Runner.IR.bool] using hn
  have result : WordCode (L := L) ρ W _ _ :=
    floatFieldL_ok (F.ebits+F.fracBits) 1 (by omega) (by decide) he
  intro fp K d c top h hK m pc hp
  exact (result h hK m pc hp).mono fun w h => h.trans field

/-- Decide whether effective operands add magnitudes or subtract them.
    Subtraction reverses the right sign before this decision, including signed zeros. -/
def floatSameSignL (F : Gleitkomma.Format) (subtract : Bool) (d : Nat)
    (a b : Nat → Option (List II × Nat)) : Option (List II × Nat) :=
  wordL 14 d
    (wordL 14 d (floatFieldL (F.ebits+F.fracBits) 1 d a)
      (floatFieldL (F.ebits+F.fracBits) 1 (d+1) b))
    (some ([ci 1 (d+1) (if subtract then 0 else 1) 0], d+2))

/-- The emitted effective-sign decision depends solely on the encoded operands
    and source operation; no intermediate sign or sign agreement is assumed. -/
theorem floatSameSignL_canonical {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    (F : Gleitkomma.Format) (hd : F.dicht) (hw : F.ebits + F.fracBits + 1 ≤ 64)
    (subtract : Bool) (a b : Gleitkomma.GBits F)
    (ha : Gleitkomma.wf F a) (hb : Gleitkomma.wf F b)
    {ea eb : Nat → Option (List II × Nat)}
    (hea : WordCode (L := L) ρ W ea (BitVec.ofNat 64 (Gleitkomma.zuBits F a)))
    (heb : WordCode (L := L) ρ W eb (BitVec.ofNat 64 (Gleitkomma.zuBits F b))) :
    WordCode (L := L) ρ W (fun d => floatSameSignL F subtract d ea eb)
      (Runner.IR.bool (a.sign == (floatAddOperand subtract F b).sign)) := by
  have sa : WordCode (L := L) ρ W _ _ := floatSignL_canonical F hd hw a ha hea
  have sb : WordCode (L := L) ρ W _ _ := floatSignL_canonical F hd hw b hb heb
  have eq : WordCode (L := L) ρ W _ _ := WordCode.bin sa sb
    (g := fun a b => some (Runner.IR.bool (a == b))) rfl rfl (by decide : 14 < 256)
  have c : WordCode (L := L) ρ W _ _ :=
    WordCode.const (if subtract then 0 else 1) (by cases subtract <;> decide)
  have result : WordCode (L := L) ρ W _ _ := WordCode.bin eq c
    (g := fun a b => some (Runner.IR.bool (a == b))) rfl rfl (by decide : 14 < 256)
  intro fp K d code top h hK m pc hp
  apply (result h hK m pc hp).mono
  intro w heq
  rw [heq]
  cases subtract <;> simp only [floatAddOperand, Bool.false_eq_true, ↓reduceIte, Gleitkomma.neg]
    <;> cases a.sign <;> cases b.sign <;> rfl

/-- The zero dispatcher preserves -0 exactly when both effective signs are
    negative. This fragment is used separately from finite cancellation. -/
def floatZeroSignL (F : Gleitkomma.Format) (subtract : Bool) (d : Nat)
    (a b : Nat → Option (List II × Nat)) : Option (List II × Nat) :=
  wordL 5 d (floatFieldL (F.ebits+F.fracBits) 1 d a)
    (if subtract then wordL 4 (d+1) (some ([ci 1 (d+1) 1 0], d+2))
      (floatFieldL (F.ebits+F.fracBits) 1 (d+2) b)
    else floatFieldL (F.ebits+F.fracBits) 1 (d+1) b)

theorem floatZeroSignL_canonical {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    (F : Gleitkomma.Format) (hd : F.dicht) (hw : F.ebits + F.fracBits + 1 ≤ 64)
    (subtract sa sb : Bool) (hz : F.bexpMax ≠ 0)
    (ha : Gleitkomma.wf F ⟨sa,0,0⟩) (hb : Gleitkomma.wf F ⟨sb,0,0⟩)
    {ea eb : Nat → Option (List II × Nat)}
    (hea : WordCode (L := L) ρ W ea (BitVec.ofNat 64 (Gleitkomma.zuBits F ⟨sa,0,0⟩)))
    (heb : WordCode (L := L) ρ W eb (BitVec.ofNat 64 (Gleitkomma.zuBits F ⟨sb,0,0⟩))) :
    WordCode (L := L) ρ W (fun d => floatZeroSignL F subtract d ea eb)
      (Runner.IR.bool (if subtract then
        Gleitkomma.sub F ⟨sa,0,0⟩ ⟨sb,0,0⟩ else
        Gleitkomma.add F ⟨sa,0,0⟩ ⟨sb,0,0⟩).sign) := by
  have a : WordCode (L := L) ρ W _ _ := floatSignL_canonical F hd hw ⟨sa,0,0⟩ ha hea
  have b : WordCode (L := L) ρ W _ _ := floatSignL_canonical F hd hw ⟨sb,0,0⟩ hb heb
  have effective : WordCode (L := L) ρ W
      (fun d => if subtract then wordL 4 d (some ([ci 1 d 1 0], d+1))
        (floatFieldL (F.ebits+F.fracBits) 1 (d+1) eb)
        else floatFieldL (F.ebits+F.fracBits) 1 d eb)
      (Runner.IR.bool (if subtract then !sb else sb)) := by
    cases subtract
    · exact b
    · have result : WordCode (L := L) ρ W _ _ := WordCode.bin
        (WordCode.const 1 (by decide)) b (g := fun a b => some (a-b))
        rfl rfl (by decide : 4 < 256)
      intro fp K d c t hc ht m pc hp
      apply (result hc ht m pc hp).mono
      intro w h
      rw [h]
      cases sb <;> simp [Runner.IR.bool]
  have result : WordCode (L := L) ρ W _ _ := WordCode.bin a effective
    (g := fun a b => some (a*b)) rfl rfl (by decide : 5 < 256)
  intro fp K d c t hc ht m pc hp
  apply (result hc ht m pc hp).mono
  intro w h
  rw [h]
  have hz' : (0 : Nat) ≠ F.bexpMax := Ne.symm hz
  cases subtract <;> cases sa <;> cases sb <;>
    simp [Gleitkomma.sub, Gleitkomma.add, Gleitkomma.neg, Gleitkomma.klasse,
      hz', Runner.IR.bool]

#print axioms floatZeroSignL_canonical

#print axioms floatSignL_canonical
#print axioms floatSameSignL_canonical

#print axioms floatScaleDistanceL_canonical

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
