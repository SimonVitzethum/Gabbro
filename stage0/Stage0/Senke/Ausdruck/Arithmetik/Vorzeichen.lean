/- The shared add/sub operand preparation uses modular integer addition.
   Adding the high bit toggles it without inspecting the floating value. -/
import Stage0.Senke.Ausdruck.Arithmetik.AddSub
import Stage0.Senke.Ausdruck.Gleit.Komposition

set_option maxRecDepth 4096

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem

/-- Addition modulo 2^64 flips exactly the binary64 sign bit. -/
def floatNegWord (w : Runner.W) : Runner.W := w + BitVec.ofNat 64 (2^63)

/-- No well-formedness premise is needed: the bit packing identity is modular. -/
theorem floatNegWord_model (a : GFloat) :
    floatNegWord (BitVec.ofNat 64 (Gleitkomma.zuBits Gleitkomma.f64 a)) =
      BitVec.ofNat 64 (Gleitkomma.zuBits Gleitkomma.f64 (Gleitkomma.neg _ a)) := by
  have hw : Gleitkomma.f64.ebits + Gleitkomma.f64.fracBits = 63 := by decide
  unfold floatNegWord Gleitkomma.zuBits Gleitkomma.neg
  rw [hw]
  cases a.sign <;>
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, Nat.zero_add, BitVec.ofNat_add]
  · ac_rfl
  · have hh : BitVec.ofNat 64 (2^63) + BitVec.ofNat 64 (2^63) = 0 := by decide
    calc
      _ = (BitVec.ofNat 64 (2^63) + BitVec.ofNat 64 (2^63)) +
          (BitVec.ofNat 64 (a.bexp * 2^Gleitkomma.f64.fracBits) + BitVec.ofNat 64 a.frac) := by
        ac_rfl
      _ = _ := by rw [hh]; simp

/-- One reusable pure lowering for the right operand of subtraction. -/
def floatNegL (d : Nat) (e : Nat → Option (List II × Nat)) : Option (List II × Nat) :=
  wordL 3 d (e d) (some (konstWL 4 (2^63) (d + 1)))

variable [Kern] {D : Deklaration} {L : Lay D}

/-- Generic emitted-code simulation includes the temporary frame agreement in
    Ok. It applies to any pure producer, not to selected source programs. -/
theorem floatNegL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {e : Nat → Option (List II × Nat)} {v : Runner.W}
    (he : WordCode (L := L) ρ W e v) :
    WordCode (L := L) ρ W (fun d => floatNegL d e) (floatNegWord v) := by
  exact WordCode.bin he (WordCode.konst (2^63) (by decide))
    (g := fun a b => some (a + b)) rfl rfl (by decide : 3 < 256)

/-- The actual integer fragment implements the canonical negation. -/
theorem floatNegL_model {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {e : Nat → Option (List II × Nat)} (a : GFloat)
    (he : WordCode (L := L) ρ W e (BitVec.ofNat 64 (Gleitkomma.zuBits _ a))) :
    WordCode (L := L) ρ W (fun d => floatNegL d e)
      (BitVec.ofNat 64 (Gleitkomma.zuBits _ (Gleitkomma.neg _ a))) := by
  rw [← floatNegWord_model]
  exact floatNegL_ok he

omit [Kern] in
/-- Joint encoded witnesses cover both zero signs, infinity, a NaN payload,
    and a finite normal. Negation preserves every bit below the sign. -/
theorem floatNegWord_model_zeuge :
    floatNegWord 0 = BitVec.ofNat 64 (2^63) ∧
    floatNegWord (BitVec.ofNat 64 (2^63)) = 0 ∧
    floatNegWord (BitVec.ofNat 64 0x7ff0000000000000) = BitVec.ofNat 64 0xfff0000000000000 ∧
    floatNegWord (BitVec.ofNat 64 0xfff0000000000009) = BitVec.ofNat 64 0x7ff0000000000009 ∧
    floatNegWord (BitVec.ofNat 64 0x3ff0000000000000) = BitVec.ofNat 64 0xbff0000000000000 := by
  decide +kernel

#print axioms floatNegWord_model
#print axioms floatNegL_model
#print axioms floatNegWord_model_zeuge

end Gabbro.Stage0.Senke
