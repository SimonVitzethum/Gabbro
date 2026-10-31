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
