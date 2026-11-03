/- Magnitude add/sub for software binary64 addition (`Block.float`, `op = .add`).

    After alignment both magnitudes sit at the common exponent with their
    signs: `softAddMag` is their exact signed sum as an `Int` (no casing
    needed at the spec level). `softAddMag_add`/`softAddMag_sub` prove the two
    implementation paths equal the spec — same signs add, differing signs
    subtract — and `softMagBound_add` keeps the added magnitudes inside one
    word. `xorSignL` selects the path from the sign xor, `addMagL`/`subMagL`
    compute the unsigned paths (the subtract path runs directionally: the
    caller orders the magnitudes, as with the gap), all from existing integer
    opcodes (`xor` 10, `add` 3, `sub` 4 via `wordL`) with `WordCode`
    correctness lemmas. -/
module
public import Stage0.Senke.Ausdruck.Aggregat.Hilfena
public import Stage0.Senke.Ausdruck.Gleit.Komposition
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik
open Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

/-- Exact signed sum of two aligned magnitudes: sign times magnitude, added.
    Magnitudes are `Nat` (words); the result is exact (an `Int`). -/
def softAddMag (sa sb : Bool) (ma mb : Nat) : Int :=
  (if sa then (-1 : Int) else 1) * (ma : Int) +
    (if sb then (-1 : Int) else 1) * (mb : Int)

/-- Same signs add: the spec factors through the magnitude sum. -/
theorem softAddMag_add (sa : Bool) (ma mb : Nat) :
    softAddMag sa sa ma mb = (if sa then (-1 : Int) else 1) * ((ma : Int) + mb) := by
  unfold softAddMag
  cases sa <;> simp <;> omega

/-- Differing signs subtract: the spec factors through the magnitude
    difference, signed by the first operand. -/
theorem softAddMag_sub (sa : Bool) (ma mb : Nat) :
    softAddMag sa (!sa) ma mb =
      (if sa then (-1 : Int) else 1) * ((ma : Int) - mb) := by
  unfold softAddMag
  cases sa <;> simp <;> omega

/-- Result sign on the subtract path: the first operand's sign when its
    magnitude covers the second's (the caller orders them so). -/
def softSubSign (sa sb : Bool) (ma mb : Nat) : Bool := if mb ≤ ma then sa else sb

/-- Added 53-bit magnitudes fit one word: the add path never wraps. -/
theorem softMagBound_add (ma mb : Nat) (ha : ma < 2 ^ 53) (hb : mb < 2 ^ 53) :
    ma + mb < 2 ^ 64 := by
  have h54 : (2 : Nat) ^ 53 + 2 ^ 53 < 2 ^ 64 := by decide
  omega

/-- Path selection word: the sign xor (opcode 10). -/
def xorSignWord (sa sb : Runner.W) : Runner.W := sa ^^^ sb

def xorSignL (d : Nat) (sa sb : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  wordL 10 d (sa d) (sb (d + 1))

/-- Added-magnitude word (opcode 3). -/
def addMagWord (ma mb : Runner.W) : Runner.W := ma + mb

def addMagL (d : Nat) (ma mb : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  wordL 3 d (ma d) (mb (d + 1))

/-- Subtracted-magnitude word, directional (opcode 4): the caller orders the
    magnitudes so the subtraction never wraps. -/
def subMagWord (ma mb : Runner.W) : Runner.W := ma - mb

def subMagL (d : Nat) (ma mb : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  wordL 4 d (ma d) (mb (d + 1))

/-- Compositional IR simulation for the sign xor. -/
theorem xorSignL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {sa sb : Nat → Option (List II × Nat)} {sav sbv : Runner.W}
    (hsa : WordCode (L := L) ρ W sa sav) (hsb : WordCode (L := L) ρ W sb sbv) :
    WordCode (L := L) ρ W (fun d => xorSignL d sa sb) (sav ^^^ sbv) := by
  have result : WordCode (L := L) ρ W _ _ := WordCode.bin hsa hsb
    (g := fun x y => some (x ^^^ y)) rfl rfl (by decide : 10 < 256)
  intro fp K d c top h hK m pc hp
  simpa only [xorSignL, xorSignWord] using
    result (fp := fp) (K := K) (d := d) (c := c) (top := top) h hK m pc hp

/-- Compositional IR simulation for the magnitude add. -/
theorem addMagL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {ma mb : Nat → Option (List II × Nat)} {mav mbv : Runner.W}
    (hma : WordCode (L := L) ρ W ma mav) (hmb : WordCode (L := L) ρ W mb mbv) :
    WordCode (L := L) ρ W (fun d => addMagL d ma mb) (mav + mbv) := by
  have result : WordCode (L := L) ρ W _ _ := WordCode.bin hma hmb
    (g := fun x y => some (x + y)) rfl rfl (by decide : 3 < 256)
  intro fp K d c top h hK m pc hp
  simpa only [addMagL, addMagWord] using
    result (fp := fp) (K := K) (d := d) (c := c) (top := top) h hK m pc hp

/-- Compositional IR simulation for the directional magnitude subtract. -/
theorem subMagL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {ma mb : Nat → Option (List II × Nat)} {mav mbv : Runner.W}
    (hma : WordCode (L := L) ρ W ma mav) (hmb : WordCode (L := L) ρ W mb mbv) :
    WordCode (L := L) ρ W (fun d => subMagL d ma mb) (mav - mbv) := by
  have result : WordCode (L := L) ρ W _ _ := WordCode.bin hma hmb
    (g := fun x y => some (x - y)) rfl rfl (by decide : 4 < 256)
  intro fp K d c top h hK m pc hp
  simpa only [subMagL, subMagWord] using
    result (fp := fp) (K := K) (d := d) (c := c) (top := top) h hK m pc hp

/-- Joint fixtures: same-sign add, opposite-sign cancellation and difference,
    the xor selection bit, and the magnitude add on closed words. -/
theorem addMag_zeuge :
    softAddMag false false 4503599627370496 2251799813685248 = 6755399441055744 ∧
    softAddMag true false 4503599627370496 4503599627370496 = 0 ∧
    softAddMag true false 4503599627370496 2251799813685248 = -2251799813685248 ∧
    softSubSign true false 4503599627370496 2251799813685248 = true ∧
    (BitVec.ofNat 64 5 ^^^ BitVec.ofNat 64 3) = BitVec.ofNat 64 6 ∧
    (BitVec.ofNat 64 4503599627370496 + BitVec.ofNat 64 2251799813685248) =
      BitVec.ofNat 64 6755399441055744 := by
  decide +kernel

#print axioms softAddMag_add
#print axioms softAddMag_sub
#print axioms softMagBound_add
#print axioms xorSignL_ok
#print axioms addMagL_ok
#print axioms subMagL_ok
#print axioms addMag_zeuge

end Gabbro.Stage0.Senke
