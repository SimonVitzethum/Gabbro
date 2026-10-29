/- Integer exponent selection from nonzero shifted prefixes. -/
import Stage0.Senke.Ausdruck.Gleit.Komposition

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

/-- Count nonzero prefixes at shifts 1 through fuel. Zero has exponent -1,
    matching the canonical integer-ratio exponent rather than log2's zero convention. -/
def floatExponentWordAux (a : Runner.W) : Nat → Runner.W
  | 0 => 0
  | n + 1 => floatExponentWordAux a n +
      (1 - Runner.IR.bool ((a >>> ((n + 1) % 64)) == 0))

def floatExponentAuxL (a : Nat → Option (List II × Nat)) :
    Nat → Nat → Option (List II × Nat)
  | 0, d => some ([ci 1 d 0 0], d + 1)
  | n + 1, d =>
    let shifted := fun j => wordK 12 j (a j) (Int.ofNat (n + 1))
    let zero := fun j => wordK 14 j (shifted j) 0
    let nonzero := fun j => wordL 4 j (some ([ci 1 j 1 0], j + 1)) (zero (j + 1))
    wordL 3 d (floatExponentAuxL a n d) (nonzero (d + 1))

/-- The 63 nontrivial shifts cover every supported unsigned magnitude. -/
def floatExponentL (d : Nat) (a : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  let zero := fun j => wordK 14 j (a j) 0
  wordL 4 d (floatExponentAuxL a 63 d) (zero (d + 1))

theorem floatExponentAuxL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a : Nat → Option (List II × Nat)} {av : Runner.W}
    (ha : WordCode (L := L) ρ W a av) (n : Nat) (hn : n ≤ 63) :
    WordCode (L := L) ρ W (floatExponentAuxL a n) (floatExponentWordAux av n) := by
  induction n with
  | zero => exact WordCode.const 0 (by decide)
  | succ n ih =>
    have hc : lit32 (Int.ofNat (n + 1)) = true := by
      simp [lit32]; omega
    have sh : WordCode (L := L) ρ W _ _ := WordCode.bin ha (WordCode.const (Int.ofNat (n + 1)) hc)
      (g := fun x y => some (x >>> (y.toNat % 64))) rfl rfl (by decide : 12 < 256)
    have ze : WordCode (L := L) ρ W _ _ := WordCode.bin sh (WordCode.const 0 (by decide))
      (g := fun x y => some (Runner.IR.bool (x == y))) rfl rfl (by decide : 14 < 256)
    have nz : WordCode (L := L) ρ W _ _ := WordCode.bin (WordCode.const 1 (by decide)) ze
      (g := fun x y => some (x - y)) rfl rfl (by decide : 4 < 256)
    have result : WordCode (L := L) ρ W _ _ := WordCode.bin (ih (by omega)) nz
      (g := fun x y => some (x + y)) rfl rfl (by decide : 3 < 256)
    intro fp K d c top h hK m pc hp
    have hv : (BitVec.ofInt 64 (Int.ofNat (n + 1))).toNat = n + 1 := by
      change (n + 1) % 2^64 = n + 1
      exact Nat.mod_eq_of_lt (by omega)
    simpa only [floatExponentWordAux, hv, BitVec.ofInt_ofNat, BitVec.ofNat_eq_ofNat] using
      result (fp := fp) (K := K) (d := d) (c := c) (top := top) h hK m pc hp

end Gabbro.Stage0.Senke
