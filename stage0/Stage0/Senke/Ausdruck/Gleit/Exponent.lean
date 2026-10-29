/- Integer exponent selection from nonzero shifted prefixes. -/
import Stage0.Senke.Ausdruck.Gleit.Komposition

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

/-- Count nonzero prefixes at shifts 1 through fuel. Zero has exponent -1,
    while canonical `findeExp 0 1` is -2. Normalization bypasses exponent
    selection for zero; correspondence requires a nonzero magnitude. -/
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

/-- Simulation includes the zero correction after prefix counting. -/
theorem floatExponentL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a : Nat → Option (List II × Nat)} {av : Runner.W}
    (ha : WordCode (L := L) ρ W a av) :
    WordCode (L := L) ρ W (fun d => floatExponentL d a)
      (floatExponentWordAux av 63 - Runner.IR.bool (av == 0)) := by
  have ze : WordCode (L := L) ρ W _ _ := WordCode.bin ha (WordCode.const 0 (by decide))
    (g := fun x y => some (Runner.IR.bool (x == y))) rfl rfl (by decide : 14 < 256)
  have result : WordCode (L := L) ρ W _ _ := WordCode.bin (floatExponentAuxL_ok ha 63 (by decide)) ze
    (g := fun x y => some (x - y)) rfl rfl (by decide : 4 < 256)

  intro fp K d c top h hK m pc hp
  exact result h hK m pc hp

/-- For a positive integer, the canonical exponent is its bit length minus one. -/
theorem findeExp_integer_nonzero (n : Nat) (hn : n ≠ 0) :
    Gleitkomma.findeExp n 1 = (Gleitkomma.bitlen n : Int) - 1 := by
  have hu := Gleitkomma.bitlen_obere n
  have hl := Gleitkomma.bitlen_untere n hn
  have hb : 0 < Gleitkomma.bitlen n := by
    cases h : Gleitkomma.bitlen n with
    | zero => simp [h] at hu; omega
    | succ k => omega
  have he : (Gleitkomma.bitlen n - 1) + 1 = Gleitkomma.bitlen n := by omega
  have hp : 2 ^ (Gleitkomma.bitlen n - 1) ≤ n := by
    rw [← he, Nat.pow_succ] at hl
    omega
  have hc : ((Gleitkomma.bitlen n : Int) - 1).toNat =
      Gleitkomma.bitlen n - 1 := by omega
  unfold Gleitkomma.findeExp Gleitkomma.findeExpBei
  have h1 : Gleitkomma.bitlen 1 = 1 := rfl
  rw [h1]
  change Gleitkomma.findeExpBei n 1 ((Gleitkomma.bitlen n : Int) - 1) = _
  unfold Gleitkomma.findeExpBei
  rw [if_pos (by omega), hc, Nat.one_mul, if_pos hp]

theorem normalize_integer_zero (F : Gleitkomma.Format) (s : Bool) :
    Gleitkomma.rundeBruchBei F s 0 1 = ⟨s, 0, 0⟩ := by
  simp [Gleitkomma.rundeBruchBei]

end Gabbro.Stage0.Senke
