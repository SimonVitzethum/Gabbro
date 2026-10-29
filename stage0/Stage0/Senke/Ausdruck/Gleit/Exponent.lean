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

/-- Generic prefix invariant: a threshold counts exactly the first positive shifts. -/
theorem floatExponentWordAux_prefix (a : Runner.W) (bound n : Nat)
    (hprefix : ∀ k, 1 ≤ k → k ≤ n →
      (a >>> (k % 64) == 0) = decide (bound < k)) :
    floatExponentWordAux a n = BitVec.ofNat 64 (min n bound) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [floatExponentWordAux, ih (fun k hk hn => hprefix k hk (by omega)),
      hprefix (n + 1) (by omega) (by omega)]
    by_cases hb : bound < n + 1
    · simp [hb, Runner.IR.bool, Nat.min_eq_right (by omega : bound ≤ n),
        Nat.min_eq_right (by omega : bound ≤ n + 1)]
    · simp [hb, Runner.IR.bool, Nat.min_eq_left (by omega : n ≤ bound),
        Nat.min_eq_left (by omega : n + 1 ≤ bound), BitVec.ofNat_add]

theorem floatExponentWordAux_bitlen (a : Runner.W) (ha : a.toNat ≠ 0) :
    floatExponentWordAux a 63 =
      BitVec.ofNat 64 (Gleitkomma.bitlen a.toNat - 1) := by
  have hu := Gleitkomma.bitlen_obere a.toNat
  have hl := Gleitkomma.bitlen_untere a.toNat ha
  have hb : 0 < Gleitkomma.bitlen a.toNat := by
    by_cases h : Gleitkomma.bitlen a.toNat = 0
    · simp [h] at hu; omega
    · omega
  have low : 2 ^ (Gleitkomma.bitlen a.toNat - 1) ≤ a.toNat := by
    have he : Gleitkomma.bitlen a.toNat = (Gleitkomma.bitlen a.toNat - 1) + 1 := by omega
    rw [he, Nat.pow_succ] at hl
    omega
  have bound : Gleitkomma.bitlen a.toNat - 1 ≤ 63 := by
    have ht := a.isLt
    have hp : 2 ^ (Gleitkomma.bitlen a.toNat - 1) < 2 ^ 64 := by omega
    have := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hp
    omega
  rw [floatExponentWordAux_prefix a (Gleitkomma.bitlen a.toNat - 1) 63,
    Nat.min_eq_right bound]
  intro k hk hk63
  have hz : (a >>> (k % 64) = 0) ↔ Gleitkomma.bitlen a.toNat - 1 < k := by
    rw [BitVec.toNat_eq]
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_zero,
      Nat.mod_eq_of_lt (by omega : k < 64), Nat.shiftRight_eq_div_pow]
    change a.toNat / 2 ^ k = 0 ↔ Gleitkomma.bitlen a.toNat - 1 < k
    rw [Nat.div_eq_zero_iff, or_iff_right (Nat.ne_of_gt (Nat.two_pow_pos k))]
    constructor
    · intro h
      have hp : 2 ^ (Gleitkomma.bitlen a.toNat - 1) < 2 ^ k := by omega
      exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hp
    · intro h
      have hp : 2 ^ Gleitkomma.bitlen a.toNat ≤ 2 ^ k :=
        (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mpr (by omega)
      omega
  exact Bool.eq_iff_iff.mpr (by simpa using hz)

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

theorem floatExponentWord_canonical (av : Runner.W) (hn : av.toNat ≠ 0) :
    floatExponentWordAux av 63 - Runner.IR.bool (av == 0) =
      BitVec.ofInt 64 (Gleitkomma.findeExp av.toNat 1) := by
  have hz : av ≠ 0 := by intro h; simp [h] at hn
  have hb : 0 < Gleitkomma.bitlen av.toNat := by
    have h := Gleitkomma.bitlen_obere av.toNat
    by_cases hh : Gleitkomma.bitlen av.toNat = 0
    · have : Gleitkomma.bitlen av.toNat = 0 := hh
      simp [this] at h
      omega
    · omega
  rw [floatExponentWordAux_bitlen av hn, findeExp_integer_nonzero av.toNat hn]
  simp only [beq_eq_false_iff_ne.mpr hz, Runner.IR.bool, Bool.false_eq_true, ite_false,
    ]
  have he : (Gleitkomma.bitlen av.toNat : Int) - 1 =
      Int.ofNat (Gleitkomma.bitlen av.toNat - 1) := by
    simp only [Int.ofNat_eq_coe]
    omega
  rw [he]
  simp [BitVec.ofInt_ofNat]

theorem floatExponentL_canonical {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {a : Nat → Option (List II × Nat)} {av : Runner.W}
    (ha : WordCode (L := L) ρ W a av) (hn : av.toNat ≠ 0) :
    WordCode (L := L) ρ W (fun d => floatExponentL d a)
      (BitVec.ofInt 64 (Gleitkomma.findeExp av.toNat 1)) := by
  rw [← floatExponentWord_canonical av hn]
  exact floatExponentL_ok ha

theorem normalize_integer_zero (F : Gleitkomma.Format) (s : Bool) :
    Gleitkomma.rundeBruchBei F s 0 1 = ⟨s, 0, 0⟩ := by
  simp [Gleitkomma.rundeBruchBei]

/-- Joint fixtures discharge simulation and nonzero premises together. -/
theorem floatExponentL_canonical_zeuge {Γ : Ctx} (ρ : Env D Γ)
    (W : Runner.Mem → Prop) :
    ∀ n ∈ ([2^16, 2^24 + 1, 2^64 - 1, 2^63] : List Nat),
      let a := fun d => some (konstWL 4 n d)
      let v := BitVec.ofNat 64 n
      WordCode (L := L) ρ W a v ∧ v.toNat ≠ 0 ∧
      WordCode (L := L) ρ W (fun d => floatExponentL d a)
        (BitVec.ofInt 64 (Gleitkomma.findeExp v.toNat 1)) := by
  intro n hn
  have bounds : n < 2^64 ∧ n % 2^64 ≠ 0 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with h | h | h | h <;> subst n <;> decide
  have hc : WordCode (L := L) ρ W (fun d => some (konstWL 4 n d)) (BitVec.ofNat 64 n) := WordCode.konst (L := L) (ρ := ρ) (W := W) n bounds.1
  exact ⟨hc, bounds.2, floatExponentL_canonical hc bounds.2⟩

theorem normalize_integer_zero_zeuge :
    Gleitkomma.rundeBruchBei Gleitkomma.f32 false 0 1 = ⟨false, 0, 0⟩ := by
  exact normalize_integer_zero _ _

end Gabbro.Stage0.Senke
