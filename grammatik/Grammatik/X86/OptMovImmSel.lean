/-
  File:      Grammatik/X86/OptMovImmSel.lean
  Subject:   MOV-immediate selection rule (lane 892).

  DESIGN section 2B rows (MOV reg, imm32 zero-extending / sign-extended
  vs imm64) as a layer-A local rewrite (DESIGN section 7 register
  discipline): a rule lemma over arbitrary values with validator-decided
  side conditions. Reuses the pilot `movImm64` row (`Codec`,
  `Ausfuehrung`) and the accepted compact zero row
  (`CompactImmMov32Zero`); the sign tile reuses canonical `sext`
  (`Wort`) at value level until lane 747 lands its row.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Codec
import Grammatik.X86.CompactImmMov32Zero
import Grammatik.X86.NarrowOps

namespace Gabbro.Grammatik.X86

/-- The three MOV-immediate tiles: the 10-byte pilot `movImm64`, the
    compact zero-extending imm32 row (lane 746), and the sign-extended
    imm32 row (value level only until lane 747 lands). -/
inductive MovTile where
  | weit (v : Wort)
  | kompakt (imm : BitVec 32)
  | sign (imm : BitVec 32)
  deriving DecidableEq, Repr

/-- Value denoted by a tile: the wide word itself, the accepted
    zero extension, or the canonical sign extension. -/
def tileWert : MovTile → Wort
  | .weit v => v
  | .kompakt imm => compactWert imm
  | .sign imm => sext .b32 (BitVec.ofNat 64 imm.toNat)

/-! ## 1. Certificate and validator-decided gates.

    DESIGN section 2B selection rules as decided data, in the section 7
    register discipline (layer-A local rewrite: rule lemma over arbitrary
    values plus re-decided side conditions; layer-B analysis citations
    are the recomputed liveness/range facts the validator rechecks, and
    layer-C duty binding is untouched: no writes, locks, atomics, FP
    modes or costs move). A refused optional tile falls back to the
    certified wide tile, never to a warning. -/

/-- The local rewrite record: the upper-half-dead answer the validator
    recomputes from liveness (layer B); the value ranges are recomputed
    from the word itself, never trusted. -/
structure MovImmCert where
  oberTot : Bool
  deriving DecidableEq, Repr

/-- The value fits an unsigned 32-bit immediate (DESIGN 2B zero row). -/
def passtU32 (v : Wort) : Bool := decide (v.toNat < 2 ^ 32)

/-- The value fits a signed 32-bit immediate (DESIGN 2B sign row). -/
def passtI32 (v : Wort) : Bool :=
  decide (v.toNat < 2 ^ 31 ∨ 2 ^ 64 - 2 ^ 31 ≤ v.toNat)

/-- Admission of the zero tile: upper half dead AND value fits u32. -/
def nullZulassen (v : Wort) (c : MovImmCert) : Bool :=
  c.oberTot && passtU32 v

/-- Narrowest-valid selection: the zero tile where admitted, the sign
    tile where its range holds, else the 10-byte wide tile, which is
    always a certified fallback. -/
def waehleMovImm (v : Wort) (c : MovImmCert) : MovTile :=
  if nullZulassen v c then .kompakt (BitVec.ofNat 32 v.toNat)
  else if passtI32 v then .sign (BitVec.ofNat 32 v.toNat)
  else .weit v

/-- Tile byte length: wide 10 (pilot row), compact 5/6 (accepted row),
    sign 7 (DESIGN 2B row data REX.W + C7 + ModRM + imm32; its codec
    lands with lane 747). -/
def tileLaenge : MovTile → Register → Nat
  | .weit _, _ => 10
  | .kompakt _, dst => compactLen dst
  | .sign _, _ => 7

/-- The u32 gate answers the range question exactly. -/
theorem passtU32_genau (v : Wort) :
    passtU32 v = true ↔ v.toNat < 2 ^ 32 := by
  simp [passtU32]

/-- The i32 gate answers the signed-range question exactly. -/
theorem passtI32_genau (v : Wort) :
    passtI32 v = true ↔
      v.toNat < 2 ^ 31 ∨ 2 ^ 64 - 2 ^ 31 ≤ v.toNat := by
  simp [passtI32]

/-- REFUSAL (upper half live): a live upper half refuses the zero tile,
    whatever the value. -/
theorem nullVerweigert_oberLebendig (v : Wort) (c : MovImmCert)
    (h : c.oberTot = false) : nullZulassen v c = false := by
  simp [nullZulassen, h]

/-- REFUSAL (value too big): a word needing imm64 refuses the zero tile,
    however dead its upper half is. -/
theorem nullVerweigert_gross (v : Wort) (c : MovImmCert)
    (h : passtU32 v = false) : nullZulassen v c = false := by
  simp [nullZulassen, h]

/-- A word needing imm64 fails the u32 gate. -/
theorem passtU32_verweigert_gross (v : Wort)
    (h : brauchtImm64 v = true) : passtU32 v = false := by
  have hle : 2 ^ 32 ≤ v.toNat := (brauchtImm64_genau v).mp h
  have hlt : ¬ v.toNat < 2 ^ 32 := by omega
  simp [passtU32, hlt]

/-- An admitted site selects the zero tile. -/
theorem waehle_null (v : Wort) (c : MovImmCert)
    (h : nullZulassen v c = true) :
    waehleMovImm v c = .kompakt (BitVec.ofNat 32 v.toNat) := by
  simp [waehleMovImm, h]

/-! ## 2. Value preservation: both narrow tiles denote exactly the word.

    The zero tile reuses the accepted `compactWert_nat` bridge. The sign
    tile goes through the canonical `sext`; its bit bridge below follows
    the accepted `RelocatedExecution` pattern (`testBit_div_pow`,
    `bit31_equiv`) with selection-local names, so this file needs no
    relocation import and introduces no duplicate Lean name. -/

/-- Every bit test is a halved division at bit zero. -/
theorem movSelBit_div_pow (n i : Nat) :
    n.testBit i = (n / 2 ^ i).testBit 0 := by
  induction i generalizing n with
  | zero => simp
  | succ k ih =>
    show n.testBit (Nat.succ k) = _
    rw [Nat.testBit_succ, ih]
    congr 1
    rw [Nat.div_div_eq_div_mul]
    congr 1
    have e : k + 1 = Nat.succ k := rfl
    rw [e, Nat.pow_succ, Nat.mul_comm (2 ^ k) 2]

/-- Bit 31 of a 32-bit value is the signed-32 boundary. -/
theorem movSelBit31 (n : Nat) (h : n < 2 ^ 32) :
    n.testBit 31 = decide (2147483648 ≤ n) := by
  have h31 : n.testBit 31 = (n / 2 ^ 31).testBit 0 :=
    movSelBit_div_pow n 31
  rw [h31, Nat.testBit_zero]
  have hdiv : n / 2 ^ 31 < 2 := by
    have h0 : (0 : Nat) < 2 ^ 31 := by decide
    rw [Nat.div_lt_iff_lt_mul h0]
    omega
  have hmod : (n / 2 ^ 31) % 2 = n / 2 ^ 31 :=
    Nat.mod_eq_of_lt hdiv
  rw [hmod]
  have hiff : (n / 2 ^ 31 = 1) ↔ (2147483648 ≤ n) := by
    omega
  simp only [hiff]

/-- The compact immediate denotes exactly a u32-fitting word: the
    upper half is cleared, nothing else changes. -/
theorem kompaktWert_rundgang (v : Wort) (h : passtU32 v = true) :
    compactWert (BitVec.ofNat 32 v.toNat) = v := by
  have hlt : v.toNat < 2 ^ 32 :=
    of_decide_eq_true (by simpa [passtU32] using h)
  apply BitVec.eq_of_toNat_eq
  rw [compactWert_nat, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt hlt

/-- Remainder of a near-top 64-bit value modulo 2^32: only the low
    part below the subtracted amount survives. -/
theorem movSelMod64_32 (k : Nat) (hk1 : 0 < k) (hk2 : k < 2 ^ 32) :
    (2 ^ 64 - k) % 2 ^ 32 = 2 ^ 32 - k := by
  have e64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  have e32 : (2 : Nat) ^ 32 = 4294967296 := rfl
  omega

/-- The sign immediate denotes exactly an i32-fitting word: upper-half
    semantics preserved through the canonical `sext`. -/
theorem signWert_rundgang (v : Wort) (h : passtI32 v = true) :
    sext .b32 (BitVec.ofNat 64 (BitVec.ofNat 32 v.toNat).toNat) = v := by
  have hisLt := v.isLt
  have e31 : (2 : Nat) ^ 31 = 2147483648 := rfl
  have e32 : (2 : Nat) ^ 32 = 4294967296 := rfl
  have e64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  have hI : v.toNat < 2 ^ 31 ∨ 2 ^ 64 - 2 ^ 31 ≤ v.toNat :=
    of_decide_eq_true (by simpa [passtI32] using h)
  have h32 : (BitVec.ofNat 32 v.toNat).toNat = v.toNat % 2 ^ 32 :=
    BitVec.toNat_ofNat _ _
  have hlo : (trunc .b32
      (BitVec.ofNat 64 (BitVec.ofNat 32 v.toNat).toNat)).toNat
      = v.toNat % 2 ^ 32 := by
    have hb : Breite.bits .b32 = 32 := rfl
    rw [narrowTruncMod, hb, h32, BitVec.toNat_ofNat]
    have hlt64 : v.toNat % 2 ^ 32 < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt hlt64, Nat.mod_mod]
  have hmod32 : v.toNat % 2 ^ 32 < 2 ^ 32 :=
    Nat.mod_lt _ (by decide)
  have hbit : (v.toNat % 2 ^ 32).testBit 31
      = decide (2147483648 ≤ v.toNat % 2 ^ 32) :=
    movSelBit31 _ hmod32
  simp only [sext, hlo, hbit, show signBit .b32 = 31 from rfl,
    show Breite.bits .b32 = 32 from rfl]
  by_cases hge : 2147483648 ≤ v.toNat % 2 ^ 32
  · rw [if_pos (decide_eq_true hge)]
    have hB : 2 ^ 64 - 2 ^ 31 ≤ v.toNat := by
      rcases hI with hA | hB
      · have hm : v.toNat % 2 ^ 32 = v.toNat :=
          Nat.mod_eq_of_lt (by omega)
        omega
      · exact hB
    have hk1 : 0 < 2 ^ 64 - v.toNat := by omega
    have hk2 : 2 ^ 64 - v.toNat < 2 ^ 32 := by omega
    have hm := movSelMod64_32 (2 ^ 64 - v.toNat) hk1 hk2
    have e : 2 ^ 64 - (2 ^ 64 - v.toNat) = v.toNat := by omega
    rw [e] at hm
    have hsum : v.toNat % 2 ^ 32 + (2 ^ 64 - 2 ^ 32) = v.toNat := by
      omega
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, hsum]
    exact Nat.mod_eq_of_lt hisLt
  · have hnge : ¬ 2147483648 ≤ v.toNat % 2 ^ 32 := hge
    rw [if_neg (fun hh => hnge (of_decide_eq_true hh))]
    have hA : v.toNat < 2 ^ 31 := by
      rcases hI with hA | hB
      · exact hA
      · have hk1 : 0 < 2 ^ 64 - v.toNat := by omega
        have hk2 : 2 ^ 64 - v.toNat < 2 ^ 32 := by omega
        have hm0 := movSelMod64_32 (2 ^ 64 - v.toNat) hk1 hk2
        have e : 2 ^ 64 - (2 ^ 64 - v.toNat) = v.toNat := by omega
        rw [e] at hm0
        have hk3 : 2 ^ 64 - v.toNat ≤ 2 ^ 31 := by omega
        have hcontra : 2147483648 ≤ v.toNat % 2 ^ 32 := by omega
        exact absurd hcontra hnge
    have hm : v.toNat % 2 ^ 32 = v.toNat :=
      Nat.mod_eq_of_lt (by omega)
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, hm]
    exact Nat.mod_eq_of_lt (by omega)

/-- The selected tile always denotes exactly the word: value
    preservation over arbitrary values. -/
theorem waehle_wert (v : Wort) (c : MovImmCert) :
    tileWert (waehleMovImm v c) = v := by
  by_cases hz : nullZulassen v c = true
  · rw [waehle_null v c hz]
    have hp : passtU32 v = true := by
      simp only [nullZulassen, Bool.and_eq_true] at hz
      exact hz.2
    exact kompaktWert_rundgang v hp
  · by_cases hs : passtI32 v = true
    · have e : waehleMovImm v c = .sign (BitVec.ofNat 32 v.toNat) := by
        simp [waehleMovImm, hz, hs]
      rw [e]
      exact signWert_rundgang v hs
    · have e : waehleMovImm v c = .weit v := by
        simp [waehleMovImm, hz, hs]
      rw [e]
      rfl

end Gabbro.Grammatik.X86
