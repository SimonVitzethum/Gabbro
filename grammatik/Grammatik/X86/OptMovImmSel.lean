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

/-! ## 3. Firewall: outside the gates the narrow tiles never fire.

    The precise refusal cases where the rule must NOT fire: a live
    upper half, an overflowing value, and a non-i32 value each force
    the certified wide fallback. A refused optional tile falls back,
    never warns. -/

/-- FIREWALL (upper half live): without a dead upper half the selector
    never emits the zero tile. -/
theorem waehle_kein_kompakt_ohne_tot (v : Wort) (c : MovImmCert)
    (h : c.oberTot = false) (imm : BitVec 32) :
    waehleMovImm v c ≠ .kompakt imm := by
  have hz : nullZulassen v c = false := nullVerweigert_oberLebendig v c h
  have hzn : ¬ nullZulassen v c = true := by simp [hz]
  simp only [waehleMovImm, if_neg hzn]
  by_cases hs : passtI32 v = true <;> simp_all

/-- FIREWALL (value too big): an overflowing value never takes the zero
    tile, however dead its upper half is. -/
theorem waehle_kein_kompakt_bei_gross (v : Wort) (c : MovImmCert)
    (h : passtU32 v = false) (imm : BitVec 32) :
    waehleMovImm v c ≠ .kompakt imm := by
  have hz : nullZulassen v c = false := nullVerweigert_gross v c h
  have hzn : ¬ nullZulassen v c = true := by simp [hz]
  simp only [waehleMovImm, if_neg hzn]
  by_cases hs : passtI32 v = true <;> simp_all

/-- FIREWALL (outside i32): a non-i32 value never takes the sign tile. -/
theorem waehle_kein_sign_ohne_bereich (v : Wort) (c : MovImmCert)
    (h : passtI32 v = false) (imm : BitVec 32) :
    waehleMovImm v c ≠ .sign imm := by
  have hsn : ¬ passtI32 v = true := by simp [h]
  by_cases hz : nullZulassen v c = true
  · rw [waehle_null v c hz]
    simp
  · have hzn : ¬ nullZulassen v c = true := hz
    rw [waehleMovImm, if_neg hzn, if_neg hsn]
    intro he
    cases he

/-! ## 4. Lengths: the rule only ever narrows.

    Wide is 10 bytes (pilot row), compact 5/6 (accepted row), sign 7
    (DESIGN 2B row data; its codec lands with lane 747). Budget side:
    `CostSummary.targetWork` counts one retired instruction either way,
    so the byte count strictly drops while the work count never grows. -/

/-- Wide length is 10 bytes for every destination and value. -/
theorem weitLaenge (dst : Register) (v : Wort) :
    (encode (.movImm64 dst v)).length = 10 := by
  cases dst <;> rfl

/-- The selected tile never exceeds the wide length. -/
theorem tileLaenge_hoechstens_weit (v : Wort) (c : MovImmCert)
    (dst : Register) : tileLaenge (waehleMovImm v c) dst ≤ 10 := by
  by_cases hz : nullZulassen v c = true
  · rw [waehle_null v c hz]
    show compactLen dst ≤ 10
    unfold compactLen
    split <;> decide
  · by_cases hs : passtI32 v = true
    · have e : waehleMovImm v c = .sign (BitVec.ofNat 32 v.toNat) := by
        simp [waehleMovImm, hz, hs]
      rw [e]
      show (7 : Nat) ≤ 10
      decide
    · have e : waehleMovImm v c = .weit v := by
        simp [waehleMovImm, hz, hs]
      rw [e]
      simp [tileLaenge]

/-! ## 5. Execution: both byte-connected tiles land the word and
    preserve every observation.

    MOV affects no flags, touches no memory, and keeps every other
    register: contracts at their place read the same values elsewhere,
    no shared access is added or removed for concurrency (no new TSO
    event; the per-access bridge stays the consumer), and any
    downstream branch -- integer or float `UCOMISD`/`Jcc` rows alike --
    observes identical flags. -/

/-- The wide tile lands the word through the canonical pilot step. -/
theorem weitSchritt_wert (dst : Register) (v : Wort) (s : Zustand) :
    (schritt ⟨.movImm64 dst v, 10⟩ s).map (fun t => t.register dst)
      = some v := by
  have h := schritt_movImm64 ⟨.movImm64 dst v, 10⟩ s dst v rfl rfl
  rw [h]
  simp [schrittRegister, regSet]

/-- The wide tile preserves the flags. -/
theorem weitSchritt_flags (dst : Register) (v : Wort) (s s' : Zustand)
    (hstep : schritt ⟨.movImm64 dst v, 10⟩ s = some s') :
    s'.flags = s.flags :=
  schritt_movImm64_flags _ s s' dst v rfl rfl hstep

/-- The wide tile changes no memory byte. -/
theorem weitSchritt_speicher (dst : Register) (v : Wort) (s s' : Zustand)
    (hstep : schritt ⟨.movImm64 dst v, 10⟩ s = some s') :
    s'.speicher = s.speicher :=
  schritt_movImm64_speicher _ s s' dst v rfl rfl hstep

/-- The wide tile keeps every other register (contract frame). -/
theorem weitSchritt_fremd (dst q : Register) (v : Wort) (s s' : Zustand)
    (hstep : schritt ⟨.movImm64 dst v, 10⟩ s = some s')
    (hq : q ≠ dst) : s'.register q = s.register q :=
  schritt_movImm64_reg _ s s' dst q v rfl rfl hstep hq

/-- An admitted site steps the compact tile to the same word. -/
theorem kompaktSchritt_wert (dst : Register) (v : Wort) (s : Zustand)
    (c : MovImmCert) (h : nullZulassen v c = true) :
    (stepCompact ⟨.mov32imm dst (BitVec.ofNat 32 v.toNat),
      compactLen dst⟩ s).map (fun t => t.register dst) = some v := by
  have hp : passtU32 v = true := by
    simp only [nullZulassen, Bool.and_eq_true] at h
    exact h.2
  have hw : compactWert (BitVec.ofNat 32 v.toNat) = v :=
    kompaktWert_rundgang v hp
  have hstep := stepCompact_mov32imm
    ⟨.mov32imm dst (BitVec.ofNat 32 v.toNat), compactLen dst⟩ s dst
    (BitVec.ofNat 32 v.toNat) (compactLen_ok dst) rfl
  have e : (stepCompact ⟨.mov32imm dst (BitVec.ofNat 32 v.toNat),
      compactLen dst⟩ s).map (fun t => t.register dst)
      = some (compactWert (BitVec.ofNat 32 v.toNat)) := by
    rw [hstep]
    simp [regSet_gleich]
  rw [e, hw]

/-- The compact tile preserves the flags. -/
theorem kompaktSchritt_flags (dst : Register) (v : Wort) (s s' : Zustand)
    (hstep : stepCompact ⟨.mov32imm dst (BitVec.ofNat 32 v.toNat),
      compactLen dst⟩ s = some s') : s'.flags = s.flags :=
  stepCompact_flags _ s s' dst _ (compactLen_ok dst) rfl hstep

/-- The compact tile changes no memory byte. -/
theorem kompaktSchritt_speicher (dst : Register) (v : Wort) (s s' : Zustand)
    (hstep : stepCompact ⟨.mov32imm dst (BitVec.ofNat 32 v.toNat),
      compactLen dst⟩ s = some s') : s'.speicher = s.speicher :=
  stepCompact_speicher _ s s' dst _ (compactLen_ok dst) rfl hstep

/-- The compact tile keeps every other register (contract frame). -/
theorem kompaktSchritt_fremd (dst q : Register) (v : Wort) (s s' : Zustand)
    (hstep : stepCompact ⟨.mov32imm dst (BitVec.ofNat 32 v.toNat),
      compactLen dst⟩ s = some s') (hq : q ≠ dst) :
    s'.register q = s.register q :=
  stepCompact_fremd _ s s' dst q _ (compactLen_ok dst) rfl hstep hq

/-- Every downstream branch observes identical flags from either tile:
    the wide and the compact successor agree on every `Bedingung`,
    including the float unordered rows. -/
theorem movSelBedingung_gleich (dst : Register) (v : Wort) (s : Zustand)
    (cond : Bedingung) (sW sN : Zustand)
    (hW : schritt ⟨.movImm64 dst v, 10⟩ s = some sW)
    (hN : stepCompact ⟨.mov32imm dst (BitVec.ofNat 32 v.toNat),
      compactLen dst⟩ s = some sN) :
    bedingung cond sW.flags = bedingung cond sN.flags := by
  have fW := weitSchritt_flags dst v s sW hW
  have hokN := compactLen_ok dst
  have fN := stepCompact_flags _ s sN dst (BitVec.ofNat 32 v.toNat)
    hokN rfl hN
  rw [fW, fN]

/-! ## 6. Bytes: the selected tiles decode through the accepted rows.

    No new codec: wide bytes round-trip through the pilot `Codec`,
    compact bytes through the accepted `decodeCompact`. The sign row's
    codec lands with lane 747. -/

/-- Wide bytes decode back to the wide tile, over any suffix. -/
theorem movSelBytes_weit (dst : Register) (v : Wort)
    (suffix : List Byte) :
    decode (encode (.movImm64 dst v) ++ suffix)
      = some (⟨.movImm64 dst v, (encode (.movImm64 dst v)).length⟩,
        suffix) :=
  roundtrip _ _

/-- Compact bytes decode back to the compact tile, over any suffix. -/
theorem movSelBytes_kompakt (dst : Register) (v : Wort)
    (suffix : List Byte) :
    decodeCompact
        (encodeCompact (.mov32imm dst (BitVec.ofNat 32 v.toNat)) ++ suffix)
      = some (⟨.mov32imm dst (BitVec.ofNat 32 v.toNat),
        (encodeCompact
          (.mov32imm dst (BitVec.ofNat 32 v.toNat))).length⟩, suffix) :=
  roundtripCompact _ _

/-! ## 7. Pins: the selector at concrete values. -/

/-- `5` with a dead upper half selects the zero tile. -/
theorem pin_waehle_fuenf : waehleMovImm (BitVec.ofNat 64 5) ⟨true⟩
    = .kompakt (BitVec.ofNat 32 5) := by
  decide

/-- `-1` (all ones) needs no zero tile but fits i32: sign tile. -/
theorem pin_waehle_minus_eins :
    waehleMovImm (BitVec.ofNat 64 0xFFFFFFFFFFFFFFFF) ⟨true⟩
      = .sign (BitVec.ofNat 32 0xFFFFFFFFFFFFFFFF) := by
  decide

/-- `2^32` fits neither narrow tile: the wide fallback holds even
    with a dead upper half. -/
theorem pin_waehle_gross_bleibt_weit :
    waehleMovImm (BitVec.ofNat 64 0x100000000) ⟨true⟩
      = .weit (BitVec.ofNat 64 0x100000000) := by
  decide

/-- A live upper half refuses admission even for `5`. -/
theorem pin_nullZulassen_oberLebendig :
    nullZulassen (BitVec.ofNat 64 5) ⟨false⟩ = false := by
  decide

end Gabbro.Grammatik.X86
