/-
  File:      Grammatik/X86/Gleitprofil.lean
  Subject:   Width-aware IEEE target FP profile over the kernel-computable model.

  Lane 286: MXCSR control-state checks (RNE, FTZ/DAZ off, masks set),
  per-context FP state, bit-pattern projection/injection for binary32/64,
  width-specific arithmetic over `Gleitkomma`, the f32-vs-f64 counterexample,
  explicit NaN/sticky/SSE gaps, and float round-trips through `X86.Speicher`.
  No `Ty.fl`/Spec change; no hardware correspondence is claimed here.
-/
import Grammatik.Gleitkomma
import Grammatik.GleitkommaBits
import Grammatik.Typen
import Grammatik.X86.Speicher

namespace Gabbro.Grammatik.X86

/-- Target FP control word: the 32-bit MXCSR. -/
abbrev MXCSR := BitVec 32

/-- One MXCSR bit as `Bool` (computable, `decide`-friendly). -/
def mxcsrBit (m : MXCSR) (i : Nat) : Bool := m.toNat.testBit i

/-- Rounding control is round-to-nearest-even (RC bits 13, 14 clear). -/
def mxcsrRundungRNE (m : MXCSR) : Bool :=
  !mxcsrBit m 13 && !mxcsrBit m 14

/-- All six exception masks set (bits 7-12): invalid, denormal, zero,
    overflow, underflow, precision. -/
def mxcsrMaskenAlle (m : MXCSR) : Bool :=
  mxcsrBit m 7 && mxcsrBit m 8 && mxcsrBit m 9 &&
    mxcsrBit m 10 && mxcsrBit m 11 && mxcsrBit m 12

/-- The target profile: RNE, FTZ (bit 15) off, DAZ (bit 6) off,
    all exception masks set. Sticky flags (bits 0-5) are NOT checked. -/
def mxcsrGueltig (m : MXCSR) : Bool :=
  mxcsrRundungRNE m && !mxcsrBit m 15 && !mxcsrBit m 6 && mxcsrMaskenAlle m

/-- The architectural reset value `0x1F80` meets the profile. -/
theorem mxcsr_standard : mxcsrGueltig 0x1F80 = true := by decide

/-- Flush-to-zero set (`0x9F80`) is refused. -/
theorem mxcsr_ftz_verweigert : mxcsrGueltig 0x9F80 = false := by decide

/-- Denormals-are-zero set (`0x1FC0`) is refused. -/
theorem mxcsr_daz_verweigert : mxcsrGueltig 0x1FC0 = false := by decide

/-- Round-down (`0x3F80`, RC = 01) is refused. -/
theorem mxcsr_runde_unten_verweigert : mxcsrGueltig 0x3F80 = false := by decide

/-- A cleared precision mask (`0x0F80`, PM clear) is refused. -/
theorem mxcsr_maske_verweigert : mxcsrGueltig 0x0F80 = false := by decide

/-! ## 1. Per-context control state (never process-global).

  Each execution context carries its own MXCSR. Saving and restoring the
  word across a context switch is ordinary software copying it out and
  back in -- user logic, modelled here as pure data movement. -/

/-- Per-context FP state: the context OWNS its MXCSR. -/
structure FPKontext where
  mxcsr : MXCSR
  deriving DecidableEq, Repr

/-- Reset context: the architectural reset value. -/
def kontextReset : FPKontext := ⟨0x1F80⟩

/-- Software save: read the word out (user logic). -/
def sichere (k : FPKontext) : MXCSR := k.mxcsr

/-- Software restore: install a saved word (user logic). -/
def stelleHer (w : MXCSR) : FPKontext := ⟨w⟩

/-- Save after restore is the saved word. -/
theorem sichere_stelleHer (w : MXCSR) : sichere (stelleHer w) = w := rfl

/-- Restore after save is the context. -/
theorem stelleHer_sichere (k : FPKontext) : stelleHer (sichere k) = k := by
  cases k
  rfl

/-- The reset context meets the profile. -/
theorem kontextReset_gueltig : mxcsrGueltig kontextReset.mxcsr = true := by decide

/-- Validity is per-context, not global: a valid and a refused word
    coexist as two contexts. -/
theorem kontext_nicht_global : ∃ k1 k2 : FPKontext,
    mxcsrGueltig k1.mxcsr = true ∧ mxcsrGueltig k2.mxcsr = false :=
  ⟨kontextReset, ⟨0x9F80⟩, by decide, by decide⟩

/-! ## 2. Sticky flags are an explicit gap.

  Bits 0-5 (IE, DE, ZE, OE, UE, PE) record sticky exceptions. The profile
  check does NOT read them: a word with every sticky flag set classifies
  exactly like the same word with none set. Sticky-flag semantics
  (accumulation, clearing, reads) is unmodelled -- see CUTS. -/

/-- Sticky flags set do not make a valid word invalid. -/
theorem mxcsr_sticky_egal_gueltig :
    mxcsrGueltig 0x1FBF = true ∧ mxcsrGueltig 0x1F80 = true := by decide

/-- Sticky flags set do not make a refused word valid. -/
theorem mxcsr_sticky_egal_verweigert :
    mxcsrGueltig 0x9FBF = false ∧ mxcsrGueltig 0x9F80 = false := by decide

/-! ## 3. Bit-pattern projection/injection for binary32/64.

  Patterns travel as target words (`BitVec 32` for binary32, the
  canonical `Wort` = `BitVec 64` for binary64); values are the
  kernel-computable `GBits` triples of `Gleitkomma.lean` -- no opaque
  Lean `Float` anywhere. -/

/-- binary32 occupies exactly 32 bits. -/
theorem f32_breite32 : Gleitkomma.f32.ebits + Gleitkomma.f32.fracBits + 1 = 32 := by
  decide

/-- binary64 occupies exactly 64 bits. -/
theorem f64_breite64 : Gleitkomma.f64.ebits + Gleitkomma.f64.fracBits + 1 = 64 := by
  decide

/-- Project a binary32 value to its target word. -/
def muster32 (g : Gleitkomma.GBits Gleitkomma.f32) : BitVec 32 :=
  BitVec.ofNat 32 (Gleitkomma.zuBits Gleitkomma.f32 g)

/-- Inject a target word as a binary32 value. -/
def bites32 (w : BitVec 32) : Gleitkomma.GBits Gleitkomma.f32 :=
  Gleitkomma.ausBits Gleitkomma.f32 w.toNat

/-- Project a binary64 value to its target word. -/
def muster64 (g : Gleitkomma.GBits Gleitkomma.f64) : Wort :=
  BitVec.ofNat 64 (Gleitkomma.zuBits Gleitkomma.f64 g)

/-- Inject a target word as a binary64 value. -/
def bites64 (w : Wort) : Gleitkomma.GBits Gleitkomma.f64 :=
  Gleitkomma.ausBits Gleitkomma.f64 w.toNat

/-- Injection always lands well-formed (field widths fit by construction),
    for every dense format -- hence binary32 and binary64. -/
theorem ausBits_wf (F : Gleitkomma.Format) (hF : F.dicht) (n : Nat) :
    Gleitkomma.wf F (Gleitkomma.ausBits F n) := by
  unfold Gleitkomma.ausBits Gleitkomma.wf
  dsimp only
  refine ⟨?_, Nat.mod_lt _ (Nat.pow_pos (by decide))⟩
  have hE : (n / 2 ^ F.fracBits) % 2 ^ F.ebits < 2 ^ F.ebits :=
    Nat.mod_lt _ (Nat.pow_pos (by decide))
  unfold Gleitkomma.Format.dicht at hF
  omega

/-- Injecting a projected binary32 value gives it back (well-formed inputs). -/
theorem bites32_muster32 (g : Gleitkomma.GBits Gleitkomma.f32)
    (hw : Gleitkomma.wf Gleitkomma.f32 g) :
    bites32 (muster32 g) = g := by
  unfold bites32 muster32
  have hlt := Gleitkomma.zuBits_lt Gleitkomma.f32 Gleitkomma.f32_dicht g hw
  rw [f32_breite32] at hlt
  have hton : (BitVec.ofNat 32 (Gleitkomma.zuBits Gleitkomma.f32 g)).toNat =
      Gleitkomma.zuBits Gleitkomma.f32 g := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  rw [hton]
  exact Gleitkomma.ausBits_zuBits Gleitkomma.f32 Gleitkomma.f32_dicht g hw

/-- Injecting a projected binary64 value gives it back (well-formed inputs). -/
theorem bites64_muster64 (g : Gleitkomma.GBits Gleitkomma.f64)
    (hw : Gleitkomma.wf Gleitkomma.f64 g) :
    bites64 (muster64 g) = g := by
  unfold bites64 muster64
  have hlt := Gleitkomma.zuBits_lt Gleitkomma.f64 Gleitkomma.f64_dicht g hw
  rw [f64_breite64] at hlt
  have hton : (BitVec.ofNat 64 (Gleitkomma.zuBits Gleitkomma.f64 g)).toNat =
      Gleitkomma.zuBits Gleitkomma.f64 g := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  rw [hton]
  exact Gleitkomma.ausBits_zuBits Gleitkomma.f64 Gleitkomma.f64_dicht g hw

/-- Projecting an injected binary32 pattern gives it back, for every
    pattern that fits 32 bits (no well-formedness premise needed:
    injected fields fit by construction). -/
theorem zuBits_ausBits32 (n : Nat) (hlt : n < 2 ^ (8 + 23 + 1)) :
    Gleitkomma.zuBits Gleitkomma.f32 (Gleitkomma.ausBits Gleitkomma.f32 n)
      = n := by
  have hq2 : n / 2 ^ (8 + 23) < 2 := by
    have hE1 : (2 : Nat) ^ (8 + 23 + 1) = 2 * 2 ^ (8 + 23) := by decide
    rw [hE1] at hlt
    exact Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide)) |>.mpr hlt
  have hER : Gleitkomma.f32.ebits + Gleitkomma.f32.fracBits = 8 + 23 := by
    rw [show Gleitkomma.f32.ebits = 8 from by decide,
      show Gleitkomma.f32.fracBits = 23 from rfl]
  have hR : Gleitkomma.f32.fracBits = 23 := rfl
  have hE : Gleitkomma.f32.ebits = 8 := by decide
  unfold Gleitkomma.ausBits Gleitkomma.zuBits
  rw [hER, hR, hE]
  dsimp only
  rcases Nat.eq_zero_or_pos (n / 2 ^ (8 + 23)) with h0 | hpos
  · rw [h0, show (if ((0 : Nat) % 2 == 1) then (2 : Nat) ^ (8 + 23) else 0) = 0
      from rfl]
    simp only [Nat.zero_add]
    omega
  · have h1 : n / 2 ^ (8 + 23) = 1 := by omega
    rw [h1, show (if ((1 : Nat) % 2 == 1) then (2 : Nat) ^ (8 + 23) else 0)
        = 2 ^ (8 + 23) from rfl]
    omega

/-- Projecting an injected binary64 pattern gives it back, for every
    pattern that fits 64 bits. -/
theorem zuBits_ausBits64 (n : Nat) (hlt : n < 2 ^ (11 + 52 + 1)) :
    Gleitkomma.zuBits Gleitkomma.f64 (Gleitkomma.ausBits Gleitkomma.f64 n)
      = n := by
  have hq2 : n / 2 ^ (11 + 52) < 2 := by
    have hE1 : (2 : Nat) ^ (11 + 52 + 1) = 2 * 2 ^ (11 + 52) := by decide
    rw [hE1] at hlt
    exact Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide)) |>.mpr hlt
  have hER : Gleitkomma.f64.ebits + Gleitkomma.f64.fracBits = 11 + 52 := by
    rw [show Gleitkomma.f64.ebits = 11 from by decide,
      show Gleitkomma.f64.fracBits = 52 from rfl]
  have hR : Gleitkomma.f64.fracBits = 52 := rfl
  have hE : Gleitkomma.f64.ebits = 11 := by decide
  unfold Gleitkomma.ausBits Gleitkomma.zuBits
  rw [hER, hR, hE]
  dsimp only
  rcases Nat.eq_zero_or_pos (n / 2 ^ (11 + 52)) with h0 | hpos
  · rw [h0, show (if ((0 : Nat) % 2 == 1) then (2 : Nat) ^ (11 + 52) else 0) = 0
      from rfl]
    simp only [Nat.zero_add]
    omega
  · have h1 : n / 2 ^ (11 + 52) = 1 := by omega
    rw [h1, show (if ((1 : Nat) % 2 == 1) then (2 : Nat) ^ (11 + 52) else 0)
        = 2 ^ (11 + 52) from rfl]
    omega

/-- Projecting an injected binary32 word gives the word back. -/
theorem muster32_bites32 (w : BitVec 32) :
    muster32 (bites32 w) = w := by
  apply BitVec.eq_of_toNat_eq
  unfold muster32 bites32
  rw [BitVec.toNat_ofNat]
  have hlt : w.toNat < 2 ^ (8 + 23 + 1) := by
    have h := w.isLt
    omega
  rw [zuBits_ausBits32 w.toNat hlt, Nat.mod_eq_of_lt w.isLt]

/-- Projecting an injected binary64 word gives the word back. -/
theorem muster64_bites64 (w : Wort) :
    muster64 (bites64 w) = w := by
  apply BitVec.eq_of_toNat_eq
  unfold muster64 bites64
  rw [BitVec.toNat_ofNat]
  have hlt : w.toNat < 2 ^ (11 + 52 + 1) := by
    have h := w.isLt
    omega
  rw [zuBits_ausBits64 w.toNat hlt, Nat.mod_eq_of_lt w.isLt]

/-! ## 4. Width-specific arithmetic over the IEEE model.

  Each operator is the existing kernel-computable model (`Gleitkomma.lean`)
  at the named width -- "exact result, then round-to-nearest-even" with
  the IEEE special cases. Wrapping `Gleitkomma.add` states the Annex F
  prescription, NOT hardware correspondence (see §7 and CUTS). -/

/-- binary32 addition. -/
def fadd32 (a b : Gleitkomma.GBits Gleitkomma.f32) :
    Gleitkomma.GBits Gleitkomma.f32 :=
  Gleitkomma.add Gleitkomma.f32 a b

/-- binary32 subtraction. -/
def fsub32 (a b : Gleitkomma.GBits Gleitkomma.f32) :
    Gleitkomma.GBits Gleitkomma.f32 :=
  Gleitkomma.sub Gleitkomma.f32 a b

/-- binary32 multiplication. -/
def fmul32 (a b : Gleitkomma.GBits Gleitkomma.f32) :
    Gleitkomma.GBits Gleitkomma.f32 :=
  Gleitkomma.mul Gleitkomma.f32 a b

/-- binary32 division. -/
def fdiv32 (a b : Gleitkomma.GBits Gleitkomma.f32) :
    Gleitkomma.GBits Gleitkomma.f32 :=
  Gleitkomma.div Gleitkomma.f32 a b

/-- binary64 addition. -/
def fadd64 (a b : Gleitkomma.GBits Gleitkomma.f64) :
    Gleitkomma.GBits Gleitkomma.f64 :=
  Gleitkomma.add Gleitkomma.f64 a b

/-- binary64 subtraction. -/
def fsub64 (a b : Gleitkomma.GBits Gleitkomma.f64) :
    Gleitkomma.GBits Gleitkomma.f64 :=
  Gleitkomma.sub Gleitkomma.f64 a b

/-- binary64 multiplication. -/
def fmul64 (a b : Gleitkomma.GBits Gleitkomma.f64) :
    Gleitkomma.GBits Gleitkomma.f64 :=
  Gleitkomma.mul Gleitkomma.f64 a b

/-- binary64 division. -/
def fdiv64 (a b : Gleitkomma.GBits Gleitkomma.f64) :
    Gleitkomma.GBits Gleitkomma.f64 :=
  Gleitkomma.div Gleitkomma.f64 a b

/-- Width arithmetic stays well-formed (binary32, all four ops). -/
theorem fadd32_wf (a b : Gleitkomma.GBits Gleitkomma.f32)
    (ha : Gleitkomma.wf Gleitkomma.f32 a)
    (hb : Gleitkomma.wf Gleitkomma.f32 b) :
    Gleitkomma.wf Gleitkomma.f32 (fadd32 a b) :=
  Gleitkomma.add_wf Gleitkomma.f32 Gleitkomma.f32_p a b ha hb

theorem fsub32_wf (a b : Gleitkomma.GBits Gleitkomma.f32)
    (ha : Gleitkomma.wf Gleitkomma.f32 a)
    (hb : Gleitkomma.wf Gleitkomma.f32 b) :
    Gleitkomma.wf Gleitkomma.f32 (fsub32 a b) :=
  Gleitkomma.sub_wf Gleitkomma.f32 Gleitkomma.f32_p a b ha hb

theorem fmul32_wf (a b : Gleitkomma.GBits Gleitkomma.f32)
    (ha : Gleitkomma.wf Gleitkomma.f32 a)
    (hb : Gleitkomma.wf Gleitkomma.f32 b) :
    Gleitkomma.wf Gleitkomma.f32 (fmul32 a b) :=
  Gleitkomma.mul_wf Gleitkomma.f32 Gleitkomma.f32_p a b ha hb

theorem fdiv32_wf (a b : Gleitkomma.GBits Gleitkomma.f32)
    (ha : Gleitkomma.wf Gleitkomma.f32 a)
    (hb : Gleitkomma.wf Gleitkomma.f32 b) :
    Gleitkomma.wf Gleitkomma.f32 (fdiv32 a b) :=
  Gleitkomma.div_wf Gleitkomma.f32 Gleitkomma.f32_p a b ha hb

/-- Width arithmetic stays well-formed (binary64, all four ops). -/
theorem fadd64_wf (a b : Gleitkomma.GBits Gleitkomma.f64)
    (ha : Gleitkomma.wf Gleitkomma.f64 a)
    (hb : Gleitkomma.wf Gleitkomma.f64 b) :
    Gleitkomma.wf Gleitkomma.f64 (fadd64 a b) :=
  Gleitkomma.add_wf Gleitkomma.f64 Gleitkomma.f64_p a b ha hb

theorem fsub64_wf (a b : Gleitkomma.GBits Gleitkomma.f64)
    (ha : Gleitkomma.wf Gleitkomma.f64 a)
    (hb : Gleitkomma.wf Gleitkomma.f64 b) :
    Gleitkomma.wf Gleitkomma.f64 (fsub64 a b) :=
  Gleitkomma.sub_wf Gleitkomma.f64 Gleitkomma.f64_p a b ha hb

theorem fmul64_wf (a b : Gleitkomma.GBits Gleitkomma.f64)
    (ha : Gleitkomma.wf Gleitkomma.f64 a)
    (hb : Gleitkomma.wf Gleitkomma.f64 b) :
    Gleitkomma.wf Gleitkomma.f64 (fmul64 a b) :=
  Gleitkomma.mul_wf Gleitkomma.f64 Gleitkomma.f64_p a b ha hb

theorem fdiv64_wf (a b : Gleitkomma.GBits Gleitkomma.f64)
    (ha : Gleitkomma.wf Gleitkomma.f64 a)
    (hb : Gleitkomma.wf Gleitkomma.f64 b) :
    Gleitkomma.wf Gleitkomma.f64 (fdiv64 a b) :=
  Gleitkomma.div_wf Gleitkomma.f64 Gleitkomma.f64_p a b ha hb

/-! ## 5. Signed zeros and subnormals survive both widths.

  Concrete kernel computations (`decide`, small triples -- no `2^1074`
  scale): the signed-zero rule of IEEE 754-2019 §6.3 and exact subnormal
  addition, plus the distinct bit patterns of `-0`/`+0` through projection. -/

/-- `-0 + -0 = -0` in binary32. -/
theorem fadd32_nullN : fadd32 (Gleitkomma.nullN Gleitkomma.f32)
    (Gleitkomma.nullN Gleitkomma.f32)
    = Gleitkomma.nullN Gleitkomma.f32 := by decide

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 2048 in
/-- Min-subnormal plus min-subnormal is the next subnormal (binary32). -/
theorem fadd32_subnormal :
    fadd32 ⟨false, 0, 1⟩ ⟨false, 0, 1⟩
      = (⟨false, 0, 2⟩ : Gleitkomma.GBits Gleitkomma.f32) := by decide

set_option maxRecDepth 100000 in
/-- `-0 + -0 = -0` in binary64. -/
theorem fadd64_nullN : fadd64 (Gleitkomma.nullN Gleitkomma.f64)
    (Gleitkomma.nullN Gleitkomma.f64)
    = Gleitkomma.nullN Gleitkomma.f64 := by decide

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 2048 in
/-- Min-subnormal plus min-subnormal is the next subnormal (binary64). -/
theorem fadd64_subnormal :
    fadd64 ⟨false, 0, 1⟩ ⟨false, 0, 1⟩
      = (⟨false, 0, 2⟩ : Gleitkomma.GBits Gleitkomma.f64) := by decide

/-- `-0` projects to `0x80000000`, `+0` to `0x00000000` (binary32). -/
theorem muster32_null : muster32 (Gleitkomma.nullN Gleitkomma.f32) = 0x80000000
    ∧ muster32 (Gleitkomma.nullP Gleitkomma.f32) = 0 := by decide

/-- `-0` projects to `0x8000000000000000`, `+0` to zero (binary64). -/
theorem muster64_null : muster64 (Gleitkomma.nullN Gleitkomma.f64)
      = 0x8000000000000000
    ∧ muster64 (Gleitkomma.nullP Gleitkomma.f64) = 0 := by decide

/-! ## 6. Treating genuine binary32 arithmetic as binary64 is observably wrong.

  `Ty.fl` carries no width and the source model computes every float in
  binary64 (the named cut of GLEITKOMMA.md §7). Genuine binary32 hardware
  rounds to 24 significand bits. The two disagree on VALUES, not merely on
  encoding width: `2^24 + 1` is exactly representable in binary64 and
  rounds to `2^24` (tie to even) in binary32. A silent widening changes
  the computed value. -/

/-- binary32 rounds `2^24 + 1` onto `2^24` (tie to even). -/
theorem f32_rundet_16777217 :
    Gleitkomma.ofInt Gleitkomma.f32 16777217
      = Gleitkomma.ofInt Gleitkomma.f32 16777216 := by decide

/-- binary64 keeps `2^24 + 1` apart from `2^24`. -/
theorem f64_trennt_16777217 :
    Gleitkomma.ofInt Gleitkomma.f64 16777217
      ≠ Gleitkomma.ofInt Gleitkomma.f64 16777216 := by decide

/-- The exact values differ: binary32 sees `2^23 * 2^1 = 2^24`,
    binary64 sees `(2^52 + 2^28) * 2^-28 = 2^24 + 1`. -/
theorem gegenbeispiel_werte :
    Gleitkomma.wertExakt Gleitkomma.f32
          (Gleitkomma.ofInt Gleitkomma.f32 16777217)
        = some ⟨8388608, 1⟩
      ∧ Gleitkomma.wertExakt Gleitkomma.f64
          (Gleitkomma.ofInt Gleitkomma.f64 16777217)
        = some ⟨4503599895805952, -28⟩ :=
  ⟨by decide, by decide⟩

/-- The bit patterns tell the same story: binary32 conflates the two
    integers, binary64 distinguishes them. -/
theorem gegenbeispiel_muster :
    Gleitkomma.zuBits Gleitkomma.f32
          (Gleitkomma.ofInt Gleitkomma.f32 16777217)
        = Gleitkomma.zuBits Gleitkomma.f32
          (Gleitkomma.ofInt Gleitkomma.f32 16777216)
      ∧ Gleitkomma.zuBits Gleitkomma.f64
          (Gleitkomma.ofInt Gleitkomma.f64 16777217)
        ≠ Gleitkomma.zuBits Gleitkomma.f64
          (Gleitkomma.ofInt Gleitkomma.f64 16777216) :=
  ⟨by decide, by decide⟩

/-- Source-type-aware reading: the current source model (`Ty.fl`,
    binary64) computes the TRUE integer `2^24 + 1`, while genuine
    binary32 computes `2^24` -- so the model value of an `f32` program
    at this point is not the target value. -/
theorem quelle_gegen_f32 :
    Gleitkomma.wertExakt Gleitkomma.f64
          (Gabbro.Grammatik.gleitAusInt 16777217)
        = some ⟨4503599895805952, -28⟩
      ∧ Gleitkomma.wertExakt Gleitkomma.f32
          (Gleitkomma.ofInt Gleitkomma.f32 16777217)
        = some ⟨8388608, 1⟩ :=
  ⟨by decide, by decide⟩

/-! ## 7. Explicit gaps: NaN payloads and the SSE correspondence.

  NaN quiet-bit/payload discipline is UNMODELLED here: classification
  (`.nan`) is claimed, payload equality never is. Likewise the step from
  "the model prescribes Annex F" to "executed SSE bytes compute it" has a
  name below and NO proof -- wrapping `Gleitkomma.add` states the
  prescription, not the meeting. -/

/-- Two distinct NaN payloads both classify as NaN, and differ:
    classification pins no payload (binary32). -/
theorem nan_nutzlast_offen32 :
    Gleitkomma.klasse Gleitkomma.f32 ⟨false, Gleitkomma.f32.bexpMax, 1⟩
        = .nan
      ∧ Gleitkomma.klasse Gleitkomma.f32 ⟨false, Gleitkomma.f32.bexpMax, 2⟩
        = .nan
      ∧ (⟨false, Gleitkomma.f32.bexpMax, 1⟩ :
          Gleitkomma.GBits Gleitkomma.f32)
        ≠ ⟨false, Gleitkomma.f32.bexpMax, 2⟩ := by decide

/-- A computed NaN is classified, never given a payload: `0 / 0` is NaN. -/
theorem nan_klasse_berechnet32 :
    Gleitkomma.klasse Gleitkomma.f32
        (fdiv32 ⟨false, 0, 0⟩ ⟨false, 0, 0⟩) = .nan := by decide

/-- OPEN correspondence claim (NOT proved here; no theorem concludes it):
    executed SSE bytes computing `fadd32` on the bit patterns. The name
    marks the gap; the model side alone is proved. -/
def SSEAdd32Entspricht (ausfuehrung : BitVec 32 → BitVec 32 → BitVec 32) :
    Prop :=
  ∀ a b, ausfuehrung a b = muster32 (fadd32 (bites32 a) (bites32 b))

/-! ## 8. Float patterns through canonical memory.

  Patterns are stored with the REAL `X86.Speicher` operations: a
  four-byte write/read round-trip for binary32, an eight-byte one for
  binary64. Both witnesses are nonzero and observably change memory, and
  the stored patterns are the model values' bits. -/

/-- The `0.1f32` pattern is the model value's bits. -/
theorem zehntel32_modell : Gleitkomma.zuBits Gleitkomma.f32
    (Gleitkomma.ofRat Gleitkomma.f32 1 10) = 0x3DCCCCCD :=
  Gleitkomma.zeuge_zehntel32

/-- The memory after the four-byte `0.1f32` write at address zero. -/
def flSpeicherNach32 : Speicher :=
  { zeugenSpeicher with bytes := writeBytesN zeugenSpeicher 0 (BitVec.ofNat 64 0x3DCCCCCD) 4 }

/-- A nonzero binary32 pattern is written, reads back, and observably
    changes memory. -/
theorem speicher32_rundlauf :
    ∃ (m m' : Speicher) (a : Adresse),
      (BitVec.ofNat 64 0x3DCCCCCD : Wort) ≠ 0
        ∧ write32 m a (BitVec.ofNat 64 0x3DCCCCCD) = some m'
        ∧ read32 m' a = some (BitVec.ofNat 64 0x3DCCCCCD)
        ∧ m.bytes a ≠ m'.bytes a := by
  refine ⟨zeugenSpeicher, flSpeicherNach32, 0, by decide, ?_, ?_, ?_⟩
  · unfold write32
    have hc : schreibbarN zeugenSpeicher 0 4 = true := rfl
    rw [if_pos hc]
    rfl
  · have hwr : write32 zeugenSpeicher 0 (BitVec.ofNat 64 0x3DCCCCCD)
        = some flSpeicherNach32 := by
      unfold write32
      have hc : schreibbarN zeugenSpeicher 0 4 = true := rfl
      rw [if_pos hc]
      rfl
    have hrd : lesbarN zeugenSpeicher 0 4 = true := rfl
    have hrb := read32_nach_write32 zeugenSpeicher flSpeicherNach32 0
      (BitVec.ofNat 64 0x3DCCCCCD) hwr hrd
    have hv : ((BitVec.ofNat 64 0x3DCCCCCD : Wort).toNat % 4294967296)
        = 0x3DCCCCCD := by decide
    rw [hv] at hrb
    exact hrb
  · have hhit := writeBytesN_hit zeugenSpeicher 0
      (BitVec.ofNat 64 0x3DCCCCCD) 4 0 (by decide) (by decide)
    rw [addrOff_null (0 : Adresse)] at hhit
    show (zeugenSpeicher.bytes 0)
      ≠ (writeBytesN zeugenSpeicher 0 (BitVec.ofNat 64 0x3DCCCCCD) 4 0)
    rw [hhit]
    decide

/-- The `0.1f64` pattern is the model value's bits. -/
theorem zehntel64_modell : Gleitkomma.zuBits Gleitkomma.f64
    (Gleitkomma.ofRat Gleitkomma.f64 1 10) = 0x3FB999999999999A :=
  Gleitkomma.zeuge_zehntel64

/-- The memory after the eight-byte `0.1f64` write at address zero. -/
def flSpeicherNach64 : Speicher :=
  { zeugenSpeicher with bytes := writeBytes zeugenSpeicher 0 (BitVec.ofNat 64 0x3FB999999999999A) }

/-- A nonzero binary64 pattern is written, reads back, and observably
    changes memory. -/
theorem speicher64_rundlauf :
    ∃ (m m' : Speicher) (a : Adresse),
      (BitVec.ofNat 64 0x3FB999999999999A : Wort) ≠ 0
        ∧ write64 m a (BitVec.ofNat 64 0x3FB999999999999A) = some m'
        ∧ read64 m' a = some (BitVec.ofNat 64 0x3FB999999999999A)
        ∧ m.bytes a ≠ m'.bytes a := by
  refine ⟨zeugenSpeicher, flSpeicherNach64, 0, by decide, ?_, ?_, ?_⟩
  · unfold write64
    have hc : schreibbar8 zeugenSpeicher 0 = true := rfl
    rw [if_pos hc]
    rfl
  · have hwr : write64 zeugenSpeicher 0 (BitVec.ofNat 64 0x3FB999999999999A)
        = some flSpeicherNach64 := by
      unfold write64
      have hc : schreibbar8 zeugenSpeicher 0 = true := rfl
      rw [if_pos hc]
      rfl
    have hrd : lesbar8 zeugenSpeicher 0 = true := rfl
    exact read64_nach_write64 zeugenSpeicher flSpeicherNach64 0
      (BitVec.ofNat 64 0x3FB999999999999A) hwr hrd
  · have hhit := writeBytesN_hit zeugenSpeicher 0
      (BitVec.ofNat 64 0x3FB999999999999A) 8 0 (by decide) (by decide)
    rw [addrOff_null (0 : Adresse)] at hhit
    show (zeugenSpeicher.bytes 0)
      ≠ (writeBytesN zeugenSpeicher 0
        (BitVec.ofNat 64 0x3FB999999999999A) 8 0)
    rw [hhit]
    decide

/- CUTS: what is not proved here.

   - No `Ty.fl`/Spec change: the source model still computes every float
     in binary64 (the named cut of GLEITKOMMA.md §7). The reviewed
     width-extension work this profile prepares, none of it done here:
     a width in `Syntax.lean` `Ty.fl`, a width dispatch in
     `Semantik.lean` `gleitRechne`/`bruch`/`gleitAusInt`/`gleitWortPasst`,
     per-width `Typen.lean` values, and the binary32 correspondence rows
     of `CFormenF.lean` (whose uncovered `stmt:float` row names exactly
     this). `quelle_gegen_f32` is the measured reason the extension is
     needed, not the extension.
   - `SSEAdd32Entspricht` is NAMED and unproved: no theorem here concludes
     anything about executed SSE bytes. Wrapping `Gleitkomma.add` states
     the Annex F prescription the target is assumed to meet, not the
     meeting. Likewise the MXCSR bit positions (RC 13-14, FTZ 15,
     DAZ 6, masks 7-12, sticky 0-5) are stated from the Intel layout, not
     verified against hardware, and no probe here checks hardware honors
     the word.
   - Sticky exception flags (bits 0-5: IE, DE, ZE, OE, UE, PE) are
     UNMODELLED: accumulation across operations, clearing, and reads have
     no definitions. `mxcsr_sticky_egal_*` prove the profile check
     ignores them -- the gap, not a semantics.
   - NaN quiet-bit/payload discipline is UNMODELLED: only classification
     (`.nan`) is ever concluded; payload equality is never concluded
     (`nan_nutzlast_offen32` shows two payloads share the class and
     differ). Signalling NaNs trap or quieten only outside this file.
   - No concurrency claim: the memory round-trips are sequential over one
     `Speicher` (read/write/frame lemmas of `X86.Speicher`); per-access
     TSO granularity, tearing and the GX refinement stay open.
   - No decoder, encoder, instruction semantics, ABI/loader, cost transfer
     or final-image acceptance: this file is profile data, pattern
     helpers, model arithmetic and memory round-trips only.
   - `sichere`/`stelleHer` are pure data movement (user logic); no
     OS/hardware context-switch semantics is claimed.
   - x87/FPCR, other rounding modes, contraction/fast-math and `libm` are
     out of scope (see GLEITKOMMA.md §§4-5 for the assumption side).
   - The `set_option maxRecDepth/exponentiation.threshold` budgets on the
     three subnormal-range `decide`s are elaboration-only (the same two
     options the model file already carries); they change no statement.
-/

#print axioms mxcsr_standard
#print axioms mxcsr_ftz_verweigert
#print axioms mxcsr_daz_verweigert
#print axioms mxcsr_runde_unten_verweigert
#print axioms mxcsr_maske_verweigert
#print axioms sichere_stelleHer
#print axioms stelleHer_sichere
#print axioms kontextReset_gueltig
#print axioms kontext_nicht_global
#print axioms mxcsr_sticky_egal_gueltig
#print axioms mxcsr_sticky_egal_verweigert
#print axioms f32_breite32
#print axioms f64_breite64
#print axioms ausBits_wf
#print axioms bites32_muster32
#print axioms bites64_muster64
#print axioms zuBits_ausBits32
#print axioms zuBits_ausBits64
#print axioms muster32_bites32
#print axioms muster64_bites64
#print axioms fadd32_wf
#print axioms fsub32_wf
#print axioms fmul32_wf
#print axioms fdiv32_wf
#print axioms fadd64_wf
#print axioms fsub64_wf
#print axioms fmul64_wf
#print axioms fdiv64_wf
#print axioms fadd32_nullN
#print axioms fadd32_subnormal
#print axioms fadd64_nullN
#print axioms fadd64_subnormal
#print axioms muster32_null
#print axioms muster64_null
#print axioms f32_rundet_16777217
#print axioms f64_trennt_16777217
#print axioms gegenbeispiel_werte
#print axioms gegenbeispiel_muster
#print axioms quelle_gegen_f32
#print axioms nan_nutzlast_offen32
#print axioms nan_klasse_berechnet32
#print axioms zehntel32_modell
#print axioms speicher32_rundlauf
#print axioms zehntel64_modell
#print axioms speicher64_rundlauf

end Gabbro.Grammatik.X86
