/-
  File:      Grammatik/X86/ScalarFloat32HardwareForms.lean
  Subject:   Essential scalar binary32 (SSE) architectural forms.

  Lane 702: legacy SSE scalar SINGLE forms (MOVSS/ADDSS/SUBSS/MULSS/DIVSS/
  UCOMISS/CVTSS2SD/CVTSD2SS/CVTSI2SS/CVTTSS2SI, register and m32 memory
  forms, REX-selected high XMM registers) through the ACCEPTED genuine
  binary32 kernel (`Gleitprofil`: `fadd32`/`fsub32`/`fmul32`/`fdiv32`,
  `muster32`/`bites32`) and raw 32-bit patterns (`read32`/`write32`).
  Binary32 source arithmetic is never silently promoted to binary64:
  the f32-vs-f64 counterexample is reused, not duplicated. No new IEEE
  interpreter is invented; NaN payloads, SNaN, DAZ/FTZ execution,
  sticky-flag accumulation and silicon correspondence stay OPEN (CUTS).

  Manual provenance (local snapshot `.tmp/HARDWARE-REFERENCES/`):
  Intel SDM combined Vols 1-4, edition 325462-093US September 2026
  (`REFERENCES.json`, sha256 `a4a62e6...f9168ee5`): Vol. 1 Chap. 5
  `INSTRUCTION SET SUMMARY` §5.5.1.1 (MOVSS), §5.5.1.2 (ADDSS/SUBSS/
  MULSS/DIVSS), §5.5.1.3 (UCOMISS), §5.5.1.6 (CVTSI2SS); Vol. 1 Chap. 10
  §10.4.1.2 (scalar single arithmetic stores the low doubleword);
  Vol. 1 Chap. 11 §11.5.2.1-§11.5.2.4 + Table 11-1 (masked SIMD FP
  exception responses). Vol. 2 opcode pages are not in the extracted
  `.txt`; byte encodings below are STATED canonical contracts mirroring
  the accepted F2 double rows (`ScalarFloatCodec`), never a silicon
  correspondence claim.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.Vektor
import Grammatik.X86.Gleitprofil
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Codec
import Grammatik.X86.Byteschritt
import Grammatik.X86.ScalarFloat
import Grammatik.X86.ScalarFloatCodec

namespace Gabbro.Grammatik.X86

/-- Lane marker: the scalar single-precision family handled here. -/
def s32Familie : Nat := 32

/-- The family marker is binary32. -/
theorem s32Familie_ist_f32 : s32Familie = 32 := rfl

/-! ## 1. The scalar single lane: low 32 bits, 96-bit preservation.

  Legacy SSE scalar single forms compute on bits 31:0 of the destination
  XMM register (`xmmTief32`); bits 127:32 are preserved by arithmetic and
  register MOVSS (`setzeTief32`), and cleared by memory MOVSS loads
  (`xmmLadeTief32`, §4). The 64-bit halves reuse `vLo`/`vHi`/`vecJoin`. -/

/-- The scalar single a register carries: the low 32 bits as data. -/
def xmmTief32 (f : XmmDatei) (r : XmmReg) : BitVec 32 :=
  BitVec.ofNat 32 (f r).toNat

/-- Scalar single write: the low 32 bits become `w`, the upper 96 bits
    of `v` are kept (legacy SSE arithmetic / register-MOVSS behaviour). -/
def setzeTief32 (v : Vektor) (w : BitVec 32) : Vektor :=
  BitVec.ofNat 128 (w.toNat + v.toNat / 2 ^ 32 * 2 ^ 32)

/-- Scalar single register write through the shared XMM file. -/
def xmmSchreibeTief32 (f : XmmDatei) (dst : XmmReg)
    (w : BitVec 32) : XmmDatei :=
  xmmSet f dst (setzeTief32 (f dst) w)

/-- Memory MOVSS load shape: the low 32 bits become `w`, the upper 96
    bits are cleared (Vol. 1 §10.4 data movement: a single from memory
    zeroes the upper doublewords). -/
def xmmLadeTief32 (f : XmmDatei) (dst : XmmReg)
    (w : BitVec 32) : XmmDatei :=
  xmmSet f dst (BitVec.ofNat 128 w.toNat)

/-- Writing then reading the low 32 bits recovers the value. -/
theorem setzeTief32_tief (v : Vektor) (w : BitVec 32) :
    BitVec.ofNat 32 (setzeTief32 v w).toNat = w := by
  have hw := w.isLt
  apply BitVec.eq_of_toNat_eq
  simp only [setzeTief32, BitVec.toNat_ofNat]
  omega

/-- The upper 96 bits survive a scalar single write. -/
theorem setzeTief32_hoch (v : Vektor) (w : BitVec 32) :
    (setzeTief32 v w).toNat / 2 ^ 32 = v.toNat / 2 ^ 32 := by
  have hw := w.isLt
  have hv := v.isLt
  have hb : w.toNat + v.toNat / 2 ^ 32 * 2 ^ 32 < 2 ^ 128 := by
    omega
  unfold setzeTief32
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
  omega

/-- The upper 64-bit half survives a scalar single write. -/
theorem setzeTief32_vHi (v : Vektor) (w : BitVec 32) :
    vHi (setzeTief32 v w) = vHi v := by
  have hw := w.isLt
  have hv := v.isLt
  apply BitVec.eq_of_toNat_eq
  simp only [setzeTief32, vHi, BitVec.toNat_ofNat]
  omega

/-- Register write answers the value at its destination. -/
theorem xmmSchreibeTief32_tief (f : XmmDatei) (dst : XmmReg)
    (w : BitVec 32) :
    xmmTief32 (xmmSchreibeTief32 f dst w) dst = w := by
  unfold xmmTief32 xmmSchreibeTief32
  rw [xmmSet_gleich]
  exact setzeTief32_tief _ _

/-- Register write keeps the upper 96 bits at its destination. -/
theorem xmmSchreibeTief32_hoch96 (f : XmmDatei) (dst : XmmReg)
    (w : BitVec 32) :
    ((xmmSchreibeTief32 f dst w) dst).toNat / 2 ^ 32
      = (f dst).toNat / 2 ^ 32 := by
  unfold xmmSchreibeTief32
  rw [xmmSet_gleich]
  exact setzeTief32_hoch _ _

/-- Register write keeps the upper 64-bit half at its destination. -/
theorem xmmSchreibeTief32_vHi (f : XmmDatei) (dst : XmmReg)
    (w : BitVec 32) :
    vHi ((xmmSchreibeTief32 f dst w) dst) = vHi (f dst) := by
  unfold xmmSchreibeTief32
  rw [xmmSet_gleich]
  exact setzeTief32_vHi _ _

/-- Every other XMM register keeps its value. -/
theorem xmmSchreibeTief32_fremd (f : XmmDatei) (dst q : XmmReg)
    (w : BitVec 32) (h : q ≠ dst) :
    xmmSchreibeTief32 f dst w q = f q :=
  xmmSet_fremd f dst q _ h

/-- A memory load answers the value at its destination. -/
theorem xmmLadeTief32_tief (f : XmmDatei) (dst : XmmReg)
    (w : BitVec 32) :
    xmmTief32 (xmmLadeTief32 f dst w) dst = w := by
  have hw := w.isLt
  unfold xmmTief32 xmmLadeTief32
  rw [xmmSet_gleich]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega

/-- A memory load clears the upper 96 bits at its destination. -/
theorem xmmLadeTief32_nullOben (f : XmmDatei) (dst : XmmReg)
    (w : BitVec 32) :
    ((xmmLadeTief32 f dst w) dst).toNat / 2 ^ 32 = 0 := by
  have hw := w.isLt
  unfold xmmLadeTief32
  rw [xmmSet_gleich, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : w.toNat < 2 ^ 128)]
  exact Nat.div_eq_of_lt hw

/-! ## 2. Genuine binary32 arithmetic on raw patterns.

  Every arithmetic form routes to the ACCEPTED binary32 kernel
  (`Gleitprofil.fadd32/fsub32/fmul32/fdiv32`) on injected patterns
  (`bites32`), projected back (`muster32`). The refinement is
  definitional: `s32Rechne` never re-implements rounding. NaN payloads
  are classified only (Gleitprofil §7 owns the gap); SNaN, DAZ/FTZ
  execution and sticky accumulation stay OPEN. -/

/-- Scalar single op: one constructor per accepted kernel op. -/
inductive S32Op where
  | add | sub | mul | div
  deriving DecidableEq, Repr

/-- One machine op on raw patterns: the kernel op, back as raw bits. -/
def s32Rechne : S32Op → BitVec 32 → BitVec 32 → BitVec 32
  | .add, a, b => muster32 (fadd32 (bites32 a) (bites32 b))
  | .sub, a, b => muster32 (fsub32 (bites32 a) (bites32 b))
  | .mul, a, b => muster32 (fmul32 (bites32 a) (bites32 b))
  | .div, a, b => muster32 (fdiv32 (bites32 a) (bites32 b))

/-- Routing is definitional for each op (every premise is the route). -/
theorem s32Rechne_routen (a b : BitVec 32) :
    s32Rechne .add a b = muster32 (fadd32 (bites32 a) (bites32 b))
      ∧ s32Rechne .sub a b = muster32 (fsub32 (bites32 a) (bites32 b))
      ∧ s32Rechne .mul a b = muster32 (fmul32 (bites32 a) (bites32 b))
      ∧ s32Rechne .div a b = muster32 (fdiv32 (bites32 a) (bites32 b)) :=
  ⟨rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 2048 in
/-- `1.0 + 2.0 = 3.0` as raw patterns. -/
theorem s32_eins_plus_zwei :
    s32Rechne .add 0x3F800000 0x40000000 = 0x40400000 := by
  decide

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 2048 in
/-- Signed zero: `+0 + -0 = +0` (round-to-nearest, Vol. 1 §11.5). -/
theorem s32_plusnull_minusnull :
    s32Rechne .add 0x00000000 0x80000000 = 0x00000000 := by
  decide

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 2048 in
/-- Subnormals are computed, not flushed: `min + min = next`. -/
theorem s32_subnormal_waechst :
    s32Rechne .add 0x00000001 0x00000001 = 0x00000002 := by
  decide

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 2048 in
/-- Masked divide-by-zero is a VALUE: `1 / 0 = +inf`. -/
theorem s32_eins_durch_null_unendlich :
    s32Rechne .div 0x3F800000 0x00000000 = 0x7F800000 := by
  decide

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 2048 in
/-- Masked invalid is a VALUE: `0 / 0` classifies as NaN. -/
theorem s32_null_durch_null_nan :
    Gleitkomma.klasse Gleitkomma.f32
      (bites32 (s32Rechne .div 0 0)) = .nan := by
  decide

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 2048 in
/-- NO SILENT PROMOTION (joint rounding counterexample, raw bits).
    Binary32 stalls at `2^24`: `2^24 + 1` rounds back to `2^24`
    (the accepted `f32_rundet_16777217` at the machine), while
    binary64 advances (the accepted `f64_trennt_16777217`). A promoted
    implementation would return the f64 pattern here. -/
theorem s32_stallt_bei_2hoch24 :
    s32Rechne .add 0x4B800000 0x3F800000 = 0x4B800000 := by
  decide

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 2048 in
theorem s32_f64_steigt_weiter :
    muster64 (fadd64 (bites64 0x4330000000000000)
      (bites64 0x3FF0000000000000)) ≠ 0x4330000000000000 := by
  decide

/-! ## 3. Width conversions through the accepted kernel.

  CVTSS2SD widens (exact: every finite f32 value is exactly
  representable in f64, routed through `wertExakt`/`rundeExakt`);
  CVTSD2SS narrows with the kernel round (`rundeExakt`: RNE,
  overflow to infinity); CVTSI2SS reuses `ofInt` at f32 (never via
  f64: promotion would double-round); CVTTSS2SI truncates toward zero
  and returns the hardware INTEGER INDEFINITE on invalid/out-of-range
  inputs -- it is NOT the source saturating wrapper `gleitRoh`
  (`cvtt_trennt_vom_saettiger`). NaN payloads stay class-only. -/

/-- Infinity of a format with the given sign, as data. -/
def s32Inf (F : Gleitkomma.Format) (s : Bool) : Gleitkomma.GBits F :=
  ⟨s, F.bexpMax, 0⟩

/-- A failed exact-value projection is NaN or infinity: the fallthrough
    arms of the conversions below are unreachable for finite inputs. -/
theorem wertExakt_none_klasse (F : Gleitkomma.Format)
    (g : Gleitkomma.GBits F)
    (h : Gleitkomma.wertExakt F g = none) :
    Gleitkomma.klasse F g = .nan ∨ Gleitkomma.klasse F g = .unendlich := by
  cases hc : Gleitkomma.klasse F g with
  | nan => exact Or.inl rfl
  | unendlich => exact Or.inr rfl
  | null =>
    have hs : Gleitkomma.wertExakt F g = some ⟨0, 0⟩ := by
      unfold Gleitkomma.wertExakt
      rw [hc]
    rw [hs] at h
    cases h
  | subnormal =>
    obtain ⟨v, hv⟩ : ∃ v, Gleitkomma.wertExakt F g = some v := by
      unfold Gleitkomma.wertExakt
      rw [hc]
      exact ⟨_, rfl⟩
    rw [hv] at h
    cases h
  | normal =>
    obtain ⟨v, hv⟩ : ∃ v, Gleitkomma.wertExakt F g = some v := by
      unfold Gleitkomma.wertExakt
      rw [hc]
      exact ⟨_, rfl⟩
    rw [hv] at h
    cases h

/-- CVTSS2SD: widen a single to a double (exact on finite inputs). -/
def cvtSS2SD (a : Gleitkomma.GBits Gleitkomma.f32) :
    Gleitkomma.GBits Gleitkomma.f64 :=
  match Gleitkomma.wertExakt Gleitkomma.f32 a with
  | some v => Gleitkomma.rundeExakt Gleitkomma.f64 v
  | none =>
    match Gleitkomma.klasse Gleitkomma.f32 a with
    | .nan => Gleitkomma.nanQ Gleitkomma.f64
    | .unendlich => s32Inf Gleitkomma.f64 a.sign
    | _ => Gleitkomma.nanQ Gleitkomma.f64

/-- CVTSD2SS: narrow a double to a single (kernel round, overflow
    to infinity). -/
def cvtSD2SS (a : Gleitkomma.GBits Gleitkomma.f64) :
    Gleitkomma.GBits Gleitkomma.f32 :=
  match Gleitkomma.wertExakt Gleitkomma.f64 a with
  | some v => Gleitkomma.rundeExakt Gleitkomma.f32 v
  | none =>
    match Gleitkomma.klasse Gleitkomma.f64 a with
    | .nan => Gleitkomma.nanQ Gleitkomma.f32
    | .unendlich => s32Inf Gleitkomma.f32 a.sign
    | _ => Gleitkomma.nanQ Gleitkomma.f32

/-- A 32-bit word as a signed 32-bit integer (sign-extended source). -/
def int32vonWort (w : Wort) : Int :=
  (BitVec.ofNat 32 w.toNat).toInt

/-- CVTSI2SS from a 32-bit signed source: direct `ofInt` at f32. -/
def cvtSI2SS32 (w : Wort) : Gleitkomma.GBits Gleitkomma.f32 :=
  Gleitkomma.ofInt Gleitkomma.f32 (int32vonWort w)

/-- CVTSI2SS from a 64-bit signed source: direct `ofInt` at f32. -/
def cvtSI2SS64 (w : Wort) : Gleitkomma.GBits Gleitkomma.f32 :=
  Gleitkomma.ofInt Gleitkomma.f32 w.toInt

/-- CVTTSS2SI: truncate toward zero; invalid or out-of-range inputs
    yield the integer indefinite (`0x8000...`), never saturation.
    `is64` selects the 64-bit (`true`) or 32-bit (`false`, zero-extended)
    destination, i.e. REX.W = 1 or 0. -/
def cvttSS2SI (w : BitVec 32) (is64 : Bool) : Wort :=
  let x := bites32 w
  let undef : Wort :=
    if is64 then BitVec.ofNat 64 0x8000000000000000
    else BitVec.ofNat 64 0x80000000
  match Gleitkomma.klasse Gleitkomma.f32 x with
  | .nan => undef
  | .unendlich => undef
  | _ =>
    match Gleitkomma.wertExakt Gleitkomma.f32 x with
    | Option.none => undef
    | Option.some v =>
      let t : Int :=
        if 0 ≤ v.zweierExp then
          v.zaehler * ((2 ^ v.zweierExp.toNat : Nat) : Int)
        else v.zaehler.tdiv ((2 ^ (-v.zweierExp).toNat : Nat) : Int)
      if is64 then
        if t < -(2 ^ 63 : Int) then undef
        else if (2 ^ 63 - 1 : Int) < t then undef
        else intWort t
      else
        if t < -(2 ^ 31 : Int) then undef
        else if (2 ^ 31 - 1 : Int) < t then undef
        else BitVec.ofNat 64 (t % 2 ^ 32).toNat

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 2048 in
/-- Widening is exact: `1.0f32` becomes `1.0f64`. -/
theorem cvtSS2SD_eins :
    muster64 (cvtSS2SD (bites32 0x3F800000)) = 0x3FF0000000000000 := by
  decide

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 2048 in
/-- Widening keeps NaN a NaN (class only, never a payload promise). -/
theorem cvtSS2SD_nan_bleibt_nan :
    Gleitkomma.klasse Gleitkomma.f64
      (cvtSS2SD (bites32 0x7FC00000)) = .nan := by
  decide

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 2048 in
/-- Widening keeps `+inf` an infinity. -/
theorem cvtSS2SD_inf_bleibt_inf :
    Gleitkomma.klasse Gleitkomma.f64
      (cvtSS2SD (bites32 0x7F800000)) = .unendlich := by
  decide

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 2048 in
/-- Narrowing `0.1f64` rounds once to `0.1f32` (`0x3DCCCCCD`). -/
theorem cvtSD2SS_zehntel :
    muster32 (cvtSD2SS (bites64 0x3FB999999999999A)) = 0x3DCCCCCD := by
  decide

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 2048 in
/-- Narrowing overflow is infinity: the largest finite double
    narrows to `+inf` (kernel `rundeBruch` overflow arm). -/
theorem cvtSD2SS_gross_wird_unendlich :
    cvtSD2SS ⟨false, 2046, 2 ^ 52 - 1⟩
      = (⟨false, Gleitkomma.f32.bexpMax, 0⟩ :
        Gleitkomma.GBits Gleitkomma.f32) := by
  decide

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 2048 in
/-- `42` converts to `42.0f32` from the 64-bit source. -/
theorem cvtSI2SS64_42 :
    muster32 (cvtSI2SS64 42) = 0x42280000 := by
  decide

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 2048 in
/-- `-1` converts to `-1.0f32` from the sign-extended 32-bit source. -/
theorem cvtSI2SS32_negEins :
    muster32 (cvtSI2SS32 0xFFFFFFFF) = 0xBF800000 := by
  decide

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 2048 in
/-- `1.9f32` truncates toward zero to `1` (64-bit destination). -/
theorem cvtt_eins_neun_ergibt_eins :
    cvttSS2SI 0x3FF33333 true = 1 := by
  decide

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 2048 in
/-- `2^31` is out of int32 range: the 32-bit indefinite. -/
theorem cvtt_gross_undef32 :
    cvttSS2SI 0x4F000000 false = 0x0000000080000000 := by
  decide

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 2048 in
/-- BARE CVTT IS NOT THE SOURCE SATURATING WRAPPER: a quiet NaN
    yields the 64-bit integer indefinite (`0x8000...`), while the
    source wrapper `gleitRoh` answers `0` on its NaN. -/
theorem cvtt_trennt_vom_saettiger :
    cvttSS2SI 0x7FC00000 true = 0x8000000000000000
      ∧ Gabbro.Grammatik.gleitRoh
          (bites64 0x7FF8000000000000) = 0 := by
  constructor <;> decide

/-! ## 4. Scalar single step semantics on the shared state.

  `s32Schritt` steps ONLY the selected binary32 forms on the ACCEPTED
  extended state `FpZustand` (canonical `Zustand` + XMM file + per-context
  MXCSR): the 14-form pilot evaluator is never redefined (`laufAlt`
  lifts it) and no second XMM file is created. Guards, in order: decode
  length (`laengeOk`, checked data), profile admission (`s32Eintritt`,
  the same essential MXCSR profile both lanes share), memory permission
  (`read32`/`write32` `none`). Arithmetic and register MOVSS write the
  low 32 bits and keep the upper 96; memory MOVSS loads clear them;
  CVTSS2SD writes the low 64 bits (reusing `xmmSchreibeTief`); UCOMISS
  writes only flags; RIP advances past the decode length. -/

/-- Selected scalar single forms: four arithmetic ops in register and
    m32-memory shape, unordered compare in both shapes, three MOVSS
    shapes, two same-register width conversions, integer conversions
    with explicit REX.W width (`is64`). -/
inductive S32Befehl where
  | addssRR (dst src : XmmReg)
  | subssRR (dst src : XmmReg)
  | mulssRR (dst src : XmmReg)
  | divssRR (dst src : XmmReg)
  | addssRM (dst : XmmReg) (base : Register) (disp : BitVec 32)
  | subssRM (dst : XmmReg) (base : Register) (disp : BitVec 32)
  | mulssRM (dst : XmmReg) (base : Register) (disp : BitVec 32)
  | divssRM (dst : XmmReg) (base : Register) (disp : BitVec 32)
  | ucomissRR (lhs rhs : XmmReg)
  | ucomissRM (lhs : XmmReg) (base : Register) (disp : BitVec 32)
  | movssRR (dst src : XmmReg)
  | movssLade (dst : XmmReg) (base : Register) (disp : BitVec 32)
  | movssSpeichere (base : Register) (src : XmmReg) (disp : BitVec 32)
  | cvtss2sdRR (dst src : XmmReg)
  | cvtsd2ssRR (dst src : XmmReg)
  | cvtsi2ss (dst : XmmReg) (src : Register) (is64 : Bool)
  | cvttss2si (dst : Register) (src : XmmReg) (is64 : Bool)
  deriving DecidableEq, Repr

/-- A decoded scalar single instruction: the form plus its decode length
    (checked `1..15` data, exactly as the pilot `Decodiert`). -/
structure S32Decodiert where
  befehl : S32Befehl
  laenge : Nat
  deriving DecidableEq, Repr

/-- Profile admission at the control word: the checked `mxcsrGueltig`
    premise both scalar lanes share. `false` is a VALIDATOR refusal,
    never a hardware fault. -/
def s32Eintritt (k : FPKontext) : Bool := mxcsrGueltig k.mxcsr

/-- The reset control word is admitted. -/
theorem s32Eintritt_reset : s32Eintritt kontextReset = true := by
  unfold s32Eintritt
  exact kontextReset_gueltig

/-- UCOMISS flag result over two model singles: ZF/PF/CF per the
    architecture (unordered NaN operand: all three set; greater: none;
    less: CF; equal: ZF). OF/SF/AF are cleared -- AF as `some false`
    (defined zero, exactly the accepted `ucomiFlags` shape at f32). -/
def ucomissFlags (a b : Gleitkomma.GBits Gleitkomma.f32) : Flags :=
  match Gleitkomma.klasse Gleitkomma.f32 a,
    Gleitkomma.klasse Gleitkomma.f32 b with
  | .nan, _ => ⟨true, true, some false, true, false, false⟩
  | _, .nan => ⟨true, true, some false, true, false, false⟩
  | _, _ =>
    if Gleitkomma.flt Gleitkomma.f32 a b then
      ⟨true, false, some false, false, false, false⟩
    else if Gleitkomma.flt Gleitkomma.f32 b a then
      ⟨false, false, some false, false, false, false⟩
    else ⟨false, false, some false, true, false, false⟩

/-- Single scalar single step; `none` is an explicit refusal (bad length,
    refused profile, or failed memory access). -/
def s32Schritt (d : S32Decodiert) (t : FpZustand) : Option FpZustand :=
  match laengeOk d.laenge with
  | false => none
  | true =>
    match s32Eintritt t.fp with
    | false => none
    | true =>
      let nach := ripNach t.kern.rip d.laenge
      match d.befehl with
      | .addssRR dst src =>
        let w := s32Rechne .add (xmmTief32 t.xmm dst) (xmmTief32 t.xmm src)
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSchreibeTief32 t.xmm dst w }
      | .subssRR dst src =>
        let w := s32Rechne .sub (xmmTief32 t.xmm dst) (xmmTief32 t.xmm src)
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSchreibeTief32 t.xmm dst w }
      | .mulssRR dst src =>
        let w := s32Rechne .mul (xmmTief32 t.xmm dst) (xmmTief32 t.xmm src)
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSchreibeTief32 t.xmm dst w }
      | .divssRR dst src =>
        let w := s32Rechne .div (xmmTief32 t.xmm dst) (xmmTief32 t.xmm src)
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSchreibeTief32 t.xmm dst w }
      | .addssRM dst base disp =>
        match read32 t.kern.speicher (effAddr t.kern base disp) with
        | some v =>
          let w := s32Rechne .add (xmmTief32 t.xmm dst) (BitVec.ofNat 32 v.toNat)
          some { t with kern := { t.kern with rip := nach }, xmm := xmmSchreibeTief32 t.xmm dst w }
        | none => none
      | .subssRM dst base disp =>
        match read32 t.kern.speicher (effAddr t.kern base disp) with
        | some v =>
          let w := s32Rechne .sub (xmmTief32 t.xmm dst) (BitVec.ofNat 32 v.toNat)
          some { t with kern := { t.kern with rip := nach }, xmm := xmmSchreibeTief32 t.xmm dst w }
        | none => none
      | .mulssRM dst base disp =>
        match read32 t.kern.speicher (effAddr t.kern base disp) with
        | some v =>
          let w := s32Rechne .mul (xmmTief32 t.xmm dst) (BitVec.ofNat 32 v.toNat)
          some { t with kern := { t.kern with rip := nach }, xmm := xmmSchreibeTief32 t.xmm dst w }
        | none => none
      | .divssRM dst base disp =>
        match read32 t.kern.speicher (effAddr t.kern base disp) with
        | some v =>
          let w := s32Rechne .div (xmmTief32 t.xmm dst) (BitVec.ofNat 32 v.toNat)
          some { t with kern := { t.kern with rip := nach }, xmm := xmmSchreibeTief32 t.xmm dst w }
        | none => none
      | .ucomissRR lhs rhs =>
        let f := ucomissFlags (bites32 (xmmTief32 t.xmm lhs))
          (bites32 (xmmTief32 t.xmm rhs))
        some { t with kern := { t.kern with rip := nach, flags := f } }
      | .ucomissRM lhs base disp =>
        match read32 t.kern.speicher (effAddr t.kern base disp) with
        | some v =>
          let f := ucomissFlags (bites32 (xmmTief32 t.xmm lhs))
            (bites32 (BitVec.ofNat 32 v.toNat))
          some { t with kern := { t.kern with rip := nach, flags := f } }
        | none => none
      | .movssRR dst src =>
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSchreibeTief32 t.xmm dst (xmmTief32 t.xmm src) }
      | .movssLade dst base disp =>
        match read32 t.kern.speicher (effAddr t.kern base disp) with
        | some v =>
          some { t with kern := { t.kern with rip := nach }, xmm := xmmLadeTief32 t.xmm dst (BitVec.ofNat 32 v.toNat) }
        | none => none
      | .movssSpeichere base src disp =>
        match write32 t.kern.speicher (effAddr t.kern base disp)
          (BitVec.setWidth 64 (xmmTief32 t.xmm src)) with
        | some m => some { t with kern := { t.kern with speicher := m, rip := nach } }
        | none => none
      | .cvtss2sdRR dst src =>
        let w := muster64 (cvtSS2SD (bites32 (xmmTief32 t.xmm src)))
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSchreibeTief t.xmm dst w }
      | .cvtsd2ssRR dst src =>
        let w := muster32 (cvtSD2SS (bites64 (xmmTief t.xmm src)))
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSchreibeTief32 t.xmm dst w }
      | .cvtsi2ss dst src is64 =>
        let w := muster32 (if is64 then cvtSI2SS64 (t.kern.register src)
          else cvtSI2SS32 (t.kern.register src))
        some { t with kern := { t.kern with rip := nach }, xmm := xmmSchreibeTief32 t.xmm dst w }
      | .cvttss2si dst src is64 =>
        let w := cvttSS2SI (xmmTief32 t.xmm src) is64
        some { t with kern := { t.kern with register := regSet t.kern.register dst w, rip := nach } }

/-- A bad decode length refuses every scalar single form. -/
theorem s32Schritt_laenge_verweigert (d : S32Decodiert) (t : FpZustand)
    (h : laengeOk d.laenge = false) : s32Schritt d t = none := by
  unfold s32Schritt
  simp [h]

/-- A refused profile refuses every scalar single form (validator
    admission, not a hardware fault). -/
theorem s32Schritt_profil_verweigert (d : S32Decodiert) (t : FpZustand)
    (hok : laengeOk d.laenge = true) (h : s32Eintritt t.fp = false) :
    s32Schritt d t = none := by
  unfold s32Schritt
  simp [hok, h]

/-- A successful 32-bit read carries a 32-bit value (four-byte
    footprint: the upper half is always zero). -/
theorem read32_wert_klein (m : Speicher) (a : Adresse) (v : Wort)
    (h : read32 m a = some v) : v.toNat < 2 ^ 32 := by
  unfold read32 at h
  by_cases hc : lesbarN m a 4 = true
  · rw [if_pos hc] at h
    cases h
    rw [BitVec.toNat_ofNat]
    have b0 := (m.bytes a).isLt
    have b1 := (m.bytes (addrOff a 1)).isLt
    have b2 := (m.bytes (addrOff a 2)).isLt
    have b3 := (m.bytes (addrOff a 3)).isLt
    have hsum : (m.bytes a).toNat + (m.bytes (addrOff a 1)).toNat * 256 +
        (m.bytes (addrOff a 2)).toNat * 65536 +
        (m.bytes (addrOff a 3)).toNat * 16777216 < 2 ^ 32 := by
      omega
    have h64 : (m.bytes a).toNat + (m.bytes (addrOff a 1)).toNat * 256 +
        (m.bytes (addrOff a 2)).toNat * 65536 +
        (m.bytes (addrOff a 3)).toNat * 16777216 < 2 ^ 64 := by
      omega
    rw [Nat.mod_eq_of_lt h64]
    exact hsum
  · rw [if_neg hc] at h
    cases h

/-- A successful 32-bit read proves the four readable bytes. -/
theorem read32_braucht_lesbar (m : Speicher) (a : Adresse) (v : Wort)
    (h : read32 m a = some v) : lesbarN m a 4 = true := by
  unfold read32 at h
  by_cases hc : lesbarN m a 4 = true
  · exact hc
  · rw [if_neg hc] at h
    cases h

/-- A successful 32-bit write proves the four writable bytes. -/
theorem write32_braucht_schreibbar (m : Speicher) (a : Adresse)
    (v : Wort) (m' : Speicher) (h : write32 m a v = some m') :
    schreibbarN m a 4 = true := by
  unfold write32 at h
  by_cases hc : schreibbarN m a 4 = true
  · exact hc
  · rw [if_neg hc] at h
    cases h

/-! ## 5. Step equations: guards, arithmetic, and their frames.

  Each equation pins the full successor; every premise is used. -/

/-- `addss` (register): the low single holds the model sum. -/
theorem s32Schritt_addssRR (d : S32Decodiert) (t : FpZustand) (dst src : XmmReg) (hok : laengeOk d.laenge = true) (hfp : s32Eintritt t.fp = true) (h : d.befehl = .addssRR dst src) : s32Schritt d t = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSchreibeTief32 t.xmm dst (s32Rechne .add (xmmTief32 t.xmm dst) (xmmTief32 t.xmm src)) } := by
  unfold s32Schritt
  simp [hok, hfp, h]

/-- `subss` (register): the low single holds the model difference. -/
theorem s32Schritt_subssRR (d : S32Decodiert) (t : FpZustand) (dst src : XmmReg) (hok : laengeOk d.laenge = true) (hfp : s32Eintritt t.fp = true) (h : d.befehl = .subssRR dst src) : s32Schritt d t = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSchreibeTief32 t.xmm dst (s32Rechne .sub (xmmTief32 t.xmm dst) (xmmTief32 t.xmm src)) } := by
  unfold s32Schritt
  simp [hok, hfp, h]

/-- `mulss` (register): the low single holds the model product. -/
theorem s32Schritt_mulssRR (d : S32Decodiert) (t : FpZustand) (dst src : XmmReg) (hok : laengeOk d.laenge = true) (hfp : s32Eintritt t.fp = true) (h : d.befehl = .mulssRR dst src) : s32Schritt d t = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSchreibeTief32 t.xmm dst (s32Rechne .mul (xmmTief32 t.xmm dst) (xmmTief32 t.xmm src)) } := by
  unfold s32Schritt
  simp [hok, hfp, h]

/-- `divss` (register): the low single holds the model quotient. -/
theorem s32Schritt_divssRR (d : S32Decodiert) (t : FpZustand) (dst src : XmmReg) (hok : laengeOk d.laenge = true) (hfp : s32Eintritt t.fp = true) (h : d.befehl = .divssRR dst src) : s32Schritt d t = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSchreibeTief32 t.xmm dst (s32Rechne .div (xmmTief32 t.xmm dst) (xmmTief32 t.xmm src)) } := by
  unfold s32Schritt
  simp [hok, hfp, h]

/-- `addss` (memory source) success: the four bytes at base plus
    displacement are the second model operand. -/
theorem s32Schritt_addssRM_erfolg (d : S32Decodiert) (t : FpZustand) (dst : XmmReg) (base : Register) (disp : BitVec 32) (v : Wort) (hok : laengeOk d.laenge = true) (hfp : s32Eintritt t.fp = true) (h : d.befehl = .addssRM dst base disp) (hrd : read32 t.kern.speicher (effAddr t.kern base disp) = some v) : s32Schritt d t = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSchreibeTief32 t.xmm dst (s32Rechne .add (xmmTief32 t.xmm dst) (BitVec.ofNat 32 v.toNat)) } := by
  unfold s32Schritt
  simp [hok, hfp, h, hrd]

/-- `addss` (memory source) refusal: a failed read is explicit. -/
theorem s32Schritt_addssRM_verweigert (d : S32Decodiert) (t : FpZustand) (dst : XmmReg) (base : Register) (disp : BitVec 32) (hok : laengeOk d.laenge = true) (hfp : s32Eintritt t.fp = true) (h : d.befehl = .addssRM dst base disp) (hrd : read32 t.kern.speicher (effAddr t.kern base disp) = none) : s32Schritt d t = none := by
  unfold s32Schritt
  simp [hok, hfp, h, hrd]

/-- `subss` (memory source) success. -/
theorem s32Schritt_subssRM_erfolg (d : S32Decodiert) (t : FpZustand) (dst : XmmReg) (base : Register) (disp : BitVec 32) (v : Wort) (hok : laengeOk d.laenge = true) (hfp : s32Eintritt t.fp = true) (h : d.befehl = .subssRM dst base disp) (hrd : read32 t.kern.speicher (effAddr t.kern base disp) = some v) : s32Schritt d t = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSchreibeTief32 t.xmm dst (s32Rechne .sub (xmmTief32 t.xmm dst) (BitVec.ofNat 32 v.toNat)) } := by
  unfold s32Schritt
  simp [hok, hfp, h, hrd]

/-- `subss` (memory source) refusal. -/
theorem s32Schritt_subssRM_verweigert (d : S32Decodiert) (t : FpZustand) (dst : XmmReg) (base : Register) (disp : BitVec 32) (hok : laengeOk d.laenge = true) (hfp : s32Eintritt t.fp = true) (h : d.befehl = .subssRM dst base disp) (hrd : read32 t.kern.speicher (effAddr t.kern base disp) = none) : s32Schritt d t = none := by
  unfold s32Schritt
  simp [hok, hfp, h, hrd]

/-- `mulss` (memory source) success. -/
theorem s32Schritt_mulssRM_erfolg (d : S32Decodiert) (t : FpZustand) (dst : XmmReg) (base : Register) (disp : BitVec 32) (v : Wort) (hok : laengeOk d.laenge = true) (hfp : s32Eintritt t.fp = true) (h : d.befehl = .mulssRM dst base disp) (hrd : read32 t.kern.speicher (effAddr t.kern base disp) = some v) : s32Schritt d t = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSchreibeTief32 t.xmm dst (s32Rechne .mul (xmmTief32 t.xmm dst) (BitVec.ofNat 32 v.toNat)) } := by
  unfold s32Schritt
  simp [hok, hfp, h, hrd]

/-- `mulss` (memory source) refusal. -/
theorem s32Schritt_mulssRM_verweigert (d : S32Decodiert) (t : FpZustand) (dst : XmmReg) (base : Register) (disp : BitVec 32) (hok : laengeOk d.laenge = true) (hfp : s32Eintritt t.fp = true) (h : d.befehl = .mulssRM dst base disp) (hrd : read32 t.kern.speicher (effAddr t.kern base disp) = none) : s32Schritt d t = none := by
  unfold s32Schritt
  simp [hok, hfp, h, hrd]

/-- `divss` (memory source) success. -/
theorem s32Schritt_divssRM_erfolg (d : S32Decodiert) (t : FpZustand) (dst : XmmReg) (base : Register) (disp : BitVec 32) (v : Wort) (hok : laengeOk d.laenge = true) (hfp : s32Eintritt t.fp = true) (h : d.befehl = .divssRM dst base disp) (hrd : read32 t.kern.speicher (effAddr t.kern base disp) = some v) : s32Schritt d t = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSchreibeTief32 t.xmm dst (s32Rechne .div (xmmTief32 t.xmm dst) (BitVec.ofNat 32 v.toNat)) } := by
  unfold s32Schritt
  simp [hok, hfp, h, hrd]

/-- `divss` (memory source) refusal. -/
theorem s32Schritt_divssRM_verweigert (d : S32Decodiert) (t : FpZustand) (dst : XmmReg) (base : Register) (disp : BitVec 32) (hok : laengeOk d.laenge = true) (hfp : s32Eintritt t.fp = true) (h : d.befehl = .divssRM dst base disp) (hrd : read32 t.kern.speicher (effAddr t.kern base disp) = none) : s32Schritt d t = none := by
  unfold s32Schritt
  simp [hok, hfp, h, hrd]

/-- `ucomiss` (register): only flags change. -/
theorem s32Schritt_ucomissRR (d : S32Decodiert) (t : FpZustand) (lhs rhs : XmmReg) (hok : laengeOk d.laenge = true) (hfp : s32Eintritt t.fp = true) (h : d.befehl = .ucomissRR lhs rhs) : s32Schritt d t = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge, flags := ucomissFlags (bites32 (xmmTief32 t.xmm lhs)) (bites32 (xmmTief32 t.xmm rhs)) } } := by
  unfold s32Schritt
  simp [hok, hfp, h]

/-- `ucomiss` (memory source) success. -/
theorem s32Schritt_ucomissRM_erfolg (d : S32Decodiert) (t : FpZustand) (lhs : XmmReg) (base : Register) (disp : BitVec 32) (v : Wort) (hok : laengeOk d.laenge = true) (hfp : s32Eintritt t.fp = true) (h : d.befehl = .ucomissRM lhs base disp) (hrd : read32 t.kern.speicher (effAddr t.kern base disp) = some v) : s32Schritt d t = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge, flags := ucomissFlags (bites32 (xmmTief32 t.xmm lhs)) (bites32 (BitVec.ofNat 32 v.toNat)) } } := by
  unfold s32Schritt
  simp [hok, hfp, h, hrd]

/-- `ucomiss` (memory source) refusal. -/
theorem s32Schritt_ucomissRM_verweigert (d : S32Decodiert) (t : FpZustand) (lhs : XmmReg) (base : Register) (disp : BitVec 32) (hok : laengeOk d.laenge = true) (hfp : s32Eintritt t.fp = true) (h : d.befehl = .ucomissRM lhs base disp) (hrd : read32 t.kern.speicher (effAddr t.kern base disp) = none) : s32Schritt d t = none := by
  unfold s32Schritt
  simp [hok, hfp, h, hrd]

/-- `movss` (register merge): the low single is copied, the upper 96
    bits are kept. -/
theorem s32Schritt_movssRR (d : S32Decodiert) (t : FpZustand) (dst src : XmmReg) (hok : laengeOk d.laenge = true) (hfp : s32Eintritt t.fp = true) (h : d.befehl = .movssRR dst src) : s32Schritt d t = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSchreibeTief32 t.xmm dst (xmmTief32 t.xmm src) } := by
  unfold s32Schritt
  simp [hok, hfp, h]

/-- `movss` (load) success: the low single is loaded and the upper 96
    bits are cleared. -/
theorem s32Schritt_movssLade_erfolg (d : S32Decodiert) (t : FpZustand) (dst : XmmReg) (base : Register) (disp : BitVec 32) (v : Wort) (hok : laengeOk d.laenge = true) (hfp : s32Eintritt t.fp = true) (h : d.befehl = .movssLade dst base disp) (hrd : read32 t.kern.speicher (effAddr t.kern base disp) = some v) : s32Schritt d t = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmLadeTief32 t.xmm dst (BitVec.ofNat 32 v.toNat) } := by
  unfold s32Schritt
  simp [hok, hfp, h, hrd]

/-- `movss` (load) refusal. -/
theorem s32Schritt_movssLade_verweigert (d : S32Decodiert) (t : FpZustand) (dst : XmmReg) (base : Register) (disp : BitVec 32) (hok : laengeOk d.laenge = true) (hfp : s32Eintritt t.fp = true) (h : d.befehl = .movssLade dst base disp) (hrd : read32 t.kern.speicher (effAddr t.kern base disp) = none) : s32Schritt d t = none := by
  unfold s32Schritt
  simp [hok, hfp, h, hrd]

/-- `movss` (store) success: the low single reaches memory. -/
theorem s32Schritt_movssSpeichere_erfolg (d : S32Decodiert) (t : FpZustand) (base : Register) (src : XmmReg) (disp : BitVec 32) (m : Speicher) (hok : laengeOk d.laenge = true) (hfp : s32Eintritt t.fp = true) (h : d.befehl = .movssSpeichere base src disp) (hwr : write32 t.kern.speicher (effAddr t.kern base disp) (BitVec.setWidth 64 (xmmTief32 t.xmm src)) = some m) : s32Schritt d t = some { t with kern := { t.kern with speicher := m, rip := ripNach t.kern.rip d.laenge } } := by
  unfold s32Schritt
  simp [hok, hfp, h, hwr]

/-- `movss` (store) refusal. -/
theorem s32Schritt_movssSpeichere_verweigert (d : S32Decodiert) (t : FpZustand) (base : Register) (src : XmmReg) (disp : BitVec 32) (hok : laengeOk d.laenge = true) (hfp : s32Eintritt t.fp = true) (h : d.befehl = .movssSpeichere base src disp) (hwr : write32 t.kern.speicher (effAddr t.kern base disp) (BitVec.setWidth 64 (xmmTief32 t.xmm src)) = none) : s32Schritt d t = none := by
  unfold s32Schritt
  simp [hok, hfp, h, hwr]

/-- `cvtss2sd`: the low double holds the widened value, the high 64
    bits are kept. -/
theorem s32Schritt_cvtss2sdRR (d : S32Decodiert) (t : FpZustand) (dst src : XmmReg) (hok : laengeOk d.laenge = true) (hfp : s32Eintritt t.fp = true) (h : d.befehl = .cvtss2sdRR dst src) : s32Schritt d t = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSchreibeTief t.xmm dst (muster64 (cvtSS2SD (bites32 (xmmTief32 t.xmm src)))) } := by
  unfold s32Schritt
  simp [hok, hfp, h]

/-- `cvtsd2ss`: the low single holds the narrowed value. -/
theorem s32Schritt_cvtsd2ssRR (d : S32Decodiert) (t : FpZustand) (dst src : XmmReg) (hok : laengeOk d.laenge = true) (hfp : s32Eintritt t.fp = true) (h : d.befehl = .cvtsd2ssRR dst src) : s32Schritt d t = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSchreibeTief32 t.xmm dst (muster32 (cvtSD2SS (bites64 (xmmTief t.xmm src)))) } := by
  unfold s32Schritt
  simp [hok, hfp, h]

/-- `cvtsi2ss`: the low single holds the converted integer. -/
theorem s32Schritt_cvtsi2ss (d : S32Decodiert) (t : FpZustand) (dst : XmmReg) (src : Register) (is64 : Bool) (hok : laengeOk d.laenge = true) (hfp : s32Eintritt t.fp = true) (h : d.befehl = .cvtsi2ss dst src is64) : s32Schritt d t = some { t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, xmm := xmmSchreibeTief32 t.xmm dst (muster32 (if is64 then cvtSI2SS64 (t.kern.register src) else cvtSI2SS32 (t.kern.register src))) } := by
  unfold s32Schritt
  simp [hok, hfp, h]

/-- `cvttss2si`: the GPR holds the truncated value or the indefinite. -/
theorem s32Schritt_cvttss2si (d : S32Decodiert) (t : FpZustand) (dst : Register) (src : XmmReg) (is64 : Bool) (hok : laengeOk d.laenge = true) (hfp : s32Eintritt t.fp = true) (h : d.befehl = .cvttss2si dst src is64) : s32Schritt d t = some { t with kern := { t.kern with register := regSet t.kern.register dst (cvttSS2SI (xmmTief32 t.xmm src) is64), rip := ripNach t.kern.rip d.laenge } } := by
  unfold s32Schritt
  simp [hok, hfp, h]

/-! ## 6. Frames: preservation versus clearing, per write kind.

  Register MOVSS preserves the upper 96 bits; memory MOVSS clears
  them; arithmetic preserves them in both shapes; CVTSS2SD keeps the
  upper 64-bit half; compares and converts touch only their documented
  state. A store reads back the stored single. -/

/-- `addss` (register) keeps the upper 96 bits at its destination. -/
theorem s32Schritt_addssRR_hoch (d : S32Decodiert) (t t' : FpZustand) (dst src : XmmReg) (hok : laengeOk d.laenge = true) (hfp : s32Eintritt t.fp = true) (h : d.befehl = .addssRR dst src) (hstep : s32Schritt d t = some t') : (t'.xmm dst).toNat / 2 ^ 32 = (t.xmm dst).toNat / 2 ^ 32 := by
  rw [s32Schritt_addssRR d t dst src hok hfp h] at hstep
  cases hstep
  exact xmmSchreibeTief32_hoch96 _ _ _

/-- `addss` (register) preserves the flags. -/
theorem s32Schritt_addssRR_flags (d : S32Decodiert) (t t' : FpZustand) (dst src : XmmReg) (hok : laengeOk d.laenge = true) (hfp : s32Eintritt t.fp = true) (h : d.befehl = .addssRR dst src) (hstep : s32Schritt d t = some t') : t'.kern.flags = t.kern.flags := by
  rw [s32Schritt_addssRR d t dst src hok hfp h] at hstep
  cases hstep
  rfl

/-- `addss` (register) changes no memory byte. -/
theorem s32Schritt_addssRR_speicher (d : S32Decodiert) (t t' : FpZustand) (dst src : XmmReg) (hok : laengeOk d.laenge = true) (hfp : s32Eintritt t.fp = true) (h : d.befehl = .addssRR dst src) (hstep : s32Schritt d t = some t') : t'.kern.speicher = t.kern.speicher := by
  rw [s32Schritt_addssRR d t dst src hok hfp h] at hstep
  cases hstep
  rfl

/-- `addss` (register) keeps every GPR. -/
theorem s32Schritt_addssRR_gpr (d : S32Decodiert) (t t' : FpZustand) (dst src : XmmReg) (q : Register) (hok : laengeOk d.laenge = true) (hfp : s32Eintritt t.fp = true) (h : d.befehl = .addssRR dst src) (hstep : s32Schritt d t = some t') : t'.kern.register q = t.kern.register q := by
  rw [s32Schritt_addssRR d t dst src hok hfp h] at hstep
  cases hstep
  rfl

/-- `addss` (memory source) keeps the upper 96 bits at its destination. -/
theorem s32Schritt_addssRM_hoch (d : S32Decodiert) (t t' : FpZustand) (dst : XmmReg) (base : Register) (disp : BitVec 32) (v : Wort) (hok : laengeOk d.laenge = true) (hfp : s32Eintritt t.fp = true) (h : d.befehl = .addssRM dst base disp) (hrd : read32 t.kern.speicher (effAddr t.kern base disp) = some v) (hstep : s32Schritt d t = some t') : (t'.xmm dst).toNat / 2 ^ 32 = (t.xmm dst).toNat / 2 ^ 32 := by
  rw [s32Schritt_addssRM_erfolg d t dst base disp v hok hfp h hrd] at hstep
  cases hstep
  exact xmmSchreibeTief32_hoch96 _ _ _

/-- REGISTER MOVSS PRESERVES: the upper 96 bits survive the merge. -/
theorem s32Schritt_movssRR_hoch (d : S32Decodiert) (t t' : FpZustand) (dst src : XmmReg) (hok : laengeOk d.laenge = true) (hfp : s32Eintritt t.fp = true) (h : d.befehl = .movssRR dst src) (hstep : s32Schritt d t = some t') : (t'.xmm dst).toNat / 2 ^ 32 = (t.xmm dst).toNat / 2 ^ 32 := by
  rw [s32Schritt_movssRR d t dst src hok hfp h] at hstep
  cases hstep
  exact xmmSchreibeTief32_hoch96 _ _ _

/-- Register MOVSS preserves the flags. -/
theorem s32Schritt_movssRR_flags (d : S32Decodiert) (t t' : FpZustand) (dst src : XmmReg) (hok : laengeOk d.laenge = true) (hfp : s32Eintritt t.fp = true) (h : d.befehl = .movssRR dst src) (hstep : s32Schritt d t = some t') : t'.kern.flags = t.kern.flags := by
  rw [s32Schritt_movssRR d t dst src hok hfp h] at hstep
  cases hstep
  rfl

/-- Register MOVSS changes no memory byte. -/
theorem s32Schritt_movssRR_speicher (d : S32Decodiert) (t t' : FpZustand) (dst src : XmmReg) (hok : laengeOk d.laenge = true) (hfp : s32Eintritt t.fp = true) (h : d.befehl = .movssRR dst src) (hstep : s32Schritt d t = some t') : t'.kern.speicher = t.kern.speicher := by
  rw [s32Schritt_movssRR d t dst src hok hfp h] at hstep
  cases hstep
  rfl

/-- MEMORY MOVSS CLEARS: a load zeroes the upper 96 bits. -/
theorem s32Schritt_movssLade_nullOben (d : S32Decodiert) (t t' : FpZustand) (dst : XmmReg) (base : Register) (disp : BitVec 32) (v : Wort) (hok : laengeOk d.laenge = true) (hfp : s32Eintritt t.fp = true) (h : d.befehl = .movssLade dst base disp) (hrd : read32 t.kern.speicher (effAddr t.kern base disp) = some v) (hstep : s32Schritt d t = some t') : (t'.xmm dst).toNat / 2 ^ 32 = 0 := by
  rw [s32Schritt_movssLade_erfolg d t dst base disp v hok hfp h hrd] at hstep
  cases hstep
  exact xmmLadeTief32_nullOben _ _ _

/-- A load preserves the flags. -/
theorem s32Schritt_movssLade_flags (d : S32Decodiert) (t t' : FpZustand) (dst : XmmReg) (base : Register) (disp : BitVec 32) (v : Wort) (hok : laengeOk d.laenge = true) (hfp : s32Eintritt t.fp = true) (h : d.befehl = .movssLade dst base disp) (hrd : read32 t.kern.speicher (effAddr t.kern base disp) = some v) (hstep : s32Schritt d t = some t') : t'.kern.flags = t.kern.flags := by
  rw [s32Schritt_movssLade_erfolg d t dst base disp v hok hfp h hrd] at hstep
  cases hstep
  rfl

/-- CVTSS2SD keeps the upper 64-bit half at its destination. -/
theorem s32Schritt_cvtss2sdRR_vHi (d : S32Decodiert) (t t' : FpZustand) (dst src : XmmReg) (hok : laengeOk d.laenge = true) (hfp : s32Eintritt t.fp = true) (h : d.befehl = .cvtss2sdRR dst src) (hstep : s32Schritt d t = some t') : vHi (t'.xmm dst) = vHi (t.xmm dst) := by
  rw [s32Schritt_cvtss2sdRR d t dst src hok hfp h] at hstep
  cases hstep
  exact xmmSchreibeTief_hoch _ _ _

/-- UCOMISS changes no XMM register. -/
theorem s32Schritt_ucomissRR_xmm (d : S32Decodiert) (t t' : FpZustand) (lhs rhs : XmmReg) (q : XmmReg) (hok : laengeOk d.laenge = true) (hfp : s32Eintritt t.fp = true) (h : d.befehl = .ucomissRR lhs rhs) (hstep : s32Schritt d t = some t') : t'.xmm q = t.xmm q := by
  rw [s32Schritt_ucomissRR d t lhs rhs hok hfp h] at hstep
  cases hstep
  rfl

/-- UCOMISS changes no memory byte. -/
theorem s32Schritt_ucomissRR_speicher (d : S32Decodiert) (t t' : FpZustand) (lhs rhs : XmmReg) (hok : laengeOk d.laenge = true) (hfp : s32Eintritt t.fp = true) (h : d.befehl = .ucomissRR lhs rhs) (hstep : s32Schritt d t = some t') : t'.kern.speicher = t.kern.speicher := by
  rw [s32Schritt_ucomissRR d t lhs rhs hok hfp h] at hstep
  cases hstep
  rfl

/-- CVTTSS2SI changes no XMM register. -/
theorem s32Schritt_cvttss2si_xmm (d : S32Decodiert) (t t' : FpZustand) (dst : Register) (src : XmmReg) (is64 : Bool) (q : XmmReg) (hok : laengeOk d.laenge = true) (hfp : s32Eintritt t.fp = true) (h : d.befehl = .cvttss2si dst src is64) (hstep : s32Schritt d t = some t') : t'.xmm q = t.xmm q := by
  rw [s32Schritt_cvttss2si d t dst src is64 hok hfp h] at hstep
  cases hstep
  rfl

/-- CVTTSS2SI changes no memory byte. -/
theorem s32Schritt_cvttss2si_speicher (d : S32Decodiert) (t t' : FpZustand) (dst : Register) (src : XmmReg) (is64 : Bool) (hok : laengeOk d.laenge = true) (hfp : s32Eintritt t.fp = true) (h : d.befehl = .cvttss2si dst src is64) (hstep : s32Schritt d t = some t') : t'.kern.speicher = t.kern.speicher := by
  rw [s32Schritt_cvttss2si d t dst src is64 hok hfp h] at hstep
  cases hstep
  rfl

/-- A store preserves the flags. -/
theorem s32Schritt_movssSpeichere_flags (d : S32Decodiert) (t t' : FpZustand) (base : Register) (src : XmmReg) (disp : BitVec 32) (m : Speicher) (hok : laengeOk d.laenge = true) (hfp : s32Eintritt t.fp = true) (h : d.befehl = .movssSpeichere base src disp) (hwr : write32 t.kern.speicher (effAddr t.kern base disp) (BitVec.setWidth 64 (xmmTief32 t.xmm src)) = some m) (hstep : s32Schritt d t = some t') : t'.kern.flags = t.kern.flags := by
  rw [s32Schritt_movssSpeichere_erfolg d t base src disp m hok hfp h hwr] at hstep
  cases hstep
  rfl

/-- A store keeps every GPR. -/
theorem s32Schritt_movssSpeichere_gpr (d : S32Decodiert) (t t' : FpZustand) (base : Register) (src : XmmReg) (disp : BitVec 32) (m : Speicher) (q : Register) (hok : laengeOk d.laenge = true) (hfp : s32Eintritt t.fp = true) (h : d.befehl = .movssSpeichere base src disp) (hwr : write32 t.kern.speicher (effAddr t.kern base disp) (BitVec.setWidth 64 (xmmTief32 t.xmm src)) = some m) (hstep : s32Schritt d t = some t') : t'.kern.register q = t.kern.register q := by
  rw [s32Schritt_movssSpeichere_erfolg d t base src disp m hok hfp h hwr] at hstep
  cases hstep
  rfl

/-- A store changes no XMM register. -/
theorem s32Schritt_movssSpeichere_xmm (d : S32Decodiert) (t t' : FpZustand) (base : Register) (src : XmmReg) (disp : BitVec 32) (m : Speicher) (q : XmmReg) (hok : laengeOk d.laenge = true) (hfp : s32Eintritt t.fp = true) (h : d.befehl = .movssSpeichere base src disp) (hwr : write32 t.kern.speicher (effAddr t.kern base disp) (BitVec.setWidth 64 (xmmTief32 t.xmm src)) = some m) (hstep : s32Schritt d t = some t') : t'.xmm q = t.xmm q := by
  rw [s32Schritt_movssSpeichere_erfolg d t base src disp m hok hfp h hwr] at hstep
  cases hstep
  rfl

/-- Zero-extension to 64 bits keeps the 32-bit value. -/
theorem setWidth64_wert (w : BitVec 32) :
    (BitVec.setWidth 64 w).toNat = w.toNat := by
  have hw := w.isLt
  have h : BitVec.ofNat 64 w.toNat = BitVec.setWidth 64 w := by simp
  rw [← h, BitVec.toNat_ofNat]
  have h64 : w.toNat < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt h64]

/-- STORE READBACK: the stored single reads back exactly. -/
theorem s32_speichere_liest_zurueck (t : FpZustand) (base : Register) (src : XmmReg) (disp : BitVec 32) (m' : Speicher) (hwr : write32 t.kern.speicher (effAddr t.kern base disp) (BitVec.setWidth 64 (xmmTief32 t.xmm src)) = some m') (hles : lesbarN t.kern.speicher (effAddr t.kern base disp) 4 = true) : read32 m' (effAddr t.kern base disp) = some (BitVec.ofNat 64 (xmmTief32 t.xmm src).toNat) := by
  have hrd := read32_nach_write32 t.kern.speicher m'
    (effAddr t.kern base disp)
    (BitVec.setWidth 64 (xmmTief32 t.xmm src)) hwr hles
  have hw := (xmmTief32 t.xmm src).isLt
  have hbridge : (BitVec.setWidth 64 (xmmTief32 t.xmm src)).toNat % 4294967296
      = (xmmTief32 t.xmm src).toNat := by
    rw [setWidth64_wert]
    have h32 : (4294967296 : Nat) = 2 ^ 32 := by decide
    rw [h32, Nat.mod_eq_of_lt hw]
  rw [hbridge] at hrd
  exact hrd

/-- UCOMISS flags: a NaN left operand is unordered (ZF, PF, CF set). -/
theorem ucomissFlags_ungeordnet :
    ucomissFlags ⟨false, Gleitkomma.f32.bexpMax, 1⟩ ⟨false, 0, 0⟩
      = ⟨true, true, some false, true, false, false⟩ := by
  rfl

/-- UCOMISS flags: `1.0 < 2.0` sets CF alone. -/
theorem ucomissFlags_kleiner :
    ucomissFlags (bites32 0x3F800000) (bites32 0x40000000)
      = ⟨true, false, some false, false, false, false⟩ := by
  decide

/-- UCOMISS flags: `1.0 = 1.0` sets ZF alone. -/
theorem ucomissFlags_gleich :
    ucomissFlags (bites32 0x3F800000) (bites32 0x3F800000)
      = ⟨false, false, some false, true, false, false⟩ := by
  decide

/-! ## 7. REX-selected byte codec for the scalar single forms.

  Canonical subset stated from the opcode map (F3 prefix for scalar
  single, F2 for the double-sourced CVTSD2SS, no prefix for UCOMISS;
  0F escape; opcodes 10/11 moves, 58/5C/59/5E arithmetic, 2E compare,
  5A conversions, 2A/2C integer conversions), exactly like the accepted
  F2 double rows state theirs: an implementation contract, never a
  hardware correspondence claim. REX.R extends the ModRM reg field
  (destination XMM, or destination GPR for CVTTSS2SI), REX.B the r/m
  field (source XMM, source GPR, or base GPR); REX.X is refused (no
  index in this subset); REX.W selects the integer width on the two
  integer conversions and is refused elsewhere as non-canonical. The
  decoder parses actual bytes and never accepts a caller-supplied
  `S32Decodiert` as fetched evidence. -/

/-- High bit of an XMM code (the REX.R/B side). -/
def fpXmmHoch (r : XmmReg) : Nat := fpXmmCode r / 8

/-- Low three bits of an XMM code (the ModRM field). -/
def fpXmmTief (r : XmmReg) : Nat := fpXmmCode r % 8

/-- Full 4-bit XMM decode (REX-selected high registers included). -/
def codeXmmVoll : Nat → Option XmmReg
  | 0 => some .xmm0 | 1 => some .xmm1 | 2 => some .xmm2 | 3 => some .xmm3
  | 4 => some .xmm4 | 5 => some .xmm5 | 6 => some .xmm6 | 7 => some .xmm7
  | 8 => some .xmm8 | 9 => some .xmm9 | 10 => some .xmm10 | 11 => some .xmm11
  | 12 => some .xmm12 | 13 => some .xmm13 | 14 => some .xmm14
  | 15 => some .xmm15
  | _ => none

/-- Decoding inverts encoding on every XMM register, high included. -/
theorem codeXmmVoll_fpXmmCode (r : XmmReg) :
    codeXmmVoll (fpXmmCode r) = some r := by
  cases r <;> rfl

/-- Every XMM code splits into its high bit and low field. -/
theorem fpXmmCode_split (r : XmmReg) :
    fpXmmHoch r * 8 + fpXmmTief r = fpXmmCode r := by
  cases r <;> decide

/-- Optional REX byte: present iff W, R or B is set (X stays 0). -/
def s32Rex (w r b : Nat) : List Byte :=
  if w == 0 && r == 0 && b == 0 then []
  else [natByte (64 + w * 8 + r * 4 + b)]

/-- No high bits and no width bit means no REX byte. -/
theorem s32Rex_kein : s32Rex 0 0 0 = [] := by
  decide

/-- REX.W+R+B for a wide high-destination pair is `0x4D`. -/
theorem s32Rex_hoch_hoch : s32Rex 1 1 1 = [natByte 77] := by
  decide

/-- A byte is a REX prefix iff it lies in `0x40..0x4F`. -/
def s32IstRex (b : Byte) : Bool :=
  decide (64 ≤ byteNat b ∧ byteNat b < 80)

/-- REX bits from the prefix value: W, R, X, B. -/
def s32RexBits (n : Nat) : Nat × Nat × Nat × Nat :=
  (n / 8 % 2, n / 4 % 2, n / 2 % 2, n % 2)

/-- Canonical scalar-single register bytes: optional REX, prefix, 0F,
    opcode, ModRM mod=11. -/
def s32EncodeRR (vor op : Nat) (dstCode srcCode : Nat) (w r b : Nat) :
    List Byte :=
  s32Rex w r b
    ++ [natByte vor, natByte 15, natByte op, modrmReg dstCode srcCode]

/-- Canonical scalar-single load bytes: optional REX, prefix, 0F,
    opcode, ModRM mod=10, disp32 (SIB 36 iff the low base code is 4). -/
def s32EncodeLade (vor op : Nat) (dstCode : Nat) (base : Register)
    (d : BitVec 32) (w r b : Nat) : List Byte :=
  let head := s32Rex w r b
    ++ [natByte vor, natByte 15, natByte op, modrmMem dstCode (regLow base)]
  if regLow base == 4 then head ++ natByte 36 :: leBytes32 d
  else head ++ leBytes32 d

/-- ADDSS register bytes: F3 0F 58 /r. -/
def s32EncodeAddssRR (dst src : XmmReg) : List Byte :=
  s32EncodeRR 243 88 (fpXmmCode dst) (fpXmmCode src) 0
    (fpXmmHoch dst) (fpXmmHoch src)

/-- SUBSS register bytes: F3 0F 5C /r. -/
def s32EncodeSubssRR (dst src : XmmReg) : List Byte :=
  s32EncodeRR 243 92 (fpXmmCode dst) (fpXmmCode src) 0
    (fpXmmHoch dst) (fpXmmHoch src)

/-- MULSS register bytes: F3 0F 59 /r. -/
def s32EncodeMulssRR (dst src : XmmReg) : List Byte :=
  s32EncodeRR 243 89 (fpXmmCode dst) (fpXmmCode src) 0
    (fpXmmHoch dst) (fpXmmHoch src)

/-- DIVSS register bytes: F3 0F 5E /r. -/
def s32EncodeDivssRR (dst src : XmmReg) : List Byte :=
  s32EncodeRR 243 94 (fpXmmCode dst) (fpXmmCode src) 0
    (fpXmmHoch dst) (fpXmmHoch src)

/-- ADDSS memory bytes: F3 0F 58 /r, mod=10, disp32. -/
def s32EncodeAddssRM (dst : XmmReg) (base : Register)
    (d : BitVec 32) : List Byte :=
  s32EncodeLade 243 88 (fpXmmCode dst) base d 0
    (fpXmmHoch dst) (regHigh base)

/-- MOVSS register-merge bytes: F3 0F 10 /r, mod=11. -/
def s32EncodeMovssRR (dst src : XmmReg) : List Byte :=
  s32EncodeRR 243 16 (fpXmmCode dst) (fpXmmCode src) 0
    (fpXmmHoch dst) (fpXmmHoch src)

/-- MOVSS load bytes: F3 0F 10 /r, mod=10, disp32. -/
def s32EncodeMovssLade (dst : XmmReg) (base : Register)
    (d : BitVec 32) : List Byte :=
  s32EncodeLade 243 16 (fpXmmCode dst) base d 0
    (fpXmmHoch dst) (regHigh base)

/-- MOVSS store bytes: F3 0F 11 /r, mod=10, disp32. -/
def s32EncodeMovssSpeichere (base : Register) (src : XmmReg)
    (d : BitVec 32) : List Byte :=
  s32EncodeLade 243 17 (fpXmmCode src) base d 0
    (fpXmmHoch src) (regHigh base)

/-- UCOMISS register bytes: 0F 2E /r, no prefix. -/
def s32EncodeUcomissRR (lhs rhs : XmmReg) : List Byte :=
  s32Rex 0 (fpXmmHoch lhs) (fpXmmHoch rhs)
    ++ [natByte 15, natByte 46, modrmReg (fpXmmCode lhs) (fpXmmCode rhs)]

/-- UCOMISS memory bytes: 0F 2E /r, mod=10, disp32, no prefix. -/
def s32EncodeUcomissRM (lhs : XmmReg) (base : Register)
    (d : BitVec 32) : List Byte :=
  let head := s32Rex 0 (fpXmmHoch lhs) (regHigh base)
    ++ [natByte 15, natByte 46, modrmMem (fpXmmCode lhs) (regLow base)]
  if regLow base == 4 then head ++ natByte 36 :: leBytes32 d
  else head ++ leBytes32 d

/-- CVTSS2SD register bytes: F3 0F 5A /r. -/
def s32EncodeCvtss2sdRR (dst src : XmmReg) : List Byte :=
  s32EncodeRR 243 90 (fpXmmCode dst) (fpXmmCode src) 0
    (fpXmmHoch dst) (fpXmmHoch src)

/-- CVTSD2SS register bytes: F2 0F 5A /r. -/
def s32EncodeCvtsd2ssRR (dst src : XmmReg) : List Byte :=
  s32EncodeRR 242 90 (fpXmmCode dst) (fpXmmCode src) 0
    (fpXmmHoch dst) (fpXmmHoch src)

/-- CVTSI2SS bytes: F3 0F 2A /r; REX.W selects the 64-bit source. -/
def s32EncodeCvtsi2ss (dst : XmmReg) (src : Register)
    (is64 : Bool) : List Byte :=
  s32EncodeRR 243 42 (fpXmmCode dst) (regCode src)
    (if is64 then 1 else 0) (fpXmmHoch dst) (regHigh src)

/-- CVTTSS2SI bytes: F3 0F 2C /r (reg=GPR destination);
    REX.W selects the 64-bit destination. -/
def s32EncodeCvttss2si (dst : Register) (src : XmmReg)
    (is64 : Bool) : List Byte :=
  s32EncodeRR 243 44 (regCode dst) (fpXmmCode src)
    (if is64 then 1 else 0) (regHigh dst) (fpXmmHoch src)

/-- Register-direct decode after prefix, escape, opcode and ModRM.
    `fam` is 0 for F3, 1 for F2, 2 for no prefix; `rex` records whether
    a REX byte was consumed (the decoded length). The opcode row selects
    the operand kinds first (a 4-bit code decodes as both XMM and GPR,
    so kind selection by opcode is load-bearing, not cosmetic). -/
def s32DecodeReg (w rBit bBit fam op reg rm : Nat) (rex : Bool)
    (rest : List Byte) : Option (S32Decodiert × List Byte) :=
  let len := (if rex then 1 else 0) + (if fam == 2 then 3 else 4)
  match fam, op with
  | 0, 42 =>
    match codeXmmVoll (rBit * 8 + reg), codeReg (bBit * 8 + rm) with
    | some xd, some gs => some (⟨.cvtsi2ss xd gs (w == 1), len⟩, rest)
    | _, _ => none
  | 0, 44 =>
    match codeReg (rBit * 8 + reg), codeXmmVoll (bBit * 8 + rm) with
    | some gd, some xs => some (⟨.cvttss2si gd xs (w == 1), len⟩, rest)
    | _, _ => none
  | _, _ =>
    match codeXmmVoll (rBit * 8 + reg), codeXmmVoll (bBit * 8 + rm) with
    | some xd, some xs =>
      match fam, op with
      | 0, 16 =>
        if w == 0 then some (⟨.movssRR xd xs, len⟩, rest) else none
      | 0, 88 =>
        if w == 0 then some (⟨.addssRR xd xs, len⟩, rest) else none
      | 0, 92 =>
        if w == 0 then some (⟨.subssRR xd xs, len⟩, rest) else none
      | 0, 89 =>
        if w == 0 then some (⟨.mulssRR xd xs, len⟩, rest) else none
      | 0, 94 =>
        if w == 0 then some (⟨.divssRR xd xs, len⟩, rest) else none
      | 0, 90 =>
        if w == 0 then some (⟨.cvtss2sdRR xd xs, len⟩, rest) else none
      | 1, 90 =>
        if w == 0 then some (⟨.cvtsd2ssRR xd xs, len⟩, rest) else none
      | 2, 46 =>
        if w == 0 then some (⟨.ucomissRR xd xs, len⟩, rest) else none
      | _, _ => none
    | _, _ => none

/-- One memory row: the decoded form with its consumed length. -/
def s32DecodeMemZeile (w fam op : Nat) (len : Nat)
    (xd : XmmReg) (base : Register) (d : BitVec 32)
    (rest : List Byte) : Option (S32Decodiert × List Byte) :=
  match fam, op with
  | 0, 16 =>
    if w == 0 then some (⟨.movssLade xd base d, len⟩, rest) else none
  | 0, 17 =>
    if w == 0 then some (⟨.movssSpeichere base xd d, len⟩, rest) else none
  | 0, 88 =>
    if w == 0 then some (⟨.addssRM xd base d, len⟩, rest) else none
  | 0, 92 =>
    if w == 0 then some (⟨.subssRM xd base d, len⟩, rest) else none
  | 0, 89 =>
    if w == 0 then some (⟨.mulssRM xd base d, len⟩, rest) else none
  | 0, 94 =>
    if w == 0 then some (⟨.divssRM xd base d, len⟩, rest) else none
  | 2, 46 =>
    if w == 0 then some (⟨.ucomissRM xd base d, len⟩, rest) else none
  | _, _ => none

/-- Memory decode after ModRM mod=10: SIB 36 iff the low base code is 4
    (the pilot rule); conversions have no memory row here. -/
def s32DecodeMem (w rBit bBit fam op reg rm : Nat) (rex : Bool) :
    List Byte → Option (S32Decodiert × List Byte)
  | [] => none
  | bytes =>
    let basis := (if rex then 1 else 0) + (if fam == 2 then 7 else 8)
    if rm == 4 then
      match bytes with
      | [] => none
      | sib :: rest2 =>
        if byteNat sib == 36 then
          match parseLe32 rest2 with
          | none => none
          | some (d, rest3) =>
            match codeXmmVoll (rBit * 8 + reg),
              codeReg (bBit * 8 + rm) with
            | some xd, some base =>
              s32DecodeMemZeile w fam op (basis + 1) xd base d rest3
            | _, _ => none
        else none
    else
      match parseLe32 bytes with
      | none => none
      | some (d, rest3) =>
        match codeXmmVoll (rBit * 8 + reg),
          codeReg (bBit * 8 + rm) with
        | some xd, some base =>
          s32DecodeMemZeile w fam op basis xd base d rest3
        | _, _ => none

/-- F3-prefix dispatch: moves, arithmetic, F3 conversions, int rows. -/
def s32DecodeF3 (w rBit bBit op : Nat) (rex : Bool) :
    List Byte → Option (S32Decodiert × List Byte)
  | [] => none
  | m :: rest =>
    let reg := byteNat m / 8 % 8
    let rm := byteNat m % 8
    match byteNat m / 64 with
    | 3 => s32DecodeReg w rBit bBit 0 op reg rm rex rest
    | 2 => s32DecodeMem w rBit bBit 0 op reg rm rex rest
    | _ => none

/-- F2-prefix dispatch: only CVTSD2SS, register-direct only. -/
def s32DecodeF2 (w rBit bBit op : Nat) (rex : Bool) :
    List Byte → Option (S32Decodiert × List Byte)
  | [] => none
  | m :: rest =>
    let reg := byteNat m / 8 % 8
    let rm := byteNat m % 8
    match byteNat m / 64 with
    | 3 => s32DecodeReg w rBit bBit 1 op reg rm rex rest
    | _ => none

/-- No-prefix dispatch: only UCOMISS, register or memory. -/
def s32DecodeNP (w rBit bBit op : Nat) (rex : Bool) :
    List Byte → Option (S32Decodiert × List Byte)
  | [] => none
  | m :: rest =>
    let reg := byteNat m / 8 % 8
    let rm := byteNat m % 8
    match byteNat m / 64 with
    | 3 => s32DecodeReg w rBit bBit 2 op reg rm rex rest
    | 2 => s32DecodeMem w rBit bBit 2 op reg rm rex rest
    | _ => none

/-- Prefix dispatcher after an optional REX byte. -/
def s32NachRex (w r b : Nat) (rex : Bool) :
    List Byte → Option (S32Decodiert × List Byte)
  | [] => none
  | p :: rest =>
    if byteNat p == 243 then
      match rest with
      | [] => none
      | e :: rest2 =>
        if byteNat e == 15 then
          match rest2 with
          | [] => none
          | op :: rest3 => s32DecodeF3 w r b (byteNat op) rex rest3
        else none
    else if byteNat p == 242 then
      match rest with
      | [] => none
      | e :: rest2 =>
        if byteNat e == 15 then
          match rest2 with
          | [] => none
          | op :: rest3 =>
            if byteNat op == 90 then
              s32DecodeF2 w r b (byteNat op) rex rest3
            else none
        else none
    else if byteNat p == 15 then
      match rest with
      | [] => none
      | op :: rest2 =>
        if byteNat op == 46 then s32DecodeNP w r b (byteNat op) rex rest2
        else none
    else none

/-- Decode the first canonical scalar-single instruction from actual
    bytes, returning it with its consumed length and the rest.
    An optional REX prefix selects high registers (R/B), the integer
    width (W), and refuses a set X bit. -/
def s32Decode : List Byte → Option (S32Decodiert × List Byte)
  | [] => none
  | b :: rest =>
    if s32IstRex b then
      let (w, r, x, bb) := s32RexBits (byteNat b)
      if x == 1 then none
      else s32NachRex w r bb true rest
    else s32NachRex 0 0 0 false (b :: rest)

/-! ## 8. Round trips, REX selection, and refusals.

  Decoding inverts encoding on all sixteen XMM registers (high
  registers only decode through their REX bit); the decoded length is
  the consumed prefix length. Cross-width bytes (F2 arithmetic/MOVSD),
  wrong prefixes, set REX.W on non-integer rows, set REX.X,
  non-canonical ModRM modes and truncations refuse explicitly. -/

/-- Encode/decode round trip for ADDSS register, every XMM pair. -/
theorem s32Roundtrip_addssRR (dst src : XmmReg) (suffix : List Byte) :
    s32Decode (s32EncodeAddssRR dst src ++ suffix) =
      some (⟨.addssRR dst src, (s32EncodeAddssRR dst src).length⟩,
        suffix) := by
  cases dst <;> cases src <;> rfl

/-- Encode/decode round trip for SUBSS register. -/
theorem s32Roundtrip_subssRR (dst src : XmmReg) (suffix : List Byte) :
    s32Decode (s32EncodeSubssRR dst src ++ suffix) =
      some (⟨.subssRR dst src, (s32EncodeSubssRR dst src).length⟩,
        suffix) := by
  cases dst <;> cases src <;> rfl

/-- Encode/decode round trip for MULSS register. -/
theorem s32Roundtrip_mulssRR (dst src : XmmReg) (suffix : List Byte) :
    s32Decode (s32EncodeMulssRR dst src ++ suffix) =
      some (⟨.mulssRR dst src, (s32EncodeMulssRR dst src).length⟩,
        suffix) := by
  cases dst <;> cases src <;> rfl

/-- Encode/decode round trip for DIVSS register. -/
theorem s32Roundtrip_divssRR (dst src : XmmReg) (suffix : List Byte) :
    s32Decode (s32EncodeDivssRR dst src ++ suffix) =
      some (⟨.divssRR dst src, (s32EncodeDivssRR dst src).length⟩,
        suffix) := by
  cases dst <;> cases src <;> rfl

/-- Encode/decode round trip for MOVSS register merge. -/
theorem s32Roundtrip_movssRR (dst src : XmmReg) (suffix : List Byte) :
    s32Decode (s32EncodeMovssRR dst src ++ suffix) =
      some (⟨.movssRR dst src, (s32EncodeMovssRR dst src).length⟩,
        suffix) := by
  cases dst <;> cases src <;> rfl

/-- Encode/decode round trip for UCOMISS register. -/
theorem s32Roundtrip_ucomissRR (lhs rhs : XmmReg)
    (suffix : List Byte) :
    s32Decode (s32EncodeUcomissRR lhs rhs ++ suffix) =
      some (⟨.ucomissRR lhs rhs, (s32EncodeUcomissRR lhs rhs).length⟩,
        suffix) := by
  cases lhs <;> cases rhs <;> rfl

/-- Encode/decode round trip for CVTSS2SD register. -/
theorem s32Roundtrip_cvtss2sdRR (dst src : XmmReg)
    (suffix : List Byte) :
    s32Decode (s32EncodeCvtss2sdRR dst src ++ suffix) =
      some (⟨.cvtss2sdRR dst src, (s32EncodeCvtss2sdRR dst src).length⟩,
        suffix) := by
  cases dst <;> cases src <;> rfl

/-- Encode/decode round trip for CVTSD2SS register. -/
theorem s32Roundtrip_cvtsd2ssRR (dst src : XmmReg)
    (suffix : List Byte) :
    s32Decode (s32EncodeCvtsd2ssRR dst src ++ suffix) =
      some (⟨.cvtsd2ssRR dst src, (s32EncodeCvtsd2ssRR dst src).length⟩,
        suffix) := by
  cases dst <;> cases src <;> rfl

/-- Encode/decode round trip for CVTSI2SS, both widths. -/
theorem s32Roundtrip_cvtsi2ss (dst : XmmReg) (src : Register)
    (is64 : Bool) (suffix : List Byte) :
    s32Decode (s32EncodeCvtsi2ss dst src is64 ++ suffix) =
      some (⟨.cvtsi2ss dst src is64,
        (s32EncodeCvtsi2ss dst src is64).length⟩, suffix) := by
  cases dst <;> cases src <;> cases is64 <;> rfl

/-- Encode/decode round trip for CVTTSS2SI, both widths. -/
theorem s32Roundtrip_cvttss2si (dst : Register) (src : XmmReg)
    (is64 : Bool) (suffix : List Byte) :
    s32Decode (s32EncodeCvttss2si dst src is64 ++ suffix) =
      some (⟨.cvttss2si dst src is64,
        (s32EncodeCvttss2si dst src is64).length⟩, suffix) := by
  cases dst <;> cases src <;> cases is64 <;> rfl

/-- HIGH-XMM REX SELECTION: `REX.R+B` (`0x45`) selects xmm8/xmm9. -/
theorem s32_rex_waehlt_hoch_addss :
    s32Decode [natByte 69, natByte 243, natByte 15, natByte 88,
      modrmReg 0 1]
      = some (⟨.addssRR .xmm8 .xmm9, 5⟩, []) := by
  decide

/-- REX.W selects the 64-bit integer source on CVTSI2SS. -/
theorem s32_rex_w_waehlt_64_cvtsi :
    s32Decode [natByte 72, natByte 243, natByte 15, natByte 42,
      modrmReg 0 1]
      = some (⟨.cvtsi2ss .xmm0 .rcx true, 5⟩, []) := by
  decide

/-- REX.W selects the 64-bit destination on CVTTSS2SI. -/
theorem s32_rex_w_waehlt_64_cvtt :
    s32Decode [natByte 72, natByte 243, natByte 15, natByte 44,
      modrmReg 0 1]
      = some (⟨.cvttss2si .rax .xmm1 true, 5⟩, []) := by
  decide

/-- WRONG WIDTH: F2-prefix arithmetic (ADDSD bytes) is refused. -/
theorem s32Decode_f2_arith_verweigert :
    s32Decode [natByte 242, natByte 15, natByte 88, modrmReg 0 1]
      = none := by
  decide

/-- WRONG WIDTH: F2-prefix moves (MOVSD bytes) are refused. -/
theorem s32Decode_movsd_verweigert :
    s32Decode [natByte 242, natByte 15, natByte 16, modrmReg 0 1]
      = none := by
  decide

/-- WRONG PREFIX: F3 on the compare opcode is refused. -/
theorem s32Decode_ucomiss_mit_f3_verweigert :
    s32Decode [natByte 243, natByte 15, natByte 46, modrmReg 0 1]
      = none := by
  decide

/-- MISSING PREFIX: prefix-less arithmetic bytes are refused. -/
theorem s32Decode_addss_ohne_praefix_verweigert :
    s32Decode [natByte 15, natByte 88, modrmReg 0 1] = none := by
  decide

/-- REX.W on an arithmetic row is non-canonical and refused. -/
theorem s32Decode_w_arith_verweigert :
    s32Decode [natByte 72, natByte 243, natByte 15, natByte 88,
      modrmReg 0 1] = none := by
  decide

/-- A set REX.X bit is outside the subset and refused. -/
theorem s32Decode_x_verweigert :
    s32Decode [natByte 66, natByte 243, natByte 15, natByte 88,
      modrmReg 0 1] = none := by
  decide

/-- A lone F3 prefix refuses. -/
theorem s32Decode_abgeschnitten_praefix :
    s32Decode [natByte 243] = none := by
  decide

/-- F3 0F without opcode and ModRM refuses. -/
theorem s32Decode_abgeschnitten_opcode :
    s32Decode [natByte 243, natByte 15] = none := by
  decide

/-- F3 0F 58 without ModRM refuses. -/
theorem s32Decode_abgeschnitten_modrm :
    s32Decode [natByte 243, natByte 15, natByte 88] = none := by
  decide

/-- ModRM mod=1 is non-canonical and refuses. -/
theorem s32Decode_modEins_verweigert :
    s32Decode [natByte 243, natByte 15, natByte 88, natByte 64]
      = none := by
  decide

/-- Opcode 11 with a register ModRM (non-canonical register store)
    refuses. -/
theorem s32Decode_speichereRegister_verweigert :
    s32Decode [natByte 243, natByte 15, natByte 17, modrmReg 0 1]
      = none := by
  decide

/-- A 66 prefix on the compare opcode refuses. -/
theorem s32Decode_sechsundsechzig_verweigert :
    s32Decode [natByte 102, natByte 15, natByte 46, modrmReg 0 1]
      = none := by
  decide

/-- CONTROL-STATE MUTATION: an FTZ word closes every form. -/
theorem s32Schritt_ftz_verweigert (d : S32Decodiert) (t : FpZustand)
    (hok : laengeOk d.laenge = true) :
    s32Schritt d ⟨t.kern, t.xmm, ⟨0x9F80⟩⟩ = none := by
  have h : s32Eintritt (⟨0x9F80⟩ : FPKontext) = false :=
    mxcsr_ftz_verweigert
  exact s32Schritt_profil_verweigert d _ hok h

/-- STICKY FLAGS DO NOT CLOSE ADMISSION: status observed, not trapped. -/
theorem s32Schritt_sticky_offen :
    s32Eintritt (⟨0x1FBF⟩ : FPKontext) = true := by
  unfold s32Eintritt
  exact (mxcsr_sticky_egal_gueltig).1

set_option maxHeartbeats 4000000 in
/-- Encode/decode round trip for the MOVSS load, both SIB shapes. -/
theorem s32Roundtrip_movssLade (dst : XmmReg) (base : Register)
    (d : BitVec 32) (suffix : List Byte) :
    s32Decode (s32EncodeMovssLade dst base d ++ suffix) =
      some (⟨.movssLade dst base d,
        (s32EncodeMovssLade dst base d).length⟩, suffix) := by
  cases dst <;> cases base <;>
    simp_all [s32EncodeMovssLade, s32EncodeLade, s32Decode, s32NachRex,
      s32DecodeF3, s32DecodeMem, s32DecodeMemZeile, codeXmmVoll, codeReg,
      fpXmmCode, fpXmmHoch, regCode, regHigh, regLow, modrmMem, leBytes32,
      parseLe32_cons, s32Rex, s32IstRex, s32RexBits, parseLe32_cons]

set_option maxHeartbeats 4000000 in
/-- Encode/decode round trip for the MOVSS store, both SIB shapes. -/
theorem s32Roundtrip_movssSpeichere (base : Register) (src : XmmReg)
    (d : BitVec 32) (suffix : List Byte) :
    s32Decode (s32EncodeMovssSpeichere base src d ++ suffix) =
      some (⟨.movssSpeichere base src d,
        (s32EncodeMovssSpeichere base src d).length⟩, suffix) := by
  cases base <;> cases src <;>
    simp_all [s32EncodeMovssSpeichere, s32EncodeLade, s32Decode,
      s32NachRex, s32DecodeF3, s32DecodeMem, s32DecodeMemZeile,
      codeXmmVoll, codeReg, fpXmmCode, fpXmmHoch, regCode, regHigh, regLow,
      modrmMem, leBytes32, parseLe32_cons, s32Rex, s32IstRex,
      s32RexBits, parseLe32_cons]

set_option maxHeartbeats 4000000 in
/-- Encode/decode round trip for ADDSS memory source, both SIB shapes. -/
theorem s32Roundtrip_addssRM (dst : XmmReg) (base : Register)
    (d : BitVec 32) (suffix : List Byte) :
    s32Decode (s32EncodeAddssRM dst base d ++ suffix) =
      some (⟨.addssRM dst base d,
        (s32EncodeAddssRM dst base d).length⟩, suffix) := by
  cases dst <;> cases base <;>
    simp_all [s32EncodeAddssRM, s32EncodeLade, s32Decode, s32NachRex,
      s32DecodeF3, s32DecodeMem, s32DecodeMemZeile, codeXmmVoll, codeReg,
      fpXmmCode, fpXmmHoch, regCode, regHigh, regLow, modrmMem, leBytes32,
      parseLe32_cons, s32Rex, s32IstRex, s32RexBits, parseLe32_cons]

set_option maxHeartbeats 4000000 in
/-- Encode/decode round trip for UCOMISS memory source. -/
theorem s32Roundtrip_ucomissRM (lhs : XmmReg) (base : Register)
    (d : BitVec 32) (suffix : List Byte) :
    s32Decode (s32EncodeUcomissRM lhs base d ++ suffix) =
      some (⟨.ucomissRM lhs base d,
        (s32EncodeUcomissRM lhs base d).length⟩, suffix) := by
  cases lhs <;> cases base <;>
    simp_all [s32EncodeUcomissRM, s32Decode, s32NachRex, s32DecodeNP,
      s32DecodeMem, s32DecodeMemZeile, codeXmmVoll, codeReg, fpXmmCode,
      fpXmmHoch, regCode, regHigh, regLow, modrmMem, leBytes32,
      parseLe32_cons, s32Rex, s32IstRex, s32RexBits, parseLe32_cons]

/- CUTS (interim):
   §§0-8 done. OPEN next: the fetched byte step, witnesses.
-/

#print axioms s32Roundtrip_addssRR
#print axioms s32_rex_waehlt_hoch_addss

end Gabbro.Grammatik.X86
