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

/- CUTS (interim):
   §§0-2 done. OPEN next: conversions, the S32 step, the REX codec,
   the fetched byte step, witnesses.
-/

#print axioms s32_eins_plus_zwei
#print axioms s32_stallt_bei_2hoch24

end Gabbro.Grammatik.X86
