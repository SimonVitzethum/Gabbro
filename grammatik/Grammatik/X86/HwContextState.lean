/-
  File:      Grammatik/X86/HwContextState.lean
  Subject:   Extended FP/vector context state across interrupts and
             context switches on the coherent multicore machine.

  Lane 1247: model FXSAVE/FXRSTOR (legacy 512-byte area: MXCSR/XMM0-15
  plus preserved zero bytes; x87 state has no model in this tree and
  stays an opaque preserved region) and XSAVE/XRSTOR for the
  XCR0-enabled components, as footprint-checked memory accesses on the
  coherent machine (`HwMaschine`/`HwSchritt`, HardwareExecution.lean
  section 11). Reuses `issueByte`/`loadByte`/`flushKern` (TSO),
  `mxcsrReserviertFrei`/`ldmxcsrArchOk` (FpControlHardwareForms),
  `xcr0SseBereit`/`Xcr0Bild` (VectorHardwareProfile) and
  `asyncSchritt`/`asyncMasch` (HwInterrupts) unchanged, never copied.
-/
import Grammatik.X86.HardwareExecution
import Grammatik.X86.HwInterrupts
import Grammatik.X86.FpControlHardwareForms
import Grammatik.X86.VectorHardwareProfile

namespace Gabbro.Grammatik.X86

/-- Snapshot of one core's saved FP/vector state: control word plus
    the full XMM file. x87 state has no model here (opaque region). -/
structure CtxBild where
  mxcsr : MXCSR
  xmm : XmmDatei
  deriving Inhabited

/-! ## 1. Legacy area layout (SDM 325462-093US Vol.2A FXSAVE64 Table 1-42,
    clone-local extract offsets 56665-56698; provenance only).

    Selected 64-bit map: MXCSR at bytes 24-27, MXCSR_MASK at 28-31,
    x87 data at 32-159, XMM0-15 at 160-415 (16 bytes each), reserved
    at 416-463, software-available at 464-511 (the processor never
    writes them: extract offset 56486). Modelled footprint below is
    exactly bytes 24-27 (MXCSR) and 160-415 (XMM0-15); everything else
    is outside the footprint (see CUTS). Alignment: 16-byte operand
    for FXSAVE/FXRSTOR (misaligned destination operand raises #GP:
    offset 56533), 64-byte operand for XSAVE/XRSTOR (offset 15150). -/

/-- FXSAVE area size in bytes (the legacy region). -/
def fxLaenge : Nat := 512

/-- FXSAVE/FXRSTOR operand alignment: 16 bytes. -/
def fxAusricht : Nat := 16

/-- XSAVE/XRSTOR operand alignment: 64 bytes. -/
def xAusricht : Nat := 64

/-- 16-byte alignment check (FXSAVE/FXRSTOR fault gate). -/
def fxAusgerichtet (a : Adresse) : Bool := decide (a.toNat % 16 = 0)

/-- 64-byte alignment check (XSAVE/XRSTOR fault gate). -/
def xAusgerichtet (a : Adresse) : Bool := decide (a.toNat % 64 = 0)

/-- XMM register number in the area (XMM0 at 160, stride 16). -/
def xmmIdx : XmmReg → Nat
  | .xmm0 => 0 | .xmm1 => 1 | .xmm2 => 2 | .xmm3 => 3
  | .xmm4 => 4 | .xmm5 => 5 | .xmm6 => 6 | .xmm7 => 7
  | .xmm8 => 8 | .xmm9 => 9 | .xmm10 => 10 | .xmm11 => 11
  | .xmm12 => 12 | .xmm13 => 13 | .xmm14 => 14 | .xmm15 => 15

/-- Inverse lookup: area slot number to register, if any. -/
def xmmVonIdx : Nat → Option XmmReg
  | 0 => some .xmm0 | 1 => some .xmm1 | 2 => some .xmm2 | 3 => some .xmm3
  | 4 => some .xmm4 | 5 => some .xmm5 | 6 => some .xmm6 | 7 => some .xmm7
  | 8 => some .xmm8 | 9 => some .xmm9 | 10 => some .xmm10 | 11 => some .xmm11
  | 12 => some .xmm12 | 13 => some .xmm13 | 14 => some .xmm14 | 15 => some .xmm15
  | _ => none

/-- Lookup inverts numbering on every register. -/
theorem xmmVonIdx_idx (r : XmmReg) : xmmVonIdx (xmmIdx r) = some r := by
  cases r <;> rfl

/-- Every register number fits the area (16 slots). -/
theorem xmmIdx_klein (r : XmmReg) : xmmIdx r < 16 := by
  cases r <;> decide

/-- One MXCSR image byte: little-endian byte `i` of the zero-extended
    control word (`wortByte`, reused unchanged). -/
def mxcsrByte (w : MXCSR) (i : Nat) : Byte :=
  wortByte (BitVec.ofNat 64 w.toNat) i

/-- Reassemble the control word from four little-endian image bytes. -/
def mxcsrAusBytes (f : Nat → Byte) : MXCSR :=
  BitVec.ofNat 32 ((f 0).toNat + (f 1).toNat * 256 +
    (f 2).toNat * 65536 + (f 3).toNat * 16777216)

/-- MXCSR image round trip (same shape as `bytesWort_wortByte`). -/
theorem mxcsr_rundlauf (w : MXCSR) :
    mxcsrAusBytes (mxcsrByte w) = w := by
  apply BitVec.eq_of_toNat_eq
  unfold mxcsrAusBytes mxcsrByte wortByte
  simp only [BitVec.toNat_ofNat]
  have hw := w.isLt
  omega

/-- Reassembly depends only on the four footprint bytes. -/
theorem mxcsrAusBytes_kongr (f g : Nat → Byte)
    (h : ∀ i, i < 4 → f i = g i) :
    mxcsrAusBytes f = mxcsrAusBytes g := by
  unfold mxcsrAusBytes
  have h0 := h 0 (by decide)
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  rw [h0, h1, h2, h3]

/-- The 512-byte area image of a context: MXCSR at 24-27, XMM slot
    bytes at 160-415 (low half then high half via `vLo`/`vHi`,
    reassembled with `vecJoin`); every other offset reads zero
    (x87/mask/reserved/available regions are outside the footprint). -/
def ctxByte (k : FPKontext) (x : XmmDatei) : Nat → Byte := fun i =>
  if i < 24 then BitVec.ofNat 8 0
  else if i < 28 then mxcsrByte k.mxcsr (i - 24)
  else if i < 160 then BitVec.ofNat 8 0
  else if i < 416 then
    match xmmVonIdx ((i - 160) / 16) with
    | some r =>
      if (i - 160) % 16 < 8 then wortByte (vLo (x r)) ((i - 160) % 16)
      else wortByte (vHi (x r)) ((i - 160) % 16 - 8)
    | none => BitVec.ofNat 8 0
  else BitVec.ofNat 8 0

/-- Image at an MXCSR footprint offset is the control byte. -/
theorem ctxByte_mxcsr (k : FPKontext) (x : XmmDatei) (j : Nat)
    (hj : j < 4) :
    ctxByte k x (24 + j) = mxcsrByte k.mxcsr j := by
  unfold ctxByte
  have e1 : ¬ (24 + j < 24) := by omega
  have e2 : 24 + j < 28 := by omega
  have e3 : 24 + j - 24 = j := by omega
  rw [if_neg e1, if_pos e2, e3]

/-- Image at an XMM footprint offset, low half. -/
theorem ctxByte_xmm_lo (k : FPKontext) (x : XmmDatei) (r : XmmReg)
    (j : Nat) (hj : j < 8) :
    ctxByte k x (160 + 16 * xmmIdx r + j) = wortByte (vLo (x r)) j := by
  have hn := xmmIdx_klein r
  have hj16 : j < 16 := by omega
  unfold ctxByte
  have e1 : ¬ (160 + 16 * xmmIdx r + j < 24) := by omega
  have e2 : ¬ (160 + 16 * xmmIdx r + j < 28) := by omega
  have e3 : ¬ (160 + 16 * xmmIdx r + j < 160) := by omega
  have e4 : 160 + 16 * xmmIdx r + j < 416 := by omega
  have e5 : (160 + 16 * xmmIdx r + j - 160) / 16 = xmmIdx r := by omega
  have e6 : (160 + 16 * xmmIdx r + j - 160) % 16 = j := by omega
  rw [if_neg e1, if_neg e2, if_neg e3, if_pos e4, e5, e6]
  simp [xmmVonIdx_idx, hj]

/-- Image at an XMM footprint offset, high half. -/
theorem ctxByte_xmm_hi (k : FPKontext) (x : XmmDatei) (r : XmmReg)
    (j : Nat) (hj : j < 8) :
    ctxByte k x (168 + 16 * xmmIdx r + j) = wortByte (vHi (x r)) j := by
  have e : 168 + 16 * xmmIdx r + j = 160 + 16 * xmmIdx r + (8 + j) := by
    omega
  have hn := xmmIdx_klein r
  rw [e]
  unfold ctxByte
  have e1 : ¬ (160 + 16 * xmmIdx r + (8 + j) < 24) := by omega
  have e2 : ¬ (160 + 16 * xmmIdx r + (8 + j) < 28) := by omega
  have e3 : ¬ (160 + 16 * xmmIdx r + (8 + j) < 160) := by omega
  have e4 : 160 + 16 * xmmIdx r + (8 + j) < 416 := by omega
  have e5 : (160 + 16 * xmmIdx r + (8 + j) - 160) / 16 = xmmIdx r := by
    omega
  have e6 : (160 + 16 * xmmIdx r + (8 + j) - 160) % 16 = 8 + j := by omega
  have e7 : ¬ (8 + j < 8) := by omega
  have e8 : 8 + j - 8 = j := by omega
  rw [if_neg e1, if_neg e2, if_neg e3, if_pos e4, e5, e6]
  simp [xmmVonIdx_idx, e7, e8]

/-- Decode an area image back to a context: MXCSR from 24-27, each
    XMM from its 16-byte slot (low half then high half). -/
def fxDekodiere (f : Nat → Byte) : CtxBild :=
  ⟨mxcsrAusBytes (fun i => f (24 + i)),
   fun r => vecJoin
     (bytesWort (fun j : Fin 8 => f (160 + 16 * xmmIdx r + j.val)))
     (bytesWort (fun j : Fin 8 => f (168 + 16 * xmmIdx r + j.val)))⟩

/-- PURE IDENTITY: decoding the saved image recovers the control word
    and every XMM register. -/
theorem ctxRundlauf_pur (k : FPKontext) (x : XmmDatei) :
    (fxDekodiere (ctxByte k x)).mxcsr = k.mxcsr ∧
      ∀ r : XmmReg, (fxDekodiere (ctxByte k x)).xmm r = x r := by
  refine ⟨?_, ?_⟩
  · unfold fxDekodiere
    simp only
    have h := mxcsrAusBytes_kongr _ _
      (fun i hi => ctxByte_mxcsr k x i hi)
    rw [h]
    exact mxcsr_rundlauf k.mxcsr
  · intro r
    unfold fxDekodiere
    simp only
    have hn := xmmIdx_klein r
    have hlo : (fun j : Fin 8 => ctxByte k x (160 + 16 * xmmIdx r + j.val)) =
        (fun j : Fin 8 => wortByte (vLo (x r)) j.val) := by
      funext j
      exact ctxByte_xmm_lo k x r j.val j.isLt
    have hhi : (fun j : Fin 8 => ctxByte k x (168 + 16 * xmmIdx r + j.val)) =
        (fun j : Fin 8 => wortByte (vHi (x r)) j.val) := by
      funext j
      exact ctxByte_xmm_hi k x r j.val j.isLt
    rw [hlo, hhi, bytesWort_wortByte, bytesWort_wortByte]
    exact vecJoin_split (x r)

end Gabbro.Grammatik.X86
