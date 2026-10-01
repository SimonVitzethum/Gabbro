/-
  File:      Grammatik/X86/FloatExceptions.lean
  Subject:   Guarded binary64 divide exceptions: masked IEEE values, no traps.

  Lane 425: masked invalid/divide-by-zero produce model VALUES under a valid
  MXCSR context; a refused context refuses the lowering slot (none), not a
  hardware fault. Reuses Gleitkomma/Gleitprofil/Speicher, claims no hardware.
-/
import Grammatik.X86.Gleitprofil

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik.Gleitkomma

/-- Lowering guard: the owning context meets the accepted MXCSR profile. -/
def floatGuard (k : FPKontext) : Bool :=
  mxcsrGueltig k.mxcsr

/-- Guarded binary64 division: model value under a valid context, refusal
    (`none`) otherwise. IEEE masked exceptions are values, never traps. -/
def guardedDiv64 (k : FPKontext)
    (a b : Gleitkomma.GBits Gleitkomma.f64) :
    Option (Gleitkomma.GBits Gleitkomma.f64) :=
  if floatGuard k then some (fdiv64 a b) else none

/-- Valid context delivers the model value (premise used to take the branch). -/
theorem guardedDiv_gueltig (k : FPKontext)
    (a b : Gleitkomma.GBits Gleitkomma.f64)
    (h : floatGuard k = true) :
    guardedDiv64 k a b = some (fdiv64 a b) := by
  unfold guardedDiv64
  simp [h]

/-- Refused context refuses the slot (premise used to take the branch). -/
theorem guardedDiv_verweigert (k : FPKontext)
    (a b : Gleitkomma.GBits Gleitkomma.f64)
    (h : floatGuard k = false) :
    guardedDiv64 k a b = none := by
  unfold guardedDiv64
  simp [h]

/-- The reset context meets the guard: the lowering slot is open. -/
theorem guard_standard : floatGuard kontextReset = true :=
  kontextReset_gueltig

/-- Flush-to-zero context refuses the slot: no Annex-F claim there. -/
theorem guard_ftz_verweigert : floatGuard ⟨0x9F80⟩ = false := by
  unfold floatGuard
  exact mxcsr_ftz_verweigert

/-- Sticky flags set do not close the slot: status is observed, not trapped. -/
theorem guard_sticky_offen : floatGuard ⟨0x1FBF⟩ = true := by
  unfold floatGuard
  exact (mxcsr_sticky_egal_gueltig).1.symm ▸ kontextReset_gueltig

/-- Masked divide-by-zero is a VALUE: `1 / 0` classifies as infinity
    in the accepted binary64 source model (reused witness). -/
theorem divEinsNull_modell :
    Gleitkomma.klasse Gleitkomma.f64
      (fdiv64 (Gleitkomma.ofInt Gleitkomma.f64 1)
        (Gleitkomma.ofInt Gleitkomma.f64 0)) = .unendlich :=
  Gleitkomma.zeuge_einsDurchNull

/-- Masked invalid is a VALUE: `0 / 0` classifies as NaN
    in the accepted binary64 source model (reused witness). -/
theorem divNullNull_modell :
    Gleitkomma.klasse Gleitkomma.f64
      (fdiv64 (Gleitkomma.ofInt Gleitkomma.f64 0)
        (Gleitkomma.ofInt Gleitkomma.f64 0)) = .nan :=
  Gleitkomma.zeuge_nullDurchNull

/-- Guarded divide-by-zero under a valid context delivers the infinite
    model value: no trap, the slot yields `some`. -/
theorem guardedDiv_einsNull (k : FPKontext)
    (h : floatGuard k = true) :
    guardedDiv64 k (Gleitkomma.ofInt Gleitkomma.f64 1)
        (Gleitkomma.ofInt Gleitkomma.f64 0)
      = some (fdiv64 (Gleitkomma.ofInt Gleitkomma.f64 1)
        (Gleitkomma.ofInt Gleitkomma.f64 0)) :=
  guardedDiv_gueltig k _ _ h

/-- Guarded `0 / 0` under a valid context delivers the NaN model value. -/
theorem guardedDiv_nullNull (k : FPKontext)
    (h : floatGuard k = true) :
    guardedDiv64 k (Gleitkomma.ofInt Gleitkomma.f64 0)
        (Gleitkomma.ofInt Gleitkomma.f64 0)
      = some (fdiv64 (Gleitkomma.ofInt Gleitkomma.f64 0)
        (Gleitkomma.ofInt Gleitkomma.f64 0)) :=
  guardedDiv_gueltig k _ _ h

/-- The `1 / 3` model pattern is the accepted bit pattern
    (reused kernel witness over the source model). -/
theorem divDrittel_muster :
    muster64 (fdiv64 (Gleitkomma.ofInt Gleitkomma.f64 1)
      (Gleitkomma.ofInt Gleitkomma.f64 3))
      = BitVec.ofNat 64 0x3FD5555555555555 := by
  unfold muster64 fdiv64
  rw [Gleitkomma.zeuge_divDrittel]

/-- The guarded `1 / 3` bit pattern as a target word. -/
def divDrittelWort : Wort := BitVec.ofNat 64 0x3FD5555555555555

/-- The memory after writing the guarded `1 / 3` pattern at address zero. -/
def divDrittelSpeicherNach : Speicher :=
  { zeugenSpeicher with bytes := writeBytes zeugenSpeicher 0 divDrittelWort }

/-- Observation: the guarded `1 / 3` value reaches memory -- a nonzero
    pattern is written, reads back, and observably changes memory.
    The guard premise is USED to open the slot. -/
theorem guardedDiv_speicher (k : FPKontext)
    (h : floatGuard k = true) :
    ∃ (m m' : Speicher) (a : Adresse),
      guardedDiv64 k (Gleitkomma.ofInt Gleitkomma.f64 1)
          (Gleitkomma.ofInt Gleitkomma.f64 3)
        = some (fdiv64 (Gleitkomma.ofInt Gleitkomma.f64 1)
          (Gleitkomma.ofInt Gleitkomma.f64 3))
        ∧ (BitVec.ofNat 64 0x3FD5555555555555 : Wort) ≠ 0
        ∧ write64 m a (BitVec.ofNat 64 0x3FD5555555555555) = some m'
        ∧ read64 m' a = some (BitVec.ofNat 64 0x3FD5555555555555)
        ∧ m.bytes a ≠ m'.bytes a := by
  refine ⟨zeugenSpeicher, divDrittelSpeicherNach, 0,
    guardedDiv_gueltig k _ _ h, by decide, ?_, ?_, ?_⟩
  · unfold write64
    have hc : schreibbar8 zeugenSpeicher 0 = true := rfl
    rw [if_pos hc]
    rfl
  · have hwr : write64 zeugenSpeicher 0
          (BitVec.ofNat 64 0x3FD5555555555555)
        = some divDrittelSpeicherNach := by
      unfold write64
      have hc : schreibbar8 zeugenSpeicher 0 = true := rfl
      rw [if_pos hc]
      rfl
    have hrd : lesbar8 zeugenSpeicher 0 = true := rfl
    exact read64_nach_write64 zeugenSpeicher divDrittelSpeicherNach 0
      (BitVec.ofNat 64 0x3FD5555555555555) hwr hrd
  · have hhit := writeBytesN_hit zeugenSpeicher 0
      (BitVec.ofNat 64 0x3FD5555555555555) 8 0 (by decide) (by decide)
    rw [addrOff_null (0 : Adresse)] at hhit
    show (zeugenSpeicher.bytes 0)
      ≠ (writeBytesN zeugenSpeicher 0
        (BitVec.ofNat 64 0x3FD5555555555555) 8 0)
    rw [hhit]
    decide

/-- JOINT witness (valid side): the reset context, `1 / 3` operands and
    the memory round-trip hold TOGETHER -- guard, value and observation. -/
theorem guardedDiv_gueltig_zeuge :
    ∃ (k : FPKontext) (a b : Gleitkomma.GBits Gleitkomma.f64),
      floatGuard k = true
        ∧ guardedDiv64 k a b = some (fdiv64 a b)
        ∧ muster64 (fdiv64 (Gleitkomma.ofInt Gleitkomma.f64 1)
            (Gleitkomma.ofInt Gleitkomma.f64 3)) ≠ 0 := by
  refine ⟨kontextReset, Gleitkomma.ofInt Gleitkomma.f64 1,
    Gleitkomma.ofInt Gleitkomma.f64 3, kontextReset_gueltig, ?_, ?_⟩
  · exact guardedDiv_gueltig kontextReset _ _ kontextReset_gueltig
  · rw [divDrittel_muster]
    decide

/-- JOINT witness (refused side): the FTZ context refuses the `1 / 0`
    slot -- the same shape the valid side delivers as an infinite value. -/
theorem guardedDiv_verweigert_zeuge :
    ∃ (k : FPKontext) (a b : Gleitkomma.GBits Gleitkomma.f64),
      floatGuard k = false
        ∧ guardedDiv64 k a b = none
        ∧ Gleitkomma.klasse Gleitkomma.f64
            (fdiv64 (Gleitkomma.ofInt Gleitkomma.f64 1)
              (Gleitkomma.ofInt Gleitkomma.f64 0)) = .unendlich := by
  refine ⟨⟨0x9F80⟩, Gleitkomma.ofInt Gleitkomma.f64 1,
    Gleitkomma.ofInt Gleitkomma.f64 0, ?_, ?_,
    Gleitkomma.zeuge_einsDurchNull⟩
  · unfold floatGuard
    exact mxcsr_ftz_verweigert
  · exact guardedDiv_verweigert ⟨0x9F80⟩ _ _
      (by unfold floatGuard; exact mxcsr_ftz_verweigert)

/- CUTS: what is not proved here.
   - Fault versus refusal: a refused MXCSR context refuses the lowering
     SLOT (`none`); no hardware fault/trap semantics is modelled here.
     Unmasked (trap-on-exception) MXCSR words are refused by the same
     guard -- trapping execution itself is unmodelled.
   - Sticky exception flags (bits 0-5) are observed, never trapped:
     `guard_sticky_offen` shows they do not close the slot; accumulation,
     clearing and reads have no definitions (inherited gap of Gleitprofil).
   - NaN payloads: only classification (`.nan`) is concluded, never
     payload equality (inherited gap of Gleitkomma/Gleitprofil).
   - binary64 divide only: no f32 source width, no FMA/fastmath, no other
     ops; overflow/underflow/inexact/denormal-input exception classes
     beyond divide-by-zero and `0 / 0` are not classified here.
   - No SSE correspondence: wrapping `fdiv64` states the Annex-F model
     prescription, not executed-byte behaviour (`SSEAdd32Entspricht`
     names that gap in Gleitprofil; no DIV counterpart is claimed here).
   - No decoder, cost transfer, concurrency/TSO claim, or final-image
     acceptance; the memory round-trip is sequential over one `Speicher`.
   - MXCSR bit positions are stated from the Intel layout via the
     accepted `Gleitprofil` checks, not verified against hardware.
-/

#print axioms guardedDiv_gueltig
#print axioms guardedDiv_verweigert
#print axioms guard_standard
#print axioms guard_ftz_verweigert
#print axioms guard_sticky_offen
#print axioms divEinsNull_modell
#print axioms divNullNull_modell
#print axioms guardedDiv_einsNull
#print axioms guardedDiv_nullNull
#print axioms divDrittel_muster
#print axioms guardedDiv_speicher
#print axioms guardedDiv_gueltig_zeuge
#print axioms guardedDiv_verweigert_zeuge

end Gabbro.Grammatik.X86
