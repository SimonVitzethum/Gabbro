/-
  File:      Grammatik/X86/LeaPureForm.lean
  Subject:   Pure LEA address arithmetic with an explicit displacement-fits-i32
             side condition, pinned bytes and out-of-range refusal.

  Lane 755: thin connection over the accepted canonical vocabulary
  (`Zustand`, `AdrForm`, `adrEff`, `decodeLea`, `leaFormSchritt`,
  `leaGeholtSchritt` from `AddressEncoding`; `dispWort` pins from
  `EffectiveAddress`; the common dispatcher `decodeExt` from
  `ExtendedExecution`). Nothing is redefined here: no new register, memory,
  decoder or source model.

  Manual provenance (clone-local snapshot `.tmp/HARDWARE-REFERENCES/`):
  Intel SDM combined volumes 1-4, edition 325462-093US, September 2026
  (`REFERENCES.json`, verified 2026-10-02). Instruction entry
  LEA - Load Effective Address (Intel SDM Vol. 2): computes the effective
  address of the source operand and stores it in the destination register;
  no memory is read and no flags are modified. Only this named entry is
  used; no vendor difference or silicon timing is claimed.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Byteschritt
import Grammatik.X86.AddressEncoding
import Grammatik.X86.EffectiveAddress
import Grammatik.X86.ExtendedExecution

namespace Gabbro.Grammatik.X86

/-- Source-level displacement admission: the signed 32-bit range. -/
def leaDispOk (neg : Bool) (m : Nat) : Bool :=
  if neg then decide (1 ≤ m ∧ m ≤ 2147483648) else decide (m ≤ 2147483647)

/-- Source-level displacement value: two's complement word when admitted. -/
def leaDispWert (neg : Bool) (m : Nat) : Option (BitVec 32) :=
  if leaDispOk neg m then
    some (if neg then BitVec.ofNat 32 (4294967296 - m) else BitVec.ofNat 32 m)
  else none

/-! ## 1. Displacement admission pins: the i32 range and its edge. -/

/-- `-1` is admitted and names the all-ones word. -/
theorem leaDisp_negEins :
    leaDispWert true 1 = some (BitVec.ofNat 32 4294967295) := by
  decide

/-- The largest forward displacement is admitted and kept. -/
theorem leaDisp_maxPos :
    leaDispWert false 2147483647 = some (BitVec.ofNat 32 2147483647) := by
  decide

/-- The largest backward displacement is admitted. -/
theorem leaDisp_minNeg :
    leaDispWert true 2147483648 = some (BitVec.ofNat 32 2147483648) := by
  decide

/-- REFUSAL: one past the largest forward displacement. -/
theorem leaDisp_zuGross : leaDispWert false 2147483648 = none := by
  decide

/-- REFUSAL: one past the largest backward displacement. -/
theorem leaDisp_negZuGross : leaDispWert true 2147483649 = none := by
  decide

/-- REFUSAL: negative zero names no displacement. -/
theorem leaDisp_negNull : leaDispWert true 0 = none := by
  decide

/-! ## 2. Bridges: admitted displacements meet canonical sign extension. -/

/-- An admitted `-1` sign-extends to the all-ones word. -/
theorem leaDispWort_negEins (d : BitVec 32)
    (h : leaDispWert true 1 = some d) :
    dispWort d = 0xFFFFFFFFFFFFFFFF := by
  rw [leaDisp_negEins] at h
  cases h
  exact dispWort_negEins

/-- An admitted largest forward displacement keeps its value. -/
theorem leaDispWort_maxPos (d : BitVec 32)
    (h : leaDispWert false 2147483647 = some d) :
    dispWort d = 0x7FFFFFFF := by
  rw [leaDisp_maxPos] at h
  cases h
  exact dispWort_maxPos

/-- An admitted largest backward displacement fills the upper bits. -/
theorem leaDispWort_minNeg (d : BitVec 32)
    (h : leaDispWert true 2147483648 = some d) :
    dispWort d = 0xFFFFFFFF80000000 := by
  rw [leaDisp_minNeg] at h
  cases h
  exact dispWort_minNeg

/-! ## 3. Fetched bytes: the witness window decodes as LEA. -/

/-- The fetched witness window is the scaled-index LEA form. -/
theorem leaGeholt_dekodiert :
    decodeLea (geholt leaWitZustand) =
      some (.rax, skaliertForm .rbx .rcx 8 (BitVec.ofNat 32 5) .d8, []) := by
  decide

/-- The fetched LEA consumes five bytes: a checked length. -/
theorem leaGeholt_laenge :
    laengeOk ((geholt leaWitZustand).length - ([] : List Byte).length) =
      true := by
  decide

/-- The common dispatcher refuses the LEA bytes: no shadowing there. -/
theorem leaGemeinsam_verweigert :
    decodeExt [natByte 72, natByte 141, natByte 68, natByte 203,
      natByte 5] = none := by
  decide

/-! ## 4. Connection: fetched LEA through actual memory is pure. -/

/-- CONNECTION: a fetched LEA decoded from actual executable memory runs
    the pure address write: the destination holds the effective address,
    flags and memory are untouched (no memory event) and RIP advances
    past the consumed bytes. Both premises are used. -/
theorem LeaPureForm_verbindung (s : Zustand) (dst : Register) (f : AdrForm)
    (rest : List Byte)
    (hdec : decodeLea (geholt s) = some (dst, f, rest))
    (hok : laengeOk ((geholt s).length - rest.length) = true) :
    ∃ s' : Zustand,
      leaGeholtSchritt s = some s' ∧
      s'.register dst = adrEff s (ripNach s.rip ((geholt s).length - rest.length)) f ∧
      s'.flags = s.flags ∧
      s'.speicher = s.speicher ∧
      s'.rip = ripNach s.rip ((geholt s).length - rest.length) := by
  have hstep : leaGeholtSchritt s = leaFormSchritt dst f ((geholt s).length - rest.length) s (ripNach s.rip ((geholt s).length - rest.length)) := by
    simp [leaGeholtSchritt, hdec, hok]
  have hsome : leaFormSchritt dst f ((geholt s).length - rest.length) s (ripNach s.rip ((geholt s).length - rest.length)) = some { s with register := regSet s.register dst (adrEff s (ripNach s.rip ((geholt s).length - rest.length)) f), rip := ripNach s.rip ((geholt s).length - rest.length) } := by
    unfold leaFormSchritt
    rw [hok]
  rw [hstep]
  exact ⟨_, hsome, by simp [regSet], rfl, rfl, rfl⟩

/-! ## 5. Joint witness: reached LEA beside a memory-changing run. -/

/-- JOINT WITNESS: both premises of `LeaPureForm_verbindung` hold jointly
    on the witness state (fetched scaled-index LEA, five checked bytes);
    the reached LEA computes `8192 + 8 + 5 = 8205` into `rax` while the
    accepted scaled store beside it changes data memory from zero to `42`
    at `8200`. Non-degenerate: a reached pure LEA plus a reached
    memory-changing run. -/
theorem LeaPureForm_verbindung_zeuge :
    (decodeLea (geholt leaWitZustand) =
      some (.rax, skaliertForm .rbx .rcx 8 (BitVec.ofNat 32 5) .d8, [])) ∧
    (laengeOk ((geholt leaWitZustand).length - ([] : List Byte).length) =
      true) ∧
    ((leaGeholtSchritt leaWitZustand).map (fun t => t.register .rax) =
      some (BitVec.ofNat 64 8205)) ∧
    ((adrStoreSchritt storeWitZustand).map
        (fun t => t.speicher.bytes (BitVec.ofNat 64 8200)) =
        some (BitVec.ofNat 8 42)) ∧
    (storeWitZustand.speicher.bytes (BitVec.ofNat 64 8200) =
      BitVec.ofNat 8 0) := by
  exact ⟨leaGeholt_dekodiert, leaGeholt_laenge, leaWit_rechnet,
    storeWit_zeuge.1, storeWit_zeuge.2.2.1⟩

/- CUTS:
   Proved here: a source-level displacement-fits-i32 side condition
   (`leaDispOk`/`leaDispWert`) with accepted boundary pins (-1, maxPos,
   minNeg) and explicit out-of-range refusals (past maxPos, past minNeg,
   negative zero); bridges from admitted displacements to the canonical
   sign extension (`dispWort` pins reused, never redefined); the fetched
   witness window decoded as LEA with its checked five-byte length; the
   common dispatcher refusal of the LEA bytes (`decodeExt` is `none`:
   no shadowing); the fetched-LEA purity connection
   (`LeaPureForm_verbindung`: destination holds the effective address,
   flags and memory untouched, RIP advanced) with its joint witness
   (reached LEA computing 8205 beside a memory-changing store run
   landing 42 from zero).
   NOT proved here, and not claimed:
   - No silicon correspondence: the LEA entry behaviour (no memory read,
     no flag change) is the named Intel SDM Vol. 2 entry cited above;
     correspondence of the stated byte rows to hardware truth is open.
   - No new codec rows: all bytes, forms and steps are the accepted
     `AddressEncoding`/`ExtendedExecution` ones; disp8/disp32 selection
     stays with the accepted compact encoder.
   - No TSO/GX bridge: LEA emits no memory event, so there is no
     footprint, no visibility and no grouping to transfer.
   - No source correspondence, no ABI/loader/entry/budget claim.
-/

#print axioms leaDisp_negEins
#print axioms leaDisp_zuGross
#print axioms leaDispWort_negEins
#print axioms leaGeholt_dekodiert
#print axioms leaGemeinsam_verweigert
#print axioms LeaPureForm_verbindung
#print axioms LeaPureForm_verbindung_zeuge

end Gabbro.Grammatik.X86
