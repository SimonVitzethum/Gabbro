/-
  Composition closing: decode-to-execution through the common dispatcher
  (lane 824).

  Producer/consumer interface closed here: the unified decoder
  (`ExtendedExecution.decodeExt` over the pilot plus narrow, multiply/divide,
  shift, SETcc/CMOVcc, scalar FP and packed-integer families) produces, the
  unified step (`stepExt` over the accepted per-family evaluators) consumes,
  and the common dispatcher (`fetchExt` over the actual fetched window plus
  `extByteschritt`) connects them. This file only composes already-accepted
  theorems; it re-proves no decoder, evaluator, fetch or lift internals and
  defines no second interpreter or executor.
-/
import Grammatik.X86.ExtendedExecution

namespace Gabbro.Grammatik.X86

/-- CLOSING INTERFACE (producer/consumer): every form the common dispatcher
    fetches and decodes reaches its unified execution rule: a fetched
    instruction `i` with any execution outcome `o` of its rule steps the
    whole dispatcher to `o`. Generic over arbitrary admitted inputs: `i`
    ranges over all eight unified families. -/
def dekodiertErreichtSchritt (t : FpZustand) (b : BereitProfil)
    (i : ExtInstr) : Prop :=
  ∀ (rest : List Byte) (o : ExtAusgang),
    fetchExt t (geholt t.kern) = some (i, rest) →
    stepExt i t b = o →
    extByteschritt t b = o

/- CUTS:
   Proved here: the decode-to-execution closing through the common
   dispatcher (`ComposeDecodeExec_verbindung`): every fetched-and-decoded
   form over arbitrary admitted inputs reaches its unified execution rule
   with decoder agreement (`dispatcher_erreicht_schritt`,
   `fetchTrifftDekodierer`), undecoded bytes never execute
   (`undekodiertVerweigert`), the pilot canonical corollary for an
   arbitrary pilot instruction (`pilotKanonischErreicht`), and the joint
   witness below: the accepted mixed pilot/scalar-FP reached run changes
   two actual memory cells from fetched bytes, starts from zeroed cells,
   and refuses past the image.
   NOT proved here, and not claimed:
   - No per-family canonical-byte closing beyond the pilot: narrow,
     multiply/divide, shift, SETcc/CMOVcc, scalar FP and packed-integer
     canonical encodings reach their arms only through the accepted pins
     (`pin_ext_*`); arbitrary-input encoder-to-dispatcher legs for those
     families need general non-shadowing (pilot and earlier families
     refuse every family row), which is not proved here. Owning lanes:
     the extension codec lanes behind `decodeNarrow`, `decodeMulDiv`,
     `decodeShift`, `decodeSetCC`/`decodeCmov`, `fpDecode`,
     `decodeVector` (see `ExtendedExecution` CUTS).
   - No hardware correspondence, no source/IR correspondence, no TSO/W/GX
     bridge, no LOCK/SIMD beyond the accepted rows, no ABI/loader/entry/
     budget connection, no whole-image coverage beyond the fetched window.
   - `verweigert` is the absence of a transition, never a termination
     claim; the divide trap (`halt`) is carried, not proved.
-/

/-- DISPATCHER-TO-RULE (success): every form the common dispatcher fetches
    reaches its unified execution rule. Composes the accepted fetch/step
    selection (`extByteschritt_weiter`); generic over arbitrary admitted
    inputs: `i` ranges over all eight unified families. -/
theorem dispatcher_erreicht_schritt (t : FpZustand) (b : BereitProfil)
    (i : ExtInstr) :
    dekodiertErreichtSchritt t b i := by
  unfold dekodiertErreichtSchritt
  intro rest o hf hs
  exact extByteschritt_weiter t b i rest o hf hs

/-- FETCH-TO-DECODER (unified): a successful dispatcher fetch decodes the
    actual fetched window and carries its checked facts: consumed length
    plus remaining suffix is the window, the length passes the guard, and
    the consumed prefix is executable. Reuses the accepted `fetchExt_erfolg`
    over the actual window `geholt t.kern`. -/
theorem fetchTrifftDekodierer (t : FpZustand) (i : ExtInstr)
    (rest : List Byte)
    (hf : fetchExt t (geholt t.kern) = some (i, rest)) :
    decodeExt (geholt t.kern) = some (i, rest) ∧
      extLen i + rest.length = (geholt t.kern).length ∧
      laengeOk (extLen i) = true ∧
      ausfuehrbarN t.kern.speicher t.kern.rip (extLen i) = true :=
  fetchExt_erfolg t (geholt t.kern) i rest hf

/-- UNDECODED-NEVER-EXECUTES: where the unified decoder refuses the actual
    fetched window, the dispatcher has no transition. No forged instruction
    can be injected: the dispatcher takes only the state and the profile.
    Composes the accepted fetch refusal (`extByteschritt_verweigert`); the
    `verweigert` is the absence of a transition, never a termination claim. -/
theorem undekodiertVerweigert (t : FpZustand) (b : BereitProfil)
    (h : decodeExt (geholt t.kern) = none) :
    extByteschritt t b = .verweigert := by
  have hf : fetchExt t (geholt t.kern) = none := by
    simp [fetchExt, h]
  exact extByteschritt_verweigert t b hf

/-- PILOT CANONICAL CLOSING: for an ARBITRARY pilot instruction, fetching
    its canonical encoding from actual executable memory reaches the pilot
    execution rule through the common dispatcher: the unified decoder takes
    the pilot arm (never shadowed, via `decodeExt_kanonisch` over the
    accepted round trip), admission holds from the accepted length bound
    and the checked execute permission, and the byte step runs the unified
    pilot rule (the accepted `schritt` lift `laufAlt`). -/
theorem pilotKanonischErreicht (t : FpZustand) (b : BereitProfil)
    (bf : Befehl) (suffix : List Byte)
    (hwin : geholt t.kern = encode bf ++ suffix)
    (hexe : ausfuehrbarN t.kern.speicher t.kern.rip (encode bf).length = true) :
    fetchExt t (geholt t.kern) =
        some (.pilot ⟨bf, (encode bf).length⟩, suffix) ∧
      extByteschritt t b =
        stepExt (.pilot ⟨bf, (encode bf).length⟩) t b := by
  have hlen := encode_len bf
  have hok : laengeOk (encode bf).length = true := by
    simp only [laengeOk, decide_eq_true_eq]
    exact hlen
  have hsum : (encode bf).length + suffix.length =
      (geholt t.kern).length := by
    rw [hwin, List.length_append]
  have hrt := roundtrip bf suffix
  rw [← hwin] at hrt
  have hdec : decodeExt (geholt t.kern) =
      some (.pilot ⟨bf, (encode bf).length⟩, suffix) :=
    decodeExt_kanonisch _ _ _ hrt
  have hzul : extZugelassen t (geholt t.kern)
      (.pilot ⟨bf, (encode bf).length⟩) suffix = true := by
    unfold extZugelassen
    simp [extLen, hsum, hok, hexe]
  have hf : fetchExt t (geholt t.kern) =
      some (.pilot ⟨bf, (encode bf).length⟩, suffix) := by
    unfold fetchExt
    rw [hdec]
    simp [hzul]
  refine ⟨hf, ?_⟩
  exact extByteschritt_weiter t b _ _ _ hf rfl

/-- DECODE-TO-EXECUTION CLOSING through the common dispatcher, generic over
    arbitrary admitted inputs: every form the dispatcher fetches reaches
    its unified execution rule (with decoder agreement), and undecoded
    bytes never execute. Composes `fetchTrifftDekodierer`,
    `dispatcher_erreicht_schritt` and `undekodiertVerweigert`; no decoder,
    evaluator, fetch or lift fact is re-proved here. -/
theorem ComposeDecodeExec_verbindung (t : FpZustand) (b : BereitProfil) :
    (∀ (i : ExtInstr) (rest : List Byte) (o : ExtAusgang),
      fetchExt t (geholt t.kern) = some (i, rest) →
      stepExt i t b = o →
      decodeExt (geholt t.kern) = some (i, rest) ∧
        extByteschritt t b = o) ∧
    (decodeExt (geholt t.kern) = none →
      extByteschritt t b = .verweigert) := by
  refine ⟨?_, ?_⟩
  · intro i rest o hf hs
    exact ⟨(fetchTrifftDekodierer t i rest hf).1,
      extByteschritt_weiter t b i rest o hf hs⟩
  · intro h
    exact undekodiertVerweigert t b h

/-- JOINT WITNESS: the closing instantiated at the accepted mixed
    pilot/scalar-FP witness (`extWitStart`, `extWitBereit`), together with
    the non-degenerate memory-changing reached run (two actual cells read
    zero, then 42 after two dispatcher steps from fetched bytes) and the
    planted refusal past the image. -/
theorem ComposeDecodeExec_verbindung_zeuge :
    (∀ (i : ExtInstr) (rest : List Byte) (o : ExtAusgang),
      fetchExt extWitStart (geholt extWitStart.kern) = some (i, rest) →
      stepExt i extWitStart extWitBereit = o →
      decodeExt (geholt extWitStart.kern) = some (i, rest) ∧
        extByteschritt extWitStart extWitBereit = o) ∧
    (decodeExt (geholt extWitStart.kern) = none →
      extByteschritt extWitStart extWitBereit = .verweigert) ∧
    extZelle (extSchritt2 extWitStart extWitBereit)
      (BitVec.ofNat 64 8192) = some (BitVec.ofNat 8 42) ∧
    extZelle (extSchritt2 extWitStart extWitBereit)
      (BitVec.ofNat 64 8200) = some (BitVec.ofNat 8 42) ∧
    extWitStart.kern.speicher.bytes (BitVec.ofNat 64 8192) =
      BitVec.ofNat 8 0 ∧
    extByteschritt
        { extWitStart with kern :=
          { extWitKern with rip := BitVec.ofNat 64 4111 } }
        extWitBereit = .verweigert := by
  obtain ⟨hconn, href⟩ :=
    ComposeDecodeExec_verbindung extWitStart extWitBereit
  exact ⟨hconn, href, extWit_zwei_schritte_speichern.1,
    extWit_zwei_schritte_speichern.2, extWit_anfang_null.1,
    extWit_nachBild_verweigert⟩

#print axioms dekodiertErreichtSchritt
#print axioms dispatcher_erreicht_schritt
#print axioms fetchTrifftDekodierer
#print axioms undekodiertVerweigert
#print axioms pilotKanonischErreicht
#print axioms ComposeDecodeExec_verbindung
#print axioms ComposeDecodeExec_verbindung_zeuge

end Gabbro.Grammatik.X86
