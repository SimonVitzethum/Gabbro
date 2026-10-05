/-
  File:      Grammatik/X86/HwLoadedImage.lean
  Subject:   Coherent machine fetching from the loaded image.

  Lane 1137: projection/embedding relating a `HwMaschine` core fetch to the
  loaded-image fetch (`Byteschritt`, `LoadedExecution`, `ComposeImageFetch`).
  Every accepted definition is reused unchanged; fetch identity on a checked
  mapping is proved, and a Hw register step of a fetched pilot instruction is
  a `Byteschritt` step on the projection. Extension rows are the stated
  obstruction: they step the Hw machine but refuse `byteschritt`.
-/
import Grammatik.X86.Kern.Typen
import Grammatik.X86.Speicher.Speicher
import Grammatik.X86.TSO.Kern.TSO
import Grammatik.X86.Kern.Byteschritt
import Grammatik.X86.Kern.Bild
import Grammatik.X86.Laden.LoadedExecution
import Grammatik.X86.Compose.Bild.ComposeImageFetch
import Grammatik.X86.Compose.Bild.ComposeMapPerms
import Grammatik.X86.Validierung.ValidatorSkeleton
import Grammatik.X86.Hw.Grundlage.HardwareExecution
import Grammatik.X86.Hw.Grundlage.ExtendedExecution

namespace Gabbro.Grammatik.X86

/-- Memory coincidence: the machine runs on the loaded image. -/
def hwBildSpeicherGleich (m : HwMaschine) (bild : Bild) (bias : Nat) : Prop :=
  m.mem = geladen bild bias

/-- Core/fetch-input agreement: the core fetches where the image state does. -/
def hwBildKernGleich (m : HwMaschine) (c : Nat) (rip : Adresse)
    (reg : Register → Wort) (fl : Flags) : Prop :=
  (m.kerne c).rip = rip ∧ (m.kerne c).register = reg ∧ (m.kerne c).flags = fl

/-- PROJECTION IDENTITY: under memory coincidence and core agreement the
    core projection IS the loaded image state. -/
theorem hwBild_zustand_gleich (m : HwMaschine) (c : Nat) (bild : Bild)
    (bias : Nat) (rip : Adresse) (reg : Register → Wort) (fl : Flags)
    (hmem : m.mem = geladen bild bias)
    (hrip : (m.kerne c).rip = rip)
    (hreg : (m.kerne c).register = reg)
    (hfl : (m.kerne c).flags = fl) :
    projZustand m c = bildZustand bild bias rip reg fl := by
  unfold projZustand bildZustand
  simp only [hrip, hreg, hfl, hmem]

/-- FETCHED-BYTE IDENTITY: the core fetches the image bytes. -/
theorem hwBild_geholt_gleich (m : HwMaschine) (c : Nat) (bild : Bild)
    (bias : Nat) (rip : Adresse) (reg : Register → Wort) (fl : Flags)
    (hmem : m.mem = geladen bild bias)
    (hrip : (m.kerne c).rip = rip)
    (hreg : (m.kerne c).register = reg)
    (hfl : (m.kerne c).flags = fl) :
    geholt (projZustand m c) = geholt (bildZustand bild bias rip reg fl) := by
  rw [hwBild_zustand_gleich m c bild bias rip reg fl hmem hrip hreg hfl]

/-- FETCH-AND-DECODE IDENTITY: the core decodes what the image decodes. -/
theorem hwBild_fetchDekodiert_gleich (m : HwMaschine) (c : Nat) (bild : Bild)
    (bias : Nat) (rip : Adresse) (reg : Register → Wort) (fl : Flags)
    (hmem : m.mem = geladen bild bias)
    (hrip : (m.kerne c).rip = rip)
    (hreg : (m.kerne c).register = reg)
    (hfl : (m.kerne c).flags = fl) :
    fetchDekodiert (projZustand m c) =
      fetchDekodiert (bildZustand bild bias rip reg fl) := by
  rw [hwBild_zustand_gleich m c bild bias rip reg fl hmem hrip hreg hfl]

/-- BYTE-STEP IDENTITY: the core projection steps where the image steps. -/
theorem hwBild_byteschritt_gleich (m : HwMaschine) (c : Nat) (bild : Bild)
    (bias : Nat) (rip : Adresse) (reg : Register → Wort) (fl : Flags)
    (hmem : m.mem = geladen bild bias)
    (hrip : (m.kerne c).rip = rip)
    (hreg : (m.kerne c).register = reg)
    (hfl : (m.kerne c).flags = fl) :
    byteschritt (projZustand m c) =
      byteschritt (bildZustand bild bias rip reg fl) := by
  rw [hwBild_zustand_gleich m c bild bias rip reg fl hmem hrip hreg hfl]

/-- DISPATCH INVERSION (pilot): a unified pilot outcome comes from the pilot. -/
theorem decodeExt_pilot_zeigt_decode (bs : List Byte) (d : Decodiert)
    (rest : List Byte)
    (h : decodeExt bs = some (.pilot d, rest)) :
    decode bs = some (d, rest) := by
  cases hdec : decode bs with
  | some pr =>
    obtain ⟨d', rest'⟩ := pr
    have hde : decodeExt bs = some (.pilot d', rest') := by
      simp only [decodeExt, hdec]
    rw [hde] at h
    cases h
    rfl
  | none =>
    simp only [decodeExt, hdec] at h
    cases hn : decodeNarrow bs with
    | some pr =>
      obtain ⟨n, r⟩ := pr
      simp only [hn] at h
      cases h
    | none =>
      cases hm : decodeMulDiv bs with
      | some pr =>
        obtain ⟨mm, r⟩ := pr
        simp only [hn, hm] at h
        cases h
      | none =>
        cases hs : decodeShift bs with
        | some pr =>
          obtain ⟨f, r⟩ := pr
          simp only [hn, hm, hs] at h
          cases h
        | none =>
          cases hc : decodeSetCC bs with
          | some pr =>
            obtain ⟨cdst, r⟩ := pr
            simp only [hn, hm, hs, hc] at h
            cases h
          | none =>
            cases hcm : decodeCmov bs with
            | some pr =>
              obtain ⟨cdsr, r⟩ := pr
              simp only [hn, hm, hs, hc, hcm] at h
              cases h
            | none =>
              cases hfp : fpDecode bs with
              | some pr =>
                obtain ⟨f, r⟩ := pr
                simp only [hn, hm, hs, hc, hcm, hfp] at h
                cases h
              | none =>
                cases hv : decodeVector bs with
                | some pr =>
                  obtain ⟨v, r⟩ := pr
                  simp only [hn, hm, hs, hc, hcm, hfp, hv] at h
                  cases h
                | none =>
                  simp only [hn, hm, hs, hc, hcm, hfp, hv] at h
                  cases h

/-- DISPATCH INVERSION (narrow): a unified narrow outcome means pilot refusal. -/
theorem decodeExt_narrow_zeigt_decode_none (bs : List Byte) (n : NarrowDec)
    (rest : List Byte)
    (h : decodeExt bs = some (.narrow n, rest)) :
    decode bs = none := by
  cases hdec : decode bs with
  | some pr =>
    obtain ⟨d', rest'⟩ := pr
    have hde : decodeExt bs = some (.pilot d', rest') := by
      simp only [decodeExt, hdec]
    rw [hde] at h
    cases h
  | none => rfl

/-- FETCH LIFTING (pilot): a checked pilot fetch-decoding is a unified fetch. -/
theorem hwBild_fetchExt_pilot (m : HwMaschine) (c : Nat) (d : Decodiert)
    (rest : List Byte)
    (hd : decode (geholt (projZustand m c)) = some (d, rest))
    (hsum : d.laenge + rest.length = (geholt (projZustand m c)).length)
    (hok : laengeOk d.laenge = true)
    (hexe : ausfuehrbarN m.mem (m.kerne c).rip d.laenge = true) :
    fetchExt (projFp m c) (geholt (projZustand m c)) =
      some (.pilot d, rest) := by
  have hde := decodeExt_kanonisch (geholt (projZustand m c)) d rest hd
  have hz : extZugelassen (projFp m c) (geholt (projZustand m c))
      (.pilot d) rest = true := by
    have e1 : decide (extLen (.pilot d) + rest.length =
        (geholt (projZustand m c)).length) = true := by
      rw [decide_eq_true_eq]
      exact hsum
    have e2 : laengeOk (extLen (.pilot d)) = true := hok
    have e3 : ausfuehrbarN (projFp m c).kern.speicher
        (projFp m c).kern.rip (extLen (.pilot d)) = true :=
      hexe
    unfold extZugelassen
    simp [e1, e2, e3]
  unfold fetchExt
  simp [hde, hz]

/-- HW-STEP-IS-BYTE-STEP (pilot): a Hw register step of a fetched pilot
    instruction is a `Byteschritt` step on the core projection, with the
    same successor core data. -/
theorem hwBild_reg_pilot_ist_byteschritt (m : HwMaschine) (c : Nat)
    (d : Decodiert) (rest : List Byte) (s' : Zustand)
    (hf : fetchExt (projFp m c) (geholt (projZustand m c)) =
      some (.pilot d, rest))
    (hs : schritt d (projZustand m c) = some s')
    (hmem : ({ projFp m c with kern := s' }).kern.speicher = m.mem) :
    HwSchritt m (setKernVonFp m c { projFp m c with kern := s' })
      (.regAusf c (.pilot d)) ∧
      byteschritt (projZustand m c) = .weiter s' := by
  have hstep : stepExt (.pilot d) (projFp m c) (m.bereit c) =
      .weiter { projFp m c with kern := s' } :=
    hwPilot_weiter m c d (m.bereit c) s' hs
  have hreg := hwByteschrittReg_rechtfertigt m c (.pilot d) rest
    { projFp m c with kern := s' } hf hstep hmem
  have herf := fetchExt_erfolg (projFp m c) (geholt (projZustand m c))
    (.pilot d) rest hf
  obtain ⟨hde, hsum, hok, hexe⟩ := herf
  have hd := decodeExt_pilot_zeigt_decode _ _ _ hde
  have hsum' : d.laenge + rest.length =
      (geholt (projZustand m c)).length := hsum
  have hexe' : ausfuehrbarN (projZustand m c).speicher
      (projZustand m c).rip d.laenge = true := hexe
  have hok' : laengeOk d.laenge = true := hok
  have hcond : (d.laenge + rest.length == (geholt (projZustand m c)).length &&
      laengeOk d.laenge &&
      ausfuehrbarN (projZustand m c).speicher (projZustand m c).rip
        d.laenge) = true := by
    have hb : (d.laenge + rest.length ==
        (geholt (projZustand m c)).length) = true := by
      rw [beq_iff_eq]
      exact hsum'
    simp [hb, hok', hexe']
  have hfd : fetchDekodiert (projZustand m c) = some (d, rest) := by
    unfold fetchDekodiert
    rw [hd]
    dsimp only
    rw [if_pos hcond]
  exact ⟨hreg.2, byteschritt_weiter _ _ _ _ hfd hs⟩

/-- OBSTRUCTION (narrow): a fetched extension row has no `Byteschritt`
    counterpart -- the pilot fetch refuses while the Hw machine steps.
    Stated for narrow; the other six families share the dispatch shape
    (see CUTS). -/
theorem hwBild_erweitert_ohne_pilot (t : FpZustand) (n : NarrowDec)
    (rest : List Byte)
    (hf : fetchExt t (geholt t.kern) = some (.narrow n, rest)) :
    fetchDekodiert t.kern = none := by
  have herf := fetchExt_erfolg t _ _ _ hf
  have hd := decodeExt_narrow_zeigt_decode_none _ _ _ herf.1
  unfold fetchDekodiert
  simp [hd]

/-- LOADED-FETCH AGREEMENT: on a checked mapping, the Hw core's fetched
    window IS the mapped file-byte prefix. The checked map (acceptance,
    member section, wrap-free window, file-backed extent, stable lookup,
    execute permission) is the premise; byte identity is derived. -/
theorem hwBild_geholt_aus_datei (m : HwMaschine) (c : Nat) (p : Profil)
    (bild : Bild) (bias : Nat) (s : Abschnitt) (k n : Nat)
    (hmemc : m.mem = geladen bild bias)
    (hrip : (m.kerne c).rip.toNat = bias + s.vaddr + k)
    (hfree : ∀ i : Nat, i < n →
      (addrOff (m.kerne c).rip i).toNat = (m.kerne c).rip.toNat + i)
    (hdatei : k + n ≤ s.dateiLen)
    (hstab : ∀ i : Nat, i < n →
      abteilFinden bild.abschnitte bias ((m.kerne c).rip.toNat + i) = some s)
    (hexe : ∀ i : Nat, i < n →
      (geladen bild bias).ausfuehrbar (addrOff (m.kerne c).rip i) = true)
    (hmemSec : s ∈ bild.abschnitte)
    (hwf : wohlgeformt p bild = true) :
    holeFetchAux m.mem (m.kerne c).rip 0 n =
      ((List.range' 0 n).map fun j =>
        dateiByte bild.datei (s.dateiOff + (k + j))) := by
  have hconn := ComposeImageFetch_verbindung p bild bias (m.kerne c).rip
    (m.kerne c).register (m.kerne c).flags s k n hmemSec hwf hrip hfree
    hdatei hstab hexe
  rw [hmemc]
  exact hconn.1

/-- WELL-FORMEDNESS SURVIVES: every Hw step of the loaded-image machine
    keeps the checked core/control profile (lifts `hwSchritt_wf`). -/
theorem hwBild_schritt_wf (m m' : HwMaschine) (e : HwEreignis)
    (h : HwSchritt m m' e) (hwf : HwWf m) : HwWf m' :=
  hwSchritt_wf m m' e h hwf

/-- EXECUTE-DENIED REFUSAL: a core whose head fetch byte is not executable
    takes no Hw register step. Fetch checks execute permission only. -/
theorem hwBild_ohne_exec_verweigert (m : HwMaschine) (c : Nat)
    (h0 : (projZustand m c).speicher.ausfuehrbar
      (addrOff (projZustand m c).rip 0) = false) :
    hwByteschrittReg m c = .verweigert := by
  have hleer : geholt (projZustand m c) = [] := by
    have hcap : fetchCap = 14 + 1 := rfl
    show holeFetchAux (projZustand m c).speicher (projZustand m c).rip 0
      fetchCap = []
    rw [hcap]
    exact fetch_leer_ohne_exec _ _ _ h0 14
  have hdec : decodeExt (geholt (projZustand m c)) = none := by
    rw [hleer]
    exact pin_ext_nichts_leer
  have hnone : fetchExt (projFp m c) (geholt (projZustand m c)) = none := by
    unfold fetchExt
    simp [hdec]
  exact hwByteschrittReg_verweigert m c hnone

/-- The loaded-image adapter: the accepted register-path plug, reused by
    name (never duplicated). Memory forms must use the issue/drain path;
    halt is an outcome, never a successor. -/
def adapterBild : HwAdapter ExtInstr := adapterInteger666

/-- ADAPTER AGREEMENT: the adapter admits exactly what the accepted
    unified evaluator accepts on the core projection. -/
theorem adapterBild_vereinbarung (m : HwMaschine) (c : Nat) (i : ExtInstr)
    (t' : FpZustand)
    (h : stepExt i (projFp m c) (m.bereit c) = .weiter t') :
    adapterBild.schritt m c i = some (setKernVonFp m c t') := by
  unfold adapterBild adapterInteger666
  simp [h]

/-- ADAPTER REFUSAL: what the evaluator refuses, the adapter refuses. -/
theorem adapterBild_verweigert (m : HwMaschine) (c : Nat) (i : ExtInstr)
    (h : stepExt i (projFp m c) (m.bereit c) = .verweigert) :
    adapterBild.schritt m c i = none := by
  unfold adapterBild adapterInteger666
  simp [h]

/-- ADAPTER HALT REFUSAL: the divide trap has no successor state. -/
theorem adapterBild_halt_verweigert (m : HwMaschine) (c : Nat) (i : ExtInstr)
    (h : stepExt i (projFp m c) (m.bereit c) = .halt) :
    adapterBild.schritt m c i = none := by
  unfold adapterBild adapterInteger666
  simp [h]

/-- Witness file: the accepted narrow+scalar image (7 bytes) then data. -/
def hwBildDatei : List Byte := hwWitBild ++ List.replicate 8 (natByte 0)

/-- Witness code section: execute-only with the 7 fetched bytes. -/
def hwBildCode : Abschnitt :=
  { dateiOff := 0, dateiLen := 7, vaddr := 0x1000, memLen := 7,
    lesbar := false, schreibbar := false, ausfuehrbar := true, ausr := 4096 }

/-- Witness data section: eight file bytes, readable and writable. -/
def hwBildDaten : Abschnitt :=
  { dateiOff := 7, dateiLen := 8, vaddr := 0x2000, memLen := 8,
    lesbar := true, schreibbar := true, ausfuehrbar := false, ausr := 4096 }

/-- The witness image: biased base 0x100000, entry at the code base. -/
def hwBild : Bild :=
  { datei := hwBildDatei
    abschnitte := [hwBildCode, hwBildDaten]
    reloks := []
    eintraege := [0x101000]
    modus := .param 0x100000 }

/-- Witness cores: core 0 fetches at the code base, core 1 idles on data. -/
def hwBildKern : Nat → HwKern
  | 0 => ⟨hwWitReg0, zeugeFlags, BitVec.ofNat 64 0x101000, hwWitXmm0,
      kontextReset⟩
  | _ => ⟨fun _ => BitVec.ofNat 64 0, zeugeFlags,
      BitVec.ofNat 64 0x102000, fun _ => BitVec.ofNat 128 0, kontextReset⟩

/-- Witness start machine: loaded image memory, two cores, empty buffers. -/
def hwBildStart : HwMaschine :=
  ⟨geladen hwBild 0x100000, hwBildKern, fun _ => [], basisHw,
    fun _ => basisBereit⟩

/-- ACCEPTANCE: the witness image validates under profile 48. -/
theorem hwBild_wohlgeformt :
    wohlgeformt .p48 hwBild = true := by
  decide

/-- The witness machine is well-formed: full silicon admits all. -/
theorem hwBildStart_wf : HwWf hwBildStart := by
  apply hwWf_aus_zugelassen
  intro c f
  cases f with
  | skalar64 => rfl
  | skalar32 => rfl
  | sseDoppel =>
    show merkmalZugelassen basisHw basisBereit .sseDoppel = true
    decide
  | paketInt128 =>
    show merkmalZugelassen basisHw basisBereit .paketInt128 = true
    decide

/-- First fetched step on core 0. -/
def hwBildO1 : HwRegAusgang := hwByteschrittReg hwBildStart 0

/-- Second fetched step on core 0 (over the first successor). -/
def hwBildO2 : HwRegAusgang :=
  match hwBildO1 with
  | .weiter m1 => hwByteschrittReg m1 0
  | x => x

/-- Step one advances RIP past the 3-byte narrow move. -/
theorem hwBild_o1_rip :
    hwRipOut hwBildO1 0 = some (BitVec.ofNat 64 0x101003) := by
  decide

/-- Step one moves the witness value into rax. -/
theorem hwBild_o1_rax :
    hwRegOut hwBildO1 0 .rax = some (BitVec.ofNat 64 9) := by
  decide

/-- Step two advances RIP past the 4-byte scalar move. -/
theorem hwBild_o2_rip :
    hwRipOut hwBildO2 0 = some (BitVec.ofNat 64 0x101007) := by
  decide

/-- Step two lands the low double-word in xmm0. -/
theorem hwBild_o2_xmm :
    hwXmmTiefOut hwBildO2 0 .xmm0 = some (BitVec.ofNat 64 7) := by
  decide

/-- The data cell starts zeroed: the run really changes memory. -/
theorem hwBild_anfang_null :
    hwBildStart.mem.bytes (BitVec.ofNat 64 0x102000) =
      BitVec.ofNat 8 0 := by
  decide

/-- FETCH-INTERIOR on the witness image: the first seven fetched bytes are
    exactly the mapped file bytes at offset 0, base `0x1000`, bias
    `0x100000`. An application of the generic `hwBild_geholt_aus_datei`,
    with every checked-map premise discharged by decision. -/
theorem hwBild_datei_vorne :
    holeFetchAux hwBildStart.mem (BitVec.ofNat 64 0x101000) 0 7 =
      ((List.range' 0 7).map fun j =>
        dateiByte hwBild.datei (hwBildCode.dateiOff + (0 + j))) := by
  have h := hwBild_geholt_aus_datei hwBildStart 0 .p48 hwBild 0x100000
    hwBildCode 0 7
    rfl
    (by decide)
    (by decide)
    (by decide)
    (by decide)
    (by decide)
    (by decide)
    hwBild_wohlgeformt
  exact h

/-- Witness data address in the loaded data section. -/
def hwBildAdr : Adresse := BitVec.ofNat 64 0x102000

/-- The machine after the two register steps, if reached. -/
def hwBildM2 : Option HwMaschine :=
  match hwBildO2 with
  | .weiter m => some m
  | _ => none

/-- Core 0 issues byte 42 at the data cell. -/
def hwBildTso1 : Option TSOZustand :=
  match hwBildM2 with
  | some m2 => issueByte (tsoAnsicht m2) 0 hwBildAdr (BitVec.ofNat 8 42)
  | none => none

/-- Core 0 observes its own byte (forwarding). -/
def hwBildLoadEigen : Option (Option Byte) :=
  match hwBildTso1 with
  | some s => some (loadByte s 0 hwBildAdr)
  | none => none

/-- Core 1 observes the old byte (no foreign forwarding). -/
def hwBildLoadFremd : Option (Option Byte) :=
  match hwBildTso1 with
  | some s => some (loadByte s 1 hwBildAdr)
  | none => none

/-- Core 0 drains its oldest entry. -/
def hwBildTso2 : Option TSOZustand :=
  match hwBildTso1 with
  | some s => flushKern s 0
  | none => none

/-- The shared byte after the drain. -/
def hwBildNachFlush : Option (Option Byte) :=
  match hwBildTso2 with
  | some s => some (some (s.mem.bytes hwBildAdr))
  | none => none

/-- Core 1 reads the drained byte from shared memory. -/
def hwBildFremdNachFlush : Option (Option Byte) :=
  match hwBildTso2 with
  | some s => some (loadByte s 1 hwBildAdr)
  | none => none

/-- Forwarding: core 0 reads its own unflushed byte. -/
theorem hwBild_weiterleitung :
    hwBildLoadEigen = some (some (BitVec.ofNat 8 42)) := by
  decide

/-- No foreign forwarding: core 1 still reads zero. -/
theorem hwBild_fremd_alt :
    hwBildLoadFremd = some (some (BitVec.ofNat 8 0)) := by
  decide

/-- The drain changes shared memory: the cell reads 42. -/
theorem hwBild_spuelung_aendert_speicher :
    hwBildNachFlush = some (some (BitVec.ofNat 8 42)) := by
  decide

/-- After the drain core 1 observes the new byte. -/
theorem hwBild_fremd_neu :
    hwBildFremdNachFlush = some (some (BitVec.ofNat 8 42)) := by
  decide

/-- Core 1 refuses: its RIP points at non-executable loaded memory. -/
theorem hwBild_kern1_verweigert :
    hwByteschrittReg hwBildStart 1 = .verweigert := by
  apply hwBild_ohne_exec_verweigert
  decide

/-- Writable-and-executable code section: refused by the checked mapping. -/
def hwBildWx : Bild :=
  { hwBild with
    abschnitte := [{ hwBildCode with schreibbar := true }, hwBildDaten] }

/-- W^X REFUSAL: a writable code section is not an accepted image. -/
theorem hwBildWx_verweigert :
    wohlgeformt .p48 hwBildWx = false := by
  decide

/-- The joint witness: an accepted loaded image whose Hw core fetches real
    file bytes, takes two register steps, forwards a buffered store to its
    owner only, drains it into shared memory (0 becomes 42, observed from
    both cores) -- with the data-section and W^X refusals beside it.
    Non-degenerate: the drain changes ACTUAL shared loaded memory. -/
theorem hwBild_zeuge :
    wohlgeformt .p48 hwBild = true ∧
      HwWf hwBildStart ∧
      hwRipOut hwBildO1 0 = some (BitVec.ofNat 64 0x101003) ∧
      hwRegOut hwBildO1 0 .rax = some (BitVec.ofNat 64 9) ∧
      hwRipOut hwBildO2 0 = some (BitVec.ofNat 64 0x101007) ∧
      hwXmmTiefOut hwBildO2 0 .xmm0 = some (BitVec.ofNat 64 7) ∧
      hwBildStart.mem.bytes (BitVec.ofNat 64 0x102000) =
        BitVec.ofNat 8 0 ∧
      holeFetchAux hwBildStart.mem (BitVec.ofNat 64 0x101000) 0 7 =
        ((List.range' 0 7).map fun j =>
          dateiByte hwBild.datei (hwBildCode.dateiOff + (0 + j))) ∧
      hwBildLoadEigen = some (some (BitVec.ofNat 8 42)) ∧
      hwBildLoadFremd = some (some (BitVec.ofNat 8 0)) ∧
      hwBildNachFlush = some (some (BitVec.ofNat 8 42)) ∧
      hwBildFremdNachFlush = some (some (BitVec.ofNat 8 42)) ∧
      hwByteschrittReg hwBildStart 1 = .verweigert := by
  refine ⟨hwBild_wohlgeformt, hwBildStart_wf, hwBild_o1_rip, hwBild_o1_rax,
    hwBild_o2_rip, hwBild_o2_xmm, hwBild_anfang_null, hwBild_datei_vorne,
    hwBild_weiterleitung, hwBild_fremd_alt, hwBild_spuelung_aendert_speicher,
    hwBild_fremd_neu, hwBild_kern1_verweigert⟩

/- CUTS:
   Proved here, reusing every accepted definition unchanged (no second
   loader, decoder, executor or ISA model):
   - projection/fetch identity between a `HwMaschine` core and the loaded
     image state (`hwBild_zustand_gleich`, `hwBild_geholt_gleich`,
     `hwBild_fetchDekodiert_gleich`, `hwBild_byteschritt_gleich`);
   - unified-dispatch inversion (pilot outcomes come from the pilot,
     narrow outcomes mean pilot refusal);
   - pilot fetch lifting and the HW-STEP-IS-BYTE-STEP connection: a Hw
     register step of a fetched pilot instruction is a `Byteschritt`
     step on the core projection with the same successor data;
   - the extension obstruction: a fetched narrow row refuses
     `fetchDekodiert` while the Hw machine steps it;
   - loaded-fetch agreement from the checked map to the fetched prefix
     (`hwBild_geholt_aus_datei`, via `ComposeImageFetch_verbindung`);
   - well-formedness survival, execute-denied refusal, the reused
     register-path adapter with admission/refusal/halt agreement;
   - a reached two-core witness on an accepted loaded image
     (`hwBild_zeuge`): real file-byte fetch, two register steps,
     owner-only forwarding, drain changing shared memory 0 to 42,
     data-section and W^X refusals beside it.
   NOT proved here, and not claimed:
   - No hardware correspondence: encodings are the accepted canonical
     subsets with self-consistency only, not x86 truth. Silicon/timing
     assumptions: none beyond the accepted lemmas reused by name.
   - No per-access target-to-W/GX simulation and no whole-word atomicity
     beyond the reused `WortGruppe` guard: the TSO stage here is the
     accepted byte equations lifted, as in lane 660.
   - Extension families beyond narrow share the dispatch shape but have
     no per-family obstruction lemma here.
   - No source/IR/ABI/loader/entry/budget link; no LOCK RMW path
     (refused, as in lane 660); `verweigert` is the absence of a
     transition, never normal program termination.
   - The full bridge to W/GX is not claimed.
-/

#print axioms hwBild_zustand_gleich
#print axioms hwBild_geholt_gleich
#print axioms hwBild_fetchDekodiert_gleich
#print axioms hwBild_byteschritt_gleich
#print axioms decodeExt_pilot_zeigt_decode
#print axioms decodeExt_narrow_zeigt_decode_none
#print axioms hwBild_fetchExt_pilot
#print axioms hwBild_reg_pilot_ist_byteschritt
#print axioms hwBild_erweitert_ohne_pilot
#print axioms hwBild_geholt_aus_datei
#print axioms hwBild_schritt_wf
#print axioms hwBild_ohne_exec_verweigert
#print axioms adapterBild_vereinbarung
#print axioms adapterBild_verweigert
#print axioms adapterBild_halt_verweigert
#print axioms hwBild_wohlgeformt
#print axioms hwBildStart_wf
#print axioms hwBild_o1_rip
#print axioms hwBild_o1_rax
#print axioms hwBild_o2_rip
#print axioms hwBild_o2_xmm
#print axioms hwBild_anfang_null
#print axioms hwBild_datei_vorne
#print axioms hwBild_weiterleitung
#print axioms hwBild_fremd_alt
#print axioms hwBild_spuelung_aendert_speicher
#print axioms hwBild_fremd_neu
#print axioms hwBild_kern1_verweigert
#print axioms hwBildWx_verweigert
#print axioms hwBild_zeuge

end Gabbro.Grammatik.X86
