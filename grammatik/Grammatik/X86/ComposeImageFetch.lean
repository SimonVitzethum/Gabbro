/-
  Composition closing: checked image to actual instruction fetch (lane 825).

  Producer/consumer interface closed here: the producers are the accepted
  `Bild` checked mapping (`wohlgeformt`, `geladen`, `abteilFinden`,
  `ladenByte`, `dateiByte`) and the accepted byte-fetch execution
  (`Byteschritt.geholt`, `fetchDekodiert`, `byteschritt`, `schritt`) with the
  generic connection lemmas of `LoadedExecution` (`holeFetchAux_geladen`,
  `geholt_geladen_innen`, `geladenByte_datei`, `geladenAusfuehrbar_fund`,
  `ausserhalb_rahmen`, `wohlgeformt_wx`, `byteschritt_weiter`,
  `byteschritt_verweigert_ohne_fetch`) and the canonical decoder fact
  `Codec.decode_nichts_leer`. Nothing is redefined here: no second loader,
  decoder, executor or ISA model. The consumer is the layout validator and
  the image-coverage proof, which discharge one fetch site by
  `ComposeImageFetch_verbindung` and refuse unmapped or non-executable
  starts by `imageSchritt_loch_verweigert` /
  `imageSchritt_ohne_exec_verweigert`.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.Codec
import Grammatik.X86.Bild
import Grammatik.X86.Byteschritt
import Grammatik.X86.LoadedExecution

namespace Gabbro.Grammatik.X86

/-- The one checked closing step: fetch, decode and execute from the
    canonically loaded image memory, never from caller-supplied memory.
    The state memory is forced to `geladen`; `rip`, registers and flags
    are the only caller inputs. -/
def imageSchritt (bild : Bild) (bias : Nat) (rip : Adresse)
    (reg : Register → Wort) (fl : Flags) : ByteAusgang :=
  byteschritt (bildZustand bild bias rip reg fl)

/-- IMAGE-TO-FETCH CONNECTION (generic, arbitrary admitted inputs): from
    the checked map (acceptance, member section, section-relative start,
    wrap-free window, file-backed extent, stable section lookup, execute
    permission) derive fetched-bytes agreement, per-byte permission
    agreement, W^X of the code section, and identity of the closing step
    with the actual fetch-execute step. Proved by applying the accepted
    producer lemmas by name; no producer fact is re-proved here. -/
theorem ComposeImageFetch_verbindung
    (p : Profil) (bild : Bild) (bias : Nat) (rip : Adresse)
    (reg : Register → Wort) (fl : Flags) (s : Abschnitt) (k n : Nat)
    (hmem : s ∈ bild.abschnitte)
    (hwf : wohlgeformt p bild = true)
    (hrip : rip.toNat = bias + s.vaddr + k)
    (hfree : ∀ i : Nat, i < n → (addrOff rip i).toNat = rip.toNat + i)
    (hdatei : k + n ≤ s.dateiLen)
    (hstab : ∀ i : Nat, i < n →
      abteilFinden bild.abschnitte bias (rip.toNat + i) = some s)
    (hexe : ∀ i : Nat, i < n →
      (geladen bild bias).ausfuehrbar (addrOff rip i) = true) :
    holeFetchAux (geladen bild bias) rip 0 n =
      ((List.range' 0 n).map fun j =>
        dateiByte bild.datei (s.dateiOff + (k + j))) ∧
    (∀ i : Nat, i < n →
      (geladen bild bias).ausfuehrbar (addrOff rip i) = s.ausfuehrbar) ∧
    wxOk s = true ∧
    imageSchritt bild bias rip reg fl =
      byteschritt (bildZustand bild bias rip reg fl) := by
  have hfr : ∀ i : Nat, i < 0 + n →
      (addrOff rip i).toNat = rip.toNat + i :=
    fun i hi => hfree i (by omega)
  have hda : k + (0 + n) ≤ s.dateiLen := by omega
  have hst : ∀ i : Nat, i < 0 + n →
      abteilFinden bild.abschnitte bias (rip.toNat + i) = some s :=
    fun i hi => hstab i (by omega)
  have hex : ∀ i : Nat, i < 0 + n →
      (geladen bild bias).ausfuehrbar (addrOff rip i) = true :=
    fun i hi => hexe i (by omega)
  refine ⟨holeFetchAux_geladen bild bias rip s 0 k n hrip hfr hda hst hex,
    ?_, wohlgeformt_wx p bild s hmem hwf, rfl⟩
  intro i hi
  have h2 : ladenAusfuehrbar bild bias (rip.toNat + i) = s.ausfuehrbar :=
    geladenAusfuehrbar_fund bild bias _ s (hstab i hi)
  have e : (addrOff rip i).toNat = rip.toNat + i := hfree i hi
  simp only [geladen]
  rw [e]
  exact h2

/-- A fetch headed by a non-executable byte takes nothing: the window
    is empty whatever `cap` follows. -/
theorem fetch_leer_ohne_exec (m : Speicher) (a : Adresse) (off : Nat)
    (h : m.ausfuehrbar (addrOff a off) = false) (cap : Nat) :
    holeFetchAux m a off (cap + 1) = [] := by
  have hne : ¬ (m.ausfuehrbar (addrOff a off) = true) := by simp [h]
  unfold holeFetchAux
  exact if_neg hne

/-- REFUSAL CORE: when the head fetch byte of loaded image memory is not
    executable, the closing step refuses. Fetch takes nothing
    (`fetch_leer_ohne_exec`), the empty window decodes to nothing
    (`decode_nichts_leer`), and the byte step has no transition
    (`byteschritt_verweigert_ohne_fetch`). -/
theorem imageSchritt_kopf_undurchlaessig (bild : Bild) (bias : Nat)
    (rip : Adresse) (reg : Register → Wort) (fl : Flags)
    (h0 : (geladen bild bias).ausfuehrbar (addrOff rip 0) = false) :
    imageSchritt bild bias rip reg fl = .verweigert := by
  have hleer : geholt (bildZustand bild bias rip reg fl) = [] := by
    have hcap : fetchCap = 14 + 1 := rfl
    show holeFetchAux (geladen bild bias) rip 0 fetchCap = []
    rw [hcap]
    exact fetch_leer_ohne_exec (geladen bild bias) rip 0 h0 14
  have hfetch : fetchDekodiert (bildZustand bild bias rip reg fl) = none := by
    unfold fetchDekodiert
    rw [hleer, decode_nichts_leer]
  have hweg := byteschritt_verweigert_ohne_fetch
    (bildZustand bild bias rip reg fl) hfetch
  unfold imageSchritt
  exact hweg

/-- UNMAPPED REFUSAL: starting the instruction pointer outside every loaded
    section admits no closing step. Outside every section nothing is
    executable (`ausserhalb_rahmen`), so the refusal core applies. -/
theorem imageSchritt_loch_verweigert (bild : Bild) (bias : Nat)
    (rip : Adresse) (reg : Register → Wort) (fl : Flags)
    (hloch : abteilFinden bild.abschnitte bias rip.toNat = none)
    (haddr : (addrOff rip 0).toNat = rip.toNat) :
    imageSchritt bild bias rip reg fl = .verweigert := by
  have hperm : ladenAusfuehrbar bild bias rip.toNat = false :=
    (ausserhalb_rahmen bild bias rip.toNat hloch).2.2.2
  have h0 : (geladen bild bias).ausfuehrbar (addrOff rip 0) = false := by
    have h1 : ladenAusfuehrbar bild bias (addrOff rip 0).toNat = false := by
      rw [haddr]
      exact hperm
    simpa [geladen] using h1
  exact imageSchritt_kopf_undurchlaessig bild bias rip reg fl h0

/-- PERMISSION REFUSAL: starting the instruction pointer in a loaded section
    without execute permission admits no closing step. The loaded execute
    permission is the section's (`geladenAusfuehrbar_fund`), which is false
    here, so the refusal core applies. Fetch checks execute permission
    only; data readability is never consulted. -/
theorem imageSchritt_ohne_exec_verweigert (bild : Bild) (bias : Nat)
    (rip : Adresse) (reg : Register → Wort) (fl : Flags) (s : Abschnitt)
    (hfind : abteilFinden bild.abschnitte bias rip.toNat = some s)
    (hnox : s.ausfuehrbar = false)
    (haddr : (addrOff rip 0).toNat = rip.toNat) :
    imageSchritt bild bias rip reg fl = .verweigert := by
  have hperm : ladenAusfuehrbar bild bias rip.toNat = s.ausfuehrbar :=
    geladenAusfuehrbar_fund bild bias _ s hfind
  have h0 : (geladen bild bias).ausfuehrbar (addrOff rip 0) = false := by
    have h1 : ladenAusfuehrbar bild bias (addrOff rip 0).toNat = false := by
      rw [haddr, hperm, hnox]
    simpa [geladen] using h1
  exact imageSchritt_kopf_undurchlaessig bild bias rip reg fl h0

/-- SUCCESS DIRECTION: a successful fetch through the closing step runs the
    existing `schritt` on the fetched instruction (`byteschritt_weiter`).
    The closing step is execution, not a conjunction of checks. -/
theorem imageSchritt_weiter (bild : Bild) (bias : Nat) (rip : Adresse)
    (reg : Register → Wort) (fl : Flags) (d : Decodiert)
    (rest : List Byte) (s' : Zustand)
    (hf : fetchDekodiert (bildZustand bild bias rip reg fl) = some (d, rest))
    (hs : schritt d (bildZustand bild bias rip reg fl) = some s') :
    imageSchritt bild bias rip reg fl = .weiter s' := by
  unfold imageSchritt
  exact byteschritt_weiter _ _ _ _ hf hs

/-- JOINT WITNESS for `ComposeImageFetch_verbindung`: all premises are
    instantiated jointly on the accepted two-section store image
    (executable code plus writable data: the non-degenerate case, the
    image analogue of a written table), with the composed fetch
    connection, a reached memory-changing run through the closing step
    (42 into the data cell, zero before), and planted refusal cases
    (mutated opcode byte, data-section start). -/
theorem ComposeImageFetch_verbindung_zeuge :
    ∃ (p : Profil) (bild : Bild) (bias : Nat) (rip : Adresse)
      (reg : Register → Wort) (fl : Flags) (s : Abschnitt) (k n : Nat),
      s ∈ bild.abschnitte ∧
      wohlgeformt p bild = true ∧
      rip.toNat = bias + s.vaddr + k ∧
      (∀ i : Nat, i < n → (addrOff rip i).toNat = rip.toNat + i) ∧
      k + n ≤ s.dateiLen ∧
      (∀ i : Nat, i < n →
        abteilFinden bild.abschnitte bias (rip.toNat + i) = some s) ∧
      (∀ i : Nat, i < n →
        (geladen bild bias).ausfuehrbar (addrOff rip i) = true) ∧
      holeFetchAux (geladen bild bias) rip 0 n =
        ((List.range' 0 n).map fun j =>
          dateiByte bild.datei (s.dateiOff + (k + j))) ∧
      ausgangByte (BitVec.ofNat 64 0x102000)
        (imageSchritt bild bias rip reg fl) = some (natByte 42) ∧
      bildStoreStart.speicher.bytes (BitVec.ofNat 64 0x102000) =
        BitVec.ofNat 8 0 ∧
      ausgangRip (byteschritt bildStoreStartMutiert) = none ∧
      ausgangRip (byteschritt
        (bildZustand bildStore 0x100000 (BitVec.ofNat 64 0x102000) storeReg
          storeFlags)) = none := by
  have hmemW : bildStoreCode ∈ bildStore.abschnitte := by decide
  have hwfW : wohlgeformt .p48 bildStore = true := bildStore_wohlgeformt
  have hripW : (BitVec.ofNat 64 0x101000).toNat =
      0x100000 + bildStoreCode.vaddr + 0 := by decide
  have hfreeW : ∀ i : Nat, i < 7 →
      (addrOff (BitVec.ofNat 64 0x101000) i).toNat =
        (BitVec.ofNat 64 0x101000).toNat + i := by decide
  have hdateiW : 0 + 7 ≤ bildStoreCode.dateiLen := by decide
  have hstabW : ∀ i : Nat, i < 7 →
      abteilFinden bildStore.abschnitte 0x100000
        ((BitVec.ofNat 64 0x101000).toNat + i) = some bildStoreCode := by
    decide
  have hexeW : ∀ i : Nat, i < 7 →
      (geladen bildStore 0x100000).ausfuehrbar
        (addrOff (BitVec.ofNat 64 0x101000) i) = true := by
    decide
  have hconn := ComposeImageFetch_verbindung .p48 bildStore 0x100000
    (BitVec.ofNat 64 0x101000) storeReg storeFlags bildStoreCode 0 7
    hmemW hwfW hripW hfreeW hdateiW hstabW hexeW
  have hmem2 := bildStore_schritt_speichert
  refine ⟨.p48, bildStore, 0x100000, BitVec.ofNat 64 0x101000, storeReg,
    storeFlags, bildStoreCode, 0, 7, hmemW, hwfW, hripW, hfreeW, hdateiW,
    hstabW, hexeW, hconn.1, ?_, hmem2.2, bildStore_mutiert_verweigert,
    bildStore_datenRip_verweigert⟩
  exact hmem2.1

/- CUTS:
    Proved here, by composing the accepted producer modules (no producer
    fact re-proved, no second loader/decoder/executor/ISA): the one
    checked closing step `imageSchritt` (state memory forced to `geladen`),
    the generic image-to-fetch connection for arbitrary admitted inputs
    (`ComposeImageFetch_verbindung`: fetched-bytes agreement, per-byte
    execute-permission agreement, W^X, step identity), the success
    direction through the existing `schritt` (`imageSchritt_weiter`), the
    refusal core for a non-executable head byte, the unmapped-start
    refusal, the non-executable-section refusal, and one joint
    non-degenerate witness with a reached memory-changing run and planted
    refusals (`ComposeImageFetch_verbindung_zeuge`).
    NOT proved here, and not claimed:
    - No source correspondence: nothing here claims the image bytes are
      the emitted form of any source program, or that duties, contracts,
      costs, locks or call logs refine anything. Source claims stay OPEN.
    - No hardware correspondence: fetch runs over the model `Speicher`
      function, not silicon; caches, TLBs, store buffers, faults beyond
      the decoded refusal, interrupts and timing are OPEN.
    - No whole-binary theorem: no multi-step control-flow validation, no
      entry legality beyond containment, no relocation patched-site
      re-decoding (owner: rel32 lane 561 via `patchSiteOk`), no ABI, cost
      or concurrency claim; the TSO/GX bridge stays with its owner.
    - No termination claim: `verweigert` is the absence of a successful
      transition, never normal program termination.
    - The full 15-byte window equality needs a 15-byte file-backed
      executable extent; the generic connection is stated for an
      arbitrary window `n`, and the joint witness uses `n = 7`.
-/

#print axioms ComposeImageFetch_verbindung
#print axioms ComposeImageFetch_verbindung_zeuge
#print axioms imageSchritt_weiter
#print axioms imageSchritt_kopf_undurchlaessig
#print axioms imageSchritt_loch_verweigert
#print axioms imageSchritt_ohne_exec_verweigert
#print axioms fetch_leer_ohne_exec

end Gabbro.Grammatik.X86
