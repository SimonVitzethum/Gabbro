/-
  Loaded image to actual instruction fetch (lane 560).

  Connects the checked `Bild` file/virtual mapping and its actual memory
  construction (`geladen`, `abteilFinden`, `ladenByte`) to the byte fetch
  (`Byteschritt.geholt`, `fetchDekodiert`, `byteschritt`). The checked map
  is a premise; fetched-byte equality and the loaded execution step are
  derived conclusions. No source refinement or hardware correspondence is
  claimed here; both stay explicitly open (see CUTS).
-/
import Grammatik.X86.Bild
import Grammatik.X86.Byteschritt

namespace Gabbro.Grammatik.X86

/-- Execution state over a canonically loaded image: registers, flags and
    `rip` are caller-chosen; memory is the checked `geladen` construction,
    never a second loader. -/
def bildZustand (bild : Bild) (bias : Nat) (rip : Adresse)
    (reg : Register → Wort) (fl : Flags) : Zustand :=
  { register := reg
    flags := fl
    rip := rip
    speicher := geladen bild bias }

/-- The loaded state carries the canonically loaded memory. -/
theorem bildZustand_speicher (bild : Bild) (bias : Nat) (rip : Adresse)
    (reg : Register → Wort) (fl : Flags) :
    (bildZustand bild bias rip reg fl).speicher = geladen bild bias := by
  rfl

/-! ## 1. Checked-map inversion: the acceptance Bool as premise.

    Each fact below takes `wohlgeformt p bild = true` as a premise and
    derives one per-section obligation for a member section. -/

/-- INVERSION (sizes): an accepted image checks every section's size. -/
theorem wohlgeformt_groesse (p : Profil) (bild : Bild) (s : Abschnitt)
    (hmem : s ∈ bild.abschnitte) (h : wohlgeformt p bild = true) :
    groesseOk s = true := by
  have h2 := h
  simp only [wohlgeformt, Bool.and_eq_true] at h2
  have hall : bild.abschnitte.all groesseOk = true :=
    h2.1.1.1.1.1.1.1.1.1.1
  exact (List.all_eq_true.mp hall) s hmem

/-- INVERSION (file containment): every section of an accepted image lies
    inside the file. -/
theorem wohlgeformt_datei (p : Profil) (bild : Bild) (s : Abschnitt)
    (hmem : s ∈ bild.abschnitte) (h : wohlgeformt p bild = true) :
    s.dateiOff + s.dateiLen ≤ bild.datei.length := by
  have h2 := h
  simp only [wohlgeformt, Bool.and_eq_true] at h2
  have hall : bild.abschnitte.all (dateiOk bild.datei) = true :=
    h2.1.1.1.1.1.1.1.1.1.2
  have hs : dateiOk bild.datei s = true :=
    (List.all_eq_true.mp hall) s hmem
  exact of_decide_eq_true hs

/-- INVERSION (W^X): no section of an accepted image is writable and
    executable at once. -/
theorem wohlgeformt_wx (p : Profil) (bild : Bild) (s : Abschnitt)
    (hmem : s ∈ bild.abschnitte) (h : wohlgeformt p bild = true) :
    wxOk s = true := by
  have h2 := h
  simp only [wohlgeformt, Bool.and_eq_true] at h2
  have hall : bild.abschnitte.all wxOk = true :=
    h2.1.1.1.1.1.2
  exact (List.all_eq_true.mp hall) s hmem

/-- INVERSION (alignment): the biased base of every section of an accepted
    image meets its declared alignment. -/
theorem wohlgeformt_ausr (p : Profil) (bild : Bild) (s : Abschnitt)
    (bias : Nat) (hbias : bias = effBias bild.modus)
    (hmem : s ∈ bild.abschnitte) (h : wohlgeformt p bild = true) :
    0 < s.ausr ∧ (bias + s.vaddr) % s.ausr = 0 := by
  have h2 := h
  simp only [wohlgeformt, Bool.and_eq_true] at h2
  have hall : bild.abschnitte.all (ausrOk (effBias bild.modus)) = true :=
    h2.1.1.1.1.1.1.2
  have hs : ausrOk (effBias bild.modus) s = true :=
    (List.all_eq_true.mp hall) s hmem
  rw [← hbias] at hs
  exact of_decide_eq_true hs

/-! ## 2. Fetch from loaded memory: file bytes as fetched prefix.

    The checked map (`abteilFinden` stability, file-backed bounds, execute
    permission, wrap-free window) is the premise; the fetched-byte equality
    over actual `geladen` memory is the derived conclusion. -/

/-- One fetch step: an executable head byte is taken, then fetching
    continues behind it. -/
theorem holeFetchAux_kopf (m : Speicher) (a : Adresse) (off n : Nat)
    (h : m.ausfuehrbar (addrOff a off) = true) :
    holeFetchAux m a off (n + 1) =
      m.bytes (addrOff a off) :: holeFetchAux m a (off + 1) n := by
  simp only [holeFetchAux, h, if_true]

/-- FETCH-INTERIOR (generic): fetching `n` bytes from loaded image memory at
    an interior position yields exactly the mapped file bytes, including
    nonzero file offset (`dateiOff`), base (`vaddr`), bias and interior
    start (`k`). Premises are the checked map: section-relative start,
    a wrap-free window, file-backed extent, stable section lookup and
    execute permission. Data-read permission is never consulted. -/
theorem holeFetchAux_geladen (bild : Bild) (bias : Nat) (rip : Adresse)
    (s : Abschnitt) (off k n : Nat)
    (hrip : rip.toNat = bias + s.vaddr + k)
    (hfree : ∀ i : Nat, i < off + n → (addrOff rip i).toNat = rip.toNat + i)
    (hdatei : k + (off + n) ≤ s.dateiLen)
    (hstab : ∀ i : Nat, i < off + n →
      abteilFinden bild.abschnitte bias (rip.toNat + i) = some s)
    (hexe : ∀ i : Nat, i < off + n →
      (geladen bild bias).ausfuehrbar (addrOff rip i) = true) :
    holeFetchAux (geladen bild bias) rip off n =
      ((List.range' off n).map fun j =>
        dateiByte bild.datei (s.dateiOff + (k + j))) := by
  induction n generalizing off with
  | zero => rfl
  | succ n ih =>
    have hexe0 : (geladen bild bias).ausfuehrbar (addrOff rip off) = true :=
      hexe off (by omega)
    have hr : List.range' off (n + 1) = off :: List.range' (off + 1) n := rfl
    have hhead : (geladen bild bias).bytes (addrOff rip off) =
        dateiByte bild.datei (s.dateiOff + (k + off)) := by
      show ladenByte bild bias (addrOff rip off).toNat = _
      have e1 : (addrOff rip off).toNat = rip.toNat + off :=
        hfree off (by omega)
      have e2 : rip.toNat + off = bias + s.vaddr + (k + off) := by
        rw [hrip]
        omega
      have hfind : abteilFinden bild.abschnitte bias (addrOff rip off).toNat =
          some s := by
        rw [e1]
        exact hstab off (by omega)
      have hhi : (addrOff rip off).toNat < bias + s.vaddr + s.dateiLen := by
        rw [e1, e2]
        omega
      have hbyte := geladenByte_datei bild bias (addrOff rip off).toNat s
        hfind hhi
      have hidx : (addrOff rip off).toNat - (bias + s.vaddr) = k + off := by
        rw [e1, e2]
        omega
      rw [hidx] at hbyte
      exact hbyte
    have htail := ih (off + 1)
      (fun i hi => hfree i (by omega))
      (by omega)
      (fun i hi => hstab i (by omega))
      (fun i hi => hexe i (by omega))
    rw [holeFetchAux_kopf _ _ _ _ hexe0, hr, List.map_cons, hhead, htail]

/-- FETCH-INTERIOR at the state window: the actual 15-byte fetch from a
    loaded image state is the mapped file-byte prefix. -/
theorem geholt_geladen_innen (bild : Bild) (bias : Nat) (rip : Adresse)
    (reg : Register → Wort) (fl : Flags) (s : Abschnitt) (k : Nat)
    (hrip : rip.toNat = bias + s.vaddr + k)
    (hfree : ∀ i : Nat, i < fetchCap → (addrOff rip i).toNat = rip.toNat + i)
    (hdatei : k + fetchCap ≤ s.dateiLen)
    (hstab : ∀ i : Nat, i < fetchCap →
      abteilFinden bild.abschnitte bias (rip.toNat + i) = some s)
    (hexe : ∀ i : Nat, i < fetchCap →
      (geladen bild bias).ausfuehrbar (addrOff rip i) = true) :
    geholt (bildZustand bild bias rip reg fl) =
      ((List.range' 0 fetchCap).map fun j =>
        dateiByte bild.datei (s.dateiOff + (k + j))) := by
  have hwin := holeFetchAux_geladen bild bias rip s 0 k fetchCap hrip
    (fun i hi => hfree i (by omega))
    (by omega)
    (fun i hi => hstab i (by omega))
    (fun i hi => hexe i (by omega))
  unfold geholt
  show holeFetchAux (geladen bild bias) rip 0 fetchCap = _
  exact hwin

/-- FETCH-BSS (generic): fetching inside the zero-defined tail of a loaded
    section yields zero bytes. The window lies past the file-backed part
    (`hlo`) but inside the section (`hstab`); execute permission still
    gates every byte. -/
theorem holeFetchAux_geladen_bss (bild : Bild) (bias : Nat) (rip : Adresse)
    (s : Abschnitt) (off n : Nat)
    (hfree : ∀ i : Nat, i < off + n → (addrOff rip i).toNat = rip.toNat + i)
    (hlo : ∀ i : Nat, i < off + n →
      bias + s.vaddr + s.dateiLen ≤ rip.toNat + i)
    (hstab : ∀ i : Nat, i < off + n →
      abteilFinden bild.abschnitte bias (rip.toNat + i) = some s)
    (hexe : ∀ i : Nat, i < off + n →
      (geladen bild bias).ausfuehrbar (addrOff rip i) = true) :
    holeFetchAux (geladen bild bias) rip off n =
      List.replicate n (BitVec.ofNat 8 0) := by
  induction n generalizing off with
  | zero => rfl
  | succ n ih =>
    have hexe0 : (geladen bild bias).ausfuehrbar (addrOff rip off) = true :=
      hexe off (by omega)
    have hhead : (geladen bild bias).bytes (addrOff rip off) =
        BitVec.ofNat 8 0 := by
      show ladenByte bild bias (addrOff rip off).toNat = _
      have e1 : (addrOff rip off).toNat = rip.toNat + off :=
        hfree off (by omega)
      have hfind : abteilFinden bild.abschnitte bias (addrOff rip off).toNat =
          some s := by
        rw [e1]
        exact hstab off (by omega)
      have hlo0 : bias + s.vaddr + s.dateiLen ≤ (addrOff rip off).toNat := by
        rw [e1]
        exact hlo off (by omega)
      exact geladenByte_bss bild bias (addrOff rip off).toNat s hfind hlo0
    have htail := ih (off + 1)
      (fun i hi => hfree i (by omega))
      (fun i hi => hlo i (by omega))
      (fun i hi => hstab i (by omega))
      (fun i hi => hexe i (by omega))
    rw [holeFetchAux_kopf _ _ _ _ hexe0, List.replicate_succ, hhead, htail]

/-! ## 3. Execute/data permission distinction.

    Fetch consults execute permission only, never data-read permission:
    flipping `lesbar` everywhere changes neither the fetched window nor
    the fetch-and-decode outcome. -/

/-- Fetch is independent of data-read permission. -/
theorem holeFetchAux_lesbar_unabhaengig (m : Speicher) (l : Adresse → Bool)
    (a : Adresse) (off cap : Nat) :
    holeFetchAux { m with lesbar := l } a off cap =
      holeFetchAux m a off cap := by
  induction cap generalizing off with
  | zero => rfl
  | succ n ih =>
    simp only [holeFetchAux, ih]

/-- The state fetch window is independent of data-read permission. -/
theorem geholt_lesbar_unabhaengig (s : Zustand) (l : Adresse → Bool) :
    geholt { s with speicher := { s.speicher with lesbar := l } } =
      geholt s := by
  unfold geholt
  show holeFetchAux { s.speicher with lesbar := l } s.rip 0 fetchCap = _
  exact holeFetchAux_lesbar_unabhaengig s.speicher l s.rip 0 fetchCap

/-- The consumed-prefix execute check is independent of data-read
    permission. -/
theorem ausfuehrbarN_lesbar_unabhaengig (m : Speicher) (l : Adresse → Bool)
    (a : Adresse) (n : Nat) :
    ausfuehrbarN { m with lesbar := l } a n = ausfuehrbarN m a n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ausfuehrbarN, ih]

/-- Fetch-and-decode is independent of data-read permission: the whole
    `fetchDekodiert` outcome consults execute permission only. -/
theorem fetchDekodiert_lesbar_unabhaengig (s : Zustand)
    (l : Adresse → Bool) :
    fetchDekodiert { s with speicher := { s.speicher with lesbar := l } } =
      fetchDekodiert s := by
  have hg := geholt_lesbar_unabhaengig s l
  have ha : ∀ d : Decodiert, ausfuehrbarN
      ({ s with speicher := { s.speicher with lesbar := l } } : Zustand).speicher
      ({ s with speicher := { s.speicher with lesbar := l } } : Zustand).rip
        d.laenge =
      ausfuehrbarN s.speicher s.rip d.laenge := by
    intro d
    show ausfuehrbarN { s.speicher with lesbar := l } s.rip d.laenge = _
    exact ausfuehrbarN_lesbar_unabhaengig s.speicher l s.rip d.laenge
  unfold fetchDekodiert
  simp only [hg, ha]

/-! ## 4. Concrete loaded execution: a store through checked mapping.

    One accepted image with nonzero file offset (`dateiOff = 3`), base
    (`vaddr = 0x1000`), bias (`0x100000`), a BSS tail on the executable
    section, and a code section that is NOT data-readable: fetch still
    succeeds because only execute permission gates it. -/

/-- Store-image file: three unmapped pad bytes, the 7-byte store encoding,
    then eight zero data bytes. -/
def bildStoreDatei : List Byte :=
  [natByte 144, natByte 144, natByte 144,
   natByte 72, natByte 137, natByte 131, natByte 0, natByte 0, natByte 0,
   natByte 0] ++
  List.replicate 8 (natByte 0)

/-- Store-image code section: file offset 3, executable with a BSS tail,
    deliberately not data-readable. -/
def bildStoreCode : Abschnitt :=
  { dateiOff := 3, dateiLen := 7, vaddr := 0x1000, memLen := 16,
    lesbar := false, schreibbar := false, ausfuehrbar := true, ausr := 4096 }

/-- Store-image data section: eight file bytes plus eight BSS bytes,
    readable and writable, never executable. -/
def bildStoreDaten : Abschnitt :=
  { dateiOff := 10, dateiLen := 8, vaddr := 0x2000, memLen := 16,
    lesbar := true, schreibbar := true, ausfuehrbar := false, ausr := 4096 }

/-- The store image: code plus data under a checked parametric base. -/
def bildStore : Bild :=
  { datei := bildStoreDatei
    abschnitte := [bildStoreCode, bildStoreDaten]
    reloks := []
    eintraege := [0x101000]
    modus := .param 0x100000 }

/-- Store operands: the value in `rax`, its data target in `rbx`. -/
def storeReg : Register → Wort := fun q =>
  if q = Register.rax then BitVec.ofNat 64 42
  else if q = Register.rbx then BitVec.ofNat 64 0x102000
  else BitVec.ofNat 64 0

/-- Store flags: nothing set. -/
def storeFlags : Flags :=
  { cf := false, pf := true, af := some false, zf := false, sf := false,
    of := false }

/-- Loaded start state: the store image at its checked base, `rip` at the
    biased entry. -/
def bildStoreStart : Zustand :=
  bildZustand bildStore 0x100000 (BitVec.ofNat 64 0x101000) storeReg
    storeFlags

/-- ACCEPTANCE: the store image validates under profile 48. -/
theorem bildStore_wohlgeformt :
    wohlgeformt .p48 bildStore = true := by
  decide

/-- FETCH-INTERIOR on the store image: the first seven fetched bytes are
    exactly the mapped file bytes at nonzero offset 3, base `0x1000` and
    bias `0x100000`. An application of the generic `holeFetchAux_geladen`,
    with every checked-map premise discharged by decision. -/
theorem bildStore_datei_vorne :
    holeFetchAux (geladen bildStore 0x100000) (BitVec.ofNat 64 0x101000) 0 7 =
      ((List.range' 0 7).map fun j =>
        dateiByte bildStore.datei (bildStoreCode.dateiOff + (0 + j))) := by
  have h := holeFetchAux_geladen bildStore 0x100000 (BitVec.ofNat 64 0x101000)
    bildStoreCode 0 0 7
    (by decide)
    (by decide)
    (by decide)
    (by decide)
    (by decide)
  exact h

/-- LOADED FETCH: the start state's actual fetch decodes to the store with
    an eight-byte zero rest (seven file bytes plus eight BSS zeros). The
    code section is not data-readable, yet fetch succeeds. -/
theorem bildStore_fetch_store :
    fetchDekodiert bildStoreStart =
      some (⟨.store64 .rbx .rax 0, 7⟩, List.replicate 8 (natByte 0)) := by
  decide

/-- LOADED STORE EXECUTION: one byte step from loaded image memory moves 42
    into the data section; the cell read zero before. A real reached
    memory-changing execution over `geladen` memory, through `byteschritt`
    rather than a hand-fed `schritt`. -/
theorem bildStore_schritt_speichert :
    ausgangByte (BitVec.ofNat 64 0x102000) (byteschritt bildStoreStart) =
      some (natByte 42) ∧
    bildStoreStart.speicher.bytes (BitVec.ofNat 64 0x102000) =
      BitVec.ofNat 8 0 := by
  decide

/-- BSS FETCH on the store image: fetching at the executable BSS tail
    yields the defined zero byte, through the generic BSS lemma. -/
theorem bildStore_bss_geholt :
    holeFetchAux (geladen bildStore 0x100000) (BitVec.ofNat 64 0x10100F) 0 1 =
      List.replicate 1 (BitVec.ofNat 8 0) := by
  have h := holeFetchAux_geladen_bss bildStore 0x100000
    (BitVec.ofNat 64 0x10100F) bildStoreCode 0 1
    (by decide)
    (by decide)
    (by decide)
    (by decide)
  exact h

/-! ## 5. Negative probes: mutation, permission, mapping. -/

/-- Mutated store image: the first executed opcode byte carries the REX.X
    bit, which the canonical decoder refuses. -/
def bildStoreMutiert : Bild :=
  { bildStore with datei :=
    ([natByte 144, natByte 144, natByte 144,
      natByte 74, natByte 137, natByte 131, natByte 0, natByte 0, natByte 0,
      natByte 0] ++
    List.replicate 8 (natByte 0)) }

/-- Start state over the mutated image. -/
def bildStoreStartMutiert : Zustand :=
  bildZustand bildStoreMutiert 0x100000 (BitVec.ofNat 64 0x101000) storeReg
    storeFlags

/-- MUTATION PIN: the mutated image still passes the checked mapping; the
    refusal below comes from decoding, never from the map. -/
theorem bildStore_mutiert_mapping_bleibt :
    wohlgeformt .p48 bildStoreMutiert = true := by
  decide

/-- MUTATION REFUSAL: the forged opcode byte turns the loaded step into a
    refusal, while the checked mapping still holds. -/
theorem bildStore_mutiert_verweigert :
    ausgangRip (byteschritt bildStoreStartMutiert) = none := by
  decide

/-- PERMISSION REFUSAL: starting the instruction pointer in the data
    section admits no fetch. Data readability without executability is
    not enough; fetch checks execute permission only. -/
theorem bildStore_datenRip_verweigert :
    ausgangRip (byteschritt
      (bildZustand bildStore 0x100000 (BitVec.ofNat 64 0x102000) storeReg
        storeFlags)) = none := by
  decide

/-- Writable-and-executable code section: refused by the checked mapping. -/
def bildStoreWx : Bild :=
  { bildStore with
    abschnitte := [{ bildStoreCode with schreibbar := true }, bildStoreDaten] }

/-- W^X REFUSAL: a writable code section is not an accepted image. -/
theorem bildStoreWx_verweigert :
    wohlgeformt .p48 bildStoreWx = false := by
  decide

/-- MAPPING REFUSAL: starting the instruction pointer in the hole between
    the loaded sections admits no fetch. -/
theorem bildStore_lochRip_verweigert :
    ausgangRip (byteschritt
      (bildZustand bildStore 0x100000 (BitVec.ofNat 64 0x101800) storeReg
        storeFlags)) = none := by
  decide

/-- Image whose entry lies outside every section. -/
def bildStoreEintrittAussen : Bild :=
  { bildStore with eintraege := [0x103000] }

/-- ENTRY REFUSAL: an entry outside every loaded section is not accepted. -/
theorem bildStoreEintrittAussen_verweigert :
    wohlgeformt .p48 bildStoreEintrittAussen = false := by
  decide

/-- JOINT WITNESS: the accepted store image fetches its mapped file bytes,
    one loaded byte step moves 42 into the writable data section (zero
    before), and the mutated image as well as the data-section start
    refuse. Joint instantiation of the generic fetch connection on a
    nondegenerate image with real reached memory-changing execution and
    planted refusals. -/
theorem bildStore_ausfuehrung_zeuge :
    wohlgeformt .p48 bildStore = true ∧
    holeFetchAux (geladen bildStore 0x100000) (BitVec.ofNat 64 0x101000) 0 7 =
      ((List.range' 0 7).map fun j =>
        dateiByte bildStore.datei (bildStoreCode.dateiOff + (0 + j))) ∧
    ausgangByte (BitVec.ofNat 64 0x102000) (byteschritt bildStoreStart) =
      some (natByte 42) ∧
    bildStoreStart.speicher.bytes (BitVec.ofNat 64 0x102000) =
      BitVec.ofNat 8 0 ∧
    ausgangRip (byteschritt bildStoreStartMutiert) = none ∧
    ausgangRip (byteschritt
      (bildZustand bildStore 0x100000 (BitVec.ofNat 64 0x102000) storeReg
        storeFlags)) = none := by
  exact ⟨bildStore_wohlgeformt, bildStore_datei_vorne,
    bildStore_schritt_speichert.1, bildStore_schritt_speichert.2,
    bildStore_mutiert_verweigert, bildStore_datenRip_verweigert⟩

/- CUTS:
   Proved here, over the ACTUAL accepted vocabulary (`Bild.wohlgeformt`,
   `geladen`/`abteilFinden`/`ladenByte`, `Byteschritt.geholt`,
   `fetchDekodiert`, `byteschritt`): acceptance-premise inversion to
   per-section facts (`wohlgeformt_groesse/datei/wx/ausr`), the generic
   fetch-interior equality from the checked map to the fetched prefix
   (`holeFetchAux_geladen`, `geholt_geladen_innen`) with nonzero file
   offset, base, bias and interior start, the BSS zero fetch
   (`holeFetchAux_geladen_bss`), execute/data-read distinction
   (fetch and fetch-and-decode never consult `lesbar`), one accepted
   store image with nonzero offset/base/bias and BSS executed through
   `byteschritt` to a real memory change, the generic lemmas applied
   to it, one joint nondegenerate witness with planted refusals, and
   mutation/permission/mapping negative probes.
   NOT proved here, and not claimed:
   - No source refinement: nothing here claims the bytes are the emitted
     form of any source program, or that duties, contracts, costs or
     locks refine anything. Source correspondence stays OPEN.
   - No hardware correspondence: fetch runs over the model `Speicher`
     function, not silicon; caches, TLBs, store buffers, interrupts,
     faults beyond the decoded refusal and timing are OPEN.
   - No whole-binary theorem: no multi-step control-flow validation, no
     entry legality beyond containment, no relocation correspondence
     (patched-site re-decoding stays OPEN), no ABI or cost claim.
   - No concurrency claim: every step here is sequential over one
     `Speicher`; the TSO/GX bridge stays with its owner.
   - `verweigert` is the absence of a successful transition, never normal
     program termination; termination stays OPEN.
-/

#print axioms bildZustand_speicher
#print axioms wohlgeformt_groesse
#print axioms wohlgeformt_datei
#print axioms wohlgeformt_wx
#print axioms wohlgeformt_ausr
#print axioms holeFetchAux_kopf
#print axioms holeFetchAux_geladen
#print axioms geholt_geladen_innen
#print axioms holeFetchAux_geladen_bss
#print axioms holeFetchAux_lesbar_unabhaengig
#print axioms geholt_lesbar_unabhaengig
#print axioms ausfuehrbarN_lesbar_unabhaengig
#print axioms fetchDekodiert_lesbar_unabhaengig
#print axioms bildStore_wohlgeformt
#print axioms bildStore_datei_vorne
#print axioms bildStore_fetch_store
#print axioms bildStore_schritt_speichert
#print axioms bildStore_bss_geholt
#print axioms bildStore_mutiert_mapping_bleibt
#print axioms bildStore_mutiert_verweigert
#print axioms bildStore_datenRip_verweigert
#print axioms bildStoreWx_verweigert
#print axioms bildStore_lochRip_verweigert
#print axioms bildStoreEintrittAussen_verweigert
#print axioms bildStore_ausfuehrung_zeuge

end Gabbro.Grammatik.X86
