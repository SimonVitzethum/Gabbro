/-
  Checked validator to loaded fetched execution (lane 598).

  Connects the accepted skeleton admission (`ValidatorSkeleton.valX86`),
  arbitrary-input decoder coverage (`DecodingCoverage.decode_abdeckung`)
  and loaded-image execution (`LoadedExecution.bildZustand`,
  `Byteschritt.fetchDekodiert`/`byteschritt`) to an admitted mapped
  entry's fetch/decode/execution consequence. The old `valX86` Bool
  checks whole-section decode from each section base plus entry
  containment; containment is NOT an instruction boundary, so an
  interior, truncated or BSS entry can be admitted yet refuse to fetch.
  This file proves that gap with concrete counterexamples and adds a
  separate optional strengthened entry check (`valEintrittStark`) with
  generic soundness. The old check and goal are untouched. No source
  refinement and no `valX86_sound` claim is made here (see CUTS).
-/
import Grammatik.X86.ValidatorSkeleton
import Grammatik.X86.DecodingCoverage
import Grammatik.X86.LoadedExecution
import Grammatik.X86.Byteschritt

namespace Gabbro.Grammatik.X86

/-- Strengthened entry admission (OPTIONAL, new): checked image mapping
    AND entry containment in an executable section AND an executable
    byte at the entry AND a successful fetch-and-decode from the actual
    loaded bytes at the entry state. A `Bool`, never a fault claim;
    the old `valX86`/`wohlgeformt` checks are reused, never re-decided. -/
def valEintrittStark (p : Profil) (bild : Bild) (bias e : Nat)
    (reg : Register → Wort) (fl : Flags) : Bool :=
  wohlgeformt p bild &&
  eintragEnthalten bias bild.abschnitte e &&
  ladenAusfuehrbar bild bias e &&
  (fetchDekodiert (bildZustand bild bias (BitVec.ofNat 64 e) reg fl)).isSome

/-- The strengthened check implies the checked image mapping. -/
theorem valStark_wohlgeformt (p : Profil) (bild : Bild) (bias e : Nat)
    (reg : Register → Wort) (fl : Flags)
    (h : valEintrittStark p bild bias e reg fl = true) :
    wohlgeformt p bild = true := by
  unfold valEintrittStark at h
  simp only [Bool.and_eq_true_iff] at h
  exact h.1.1.1

/-- The strengthened check implies entry containment in an
    executable section. -/
theorem valStark_eintrag (p : Profil) (bild : Bild) (bias e : Nat)
    (reg : Register → Wort) (fl : Flags)
    (h : valEintrittStark p bild bias e reg fl = true) :
    eintragEnthalten bias bild.abschnitte e = true := by
  unfold valEintrittStark at h
  simp only [Bool.and_eq_true_iff] at h
  exact h.1.1.2

/-- The strengthened check implies an executable byte at the entry. -/
theorem valStark_ausfuehrbar (p : Profil) (bild : Bild) (bias e : Nat)
    (reg : Register → Wort) (fl : Flags)
    (h : valEintrittStark p bild bias e reg fl = true) :
    ladenAusfuehrbar bild bias e = true := by
  unfold valEintrittStark at h
  simp only [Bool.and_eq_true_iff] at h
  exact h.1.2

/-- The strengthened check implies a successful fetch-and-decode from
    the actual loaded bytes at the entry state. -/
theorem valStark_fetch_exist (p : Profil) (bild : Bild) (bias e : Nat)
    (reg : Register → Wort) (fl : Flags)
    (h : valEintrittStark p bild bias e reg fl = true) :
    ∃ (d : Decodiert) (rest : List Byte),
      fetchDekodiert (bildZustand bild bias (BitVec.ofNat 64 e) reg fl) =
        some (d, rest) := by
  unfold valEintrittStark at h
  simp only [Bool.and_eq_true_iff] at h
  obtain ⟨⟨⟨_, _⟩, _⟩, hfetch⟩ := h
  have hne : fetchDekodiert
      (bildZustand bild bias (BitVec.ofNat 64 e) reg fl) ≠ none := by
    intro hcontra
    simp [hcontra] at hfetch
  rw [Option.ne_none_iff_exists'] at hne
  obtain ⟨pr, hpr⟩ := hne
  cases pr with
  | mk d rest =>
    exact ⟨d, rest, hpr⟩

/-- SECTION/PERMISSION WITNESS: the strengthened check names the actual
    member section holding the entry, with its bounds and its execute
    flag. No second register: `eintragEnthalten` is the check the
    image well-formedness uses. -/
theorem valStark_fundstelle (p : Profil) (bild : Bild) (bias e : Nat)
    (reg : Register → Wort) (fl : Flags)
    (h : valEintrittStark p bild bias e reg fl = true) :
    ∃ s, s ∈ bild.abschnitte ∧ inAbschnitt bias s e = true ∧
      s.ausfuehrbar = true := by
  have he := valStark_eintrag p bild bias e reg fl h
  unfold eintragEnthalten at he
  rw [List.any_eq_true] at he
  obtain ⟨s, hmem, hs⟩ := he
  simp only [Bool.and_eq_true_iff] at hs
  exact ⟨s, hmem, hs.1, hs.2⟩

/-- ENTRY-AT-DECODED-START (generic soundness): from the
    strengthened check, the entry is contained in an executable
    section AND the actual fetched bytes at the loaded entry state
    decode to a covered pilot form at its exact length, with the
    consumed prefix executable. The decode is derived from the real
    validator premise through the actual fetch, never assumed. -/
theorem valStark_gibt_deckung (p : Profil) (bild : Bild) (bias e : Nat)
    (reg : Register → Wort) (fl : Flags)
    (h : valEintrittStark p bild bias e reg fl = true) :
    eintragEnthalten bias bild.abschnitte e = true ∧
    ladenAusfuehrbar bild bias e = true ∧
    ∃ (d : Decodiert) (rest : List Byte),
      fetchDekodiert (bildZustand bild bias (BitVec.ofNat 64 e) reg fl) =
        some (d, rest) ∧
      decktAb d ∧
      d.laenge + rest.length =
        (geholt (bildZustand bild bias (BitVec.ofNat 64 e) reg fl)).length ∧
      laengeOk d.laenge = true ∧
      ausfuehrbarN (bildZustand bild bias (BitVec.ofNat 64 e) reg fl).speicher
        (bildZustand bild bias (BitVec.ofNat 64 e) reg fl).rip d.laenge =
        true := by
  obtain ⟨d, rest, hf⟩ := valStark_fetch_exist p bild bias e reg fl h
  have hdec := (fetchDekodiert_entspricht _ d rest hf).1
  obtain ⟨heq, hok, hshape, _⟩ := decode_abdeckung _ d rest hdec
  refine ⟨valStark_eintrag p bild bias e reg fl h,
    valStark_ausfuehrbar p bild bias e reg fl h,
    d, rest, hf, hshape, heq, hok,
    (fetchDekodiert_entspricht _ d rest hf).2.2.2⟩

/-- LOADED-STEP CONSEQUENCE (generic soundness): from the strengthened
    check, the entry is contained AND the fetched instruction at the
    loaded entry state takes the same byte step as the canonical
    executor. Where the validator premise holds, loaded bytes and the
    decoded step agree; refusal shapes stay refusals. -/
theorem valStark_schritt (p : Profil) (bild : Bild) (bias e : Nat)
    (reg : Register → Wort) (fl : Flags)
    (h : valEintrittStark p bild bias e reg fl = true)
    (s' : Zustand) (d : Decodiert) (rest : List Byte)
    (hf : fetchDekodiert (bildZustand bild bias (BitVec.ofNat 64 e) reg fl) =
      some (d, rest))
    (hs : schritt d (bildZustand bild bias (BitVec.ofNat 64 e) reg fl) =
      some s') :
    eintragEnthalten bias bild.abschnitte e = true ∧
      byteschritt (bildZustand bild bias (BitVec.ofNat 64 e) reg fl) =
        .weiter s' := by
  refine ⟨valStark_eintrag p bild bias e reg fl h,
    byteschritt_weiter _ s' d rest hf hs⟩

/-! ## Counterexample: whole-section decode plus containment
    admits an interior entry.

    The section below holds one 3-byte register move
    (`72 137 216`: REX.W + opcode + ModRM, `movReg64`, length 3), so
    decoding from the section base covers every byte. Both the base
    `0x1000` and the interior byte `0x1001` lie in the executable
    section, so the old `valX86` Bool admits the image. But fetching
    at `0x1001` starts mid-instruction (`137` alone is no canonical
    form) and refuses. Whole-section decode is not entry-at-start. -/

/-- Interior-entry code: one 3-byte move, readable and executable,
    never writable. -/
def innenCode : Abschnitt :=
  { dateiOff := 0, dateiLen := 3, vaddr := 0x1000, memLen := 3,
    lesbar := true, schreibbar := false, ausfuehrbar := true, ausr := 4096 }

/-- Interior-entry image: one 3-byte move, entries at the base and one
    byte inside the instruction. -/
def innenBild : Bild :=
  { datei := [natByte 72, natByte 137, natByte 216]
    abschnitte := [innenCode]
    reloks := []
    eintraege := [0x1000, 0x1001]
    modus := .fest }

/-- The old skeleton admits the image with its interior entry. -/
theorem innen_valX86 : valX86 .p48 innenBild = true := by
  decide

/-- The interior byte is contained in the executable section. -/
theorem innen_eintrag_innen :
    eintragEnthalten 0 innenBild.abschnitte 0x1001 = true := by
  decide

/-- Fetching actual loaded bytes at the interior entry refuses: the
    first byte `137` is no canonical instruction start. -/
theorem innen_fetch_verweigert :
    fetchDekodiert
      (bildZustand innenBild 0 (BitVec.ofNat 64 0x1001) storeReg storeFlags) =
      none := by
  decide

/-- The strengthened check refuses the interior entry, although the
    old skeleton admits the image. -/
theorem innen_stark_verweigert :
    valEintrittStark .p48 innenBild 0 0x1001 storeReg storeFlags =
      false := by
  decide

/-- The base entry passes the strengthened check: the same image, the
    decoded start. -/
theorem innen_stark_basis :
    valEintrittStark .p48 innenBild 0 0x1000 storeReg storeFlags =
      true := by
  decide

/-- INTERIOR COUNTEREXAMPLE (joint): skeleton admits, containment
    admits, fetch refuses, the strengthened check refuses the interior
    entry and admits the base. -/
theorem innen_gegenbeispiel :
    valX86 .p48 innenBild = true ∧
    eintragEnthalten 0 innenBild.abschnitte 0x1001 = true ∧
    fetchDekodiert
      (bildZustand innenBild 0 (BitVec.ofNat 64 0x1001) storeReg storeFlags) =
      none ∧
    valEintrittStark .p48 innenBild 0 0x1001 storeReg storeFlags = false ∧
    valEintrittStark .p48 innenBild 0 0x1000 storeReg storeFlags = true := by
  exact ⟨innen_valX86, innen_eintrag_innen, innen_fetch_verweigert,
    innen_stark_verweigert, innen_stark_basis⟩

/-! ## Truncated, BSS and permission refusals.

    Three more shapes the old containment check admits (or the mapping
    pins) but fetched execution refuses. The truncated shape also pins
    why the strengthened check is fetch-based: decoding the full
    15-byte loaded window (`eintrittDekodiert`) succeeds there by
    reading past the executable boundary, while the actual executable
    fetch (`fetchDekodiert`) refuses. -/

/-- Truncated code: a lone `232` byte, readable and executable. -/
def stumpfCode : Abschnitt :=
  { dateiOff := 0, dateiLen := 1, vaddr := 0x1000, memLen := 1,
    lesbar := true, schreibbar := false, ausfuehrbar := true, ausr := 4096 }

/-- Truncated image: a lone `232` (`call32` opcode without its four
    displacement bytes) as the whole executable section. -/
def stumpfBild : Bild :=
  { datei := [natByte 232]
    abschnitte := [stumpfCode]
    reloks := []
    eintraege := [0x1000]
    modus := .fest }

/-- The mapping admits the truncated entry (containment only). -/
theorem stumpf_eintrag_enthalten :
    eintragEnthalten 0 stumpfBild.abschnitte 0x1000 = true ∧
    wohlgeformt .p48 stumpfBild = true := by
  refine ⟨by decide, by decide⟩

/-- Whole-section decode coverage refuses the truncated section. -/
theorem stumpf_deckung_verweigert :
    bildDeckung stumpfBild = false := by
  decide

/-- The 15-byte loaded window decodes (it reads zeros past the
    executable boundary), but the actual executable fetch refuses:
    `geholt` holds only the one executable byte. -/
theorem stumpf_fetch_verweigert :
    (eintrittDekodiert stumpfBild 0 0x1000).isSome = true ∧
    fetchDekodiert
      (bildZustand stumpfBild 0 (BitVec.ofNat 64 0x1000) storeReg storeFlags) =
      none ∧
    valEintrittStark .p48 stumpfBild 0 0x1000 storeReg storeFlags =
      false := by
  refine ⟨by decide, by decide, by decide⟩

/-- BSS-entry code: the same 3-byte move with a five-byte zero
    tail, readable and executable. -/
def bssEintrittCode : Abschnitt :=
  { dateiOff := 0, dateiLen := 3, vaddr := 0x1000, memLen := 8,
    lesbar := true, schreibbar := false, ausfuehrbar := true, ausr := 4096 }

/-- BSS-entry image: the same 3-byte move with a five-byte zero tail,
    entries at the base and inside the BSS tail. -/
def bssEintrittBild : Bild :=
  { datei := [natByte 72, natByte 137, natByte 216]
    abschnitte := [bssEintrittCode]
    reloks := []
    eintraege := [0x1000, 0x1005]
    modus := .fest }

/-- BSS COUNTEREXAMPLE (joint): the old skeleton admits the image
    with its BSS entry (containment spans `memLen`, decode coverage
    reads only file bytes), yet fetching defined-zero BSS bytes
    refuses, and the strengthened check refuses the BSS entry while
    admitting the base. -/
theorem bss_eintritt_gegenbeispiel :
    valX86 .p48 bssEintrittBild = true ∧
    eintragEnthalten 0 bssEintrittBild.abschnitte 0x1005 = true ∧
    fetchDekodiert
      (bildZustand bssEintrittBild 0 (BitVec.ofNat 64 0x1005) storeReg
        storeFlags) = none ∧
    valEintrittStark .p48 bssEintrittBild 0 0x1005 storeReg storeFlags =
      false ∧
    valEintrittStark .p48 bssEintrittBild 0 0x1000 storeReg storeFlags =
      true := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- Permission mutation: the interior code with execute permission
    cleared. -/
def innenCodeOhneExec : Abschnitt :=
  { dateiOff := 0, dateiLen := 3, vaddr := 0x1000, memLen := 3,
    lesbar := true, schreibbar := false, ausfuehrbar := false,
    ausr := 4096 }

/-- Permission mutation: the interior image with execute permission
    cleared refuses mapping, fetch and the strengthened check. -/
def innenBildOhneExec : Bild :=
  { innenBild with abschnitte := [innenCodeOhneExec] }

/-- PERMISSION REFUSAL (joint): no execute flag means no mapping, no
    fetch and no strengthened admission at either entry. -/
theorem permission_verweigert :
    wohlgeformt .p48 innenBildOhneExec = false ∧
    fetchDekodiert
      (bildZustand innenBildOhneExec 0 (BitVec.ofNat 64 0x1000) storeReg
        storeFlags) = none ∧
    valEintrittStark .p48 innenBildOhneExec 0 0x1000 storeReg storeFlags =
      false ∧
    valEintrittStark .p48 innenBildOhneExec 0 0x1001 storeReg storeFlags =
      false := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-! ## Positive witness: an admitted entry whose loaded step
    changes memory.

    The accepted store image (`LoadedExecution.bildStore`: nonzero
    file offset, base, bias, BSS tail, non-readable code) fetches its
    mapped bytes at the biased entry and steps 42 into the writable
    data section. The strengthened state is definitionally the loaded
    start state, so admission and the memory-changing step share one
    state, not two models. -/

/-- The loaded start state is the strengthened entry state. -/
theorem valStark_store_start :
    bildZustand bildStore 0x100000 (BitVec.ofNat 64 0x101000) storeReg
      storeFlags = bildStoreStart := by
  rfl

/-- ACCEPTANCE: the biased store entry passes the strengthened check. -/
theorem valStark_store_ok :
    valEintrittStark .p48 bildStore 0x100000 0x101000 storeReg storeFlags =
      true := by
  decide

/-- A writable code section refuses the strengthened check on the
    store image (permission mutation of the positive witness). -/
theorem valStark_store_wx_verweigert :
    valEintrittStark .p48 bildStoreWx 0x100000 0x101000 storeReg storeFlags =
      false := by
  decide

/-- JOINT WITNESS: the strengthened entry is admitted, its actual
    fetch decodes the store, one loaded byte step moves 42 into the
    data section (zero before), a real memory-changing write/read
    exists, and the interior entry of the counterexample image is
    refused. Admission, execution and refusal share the actual loaded
    bytes; nothing is a second model. -/
theorem valStark_store_zeuge :
    valEintrittStark .p48 bildStore 0x100000 0x101000 storeReg storeFlags =
      true ∧
    fetchDekodiert bildStoreStart =
      some (⟨.store64 .rbx .rax 0, 7⟩, List.replicate 8 (natByte 0)) ∧
    ausgangByte (BitVec.ofNat 64 0x102000) (byteschritt bildStoreStart) =
      some (natByte 42) ∧
    bildStoreStart.speicher.bytes (BitVec.ofNat 64 0x102000) =
      BitVec.ofNat 8 0 ∧
    (∃ (m m' : Speicher) (a : Adresse) (v : Wort),
      v ≠ 0 ∧ write64 m a v = some m' ∧ read64 m' a = some v ∧
        m.bytes a ≠ m'.bytes a) ∧
    valEintrittStark .p48 innenBild 0 0x1001 storeReg storeFlags =
      false := by
  refine ⟨valStark_store_ok, bildStore_fetch_store,
    bildStore_schritt_speichert.1, bildStore_schritt_speichert.2,
    schreibLese_zeuge, innen_stark_verweigert⟩

/- CUTS:
   Proved here, over the ACTUAL accepted vocabulary
   (`Bild.wohlgeformt`/`eintragEnthalten`/`ladenAusfuehrbar`,
   `ValidatorSkeleton.valX86`/`bildDeckung`,
   `DecodingCoverage.decode_abdeckung`/`eintrittDekodiert`,
   `LoadedExecution.bildZustand`/`bildStore`,
   `Byteschritt.fetchDekodiert`/`byteschritt`/`fetchDekodiert_entspricht`,
   `Bild.schreibLese_zeuge`): the optional strengthened entry check
   (`valEintrittStark`: mapping AND containment AND execute byte AND
   successful fetch from actual loaded bytes) with its mapping, entry,
   permission and fetch-existence projections, the member-section
   witness (`valStark_fundstelle`), the generic entry-at-decoded-start
   consequence (`valStark_gibt_deckung`: covered pilot form at its
   exact length with executable prefix) and the loaded-step
   consequence (`valStark_schritt`: the same decoded step runs), two
   concrete counterexamples admitted by the old Bool yet refusing
   fetch (interior byte `innenBild`, BSS byte `bssEintrittBild`), the
   truncation pin (15-byte window decodes past the boundary while the
   executable fetch refuses), permission-mutation refusals, one
   admitted loaded store with a real memory change and the joint
   witness with planted refusals.
   NOT proved here, and not claimed:
   - No `valX86_sound`: nothing here claims an admitted image is the
     emitted form of any source program, or refines any contract,
     duty, cost, lock or budget. Source correspondence stays OPEN
     (shared IR of lane 287 is PENDING; no substitute is invented).
   - No hardware claim: bytes are model `Byte` lists, memory the model
     `Speicher`; silicon, caches, TLBs, store buffers (per-byte TSO is
     not multi-byte atomicity), interrupts, faults beyond the decoded
     refusal and timing are OPEN. Refusal `Bool`s are validator
     admission, never fault claims.
   - No multi-step control-flow, relocation re-decode, gate/OS
     contract (user logic, never an assumption), concurrency
     (TSO/GX bridge stays with its owner), cost/time or termination
     claim. `verweigert` is the absence of a transition.
   - `valEintrittStark` is OPTIONAL and new: the old `valX86` goal,
     checker and admission are preserved untouched; nothing existing
     is re-decided or weakened.
-/

#print axioms valStark_wohlgeformt
#print axioms valStark_eintrag
#print axioms valStark_ausfuehrbar
#print axioms valStark_fetch_exist
#print axioms valStark_fundstelle
#print axioms valStark_gibt_deckung
#print axioms valStark_schritt
#print axioms innen_valX86
#print axioms innen_eintrag_innen
#print axioms innen_fetch_verweigert
#print axioms innen_stark_verweigert
#print axioms innen_stark_basis
#print axioms innen_gegenbeispiel
#print axioms stumpf_eintrag_enthalten
#print axioms stumpf_deckung_verweigert
#print axioms stumpf_fetch_verweigert
#print axioms bss_eintritt_gegenbeispiel
#print axioms permission_verweigert
#print axioms valStark_store_start
#print axioms valStark_store_ok
#print axioms valStark_store_wx_verweigert
#print axioms valStark_store_zeuge

end Gabbro.Grammatik.X86
