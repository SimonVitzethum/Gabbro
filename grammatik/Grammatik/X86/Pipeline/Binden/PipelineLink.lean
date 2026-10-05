/-
  File:      Grammatik/X86/PipelineLink.lean
  Subject:   Generic linking of separately lowered units: symbol
             resolution, relocation operands (rel32/abs64) applied then
             re-decoded, file offsets vs virtual addresses vs load bias
             checked against the ACTUAL executed mapping, W^X.

             Reused, not duplicated (no second decoder, loader, executor,
             ISA model or IR):
             - patching: `Relokation.patchAt`/`patchRel32`/`patchAbs64`
               with `patchAt_bereich`/`_stelle`/`_rahmen`, `rel32Bytes`,
               `abs64Bytes`, `patchRel32_stelle`, `patchAbs64_stelle`;
             - re-decode: `ComposePatchBytes.ComposePatchBytes_feld_verbindung`
               (patched displacement re-decoded, through decoder
               determinism, never decoder internals);
             - mapping: `Bild.geladen`/`ladenByte`/`abteilFinden` with
               `geladenByte_datei`, `ValidatorSkeleton.transferOk`,
               `LoadedExecution.wohlgeformt_wx`;
             - run: `RelocatedExecution.ruf_schritt_zeuge` (reached
               memory-changing call run through actual bytes).
             The pipeline connection (`Pipeline.pipeline_correct`) is NOT
             remade here: units arrive already lowered, linking only
             concatenates, resolves, patches and re-checks.
-/
import Grammatik.X86.Kern.Bild
import Grammatik.X86.Laden.Relokation
import Grammatik.X86.Laden.RelocatedExecution
import Grammatik.X86.Validierung.DecodingCoverage
import Grammatik.X86.Validierung.ValidatorSkeleton
import Grammatik.X86.Laden.LoadedExecution
import Grammatik.X86.Compose.Bild.ComposePatchBytes
namespace Gabbro.Grammatik.X86

/-- One separately lowered unit: its bytes and its link-time virtual base.
    File offsets never become virtual addresses directly: byte `k` of
    unit `u` maps to `bias + u.vaddr + k`. -/
structure LinkEinheit where
  bytes : List Byte
  vaddr : Nat
  deriving DecidableEq, Repr

/-- Linked file bytes: concatenation of the units' bytes, in link order. -/
def verknuepfeDatei (a b : LinkEinheit) : List Byte :=
  a.bytes ++ b.bytes

/-- Relocation operand kind at link time: rel32 displacement or abs64
    value. Only these two operand shapes link here; every other shape
    is refused (`none`), never guessed. -/
inductive LinkFeld where
  | rel32 (disp : Int)
  | abs64 (wert : Wort)
  deriving DecidableEq, Repr

/-- The bytes one operand writes: the canonical rel32/abs64 split,
    never a second codec. -/
def feldBytes : LinkFeld → List Byte
  | .rel32 d => rel32Bytes d
  | .abs64 v => abs64Bytes v

/-- Apply one relocation operand at file offset `off`. rel32 refuses
    out-of-range displacements with `none`; abs64 patches eight bytes
    at any in-range site. -/
def linkPatch (img : List Byte) (off : Nat) : LinkFeld → Option (List Byte)
  | .rel32 d => patchRel32 img off d
  | .abs64 v => patchAbs64 img off v

/-- Symbol table: relocation id to resolved absolute target address.
    Only a listed id resolves; anything else stays `none` (refused,
    never defaulted). -/
def loeseSymbol : List (Nat × Nat) → Nat → Option Nat
  | [], _ => none
  | (id, w) :: rest, q => if id = q then some w else loeseSymbol rest q

/-- A rel32 operand is four bytes wide. -/
theorem feldBytes_rel32_laenge (d : Int) :
    (feldBytes (.rel32 d)).length = 4 := by
  simp [feldBytes, rel32Bytes_laenge]

/-- An abs64 operand is eight bytes wide. -/
theorem feldBytes_abs64_laenge (v : Wort) :
    (feldBytes (.abs64 v)).length = 8 := by
  simp [feldBytes, abs64Bytes_laenge]

/-! ## 1. Symbol resolution: only listed ids resolve. -/

/-- A listed id resolves to its listed absolute target. -/
theorem loeseSymbol_trifft (tab : List (Nat × Nat)) (q w : Nat) :
    loeseSymbol ((q, w) :: tab) q = some w := by
  simp [loeseSymbol]

/-- Nothing resolves in the empty table. -/
theorem loeseSymbol_leer (q : Nat) : loeseSymbol [] q = none := rfl

/-- An unlisted id refuses, never defaults. Both premises are
    load-bearing: `hne` picks the `else` branch, `ih` runs the tail. -/
theorem loeseSymbol_fremd_verweigert (id w q : Nat) (tab : List (Nat × Nat))
    (hne : id ≠ q) (ih : loeseSymbol tab q = none) :
    loeseSymbol ((id, w) :: tab) q = none := by
  simp only [loeseSymbol, if_neg hne, ih]

/-! ## 2. One applied operand: range, site bytes, frame, length.

    NO relocation changes a byte outside its operand: `linkPatch_rahmen`
    is the frame leg every link closing below carries. Each proof goes
    through the accepted `patchAt_*` producer facts by case on the
    operand kind; the rel32 leg additionally discharges the fit check
    that `patchRel32` gates on. -/

/-- A successful link patch lies inside the image. -/
theorem linkPatch_bereich (img : List Byte) (off : Nat) (f : LinkFeld)
    (out : List Byte) (h : linkPatch img off f = some out) :
    off + (feldBytes f).length ≤ img.length := by
  cases f with
  | rel32 d =>
    simp only [linkPatch, feldBytes] at h ⊢
    unfold patchRel32 at h
    split at h
    · exact patchAt_bereich img off (rel32Bytes d) out h
    · cases h
  | abs64 v =>
    simp only [linkPatch, feldBytes, patchAbs64] at h ⊢
    exact patchAt_bereich img off (abs64Bytes v) out h

/-- A successful link patch writes exactly the operand bytes. -/
theorem linkPatch_stelle (img : List Byte) (off : Nat) (f : LinkFeld)
    (out : List Byte) (h : linkPatch img off f = some out)
    (k : Nat) (hk : k < (feldBytes f).length) :
    out[off + k]? = (feldBytes f)[k]? := by
  cases f with
  | rel32 d =>
    simp only [linkPatch] at h
    simp only [feldBytes] at hk ⊢
    rw [rel32Bytes_laenge] at hk
    exact patchRel32_stelle img off d out h k hk
  | abs64 v =>
    simp only [linkPatch, patchAbs64] at h
    simp only [feldBytes] at hk ⊢
    rw [abs64Bytes_laenge] at hk
    exact patchAbs64_stelle img off v out h k hk

/-- FRAME: bytes outside the operand keep their image bytes. No
    relocation, rel32 or abs64, touches anything else. -/
theorem linkPatch_rahmen (img : List Byte) (off : Nat) (f : LinkFeld)
    (out : List Byte) (h : linkPatch img off f = some out)
    (i : Nat) (haussen : ∀ k, k < (feldBytes f).length → i ≠ off + k) :
    out[i]? = img[i]? := by
  cases f with
  | rel32 d =>
    simp only [linkPatch] at h
    simp only [feldBytes] at haussen
    unfold patchRel32 at h
    split at h
    · exact patchAt_rahmen img off (rel32Bytes d) out h i haussen
    · cases h
  | abs64 v =>
    simp only [linkPatch, patchAbs64] at h
    simp only [feldBytes] at haussen
    exact patchAt_rahmen img off (abs64Bytes v) out h i haussen

/-- A successful link patch keeps the image length. -/
theorem linkPatch_laenge (img : List Byte) (off : Nat) (f : LinkFeld)
    (out : List Byte) (h : linkPatch img off f = some out) :
    out.length = img.length := by
  cases f with
  | rel32 d =>
    simp only [linkPatch] at h
    unfold patchRel32 at h
    split at h
    · exact patchAt_laenge img off (rel32Bytes d) out h
    · cases h
  | abs64 v =>
    simp only [linkPatch, patchAbs64] at h
    exact patchAt_laenge img off (abs64Bytes v) out h

/-! ## 3. The linked image: two units, one file, checked mapping.

    File offsets vs virtual addresses vs load bias: byte `k` of unit `u`
    maps to `bias + u.vaddr + k`, through the ACTUAL `geladen` mapping --
    never by adding a file offset to an address. Both code sections are
    executable and NOT writable (W^X); data, entries and relocations
    beyond the two code sections are OPEN (see CUTS). -/

/-- Code section of unit A: A's bytes at A's base, executable, not writable. -/
def linkAbschnittA (a : LinkEinheit) (_b : LinkEinheit) : Abschnitt :=
  { dateiOff := 0, dateiLen := a.bytes.length, vaddr := a.vaddr,
    memLen := a.bytes.length, lesbar := true, schreibbar := false,
    ausfuehrbar := true, ausr := 1 }

/-- Code section of unit B: B's bytes behind A's, at B's base. -/
def linkAbschnittB (a b : LinkEinheit) : Abschnitt :=
  { dateiOff := a.bytes.length, dateiLen := b.bytes.length,
    vaddr := b.vaddr, memLen := b.bytes.length, lesbar := true,
    schreibbar := false, ausfuehrbar := true, ausr := 1 }

/-- The linked image over explicit file bytes (patched or not), with the
    entry vector and fixed bias. `reloks` stays empty: every relocation
    is already applied by `linkPatch`, never pending. -/
def linkBildAus (a b : LinkEinheit) (datei : List Byte)
    (eintrag : Nat) : Bild :=
  { datei := datei
    abschnitte := [linkAbschnittA a b, linkAbschnittB a b]
    reloks := []
    eintraege := [eintrag]
    modus := .fest }

/-- The linked image over the unpatched concatenation. -/
def linkBild (a b : LinkEinheit) (eintrag : Nat) : Bild :=
  linkBildAus a b (verknuepfeDatei a b) eintrag

/-- COVERAGE UNION: the linked image's decode coverage equals the union
    of the units' coverages -- each unit's section coverage, conjoined.
    Proved by unfolding `bildDeckung` over the two-section list; no
    decoder fact is re-proved. -/
theorem verknuepft_abdeckung_union (a b : LinkEinheit) (datei : List Byte)
    (eintrag : Nat) :
    bildDeckung (linkBildAus a b datei eintrag) =
      (abschnittDeckung (linkBildAus a b datei eintrag) (linkAbschnittA a b) &&
        abschnittDeckung (linkBildAus a b datei eintrag)
          (linkAbschnittB a b)) := by
  simp [bildDeckung, linkBildAus]

/-- MAPPING: a found virtual address loads the mapped file byte, through
    the ACTUAL `geladen` mapping. File offsets never become addresses
    directly: the site start is always `bias + vaddr + off`. -/
theorem verknuepft_byte_geladen (a b : LinkEinheit) (datei : List Byte)
    (eintrag bias va : Nat) (s : Abschnitt)
    (hfind : abteilFinden (linkBildAus a b datei eintrag).abschnitte bias va =
      some s)
    (hhi : va < bias + s.vaddr + s.dateiLen) :
    ladenByte (linkBildAus a b datei eintrag) bias va =
      dateiByte (linkBildAus a b datei eintrag).datei
        (s.dateiOff + (va - (bias + s.vaddr))) :=
  geladenByte_datei _ _ _ _ hfind hhi

/-- W^X: every member section of a well-formed linked image is not
    writable-and-executable. -/
theorem verknuepft_wx (p : Profil) (a b : LinkEinheit) (datei : List Byte)
    (eintrag : Nat) (s : Abschnitt)
    (hmem : s ∈ (linkBildAus a b datei eintrag).abschnitte)
    (hwf : wohlgeformt p (linkBildAus a b datei eintrag) = true) :
    wxOk s = true :=
  wohlgeformt_wx p _ s hmem hwf

/-! ## 4. The link closing: patch, re-decode, mapping, W^X. -/

/-- RE-DECODE: a patched rel32 jump operand re-decodes to the patched
    displacement, through the accepted producer closing (decoder
    determinism, never decoder internals). -/
theorem verknuepft_rel32_schliesst (img : List Byte) (istart : Nat)
    (disp : Int) (out : List Byte) (d : BitVec 32) (rest : List Byte)
    (himg : img[istart]? = some (natByte 233))
    (hpatch : patchRel32 img (istart + 1) disp = some out)
    (hdec : decode (out.drop istart) = some ((⟨.jump32 d, 5⟩, rest))) :
    dispSigned d = disp ∧
    5 + rest.length = (out.drop istart).length ∧
    rel32Passt disp = true ∧
    out[istart]? = some (natByte 233) ∧
    (∀ k, k < 4 → out[istart + 1 + k]? = (rel32Bytes disp)[k]?) ∧
    decktAb ⟨.jump32 d, 5⟩ ∧
    decode ((out.drop istart).take 5 ++ rest) =
      some ((⟨.jump32 d, 5⟩, rest)) :=
  ComposePatchBytes_feld_verbindung img istart disp out d rest himg
    hpatch hdec

/-- **LINK CORRECTNESS.** For two separately lowered units linked in
    order, one applied rel32 operand at a jump opcode, its re-decode,
    and the checked linked image over the PATCHED bytes: the re-decoded
    displacement is the patched value, the fit holds, the form is
    covered, the linked decode coverage is the union of the units', the
    section is W^X, the executed mapping loads the patched file byte,
    the site lies in range, and no byte outside the operand changed.
    Every premise is load-bearing (see the proof). -/
theorem verknuepft_korrekt
    (a b : LinkEinheit) (eintrag istart : Nat) (disp : Int)
    (out : List Byte) (d : BitVec 32) (rest : List Byte)
    (s : Abschnitt) (va i : Nat)
    (hpatch : linkPatch (verknuepfeDatei a b) (istart + 1) (.rel32 disp) =
      some out)
    (himg : (verknuepfeDatei a b)[istart]? = some (natByte 233))
    (hdec : decode (out.drop istart) = some ((⟨.jump32 d, 5⟩, rest)))
    (hwf : wohlgeformt .p48 (linkBildAus a b out eintrag) = true)
    (hmem : s ∈ (linkBildAus a b out eintrag).abschnitte)
    (hfind : abteilFinden (linkBildAus a b out eintrag).abschnitte 0 va =
      some s)
    (hhi : va < 0 + s.vaddr + s.dateiLen)
    (haussen : ∀ k, k < (feldBytes (.rel32 disp)).length →
      i ≠ (istart + 1) + k) :
    dispSigned d = disp ∧
    rel32Passt disp = true ∧
    decktAb ⟨.jump32 d, 5⟩ ∧
    bildDeckung (linkBildAus a b out eintrag) =
      (abschnittDeckung (linkBildAus a b out eintrag) (linkAbschnittA a b) &&
        abschnittDeckung (linkBildAus a b out eintrag)
          (linkAbschnittB a b)) ∧
    wxOk s = true ∧
    ladenByte (linkBildAus a b out eintrag) 0 va =
      dateiByte out (s.dateiOff + (va - (0 + s.vaddr))) ∧
    istart + 1 + (feldBytes (.rel32 disp)).length ≤
      (verknuepfeDatei a b).length ∧
    out[i]? = (verknuepfeDatei a b)[i]? := by
  have hpr : patchRel32 (verknuepfeDatei a b) (istart + 1) disp =
      some out := hpatch
  have hfeld := ComposePatchBytes_feld_verbindung (verknuepfeDatei a b)
    istart disp out d rest himg hpr hdec
  obtain ⟨hdisp, _, hfit, _, _, hdeckt, _⟩ := hfeld
  refine ⟨hdisp, hfit, hdeckt, ?_, ?_, ?_, ?_, ?_⟩
  · exact verknuepft_abdeckung_union a b out eintrag
  · exact verknuepft_wx .p48 a b out eintrag s hmem hwf
  · exact verknuepft_byte_geladen a b out eintrag 0 va s hfind hhi
  · exact linkPatch_bereich (verknuepfeDatei a b) (istart + 1) (.rel32 disp)
      out hpatch
  · exact linkPatch_rahmen (verknuepfeDatei a b) (istart + 1) (.rel32 disp)
      out hpatch i haussen

/-! ## 5. Joint witness: two separately lowered units, linked.

    Unit A is a five-byte jump with zero displacement, unit B a
    one-byte `ret`. Linking concatenates; the rel32 operand `+16` is
    applied at file offset 1; the patched window re-decodes to
    `jump32 +16` with unit B's byte as the rest. -/

/-- Witness unit A: a five-byte jump with zero displacement. -/
def zeugenEinheitA : LinkEinheit :=
  { bytes := [natByte 233, natByte 0, natByte 0, natByte 0, natByte 0]
    vaddr := 0x1000 }

/-- Witness unit B: a one-byte `ret`. -/
def zeugenEinheitB : LinkEinheit :=
  { bytes := [natByte 195], vaddr := 0x2000 }

/-- Witness displacement field: +16. -/
def zeugenDispField : BitVec 32 := BitVec.ofNat 32 16

/-- Witness linked file: A ++ B. -/
def zeugenVerknuepft : List Byte :=
  verknuepfeDatei zeugenEinheitA zeugenEinheitB

/-- Witness patched file: displacement +16 applied at offset 1. -/
def zeugenGepatcht : List Byte :=
  [natByte 233, natByte 16, natByte 0, natByte 0, natByte 0, natByte 195]

/-- The link concatenation is the two units' bytes in order. -/
theorem zeugen_datei : zeugenVerknuepft =
    [natByte 233, natByte 0, natByte 0, natByte 0, natByte 0,
      natByte 195] := rfl

/-- The rel32 operand applies: patched bytes at the site window. -/
theorem zeugen_patch : linkPatch zeugenVerknuepft 1 (.rel32 16) =
    some zeugenGepatcht := by
  decide

/-- The opcode byte survives at the site start. -/
theorem zeugen_opcode :
    zeugenVerknuepft[0]? = some (natByte 233) := by
  decide

/-- The patched window re-decodes to `jump32 +16`, unit B's byte as rest. -/
theorem zeugen_dek : decode (zeugenGepatcht.drop 0) =
    some ((⟨.jump32 zeugenDispField, 5⟩, [natByte 195])) := by
  decide

/-- The checked linked image over the PATCHED bytes is well-formed. -/
theorem zeugen_bild_wohlgeformt : wohlgeformt .p48
    (linkBildAus zeugenEinheitA zeugenEinheitB zeugenGepatcht 0x1000) =
      true := by
  decide

/-- The linked image's decode coverage holds (both units decode). -/
theorem zeugen_deckung : bildDeckung
    (linkBildAus zeugenEinheitA zeugenEinheitB zeugenGepatcht 0x1000) =
      true := by
  decide

/-- Unit A's section is found at its linked virtual address. -/
theorem zeugen_find : abteilFinden
    (linkBildAus zeugenEinheitA zeugenEinheitB zeugenGepatcht
      0x1000).abschnitte 0 0x1000 =
    some (linkAbschnittA zeugenEinheitA zeugenEinheitB) := by
  decide

/-- The witness address lies in the file-backed part of A's section. -/
theorem zeugen_innen : 0x1000 <
    0 + (linkAbschnittA zeugenEinheitA zeugenEinheitB).vaddr +
      (linkAbschnittA zeugenEinheitA zeugenEinheitB).dateiLen := by
  decide

/-- Unit A's section is a member of the linked image. -/
theorem zeugen_mem : linkAbschnittA zeugenEinheitA zeugenEinheitB ∈
    (linkBildAus zeugenEinheitA zeugenEinheitB zeugenGepatcht
      0x1000).abschnitte := by
  decide

/-- Byte 5 (unit B's `ret`) lies outside the operand `[1, 5)`. -/
theorem zeugen_aussen : ∀ k, k < (feldBytes (.rel32 16)).length →
    5 ≠ (0 + 1) + k := by
  intro k hk
  simp only [feldBytes, rel32Bytes_laenge] at hk
  omega

/-- The displacement field carries the site displacement. -/
theorem zeugen_disp : dispSigned zeugenDispField = 16 := by
  decide

/-! ## 6. Planted refusals: overlap, overrun, range, symbol, W^X,
    forged opcode, unlisted target. Unsupported shapes are REFUSED,
    never guessed. -/

/-- OVERLAP REFUSAL: overlapping operand sites are refused, never merged. -/
theorem verknuepft_ueberlapp_verweigert :
    patchZwei [natByte 0, natByte 0, natByte 0, natByte 0, natByte 0,
      natByte 0, natByte 0, natByte 0] 1
      [natByte 0xAA, natByte 0xBB] 2
      [natByte 0xCC, natByte 0xDD] = none := by
  decide

/-- OVERRUN REFUSAL: a four-byte operand two bytes before the end of a
    three-byte image is refused, never wrapped. -/
theorem verknuepft_ueberlauf_verweigert :
    linkPatch [natByte 233, natByte 0, natByte 0] 2 (.rel32 16) =
      none := by
  decide

/-- RANGE REFUSAL: an out-of-range displacement patches nothing. -/
theorem verknuepft_aussen_verweigert :
    linkPatch zeugenVerknuepft 1 (.rel32 2147483648) = none := by
  decide

/-- SYMBOL REFUSAL: an unlisted relocation id resolves nothing. -/
theorem verknuepft_symbol_verweigert :
    loeseSymbol [(0, 0x1000)] 7 = none := by
  decide

/-- W^X violation image: one section, writable AND executable. -/
def wxVerletzt : Bild :=
  { datei := [natByte 195]
    abschnitte :=
      [{ dateiOff := 0, dateiLen := 1, vaddr := 0x1000, memLen := 1,
         lesbar := true, schreibbar := true, ausfuehrbar := true,
         ausr := 1 }]
    reloks := []
    eintraege := [0x1000]
    modus := .fest }

/-- W^X REFUSAL: a writable-and-executable section admits no image. -/
theorem verknuepft_wx_verweigert :
    wohlgeformt .p48 wxVerletzt = false := by
  decide

/-- FORGED-OPCODE REFUSAL: a non-canonical head byte refuses re-decode. -/
theorem verknuepft_opcode_falsch_verweigert :
    decode ([natByte 6] ++ rel32Bytes 16) = none := by
  decide

/-- UNLISTED-TARGET REFUSAL: the hole address is no executed mapping. -/
theorem verknuepft_loch_verweigert :
    transferOk (linkBildAus zeugenEinheitA zeugenEinheitB zeugenGepatcht
      0x1000) 0 0x1800 = false := by
  decide

/-! ## 7. Joint inhabitation: premises jointly held, run reached. -/

/-- JOINT WITNESS for `verknuepft_korrekt`: all premises instantiated
    jointly on the non-degenerate two-unit link (jump unit plus `ret`
    unit), the closing's conclusions derived through it, a reached
    memory-changing run through actual bytes (`ruf_schritt_zeuge`:
    return address stored, byte observably changed), and the planted
    refusals. -/
theorem verknuepft_korrekt_zeuge :
    ∃ (a b : LinkEinheit) (eintrag istart : Nat) (disp : Int)
      (out : List Byte) (d : BitVec 32) (rest : List Byte)
      (s : Abschnitt) (va i : Nat),
      linkPatch (verknuepfeDatei a b) (istart + 1) (.rel32 disp) =
        some out ∧
      (verknuepfeDatei a b)[istart]? = some (natByte 233) ∧
      decode (out.drop istart) = some ((⟨.jump32 d, 5⟩, rest)) ∧
      wohlgeformt .p48 (linkBildAus a b out eintrag) = true ∧
      s ∈ (linkBildAus a b out eintrag).abschnitte ∧
      abteilFinden (linkBildAus a b out eintrag).abschnitte 0 va =
        some s ∧
      va < 0 + s.vaddr + s.dateiLen ∧
      (∀ k, k < (feldBytes (.rel32 disp)).length →
        i ≠ (istart + 1) + k) ∧
      dispSigned d = disp ∧
      rel32Passt disp = true ∧
      decktAb ⟨.jump32 d, 5⟩ ∧
      bildDeckung (linkBildAus a b out eintrag) =
        (abschnittDeckung (linkBildAus a b out eintrag)
            (linkAbschnittA a b) &&
          abschnittDeckung (linkBildAus a b out eintrag)
            (linkAbschnittB a b)) ∧
      wxOk s = true ∧
      ladenByte (linkBildAus a b out eintrag) 0 va =
        dateiByte out (s.dateiOff + (va - (0 + s.vaddr))) ∧
      istart + 1 + (feldBytes (.rel32 disp)).length ≤
        (verknuepfeDatei a b).length ∧
      out[i]? = (verknuepfeDatei a b)[i]? ∧
      (∃ m : Speicher, byteschritt zustandRuf =
        .weiter (schrittCall zustandRuf Register.rsp m
          (zustandRuf.register Register.rsp - BitVec.ofNat 64 8)
          (BitVec.ofNat 64 0x1015)) ∧
        read64 m (BitVec.ofNat 64 0x1FF8) =
          some (BitVec.ofNat 64 0x1005) ∧
        m.bytes (BitVec.ofNat 64 0x1FF8) ≠
          zustandRuf.speicher.bytes (BitVec.ofNat 64 0x1FF8)) ∧
      linkPatch [natByte 233, natByte 0, natByte 0] 2 (.rel32 16) =
        none ∧
      linkPatch zeugenVerknuepft 1 (.rel32 2147483648) = none ∧
      loeseSymbol [(0, 0x1000)] 7 = none ∧
      wohlgeformt .p48 wxVerletzt = false := by
  have hconn := verknuepft_korrekt zeugenEinheitA zeugenEinheitB 0x1000 0
    16 zeugenGepatcht zeugenDispField [natByte 195]
    (linkAbschnittA zeugenEinheitA zeugenEinheitB) 0x1000 5
    zeugen_patch zeugen_opcode zeugen_dek zeugen_bild_wohlgeformt
    zeugen_mem zeugen_find zeugen_innen zeugen_aussen
  obtain ⟨hdisp, hfit, hdeckt, hunion, hwx, hmap, hrange, hframe⟩ := hconn
  exact ⟨zeugenEinheitA, zeugenEinheitB, 0x1000, 0, 16, zeugenGepatcht,
    zeugenDispField, [natByte 195],
    linkAbschnittA zeugenEinheitA zeugenEinheitB, 0x1000, 5,
    zeugen_patch, zeugen_opcode, zeugen_dek, zeugen_bild_wohlgeformt,
    zeugen_mem, zeugen_find, zeugen_innen, zeugen_aussen,
    hdisp, hfit, hdeckt, hunion, hwx, hmap, hrange, hframe,
    ruf_schritt_zeuge, verknuepft_ueberlauf_verweigert,
    verknuepft_aussen_verweigert, verknuepft_symbol_verweigert,
    verknuepft_wx_verweigert⟩

/- CUTS:
   - Proved here: symbol resolution (`loeseSymbol_*`: only listed ids
     resolve); one-operand application (`linkPatch_bereich`/`_stelle`/
     `_rahmen`/`_laenge`: range, exact site bytes, the frame -- no
     relocation changes a byte outside its operand -- length kept);
     the linked image (`linkBildAus`/`linkBild`: two units, one file,
     no pending relocations) with the coverage union
     (`verknuepft_abdeckung_union`: linked decode coverage equals the
     conjunction of the units' section coverages), the executed-mapping
     leg (`verknuepft_byte_geladen`: through the ACTUAL `geladen`
     mapping) and W^X (`verknuepft_wx`); the rel32 re-decode leg
     (`verknuepft_rel32_schliesst`, reusing the accepted producer
     closing); the link closing (`verknuepft_korrekt`); planted
     refusals for overlap, overrun, out-of-range displacement,
     unlisted symbol, W^X violation, forged opcode and unlisted
     target; the joint `_zeuge` witness with a reached
     memory-changing run.
   - Explicitly OPEN (never assumed here): source correspondence --
     units arrive already lowered, nothing here claims the bytes are
     the emitted form of any source block or that duties, contracts,
     costs, locks or call logs refine anything (consumer: pipeline
     and validator lanes); `valX86_sound` and any full
     source-to-final-loaded-byte closing theorem; hardware
     correspondence -- fetch runs over the model `Speicher` function,
     not silicon; TSO/GX bridge, concurrency, budget/work transfer,
     allocator behaviour (other lanes).
   - Explicitly OPEN link scope: exactly two code units and one
     operand per closing step; multi-unit convergence, fall-through
     coverage across the unit boundary beyond the re-decoded window,
     data-field/abs64-operand re-decode (abs64 patches but never
     decodes here), rel8 short selection, conditional-site field
     agreement and any instruction outside jump/call/conditional stay
     with the extension codec lanes. Overlapping sites are refused
     (`patchZwei`), never merged.
   - No loader execution, entry handoff or OS interaction is modelled:
     `geladen` stays the pure mapping function; entries are contained
     by `wohlgeformt`, never executed here.
   - No second decoder, loader, executor, ISA model or IR is created
     here: every fact reuses the named producer theorems.
-/

#print axioms loeseSymbol_trifft
#print axioms loeseSymbol_fremd_verweigert
#print axioms linkPatch_bereich
#print axioms linkPatch_stelle
#print axioms linkPatch_rahmen
#print axioms linkPatch_laenge
#print axioms verknuepft_abdeckung_union
#print axioms verknuepft_byte_geladen
#print axioms verknuepft_wx
#print axioms verknuepft_rel32_schliesst
#print axioms verknuepft_korrekt
#print axioms verknuepft_ueberlauf_verweigert
#print axioms verknuepft_aussen_verweigert
#print axioms verknuepft_symbol_verweigert
#print axioms verknuepft_wx_verweigert
#print axioms verknuepft_opcode_falsch_verweigert
#print axioms verknuepft_loch_verweigert
#print axioms verknuepft_korrekt_zeuge

end Gabbro.Grammatik.X86
