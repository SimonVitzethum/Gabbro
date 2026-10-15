/-
  Checked byte image and loaded memory (lane 283).

  Canonical finite image representation over the shared `Typen`/`Speicher`
  vocabulary: file bytes, file-to-virtual section mapping, permissions,
  entries and load-bias modes, with decidable well-formedness. The loaded
  canonical `Speicher` is built from accepted sections; layout facts are
  proved here, decoded boundaries and control flow stay OPEN.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher

namespace Gabbro.Grammatik.X86

/-- Address profile: canonical width is 48 or 57, nothing else. -/
inductive Profil where
  | p48
  | p57
  deriving DecidableEq, Repr

/-- Canonical width in bits of a profile. -/
def Profil.breite : Profil → Nat
  | .p48 => 48
  | .p57 => 57

/-- One section extent: file range, virtual range, permissions,
    and the declared alignment the target data demands. -/
structure Abschnitt where
  dateiOff : Nat
  dateiLen : Nat
  vaddr : Nat
  memLen : Nat
  lesbar : Bool
  schreibbar : Bool
  ausfuehrbar : Bool
  ausr : Nat
  deriving DecidableEq, Repr

/-- A whole interval `[lo, lo + len)` is canonical for a profile:
    it sits inside the low half or inside the high half. This implies
    no arithmetic wrap (`lo + len ≤ 2 ^ 64`) and canonicality of every
    address in the range. -/
def kanonischBereich (p : Profil) (lo len : Nat) : Bool :=
  let halb := 2 ^ (p.breite - 1)
  decide (lo + len ≤ halb ∨ (2 ^ 64 - halb ≤ lo ∧ lo + len ≤ 2 ^ 64))

/-- Relocation admissibility class: a site is either a code-operand
    field of one decoded instruction or a standalone data field. -/
inductive RelArt where
  | codeOperand
  | datenFeld
  deriving DecidableEq, Repr

/-- Resolution state: only `aufgeloest` carries a checked value.
    `offen`/`verweigert` are explicit refused states, never trusted. -/
inductive RelStatus where
  | aufgeloest (wert : Nat)
  | offen
  | verweigert
  deriving DecidableEq, Repr

/-- One relocation: site as section index plus offset, kind, status. -/
structure Relok where
  abschnitt : Nat
  siteOff : Nat
  art : RelArt
  status : RelStatus
  deriving DecidableEq, Repr

/-- Load bias mode: fixed absolute addresses or one parametric base
    with checked side conditions. No third case exists. -/
inductive Modus where
  | fest
  | param (basis : Nat)
  deriving DecidableEq, Repr

/-- Effective load bias of a mode: fixed means zero. -/
def effBias : Modus → Nat
  | .fest => 0
  | .param b => b

/-- The candidate final image: exact file bytes, section extents,
    resolved relocations and the machine entry vector, in one mode. -/
structure Bild where
  datei : List Byte
  abschnitte : List Abschnitt
  reloks : List Relok
  eintraege : List Nat
  modus : Modus
  deriving DecidableEq, Repr

/-! ## 1. Canonical boundary probes.

    Real 48/57-bit boundary facts: the low-half top and the high-half
    bottom are canonical, the hole between the halves is not, and the
    full-range check rejects a range spanning the hole. -/

/-- Low-half top is canonical for profile 48. -/
theorem kanonisch_tief_48 : kanonischBereich .p48 0 (2 ^ 47) = true := by
  decide

/-- High-half bottom is canonical for profile 48. -/
theorem kanonisch_hoch_48 :
    kanonischBereich .p48 (2 ^ 64 - 2 ^ 47) (2 ^ 47) = true := by
  decide

/-- The hole between the halves is not canonical for profile 48. -/
theorem kanonisch_loch_48 :
    kanonischBereich .p48 (2 ^ 47) 4096 = false := by
  decide

/-- Profile 57 admits a wider low half than profile 48. -/
theorem kanonisch_57_weiter_als_48 :
    kanonischBereich .p57 0 (2 ^ 56) = true ∧
    kanonischBereich .p48 0 (2 ^ 56) = false := by
  decide

/-! ## 2. Section mapping and decidable well-formedness.

    File ranges and virtual ranges are different things, related by one
    checked mapping: file byte at `dateiOff + i` (`i < dateiLen`) maps to
    virtual address `bias + vaddr + i`, and to no other address. File
    offsets never become virtual addresses directly. -/

/-- File interval of a section: `[dateiOff, dateiOff + dateiLen)`. -/
def fileReich (s : Abschnitt) : Nat × Nat :=
  (s.dateiOff, s.dateiOff + s.dateiLen)

/-- Virtual interval of a section under a bias:
    `[bias + vaddr, bias + vaddr + memLen)`. -/
def virtReich (bias : Nat) (s : Abschnitt) : Nat × Nat :=
  (bias + s.vaddr, bias + s.vaddr + s.memLen)

/-- Two Nat intervals are disjoint (empty intervals touch nothing). -/
def disjunktPaar (a₁ e₁ a₂ e₂ : Nat) : Bool :=
  decide (e₁ ≤ a₂ ∨ e₂ ≤ a₁)

/-- Pairwise disjointness of the mapped intervals over a section list. -/
def paarweise : (Abschnitt → Nat × Nat) → List Abschnitt → Bool
  | _, [] => true
  | f, s :: rest =>
    rest.all (fun t => match f s, f t with
      | (a₁, e₁), (a₂, e₂) => disjunktPaar a₁ e₁ a₂ e₂) &&
    paarweise f rest

/-- A virtual address lies in a section's biased range. -/
def inAbschnitt (bias : Nat) (s : Abschnitt) (a : Nat) : Bool :=
  decide (bias + s.vaddr ≤ a ∧ a < bias + s.vaddr + s.memLen)

/-- First section whose biased virtual range holds `a`, if any. -/
def abteilFinden : List Abschnitt → Nat → Nat → Option Abschnitt
  | [], _, _ => none
  | s :: rest, bias, a =>
    if bias + s.vaddr ≤ a ∧ a < bias + s.vaddr + s.memLen then some s
    else abteilFinden rest bias a

/-- File byte with zero default outside the file (total function;
    well-formedness keeps mapped reads inside). -/
def dateiByte (datei : List Byte) (i : Nat) : Byte :=
  datei.getD i (BitVec.ofNat 8 0)

/-- Loaded byte at virtual address `a`: the mapped file byte in the
    file-backed part, zero in the BSS tail and outside every section. -/
def ladenByte (bild : Bild) (bias a : Nat) : Byte :=
  match abteilFinden bild.abschnitte bias a with
  | none => BitVec.ofNat 8 0
  | some s =>
    if a < bias + s.vaddr + s.dateiLen then
      dateiByte bild.datei (s.dateiOff + (a - (bias + s.vaddr)))
    else BitVec.ofNat 8 0

/-- Loaded read permission: the containing section's, else false. -/
def ladenLesbar (bild : Bild) (bias a : Nat) : Bool :=
  match abteilFinden bild.abschnitte bias a with
  | none => false
  | some s => s.lesbar

/-- Loaded write permission: the containing section's, else false. -/
def ladenSchreibbar (bild : Bild) (bias a : Nat) : Bool :=
  match abteilFinden bild.abschnitte bias a with
  | none => false
  | some s => s.schreibbar

/-- Loaded execute permission: the containing section's, else false. -/
def ladenAusfuehrbar (bild : Bild) (bias a : Nat) : Bool :=
  match abteilFinden bild.abschnitte bias a with
  | none => false
  | some s => s.ausfuehrbar

/-- The canonical loaded memory: bytes and permissions from the
    checked mapping, over the actual shared `Speicher` vocabulary. -/
def geladen (bild : Bild) (bias : Nat) : Speicher :=
  { bytes := fun adr => ladenByte bild bias adr.toNat
    lesbar := fun adr => ladenLesbar bild bias adr.toNat
    schreibbar := fun adr => ladenSchreibbar bild bias adr.toNat
    ausfuehrbar := fun adr => ladenAusfuehrbar bild bias adr.toNat }

/-! ## 3. Well-formedness: every check the validator decides.

    Finite ranges, no wrap, canonical form, `filesz ≤ memsz`, declared
    alignment, W^X, disjoint file/virtual ranges, entry containment,
    resolved class-checked relocations and the mode side conditions.
    Decoded re-checks of patched sites are OPEN (next dependency). -/

/-- `dateiLen ≤ memLen`: BSS is the tail, never negative. -/
def groesseOk (s : Abschnitt) : Bool :=
  decide (s.dateiLen ≤ s.memLen)

/-- File containment: `dateiOff + dateiLen` stays inside the file. -/
def dateiOk (datei : List Byte) (s : Abschnitt) : Bool :=
  decide (s.dateiOff + s.dateiLen ≤ datei.length)

/-- Virtual nonwrap under the bias. -/
def virtuellOk (bias : Nat) (s : Abschnitt) : Bool :=
  decide (bias + s.vaddr + s.memLen ≤ 2 ^ 64)

/-- Declared alignment is nonzero and divides the biased base. -/
def ausrOk (bias : Nat) (s : Abschnitt) : Bool :=
  decide (0 < s.ausr ∧ (bias + s.vaddr) % s.ausr = 0)

/-- W^X: no section is writable and executable at once. -/
def wxOk (s : Abschnitt) : Bool :=
  !(s.schreibbar && s.ausfuehrbar)

/-- An entry lies in an executable section's biased range. -/
def eintragEnthalten (bias : Nat) (secs : List Abschnitt) (e : Nat) : Bool :=
  secs.any (fun s => inAbschnitt bias s e && s.ausfuehrbar)

/-- A resolved value lies in some executable section (code target rule). -/
def zielInCode (bias : Nat) (secs : List Abschnitt) (w : Nat) : Bool :=
  secs.any (fun s => inAbschnitt bias s w && s.ausfuehrbar)

/-- A resolved value lies in some section at all (data target rule). -/
def zielInIrgendwo (bias : Nat) (secs : List Abschnitt) (w : Nat) : Bool :=
  secs.any (fun s => inAbschnitt bias s w)

/-- One relocation is resolved, sited inside its section, class-checked
    against the section kind, and its value meets the kind's target rule.
    Re-decoding of the patched bytes is OPEN, not checked here. -/
def relokOk (bias : Nat) (secs : List Abschnitt) (r : Relok) : Bool :=
  match secs[r.abschnitt]? with
  | none => false
  | some s =>
    match r.status with
    | .offen => false
    | .verweigert => false
    | .aufgeloest w =>
      decide (r.siteOff < s.memLen) &&
      match r.art with
      | .codeOperand => s.ausfuehrbar && zielInCode bias secs w
      | .datenFeld => (!s.ausfuehrbar) && zielInIrgendwo bias secs w

/-- Mode side condition: a parametric base keeps the target alignment.
    Fixed mode carries no extra condition (bias zero is aligned). -/
def modusOk : Modus → Bool
  | .fest => true
  | .param b => decide (b % 4096 = 0)

/-- The full image check: every section and list obligation at once. -/
def wohlgeformt (p : Profil) (bild : Bild) : Bool :=
  let bias := effBias bild.modus
  bild.abschnitte.all groesseOk &&
  bild.abschnitte.all (dateiOk bild.datei) &&
  bild.abschnitte.all (virtuellOk bias) &&
  bild.abschnitte.all (fun s => kanonischBereich p (bias + s.vaddr) s.memLen) &&
  bild.abschnitte.all (ausrOk bias) &&
  bild.abschnitte.all wxOk &&
  paarweise fileReich bild.abschnitte &&
  paarweise (virtReich bias) bild.abschnitte &&
  bild.eintraege.all (eintragEnthalten bias bild.abschnitte) &&
  bild.reloks.all (relokOk bias bild.abschnitte) &&
  modusOk bild.modus

/-! ## 4. Loaded-memory facts: what accepted sections establish.

    Generic over every image: mapped bytes equal file bytes, the BSS tail
    reads zero, permissions agree with the section, and outside every
    section bytes are zero and nothing is readable, writable or
    executable. Each proof uses all its premises. -/

/-- MAPPED-BYTE EQUALITY: inside the file-backed part of the found
    section, the loaded byte is the mapped file byte. -/
theorem geladenByte_datei (bild : Bild) (bias a : Nat) (s : Abschnitt)
    (hfind : abteilFinden bild.abschnitte bias a = some s)
    (hhi : a < bias + s.vaddr + s.dateiLen) :
    ladenByte bild bias a =
      dateiByte bild.datei (s.dateiOff + (a - (bias + s.vaddr))) := by
  simp [ladenByte, hfind, hhi]

/-- BSS ZERO: past the file-backed part but inside the found section,
    the loaded byte is defined zero. -/
theorem geladenByte_bss (bild : Bild) (bias a : Nat) (s : Abschnitt)
    (hfind : abteilFinden bild.abschnitte bias a = some s)
    (hlo : bias + s.vaddr + s.dateiLen ≤ a) :
    ladenByte bild bias a = BitVec.ofNat 8 0 := by
  simp [ladenByte, hfind, Nat.not_lt.mpr hlo]

/-- PERMISSION AGREEMENT: the loaded read permission is the section's. -/
theorem geladenLesbar_fund (bild : Bild) (bias a : Nat) (s : Abschnitt)
    (hfind : abteilFinden bild.abschnitte bias a = some s) :
    ladenLesbar bild bias a = s.lesbar := by
  simp [ladenLesbar, hfind]

/-- PERMISSION AGREEMENT: the loaded write permission is the section's. -/
theorem geladenSchreibbar_fund (bild : Bild) (bias a : Nat) (s : Abschnitt)
    (hfind : abteilFinden bild.abschnitte bias a = some s) :
    ladenSchreibbar bild bias a = s.schreibbar := by
  simp [ladenSchreibbar, hfind]

/-- PERMISSION AGREEMENT: the loaded execute permission is the section's. -/
theorem geladenAusfuehrbar_fund (bild : Bild) (bias a : Nat) (s : Abschnitt)
    (hfind : abteilFinden bild.abschnitte bias a = some s) :
    ladenAusfuehrbar bild bias a = s.ausfuehrbar := by
  simp [ladenAusfuehrbar, hfind]

/-- OUTSIDE-DOMAIN FRAME: outside every section the byte is zero and
    nothing is readable, writable or executable. -/
theorem ausserhalb_rahmen (bild : Bild) (bias a : Nat)
    (hfind : abteilFinden bild.abschnitte bias a = none) :
    ladenByte bild bias a = BitVec.ofNat 8 0 ∧
    ladenLesbar bild bias a = false ∧
    ladenSchreibbar bild bias a = false ∧
    ladenAusfuehrbar bild bias a = false := by
  simp [ladenByte, ladenLesbar, ladenSchreibbar, ladenAusfuehrbar, hfind]

/-! ## 5. Concrete image witnesses: acceptance and refusals.

    A two-section image (executable code plus writable data with a
    nonzero byte) is accepted; overlap, wrap, an outside entry and an
    unresolved relocation are each refused with a closed witness. -/

/-- Witness file: four code bytes then eight data bytes, nonzero at 4. -/
def zeugenDatei : List Byte :=
  [0x90, 0x90, 0x90, 0x90, 9, 1, 2, 3, 4, 5, 6, 7]

/-- Witness code section: readable and executable, never writable. -/
def zeugenCode : Abschnitt :=
  { dateiOff := 0, dateiLen := 4, vaddr := 0x1000, memLen := 4,
    lesbar := true, schreibbar := false, ausfuehrbar := true, ausr := 4096 }

/-- Witness data section: readable and writable, never executable,
    with a mapped nonzero byte at its base. -/
def zeugenDaten : Abschnitt :=
  { dateiOff := 4, dateiLen := 8, vaddr := 0x2000, memLen := 8,
    lesbar := true, schreibbar := true, ausfuehrbar := false, ausr := 4096 }

/-- The accepted witness image: fixed bias, entry inside code. -/
def zeugenBild : Bild :=
  { datei := zeugenDatei
    abschnitte := [zeugenCode, zeugenDaten]
    reloks := []
    eintraege := [0x1000]
    modus := .fest }

/-- The witness image is accepted under profile 48. -/
theorem zeugenBild_wohlgeformt :
    wohlgeformt .p48 zeugenBild = true := by
  decide

/-- The data base resolves to the data section (real find probe). -/
theorem zeugenFund_daten :
    abteilFinden zeugenBild.abschnitte 0 0x2000 = some zeugenDaten := by
  decide

/-- An address between the sections resolves to nothing. -/
theorem zeugenFund_loch :
    abteilFinden zeugenBild.abschnitte 0 0x1800 = none := by
  decide

/-- The mapped nonzero writable byte, through the generic equality. -/
theorem zeugenByte_geladen :
    ladenByte zeugenBild 0 0x2000 = dateiByte zeugenBild.datei 4 ∧
    ladenByte zeugenBild 0 0x2000 ≠ BitVec.ofNat 8 0 := by
  have hfind := zeugenFund_daten
  have hbyte := geladenByte_datei zeugenBild 0 0x2000 zeugenDaten
    hfind (by decide)
  rw [hbyte]
  exact ⟨rfl, by decide⟩

/-- OVERLAP REFUSAL: file ranges `[0, 8)` and `[4, 12)` share bytes. -/
def bildUeberlapp : Bild :=
  { datei := List.replicate 16 (BitVec.ofNat 8 0)
    abschnitte :=
      [{ dateiOff := 0, dateiLen := 8, vaddr := 0x1000, memLen := 8,
         lesbar := true, schreibbar := false, ausfuehrbar := true,
         ausr := 4096 },
       { dateiOff := 4, dateiLen := 8, vaddr := 0x2000, memLen := 8,
         lesbar := true, schreibbar := true, ausfuehrbar := false,
         ausr := 4096 }]
    reloks := []
    eintraege := [0x1000]
    modus := .fest }

/-- Overlapping file ranges are refused. -/
theorem bildUeberlapp_verweigert :
    wohlgeformt .p48 bildUeberlapp = false := by
  decide

/-- WRAP REFUSAL: `vaddr + memLen` leaves 64 bits. -/
def bildUmbruch : Bild :=
  { datei := []
    abschnitte :=
      [{ dateiOff := 0, dateiLen := 0, vaddr := 2 ^ 64 - 4, memLen := 8,
         lesbar := true, schreibbar := true, ausfuehrbar := false,
         ausr := 4096 }]
    reloks := []
    eintraege := []
    modus := .fest }

/-- A wrapping virtual range is refused. -/
theorem bildUmbruch_verweigert :
    wohlgeformt .p48 bildUmbruch = false := by
  decide

/-- ENTRY REFUSAL: the entry lies outside every section. -/
def bildEintrittAussen : Bild :=
  { zeugenBild with eintraege := [0x5000] }

/-- An entry outside every section is refused. -/
theorem bildEintrittAussen_verweigert :
    wohlgeformt .p48 bildEintrittAussen = false := by
  decide

/-- UNRESOLVED REFUSAL: a relocation the loader would still apply. -/
def bildRelokOffen : Bild :=
  { zeugenBild with
    reloks := [{ abschnitt := 0, siteOff := 0,
                 art := .codeOperand, status := .offen }] }

/-- An unresolved relocation is refused, never assumed. -/
theorem bildRelokOffen_verweigert :
    wohlgeformt .p48 bildRelokOffen = false := by
  decide

/-! ## 6. Memory-changing witness over loaded memory.

    The data base of the accepted image is readable and writable through
    the loaded `Speicher`; an actual `write64` there reads back through
    `read64` and observably changes the byte. This reuses the shared byte
    memory operations, not a second model. -/

/-- The loaded data base is readable for eight bytes. -/
theorem zeugenLesbar8 :
    lesbar8 (geladen zeugenBild 0) (BitVec.ofNat 64 0x2000) = true := by
  decide

/-- The loaded data base is writable for eight bytes. -/
theorem zeugenSchreibbar8 :
    schreibbar8 (geladen zeugenBild 0) (BitVec.ofNat 64 0x2000) = true := by
  decide

/-- JOINT WITNESS: a nonzero write through loaded image memory reads
    back and observably changes the byte. -/
theorem schreibLese_zeuge :
    ∃ (m m' : Speicher) (a : Adresse) (v : Wort),
      v ≠ 0 ∧ write64 m a v = some m' ∧ read64 m' a = some v ∧
        m.bytes a ≠ m'.bytes a := by
  have hbyte : (geladen zeugenBild 0).bytes (BitVec.ofNat 64 0x2000) =
      BitVec.ofNat 8 9 := by
    decide
  have hwr : write64 (geladen zeugenBild 0) (BitVec.ofNat 64 0x2000) 42 =
      some { geladen zeugenBild 0 with
        bytes := writeBytes (geladen zeugenBild 0)
          (BitVec.ofNat 64 0x2000) 42 } := by
    unfold write64
    rw [if_pos zeugenSchreibbar8]
  refine ⟨geladen zeugenBild 0, _, BitVec.ofNat 64 0x2000, 42,
    by decide, hwr,
    read64_nach_write64 _ _ _ _ hwr zeugenLesbar8, ?_⟩
  have hhit := writeBytesN_hit (geladen zeugenBild 0)
    (BitVec.ofNat 64 0x2000) 42 8 0 (by decide) (by decide)
  rw [addrOff_null] at hhit
  show (geladen zeugenBild 0).bytes (BitVec.ofNat 64 0x2000) ≠
    writeBytesN (geladen zeugenBild 0) (BitVec.ofNat 64 0x2000) 42 8
      (BitVec.ofNat 64 0x2000)
  rw [hbyte, hhit]
  decide

/-- BSS witness section: no file bytes, eight zero-defined bytes. -/
def zeugenBss : Abschnitt :=
  { dateiOff := 0, dateiLen := 0, vaddr := 0x3000, memLen := 8,
    lesbar := true, schreibbar := true, ausfuehrbar := false, ausr := 4096 }

/-- Image with a BSS tail section beside the code section. -/
def bildBss : Bild :=
  { datei := [0x90, 0x90, 0x90, 0x90]
    abschnitte := [zeugenCode, zeugenBss]
    reloks := []
    eintraege := [0x1000]
    modus := .fest }

/-- The BSS image is accepted. -/
theorem bildBss_wohlgeformt :
    wohlgeformt .p48 bildBss = true := by
  decide

/-- The BSS tail reads defined zero, through the generic BSS fact. -/
theorem bildBss_null :
    ladenByte bildBss 0 0x3000 = BitVec.ofNat 8 0 := by
  have hfind : abteilFinden bildBss.abschnitte 0 0x3000 = some zeugenBss := by
    decide
  exact geladenByte_bss bildBss 0 0x3000 zeugenBss hfind (by decide)

/-- Parametric-bias image: same sections as the witness, loaded at a
    checked base; entries name biased addresses, never base + offset. -/
def bildParam : Bild :=
  { zeugenBild with
    eintraege := [0x101000]
    modus := .param 0x100000 }

/-- The parametric image is accepted: base aligned, ranges canonical
    and disjoint after the bias. -/
theorem bildParam_wohlgeformt :
    wohlgeformt .p48 bildParam = true := by
  decide

/-- Under the parametric base the data byte maps through its section,
    not through base + file offset. -/
theorem bildParam_byte :
    ladenByte bildParam 0x100000 0x102000 =
      dateiByte bildParam.datei 4 := by
  have hfind :
      abteilFinden bildParam.abschnitte 0x100000 0x102000 =
        some zeugenDaten := by
    decide
  exact geladenByte_datei bildParam 0x100000 0x102000 zeugenDaten
    hfind (by decide)

/- CUTS:
    - No instruction decoder, encoding, round-trip, or boundary proof:
      `abteilFinden` matches on section ranges, never on decoded bytes.
      Decoded instruction starts, control-flow targets and the re-decode
      of patched relocation sites are the next dependency and OPEN; no
      image metadata is assumed to describe decoding correctly.
    - No relocation correspondence: `relokOk` checks resolution state,
      site containment, class-vs-section-kind and the value target rule
      only. Patched-byte re-decoding and correspondence are OPEN.
    - No source correspondence: nothing here claims the bytes are the
      emitted form of any source program, or that duties, costs, locks,
      entries or templates refine anything. Source, concurrency and
      hardware claims are OPEN unless actually proved elsewhere.
    - No OS or loader software assumption: `geladen` is a pure function
      of the image; BSS zero and permission agreement are proved of that
      function, not of any loader. The loader contract is unwitnessed.
    - `kanonischBereich` admits only profiles 48 and 57 (`Profil` has no
      other constructor); other widths need an explicit new profile.
    - Alignment is the section's declared `ausr` (nonzero, divides the
      biased base); the 4096 bare-metal demand is target data, not proved.
-/

#print axioms Profil.breite
#print axioms kanonisch_tief_48
#print axioms kanonisch_hoch_48
#print axioms kanonisch_loch_48
#print axioms kanonisch_57_weiter_als_48
#print axioms geladenByte_datei
#print axioms geladenByte_bss
#print axioms geladenLesbar_fund
#print axioms geladenSchreibbar_fund
#print axioms geladenAusfuehrbar_fund
#print axioms ausserhalb_rahmen
#print axioms zeugenBild_wohlgeformt
#print axioms zeugenFund_daten
#print axioms zeugenFund_loch
#print axioms zeugenByte_geladen
#print axioms bildUeberlapp_verweigert
#print axioms bildUmbruch_verweigert
#print axioms bildEintrittAussen_verweigert
#print axioms bildRelokOffen_verweigert
#print axioms zeugenLesbar8
#print axioms zeugenSchreibbar8
#print axioms schreibLese_zeuge
#print axioms bildBss_wohlgeformt
#print axioms bildBss_null
#print axioms bildParam_wohlgeformt
#print axioms bildParam_byte

end Gabbro.Grammatik.X86
