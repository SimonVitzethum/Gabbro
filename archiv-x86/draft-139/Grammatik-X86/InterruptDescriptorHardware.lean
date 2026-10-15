/-
  File:      Grammatik/X86/InterruptDescriptorHardware.lean
  Subject:   Actual IDT gate parsing and TSS entry-stack selection on
             canonical memory (long mode).

  Lane 728: the missing generic descriptor-read/check layer -- IDTR
  base/limit, vector gate selection, 16-byte gate parsing,
  type/present/reserved/DPL/selector/canonical-handler checks,
  long-mode TSS IST/RSP slot lookup and stack selection. Checked
  descriptor/stack producer for lanes 672/708. No trusted parsed
  descriptor, no hidden valid-entry assumption.

  Manual provenance (clone-local `.tmp/HARDWARE-REFERENCES/`):
  - Table 6-1 vectors, Vol. 1 Ch. 6 (txt lines 9641-9671).
  - Canonical addresses, Vol. 1 §3.3.7.1 (txt line 4220).
  - IDT delivery push order, Vol. 1 §6.5.1 (txt lines 9690-9705).
  - INT n entry: software-INT DPL check, IA-32e limit/type checks,
    IST/RSP slot arithmetic, push order, IF clearing (txt 58904-59680).
  - The 16-byte gate/TSS figures live in Vol. 3 (outside the local
    txt snapshot): field positions are stated architecture, and every
    CHECK on them is proved from canonical-memory equations.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.Codec
import Grammatik.X86.HardwareFaults

namespace Gabbro.Grammatik.X86

/-- Architectural control state: IDT register, current TSS window,
    privilege level and the interrupt-enable bit. No OS content. -/
structure Steuerstand where
  idtBasis : Adresse
  idtLimit : Nat
  tssBasis : Adresse
  tssLimit : Nat
  cpl : Nat
  ifBit : Bool
  deriving DecidableEq, Repr

/-- A 64-bit gate is 16 bytes; a vector selects `basis + v * 16`. -/
def torAdresse (idtBasis : Adresse) (vektor : Nat) : Adresse :=
  idtBasis + BitVec.ofNat 64 (vektor * 16)

/-- The 16 gate bytes fit inside the IDT limit (pseudocode
    `(vector « 4) + 15` within limits, INT entry). -/
def torImLimit (idtLimit vektor : Nat) : Bool :=
  decide (vektor * 16 + 15 ≤ idtLimit)

/-! ## 1. Gate bytes from canonical memory: two accepted `read64` halves.

  The 16-byte gate at `a` is the low qword at `a` plus the high qword
  at `a + 8`. Any unreadable half refuses with `none`: no partial
  descriptor is ever trusted. -/

/-- Read the two qwords covering one 16-byte gate. -/
def liesTorBytes (m : Speicher) (a : Adresse) : Option (Wort × Wort) :=
  match read64 m a with
  | none => none
  | some lo =>
    match read64 m (addrOff a 8) with
    | none => none
    | some hi => some (lo, hi)

/-- Gate byte `i`: low qword first, then high qword. -/
def torByte (t : Wort × Wort) (i : Nat) : Byte :=
  if i < 8 then wortByte t.1 i else wortByte t.2 (i - 8)

/-- A refused low half refuses the whole gate. -/
theorem liesTorBytes_verweigert_unten (m : Speicher) (a : Adresse)
    (h : read64 m a = none) :
    liesTorBytes m a = none := by
  simp [liesTorBytes, h]

/-- A refused high half refuses the whole gate. -/
theorem liesTorBytes_verweigert_oben (m : Speicher) (a : Adresse)
    (lo : Wort)
    (hlo : read64 m a = some lo) (hhi : read64 m (addrOff a 8) = none) :
    liesTorBytes m a = none := by
  simp [liesTorBytes, hlo, hhi]

/-- Two readable halves yield both qwords. -/
theorem liesTorBytes_erfolg (m : Speicher) (a : Adresse)
    (lo hi : Wort)
    (hlo : read64 m a = some lo) (hhi : read64 m (addrOff a 8) = some hi) :
    liesTorBytes m a = some (lo, hi) := by
  simp [liesTorBytes, hlo, hhi]

/-! ## 2. Field extraction from the 16 gate bytes (long mode).

  Byte positions are stated 64-bit architecture (Vol. 3 gate figure,
  outside the local txt snapshot): offset 15:0 in bytes 0-1, selector
  in bytes 2-3, IST in byte 4 bits 2:0 (bits 7:3 reserved), type/DPL/P
  in byte 5, offset 31:16 in bytes 6-7, offset 63:32 in bytes 8-11,
  bytes 12-15 reserved. Interrupt gate type is `0xE`, trap gate `0xF`.
  Every CHECK below is proved from canonical-memory equations. -/

/-- Parsed 64-bit IDT gate: handler offset, code selector, IST slot,
    gate DPL and the interrupt-vs-trap kind. -/
structure IdtTor where
  offset : Adresse
  selektor : Nat
  ist : Nat
  dpl : Nat
  unterbrechung : Bool
  deriving DecidableEq, Repr

/-- Handler offset as a natural: bytes 0-1, 6-7, 8-11 little-endian. -/
def torOffsetNat (t : Wort × Wort) : Nat :=
  (torByte t 0).toNat + (torByte t 1).toNat * 256 +
    (torByte t 6).toNat * 65536 + (torByte t 7).toNat * 16777216 +
    (torByte t 8).toNat * 4294967296 +
    (torByte t 9).toNat * 1099511627776 +
    (torByte t 10).toNat * 281474976710656 +
    (torByte t 11).toNat * 72057594037927936

/-- Handler offset as an address. -/
def torOffset (t : Wort × Wort) : Adresse :=
  BitVec.ofNat 64 (torOffsetNat t)

/-- Code-segment selector: bytes 2-3 little-endian. -/
def torSelektor (t : Wort × Wort) : Nat :=
  (torByte t 2).toNat + (torByte t 3).toNat * 256

/-- IST index: byte 4 bits 2:0. -/
def torIst (t : Wort × Wort) : Nat :=
  (torByte t 4).toNat % 8

/-- IST reserved bits 7:3 are all zero. -/
def torIstReserviertOk (t : Wort × Wort) : Bool :=
  decide ((torByte t 4).toNat / 8 = 0)

/-- Gate type nibble: byte 5 bits 3:0. -/
def torTyp (t : Wort × Wort) : Nat :=
  (torByte t 5).toNat % 16

/-- Gate DPL: byte 5 bits 6:5. -/
def torDpl (t : Wort × Wort) : Nat :=
  (torByte t 5).toNat / 32 % 4

/-- Present bit: byte 5 bit 7. -/
def torVorhanden (t : Wort × Wort) : Bool :=
  decide (128 ≤ (torByte t 5).toNat)

/-- High reserved bytes 12-15 are all zero. -/
def torHochReserviertOk (t : Wort × Wort) : Bool :=
  decide ((torByte t 12).toNat = 0 ∧ (torByte t 13).toNat = 0 ∧
    (torByte t 14).toNat = 0 ∧ (torByte t 15).toNat = 0)

/-- Parse refusal detail: wrong type, IST-reserved or high-reserved. -/
inductive TorDetail where
  | ok : IdtTor → TorDetail
  | falscherTyp : TorDetail
  | reserviertIst : TorDetail
  | reserviertHoch : TorDetail
  deriving DecidableEq, Repr

/-- Checked parse: type must be interrupt (`0xE`) or trap (`0xF`) and
    both reserved groups must be zero. DPL needs no range check: two
    bits always name 0-3. -/
def zerlegeTor (t : Wort × Wort) : TorDetail :=
  if torTyp t = 14 ∨ torTyp t = 15 then
    if torIstReserviertOk t then
      if torHochReserviertOk t then
        .ok ⟨torOffset t, torSelektor t, torIst t, torDpl t,
          decide (torTyp t = 14)⟩
      else .reserviertHoch
    else .reserviertIst
  else .falscherTyp

/-- A gate whose type is neither `0xE` nor `0xF` is refused. -/
theorem zerlegeTor_typ (t : Wort × Wort)
    (h : torTyp t ≠ 14) (h2 : torTyp t ≠ 15) :
    zerlegeTor t = .falscherTyp := by
  unfold zerlegeTor
  have hdis : ¬ (torTyp t = 14 ∨ torTyp t = 15) := by
    intro hcon
    cases hcon with
    | inl hl => exact h hl
    | inr hr => exact h2 hr
  simp [hdis]

/-- A nonzero IST-reserved bit refuses the gate. -/
theorem zerlegeTor_ist (t : Wort × Wort)
    (ht : torTyp t = 14 ∨ torTyp t = 15)
    (hr : torIstReserviertOk t = false) :
    zerlegeTor t = .reserviertIst := by
  unfold zerlegeTor
  simp [ht, hr]

/-- A nonzero high-reserved byte refuses the gate. -/
theorem zerlegeTor_hoch (t : Wort × Wort)
    (ht : torTyp t = 14 ∨ torTyp t = 15)
    (hi : torIstReserviertOk t = true)
    (hr : torHochReserviertOk t = false) :
    zerlegeTor t = .reserviertHoch := by
  unfold zerlegeTor
  simp [ht, hi, hr]

/-! ## 3. Check pipeline in pseudocode order (INT entry, IA-32e).

  Delivery source: `Herkunft`. A software interrupt (`INT n`,
  `INT3`, `INTO`) with CPL above the gate DPL faults with #GP; the
  `INT1` debug trap is exempt (INT entry decision note); external
  delivery never takes the DPL check. Selector and code-segment
  checks follow the present check; the GDT row itself (`codeOk`) is
  owned downstream and arrives as an explicit checked input. -/

/-- Delivery source: software interrupt (with the INT1 exemption
    flag) or external/event delivery. -/
inductive Herkunft where
  | softwareInt : Bool → Herkunft
  | extern : Herkunft
  deriving DecidableEq, Repr

/-- Descriptor-path fault: every member names its manual class and
    carries the vector (or the failing value) for the error code. -/
inductive TorFehler where
  | limitFehler : Nat → TorFehler
  | typFehler : Nat → TorFehler
  | dplFehler : Nat → TorFehler
  | nichtVorhanden : Nat → TorFehler
  | reserviertFehler : Nat → TorFehler
  | selektorFehler : Nat → TorFehler
  | zielFehler : TorFehler
  | tssFehler : Nat → TorFehler
  | stapelFehler : TorFehler
  deriving DecidableEq, Repr

/-- Outcome of the descriptor path: a checked gate or the precise
    first failing check. -/
inductive TorErgebnis where
  | bereit : IdtTor → TorErgebnis
  | fehler : TorFehler → TorErgebnis
  deriving DecidableEq, Repr

/-- DPL admission: software INT (except INT1) needs `cpl ≤ dpl`;
    INT1 and external delivery always pass. -/
def dplZugelassen (h : Herkunft) (gateDpl cpl : Nat) : Bool :=
  match h with
  | .softwareInt true => true
  | .softwareInt false => decide (cpl ≤ gateDpl)
  | .extern => true

/-- Software INT at a higher CPL than the gate DPL is refused. -/
theorem dpl_verweigert_software (gateDpl cpl : Nat)
    (h : ¬ cpl ≤ gateDpl) :
    dplZugelassen (.softwareInt false) gateDpl cpl = false := by
  simp [dplZugelassen, h]

/-- The INT1 trap is exempt from the DPL check. -/
theorem dpl_int1_frei (gateDpl cpl : Nat) :
    dplZugelassen (.softwareInt true) gateDpl cpl = true := rfl

/-- External delivery never takes the DPL check. -/
theorem dpl_extern_frei (gateDpl cpl : Nat) :
    dplZugelassen .extern gateDpl cpl = true := rfl

/-- Post-parse checks: DPL, present, selector, canonical handler.
    Split out so the parse match stays first-order. The NULL check
    precedes the code-row check, both as pure `Bool` tests. -/
def pruefeTorKern (vektor : Nat) (t : Wort × Wort) (g : IdtTor)
    (h : Herkunft) (cpl : Nat) (codeOk : Bool) : TorErgebnis :=
  if !dplZugelassen h g.dpl cpl then .fehler (.dplFehler vektor)
  else if !torVorhanden t then .fehler (.nichtVorhanden vektor)
  else if g.selektor == 0 then .fehler (.selektorFehler g.selektor)
  else if !codeOk then .fehler (.selektorFehler g.selektor)
  else if !istKanonisch g.offset then .fehler .zielFehler
  else .bereit g

/-- Full gate check in pseudocode order: limit, type/reserved, then
    `pruefeTorKern`. The first failure wins. -/
def pruefeTor (vektor : Nat) (idtLimit : Nat) (t : Wort × Wort)
    (h : Herkunft) (cpl : Nat) (codeOk : Bool) : TorErgebnis :=
  if !torImLimit idtLimit vektor then .fehler (.limitFehler vektor)
  else match zerlegeTor t with
  | .falscherTyp => .fehler (.typFehler vektor)
  | .reserviertIst => .fehler (.reserviertFehler vektor)
  | .reserviertHoch => .fehler (.reserviertFehler vektor)
  | .ok g => pruefeTorKern vektor t g h cpl codeOk

/-- A vector past the IDT limit faults before any byte is read. -/
theorem pruefeTor_limit (vektor idtLimit : Nat) (t : Wort × Wort)
    (h : Herkunft) (cpl : Nat) (codeOk : Bool)
    (hl : torImLimit idtLimit vektor = false) :
    pruefeTor vektor idtLimit t h cpl codeOk =
      .fehler (.limitFehler vektor) := by
  simp [pruefeTor, hl]

/-- A software INT above the gate DPL faults with the vector. -/
theorem pruefeTor_dpl (vektor idtLimit : Nat) (t : Wort × Wort)
    (cpl : Nat) (codeOk : Bool) (g : IdtTor)
    (hl : torImLimit idtLimit vektor = true)
    (hz : zerlegeTor t = .ok g)
    (hd : dplZugelassen (.softwareInt false) g.dpl cpl = false) :
    pruefeTor vektor idtLimit t (.softwareInt false) cpl codeOk =
      .fehler (.dplFehler vektor) := by
  unfold pruefeTor pruefeTorKern
  simp [hl, hz, hd]

/-- A non-present gate faults with #NP after the DPL check. -/
theorem pruefeTor_abwesend (vektor idtLimit : Nat) (t : Wort × Wort)
    (h : Herkunft) (cpl : Nat) (codeOk : Bool) (g : IdtTor)
    (hl : torImLimit idtLimit vektor = true)
    (hz : zerlegeTor t = .ok g)
    (hd : dplZugelassen h g.dpl cpl = true)
    (hp : torVorhanden t = false) :
    pruefeTor vektor idtLimit t h cpl codeOk =
      .fehler (.nichtVorhanden vektor) := by
  unfold pruefeTor pruefeTorKern
  simp [hl, hz, hd, hp]

/-- A NULL selector faults after the present check. -/
theorem pruefeTor_selektor_null (vektor idtLimit : Nat) (t : Wort × Wort)
    (h : Herkunft) (cpl : Nat) (codeOk : Bool) (g : IdtTor)
    (hl : torImLimit idtLimit vektor = true)
    (hz : zerlegeTor t = .ok g)
    (hd : dplZugelassen h g.dpl cpl = true)
    (hp : torVorhanden t = true)
    (hs : g.selektor = 0) :
    pruefeTor vektor idtLimit t h cpl codeOk =
      .fehler (.selektorFehler g.selektor) := by
  have hbb : (g.selektor == 0) = true := by
    rw [beq_iff_eq]
    exact hs
  unfold pruefeTor pruefeTorKern
  simp [hl, hz, hd, hp, hbb]

/-- A wrong gate type faults with the vector. -/
theorem pruefeTor_typ (vektor idtLimit : Nat) (t : Wort × Wort)
    (h : Herkunft) (cpl : Nat) (codeOk : Bool)
    (hl : torImLimit idtLimit vektor = true)
    (hz : zerlegeTor t = .falscherTyp) :
    pruefeTor vektor idtLimit t h cpl codeOk =
      .fehler (.typFehler vektor) := by
  unfold pruefeTor
  simp [hl, hz]

/-- A nonzero IST-reserved bit faults with the vector. -/
theorem pruefeTor_reserviert_ist (vektor idtLimit : Nat) (t : Wort × Wort)
    (h : Herkunft) (cpl : Nat) (codeOk : Bool)
    (hl : torImLimit idtLimit vektor = true)
    (hz : zerlegeTor t = .reserviertIst) :
    pruefeTor vektor idtLimit t h cpl codeOk =
      .fehler (.reserviertFehler vektor) := by
  unfold pruefeTor
  simp [hl, hz]

/-- A nonzero high-reserved byte faults with the vector. -/
theorem pruefeTor_reserviert_hoch (vektor idtLimit : Nat) (t : Wort × Wort)
    (h : Herkunft) (cpl : Nat) (codeOk : Bool)
    (hl : torImLimit idtLimit vektor = true)
    (hz : zerlegeTor t = .reserviertHoch) :
    pruefeTor vektor idtLimit t h cpl codeOk =
      .fehler (.reserviertFehler vektor) := by
  unfold pruefeTor
  simp [hl, hz]

/-- Pure parse-shape split: first-order, no delivery premise. -/
theorem torDetail_faelle (t : Wort × Wort) :
    zerlegeTor t = .falscherTyp ∨ zerlegeTor t = .reserviertIst ∨
      zerlegeTor t = .reserviertHoch ∨ ∃ g, zerlegeTor t = .ok g :=
  match _hzt : zerlegeTor t with
  | .falscherTyp => Or.inl rfl
  | .reserviertIst => Or.inr (Or.inl rfl)
  | .reserviertHoch => Or.inr (Or.inr (Or.inl rfl))
  | .ok g => Or.inr (Or.inr (Or.inr ⟨g, rfl⟩))

/-- Full admission: every check passes, the gate is ready. -/
theorem pruefeTor_bereit (vektor idtLimit : Nat) (t : Wort × Wort)
    (h : Herkunft) (cpl : Nat) (codeOk : Bool) (g : IdtTor)
    (hl : torImLimit idtLimit vektor = true)
    (hz : zerlegeTor t = .ok g)
    (hd : dplZugelassen h g.dpl cpl = true)
    (hp : torVorhanden t = true)
    (hs : g.selektor ≠ 0)
    (hc : codeOk = true)
    (hk : istKanonisch g.offset = true) :
    pruefeTor vektor idtLimit t h cpl codeOk = .bereit g := by
  have hbb : (g.selektor == 0) = false := by simp [hs]
  unfold pruefeTor pruefeTorKern
  simp [hl, hz, hd, hp, hbb, hc, hk]

/-! ## 4. TSS slot lookup and entry-stack selection (IA-32e).

  Pseudocode arithmetic (INT entry): with a nonzero IST the slot is
  at `(IST « 3) + 28`, else the RSP slot of the target level at
  `(DPL « 3) + 4`; `(slot + 7) > TSS limit` faults with #TS and the
  new pointer is the 8 bytes at `TSS base + slot`. With no privilege
  change and IST zero the current stack is kept and the TSS is never
  read. A refused TSS read is a TSS-access fault (#TS, Table 6-1). -/

/-- TSS slot byte offset: a nonzero IST wins over the RSP slot. -/
def stapelSlotOffset (ist neuDpl : Nat) : Nat :=
  if ist = 0 then neuDpl * 8 + 4 else ist * 8 + 28

/-- Slot bytes fit inside the TSS limit. -/
def slotImLimit (tssLimit off : Nat) : Bool :=
  decide (off + 7 ≤ tssLimit)

/-- Stack outcome: keep the current pointer, switch to a loaded one,
    or the precise fault. -/
inductive StapelWahl where
  | behalten : Wort → StapelWahl
  | wechseln : Wort → StapelWahl
  | stapelFehler : TorFehler → StapelWahl
  deriving DecidableEq, Repr

/-- Entry-stack selection: no read where nothing switches; limit
    checked before the 8-byte load. -/
def waehleStapel (m : Speicher) (s : Steuerstand) (ist neuDpl : Nat)
    (wechsel : Bool) (curRsp : Wort) : StapelWahl :=
  if !wechsel && ist == 0 then .behalten curRsp
  else
    let off := stapelSlotOffset ist neuDpl
    if !slotImLimit s.tssLimit off then .stapelFehler (.tssFehler off)
    else match read64 m (s.tssBasis + BitVec.ofNat 64 off) with
    | none => .stapelFehler (.tssFehler off)
    | some rsp => .wechseln rsp

/-- IST slot pins: IST1 at 36, IST7 at 84. -/
theorem slot_ist_pins :
    stapelSlotOffset 1 0 = 36 ∧ stapelSlotOffset 7 3 = 84 := by
  decide

/-- RSP slot pins: level 0 at 4, level 3 at 28. -/
theorem slot_rsp_pins :
    stapelSlotOffset 0 0 = 4 ∧ stapelSlotOffset 0 3 = 28 := by
  decide

/-- Same-level delivery without IST keeps the stack and reads no TSS. -/
theorem waehleStapel_behalten (m : Speicher) (s : Steuerstand)
    (neuDpl : Nat) (curRsp : Wort) :
    waehleStapel m s 0 neuDpl false curRsp = .behalten curRsp := by
  simp [waehleStapel]

/-- A slot past the TSS limit faults with #TS before any load. -/
theorem waehleStapel_tss_limit (m : Speicher) (s : Steuerstand)
    (ist neuDpl : Nat) (wechsel : Bool) (curRsp : Wort)
    (hbr : (!wechsel && ist == 0) = false)
    (hlim : slotImLimit s.tssLimit (stapelSlotOffset ist neuDpl) = false) :
    waehleStapel m s ist neuDpl wechsel curRsp =
      .stapelFehler (.tssFehler (stapelSlotOffset ist neuDpl)) := by
  simp [waehleStapel, hbr, hlim]

/-- An in-limit slot loads the new stack pointer. -/
theorem waehleStapel_wechseln (m : Speicher) (s : Steuerstand)
    (ist neuDpl : Nat) (wechsel : Bool) (curRsp rsp : Wort)
    (hbr : (!wechsel && ist == 0) = false)
    (hlim : slotImLimit s.tssLimit (stapelSlotOffset ist neuDpl) = true)
    (hrd : read64 m
      (s.tssBasis + BitVec.ofNat 64 (stapelSlotOffset ist neuDpl)) =
      some rsp) :
    waehleStapel m s ist neuDpl wechsel curRsp = .wechseln rsp := by
  simp [waehleStapel, hbr, hlim, hrd]

/-! ## 5. Fault class, error code and priority.

  Vectors follow Table 6-1. Error codes follow the INT pseudocode:
  IDT faults name the vector with the IDT bit set; selector faults
  name the selector; NULL/canonical/stack faults carry zero. The EXT
  bit is clear for software delivery and set for external delivery
  (pseudocode comments on each `error_code`). The #TS code's TSS
  selector field needs the TR/GDT owner (downstream): only the EXT
  bit is modelled here. Priority IS the check order: the pipeline
  returns the first failing stage. -/

/-- Vector number of each descriptor-path fault (Table 6-1). -/
def torVektor : TorFehler → Nat
  | .limitFehler _ => 13
  | .typFehler _ => 13
  | .dplFehler _ => 13
  | .nichtVorhanden _ => 11
  | .reserviertFehler _ => 13
  | .selektorFehler _ => 13
  | .zielFehler => 13
  | .tssFehler _ => 10
  | .stapelFehler => 12

/-- EXT bit of the error code: set for external delivery only. -/
def extVonHerkunft : Herkunft → Bool
  | .softwareInt _ => false
  | .extern => true

/-- Error code for an IDT fault: vector with the IDT bit. -/
def codeFuerIdt (vektor : Nat) (ext : Bool) : Wort :=
  BitVec.ofNat 64 (vektor * 8 + 2 + if ext then 1 else 0)

/-- Error code for a selector fault: selector with the EXT bit. -/
def codeFuerSelektor (sel : Nat) (ext : Bool) : Wort :=
  BitVec.ofNat 64 (sel / 8 * 8 + if ext then 1 else 0)

/-- Error code word of each descriptor-path fault. -/
def torFehlerCode (f : TorFehler) (h : Herkunft) : Wort :=
  let ext := extVonHerkunft h
  match f with
  | .limitFehler v => codeFuerIdt v ext
  | .typFehler v => codeFuerIdt v ext
  | .dplFehler v => codeFuerIdt v false
  | .nichtVorhanden v => codeFuerIdt v ext
  | .reserviertFehler v => codeFuerIdt v ext
  | .selektorFehler s => codeFuerSelektor s ext
  | .zielFehler => 0
  | .tssFehler _ => BitVec.ofNat 64 (if ext then 1 else 0)
  | .stapelFehler => 0

/-- Bridge to the admitted fault vocabulary: #GP and #SS members
    translate; #NP (vector 11) and #TS (vector 10) have no admitted
    member, so the consumer reads them from `torVektor`. -/
def alsArch : TorFehler → Option ArchFehler
  | .limitFehler _ => some .gp
  | .typFehler _ => some .gp
  | .dplFehler _ => some .gp
  | .nichtVorhanden _ => none
  | .reserviertFehler _ => some .gp
  | .selektorFehler _ => some .gp
  | .zielFehler => some .gp
  | .tssFehler _ => none
  | .stapelFehler => some .ss

/-- Every #GP-family member translates. -/
theorem alsArch_gp (v : Nat) :
    alsArch (.limitFehler v) = some .gp ∧
      alsArch (.typFehler v) = some .gp ∧
      alsArch (.dplFehler v) = some .gp ∧
      alsArch (.reserviertFehler v) = some .gp ∧
      alsArch (.selektorFehler v) = some .gp ∧
      alsArch .zielFehler = some .gp ∧
      alsArch .stapelFehler = some .ss := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- #NP and #TS have no admitted member: the vector is the fact. -/
theorem alsArch_ohne_mitglied (v off : Nat) :
    alsArch (.nichtVorhanden v) = none ∧
      alsArch (.tssFehler off) = none ∧
      torVektor (.nichtVorhanden v) = 11 ∧
      torVektor (.tssFehler off) = 10 := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- Priority rank: the pseudocode check order, lowest first. -/
def fehlerRang : TorFehler → Nat
  | .limitFehler _ => 0
  | .typFehler _ => 1
  | .reserviertFehler _ => 1
  | .dplFehler _ => 2
  | .nichtVorhanden _ => 3
  | .selektorFehler _ => 4
  | .zielFehler => 5
  | .tssFehler _ => 6
  | .stapelFehler => 7

/-- PRIORITY: a DPL fault implies the limit and type stages passed --
    the first failing check wins, never a later one. -/
theorem erste_pruefung_gewinnt_dpl (vektor idtLimit : Nat)
    (t : Wort × Wort) (cpl : Nat) (codeOk : Bool)
    (h : pruefeTor vektor idtLimit t (.softwareInt false) cpl codeOk =
      .fehler (.dplFehler vektor)) :
    torImLimit idtLimit vektor = true ∧
      ∃ g : IdtTor, zerlegeTor t = .ok g ∧
        dplZugelassen (.softwareInt false) g.dpl cpl = false := by
  by_cases hl : torImLimit idtLimit vektor = true
  · rcases torDetail_faelle t with h1 | h1 | h1 | ⟨g, hzg⟩
    · have hcon :=
        pruefeTor_typ vektor idtLimit t (.softwareInt false) cpl codeOk hl h1
      rw [hcon] at h
      cases h
    · have hcon :=
        pruefeTor_reserviert_ist vektor idtLimit t (.softwareInt false) cpl
          codeOk hl h1
      rw [hcon] at h
      cases h
    · have hcon :=
        pruefeTor_reserviert_hoch vektor idtLimit t (.softwareInt false) cpl
          codeOk hl h1
      rw [hcon] at h
      cases h
    · unfold pruefeTor at h
      simp only [hl, hzg, Bool.not_true] at h
      unfold pruefeTorKern at h
      by_cases hd : dplZugelassen (.softwareInt false) g.dpl cpl = true
      · have hnz : (!dplZugelassen (.softwareInt false) g.dpl cpl) =
            false := by simp [hd]
        simp only [hnz] at h
        by_cases hv : (!torVorhanden t) = true
        · simp only [hv] at h
          cases h
        · simp only [hv] at h
          by_cases hb : (g.selektor == 0) = true
          · simp only [hb] at h
            cases h
          · simp only [hb] at h
            by_cases hc2 : (!codeOk) = true
            · simp only [hc2] at h
              cases h
            · simp only [hc2] at h
              by_cases hk2 : (!istKanonisch g.offset) = true
              · simp only [hk2] at h
                cases h
              · simp only [hk2] at h
                cases h
      · have h2 : dplZugelassen (.softwareInt false) g.dpl cpl = false := by
          cases hc : dplZugelassen (.softwareInt false) g.dpl cpl with
          | true => simp_all
          | false => rfl
        exact ⟨hl, g, hzg, h2⟩
  · have hlf : torImLimit idtLimit vektor = false := by simpa using hl
    have hcon := pruefeTor_limit vektor idtLimit t (.softwareInt false) cpl
      codeOk hlf
    rw [hcon] at h
    cases h

/-! ## 6. Frame push and end-to-end delivery.

  A 64-bit gate pushes old SS, old RSP, RFLAGS, old CS, old RIP and,
  where the vector carries one, the error code -- each an 8-byte
  push descending from the selected top (INT entry, IA-32e paths).
  Every push is an accepted `write64`: a refused push refuses the
  whole delivery with #SS and changes nothing. A noncanonical
  selected pointer faults with #SS before any push. An interrupt
  gate clears IF; a trap gate keeps it. -/

/-- Push a word list descending from `top`: each word lands 8 bytes
    below the previous top. -/
def schiebeRahmen : Speicher → Adresse → List Wort → Option Speicher
  | m, _, [] => some m
  | m, top, w :: rest =>
    match write64 m (top - BitVec.ofNat 64 8) w with
    | none => none
    | some m' => schiebeRahmen m' (top - BitVec.ofNat 64 8) rest

/-- Empty frame pushes nothing. -/
theorem schiebeRahmen_leer (m : Speicher) (top : Adresse) :
    schiebeRahmen m top [] = some m := rfl

/-- Delivery request: vector, raw gate words, source, code-row input,
    privilege-change data, current pointer and the frame words. The
    code-segment row itself (`codeOk`) stays downstream-owned. -/
structure LieferAnfrage where
  vektor : Nat
  tor : Wort × Wort
  herkunft : Herkunft
  codeOk : Bool
  wechsel : Bool
  neuDpl : Nat
  curRsp : Wort
  ssAlt : Wort
  rflags : Wort
  csAlt : Wort
  ripAlt : Wort
  fehlercode : Option Wort

/-- Frame words in push order: SS, RSP, RFLAGS, CS, RIP, error code. -/
def rahmenWorte (q : LieferAnfrage) : List Wort :=
  [q.ssAlt, q.curRsp, q.rflags, q.csAlt, q.ripAlt] ++ q.fehlercode.toList

/-- Frame length: five words, six with an error code. -/
theorem rahmenWorte_laenge (q : LieferAnfrage) :
    (rahmenWorte q).length = 5 + q.fehlercode.toList.length := by
  cases hq : q.fehlercode with
  | none => simp [rahmenWorte, hq]
  | some e => simp [rahmenWorte, hq]

/-- Delivery outcome: the new memory with handler RIP and new IF,
    or the precise fault with its error code. No equality: memory
    has none. -/
inductive LieferErgebnis where
  | zugestellt : Speicher → Adresse → Bool → Bool → LieferErgebnis
  | lieferFehler : TorFehler → Wort → LieferErgebnis

/-- Push stage: canonical-pointer check, then the accepted frame
    chain. Shared by the kept and the switched stack. -/
def schiebeUndStelle (m : Speicher) (g : IdtTor) (s : Steuerstand)
    (q : LieferAnfrage) (rsp : Wort) (gewechselt : Bool) : LieferErgebnis :=
  if !istKanonisch rsp then .lieferFehler .stapelFehler 0
  else match schiebeRahmen m rsp (rahmenWorte q) with
  | none => .lieferFehler .stapelFehler 0
  | some m' =>
    .zugestellt m' g.offset
      (if g.unterbrechung then false else s.ifBit) gewechselt

/-- End-to-end delivery: gate check, stack selection, push stage.
    Faults carry their error code; memory moves only on success. -/
def liefere (m : Speicher) (s : Steuerstand)
    (q : LieferAnfrage) : LieferErgebnis :=
  match pruefeTor q.vektor s.idtLimit q.tor q.herkunft s.cpl q.codeOk with
  | .fehler f => .lieferFehler f (torFehlerCode f q.herkunft)
  | .bereit g =>
    match waehleStapel m s g.ist q.neuDpl q.wechsel q.curRsp with
    | .stapelFehler f => .lieferFehler f (torFehlerCode f q.herkunft)
    | .behalten rsp => schiebeUndStelle m g s q rsp false
    | .wechseln rsp => schiebeUndStelle m g s q rsp true

/-- CHECKS BEFORE EFFECTS: a failed gate check delivers the fault
    with its code and produces no memory. -/
theorem liefere_prueft_zuerst (m : Speicher) (s : Steuerstand)
    (q : LieferAnfrage) (f : TorFehler)
    (h : pruefeTor q.vektor s.idtLimit q.tor q.herkunft s.cpl q.codeOk =
      .fehler f) :
    liefere m s q = .lieferFehler f (torFehlerCode f q.herkunft) := by
  simp [liefere, h]

/-- STACK FAULT BEFORE PUSH: a failed stack selection faults with
    its code and pushes nothing. -/
theorem liefere_stapel_vor_wirkung (m : Speicher) (s : Steuerstand)
    (q : LieferAnfrage) (g : IdtTor) (f : TorFehler)
    (hp : pruefeTor q.vektor s.idtLimit q.tor q.herkunft s.cpl q.codeOk =
      .bereit g)
    (hs : waehleStapel m s g.ist q.neuDpl q.wechsel q.curRsp =
      .stapelFehler f) :
    liefere m s q = .lieferFehler f (torFehlerCode f q.herkunft) := by
  simp [liefere, hp, hs]

/-- NONCANONICAL POINTER BEFORE PUSH: the loaded pointer is checked
    before the first frame word lands. -/
theorem liefere_rsp_nichtkanonisch (m : Speicher) (s : Steuerstand)
    (q : LieferAnfrage) (g : IdtTor) (rsp : Wort)
    (hp : pruefeTor q.vektor s.idtLimit q.tor q.herkunft s.cpl q.codeOk =
      .bereit g)
    (hs : waehleStapel m s g.ist q.neuDpl q.wechsel q.curRsp =
      .wechseln rsp)
    (hk : istKanonisch rsp = false) :
    liefere m s q = .lieferFehler .stapelFehler 0 := by
  unfold liefere schiebeUndStelle
  simp [hp, hs, hk]

/-- SUCCESS over a switched stack: the frame lands and control state
    follows the gate kind. -/
theorem liefere_zugestellt_wechsel (m m' : Speicher) (s : Steuerstand)
    (q : LieferAnfrage) (g : IdtTor) (rsp : Wort)
    (hp : pruefeTor q.vektor s.idtLimit q.tor q.herkunft s.cpl q.codeOk =
      .bereit g)
    (hs : waehleStapel m s g.ist q.neuDpl q.wechsel q.curRsp =
      .wechseln rsp)
    (hk : istKanonisch rsp = true)
    (hpush : schiebeRahmen m rsp (rahmenWorte q) = some m') :
    liefere m s q = .zugestellt m' g.offset
      (if g.unterbrechung then false else s.ifBit) true := by
  unfold liefere schiebeUndStelle
  simp [hp, hs, hk, hpush]

/-- SUCCESS over the kept stack: same frame, no switch flag. -/
theorem liefere_zugestellt_behalten (m m' : Speicher) (s : Steuerstand)
    (q : LieferAnfrage) (g : IdtTor) (rsp : Wort)
    (hp : pruefeTor q.vektor s.idtLimit q.tor q.herkunft s.cpl q.codeOk =
      .bereit g)
    (hs : waehleStapel m s g.ist q.neuDpl q.wechsel q.curRsp =
      .behalten rsp)
    (hk : istKanonisch rsp = true)
    (hpush : schiebeRahmen m rsp (rahmenWorte q) = some m') :
    liefere m s q = .zugestellt m' g.offset
      (if g.unterbrechung then false else s.ifBit) false := by
  unfold liefere schiebeUndStelle
  simp [hp, hs, hk, hpush]

/-! ## 7. Joint witness: byte-populated IDT/TSS, real delivery.

  IDT at 4096 (three entries, limit 47); vector 2 is a present
  interrupt gate (type `0xE`, DPL 0, IST 1, selector `0x08`) naming
  handler `0x2000`. TSS at 12288 (limit 103); IST1 holds `0x4000`.
  External delivery at CPL 0 clears IF through the interrupt gate,
  switches to the IST stack and pushes five nonzero frame words. -/

/-- Witness gate low word: offset `0x2000`, selector `0x08`, IST 1,
    `P/DPL/type = 0x8E`. -/
def loWitNat : Nat :=
  32 * 256 + 8 * 65536 + 1 * 4294967296 + 142 * 1099511627776

/-- Witness gate low word. -/
def loWit : Wort := BitVec.ofNat 64 loWitNat

/-- IDT image bytes relative to 4096: the vector-2 gate at +32. -/
def witIdtByte (n : Nat) : Byte :=
  match n with
  | 32 => natByte 0
  | 33 => natByte 32
  | 34 => natByte 8
  | 35 => natByte 0
  | 36 => natByte 1
  | 37 => natByte 142
  | _ => BitVec.ofNat 8 0

/-- TSS image bytes relative to 12288: IST1 (`0x4000`) at +36. -/
def witTssByte (n : Nat) : Byte :=
  match n with
  | 36 => natByte 0
  | 37 => natByte 64
  | _ => BitVec.ofNat 8 0

/-- Witness bytes: IDT and TSS images, zero elsewhere. -/
def idtWitBytes (a : Adresse) : Byte :=
  if a.toNat < 4096 then BitVec.ofNat 8 0
  else if a.toNat < 4096 + 48 then witIdtByte (a.toNat - 4096)
  else if a.toNat < 12288 then BitVec.ofNat 8 0
  else if a.toNat < 12288 + 48 then witTssByte (a.toNat - 12288)
  else BitVec.ofNat 8 0

/-- Witness memory: IDT/TSS/stack readable, IDT/TSS never
    executable and stack writable (delivery never fetches here). -/
def witMem : Speicher :=
  { bytes := idtWitBytes
    lesbar := fun a =>
      decide (4096 ≤ a.toNat ∧ a.toNat < 4096 + 48) ||
        decide (12288 ≤ a.toNat ∧ a.toNat < 12288 + 48) ||
        decide (16336 ≤ a.toNat ∧ a.toNat < 16384)
    schreibbar := fun a => decide (16336 ≤ a.toNat ∧ a.toNat < 16384)
    ausfuehrbar := fun _ => false }

/-- Witness control state: IDT limit 47, TSS limit 103, CPL 0. -/
def idtWitSteuer : Steuerstand :=
  ⟨BitVec.ofNat 64 4096, 47, BitVec.ofNat 64 12288, 103, 0, true⟩

/-- Witness request: external vector 2, no privilege change data,
    nonzero frame words, no error code. -/
def witAnfrage : LieferAnfrage :=
  ⟨2, (loWit, BitVec.ofNat 64 0), .extern, true, false, 0,
    BitVec.ofNat 64 20480, BitVec.ofNat 64 16, BitVec.ofNat 64 514,
    BitVec.ofNat 64 8, BitVec.ofNat 64 4660, none⟩

/-- Gate address of vector 2 is 4128. -/
theorem wit_torAdresse :
    torAdresse (BitVec.ofNat 64 4096) 2 = BitVec.ofNat 64 4128 := by
  decide

/-- Vector 2 fits the witness IDT limit. -/
theorem wit_imLimit : torImLimit 47 2 = true := by
  decide

/-- The gate bytes read back as the two witness words. -/
theorem idtWit_liest :
    liesTorBytes witMem (BitVec.ofNat 64 4128) = some (loWit, 0) := by
  decide

/-- The witness words parse to the expected gate. -/
theorem wit_zerlegt :
    zerlegeTor (loWit, (0 : Wort)) =
      .ok ⟨BitVec.ofNat 64 8192, 8, 1, 0, true⟩ := by
  decide

/-- The witness gate is admitted. -/
theorem wit_bereit :
    pruefeTor 2 47 (loWit, (0 : Wort)) .extern 0 true =
      .bereit ⟨BitVec.ofNat 64 8192, 8, 1, 0, true⟩ := by
  decide

/-- The witness TSS slot loads the IST stack. -/
theorem wit_stapel :
    waehleStapel witMem idtWitSteuer 1 0 false (BitVec.ofNat 64 20480) =
      .wechseln (BitVec.ofNat 64 16384) := by
  decide

/-! ## 8. Negative probes: every malformed shape faults precisely.

  Each probe names its vector, class and code: limit/type/DPL/
  present/reserved/selector/canonical/TSS-limit/stack faults plus
  the INT1 exemption and the error-code values. -/

/-- Fault vector and code projections for downstream consumers. -/
def ergebnisVektor : LieferErgebnis → Option Nat
  | .zugestellt _ _ _ _ => none
  | .lieferFehler f _ => some (torVektor f)

/-- Fault error-code projection. -/
def ergebnisCode : LieferErgebnis → Option Wort
  | .zugestellt _ _ _ _ => none
  | .lieferFehler _ c => some c

/-- LIMIT: vector 3 lies past the witness IDT. -/
theorem neg_limit :
    pruefeTor 3 47 (loWit, (0 : Wort)) .extern 0 true =
      .fehler (.limitFehler 3) := by
  decide

/-- TYPE: `P=1, type=0` is no interrupt or trap gate. -/
def loTypFalsch : Wort :=
  BitVec.ofNat 64 (32 * 256 + 8 * 65536 + 1 * 4294967296 + 128 * 1099511627776)

/-- Wrong-type gate parses as `falscherTyp` and faults. -/
theorem neg_typ :
    zerlegeTor (loTypFalsch, (0 : Wort)) = .falscherTyp ∧
      pruefeTor 2 47 (loTypFalsch, (0 : Wort)) .extern 0 true =
        .fehler (.typFehler 2) := by
  decide

/-- PRESENT: `P=0, type=0xE` admits the shape but not the gate. -/
def loAbwesend : Wort :=
  BitVec.ofNat 64 (32 * 256 + 8 * 65536 + 1 * 4294967296 + 14 * 1099511627776)

/-- Non-present gate faults with #NP after the DPL stage. -/
theorem neg_abwesend :
    pruefeTor 2 47 (loAbwesend, (0 : Wort)) .extern 0 true =
      .fehler (.nichtVorhanden 2) := by
  decide

/-- IST-RESERVED: nonzero bit 3 of the IST byte. -/
def loIstReserviert : Wort :=
  BitVec.ofNat 64 (32 * 256 + 8 * 65536 + 9 * 4294967296 + 142 * 1099511627776)

/-- Reserved IST bits fault with the vector. -/
theorem neg_reserviert_ist :
    zerlegeTor (loIstReserviert, (0 : Wort)) = .reserviertIst ∧
      pruefeTor 2 47 (loIstReserviert, (0 : Wort)) .extern 0 true =
        .fehler (.reserviertFehler 2) := by
  decide

/-- HIGH-RESERVED: gate byte 12 (high-word byte 4) set. -/
theorem neg_reserviert_hoch :
    zerlegeTor (loWit, BitVec.ofNat 64 4294967296) = .reserviertHoch := by
  decide

/-- NULL selector: zero selector faults after the present check. -/
def loSelektorNull : Wort :=
  BitVec.ofNat 64 (32 * 256 + 1 * 4294967296 + 142 * 1099511627776)

/-- NULL selector faults naming the zero selector. -/
theorem neg_selektor :
    pruefeTor 2 47 (loSelektorNull, (0 : Wort)) .extern 0 true =
      .fehler (.selektorFehler 0) := by
  decide

/-- NONCANONICAL handler: offset `2 ^ 47` lives in gate byte 9. -/
def loZielFalsch : Wort :=
  BitVec.ofNat 64 (8 * 65536 + 1 * 4294967296 + 142 * 1099511627776)

/-- High word carrying gate byte 9 = 128. -/
def hiZielFalsch : Wort := BitVec.ofNat 64 32768

/-- Noncanonical handler faults before any stack is read. -/
theorem neg_ziel :
    pruefeTor 2 47 (loZielFalsch, hiZielFalsch) .extern 0 true =
      .fehler .zielFehler := by
  decide

/-- DPL: software INT at CPL 3 against DPL 0 faults; INT1 and
    external delivery pass the same gate. -/
theorem neg_dpl_kontrast :
    pruefeTor 2 47 (loWit, (0 : Wort)) (.softwareInt false) 3 true =
        .fehler (.dplFehler 2) ∧
      pruefeTor 2 47 (loWit, (0 : Wort)) (.softwareInt true) 3 true =
        .bereit ⟨BitVec.ofNat 64 8192, 8, 1, 0, true⟩ ∧
      pruefeTor 2 47 (loWit, (0 : Wort)) .extern 3 true =
        .bereit ⟨BitVec.ofNat 64 8192, 8, 1, 0, true⟩ := by
  decide

/-- Short TSS: slot 36 needs bytes through 43. -/
def idtWitSteuerKurz : Steuerstand :=
  ⟨BitVec.ofNat 64 4096, 47, BitVec.ofNat 64 12288, 42, 0, true⟩

/-- TSS-limit fault names the offending slot offset. -/
theorem neg_tss_limit :
    waehleStapel witMem idtWitSteuerKurz 1 0 true (BitVec.ofNat 64 20480) =
      .stapelFehler (.tssFehler 36) := by
  decide

/-- IST zero without privilege change keeps the stack. -/
theorem neg_kein_wechsel :
    waehleStapel witMem idtWitSteuer 0 0 false (BitVec.ofNat 64 20480) =
      .behalten (BitVec.ofNat 64 20480) := by
  decide

/-- Dark stack: no writable frame cell, delivery faults with #SS. -/
def witMemDunkel : Speicher :=
  { witMem with schreibbar := fun _ => false }

/-- Dark-stack delivery faults: vector 12, code zero. -/
theorem neg_dunkel_vektor :
    ergebnisVektor (liefere witMemDunkel idtWitSteuer witAnfrage) = some 12 ∧
      ergebnisCode (liefere witMemDunkel idtWitSteuer witAnfrage) =
        some 0 := by
  decide

/-- Error-code values: IDT fault with/without EXT, selector fault. -/
theorem neg_codes :
    torFehlerCode (.limitFehler 3) (.softwareInt false) =
        BitVec.ofNat 64 26 ∧
      torFehlerCode (.nichtVorhanden 2) .extern =
        BitVec.ofNat 64 19 ∧
      torFehlerCode (.selektorFehler 24) .extern =
        BitVec.ofNat 64 25 := by
  decide

/-! ## 9. Joint witness and producer interface.

  One conjunction ties the byte-populated IDT/TSS run to its
  checked facts: the gate reads from actual canonical bytes, parses,
  is admitted, the IST stack loads, delivery switches stacks,
  clears IF through the interrupt gate, pushes five nonzero frame
  words that read back, and observably changes memory from zero.
  Non-degenerate: two frame cells change actual bytes.

  CONSUMED BY 672 (delivery): `idtWit_liest` (bytes), `wit_zerlegt`
  (shape), `wit_bereit` (admission order), `wit_stapel` (slot),
  `liefere_zugestellt_wechsel/behalten` (frame equations),
  `torFehlerCode` + `torVektor` (fault data),
  `erste_pruefung_gewinnt_dpl` (check order). CONSUMED BY 708
  (entry): the `zugestellt` fields -- new memory, handler RIP,
  new IF. Full async delivery, TSO/store-buffer interaction and
  the GDT/code-row ownership stay downstream. -/

/-- Project the delivered memory (witness memory on fault). -/
def ergebnisSpeicher : LieferErgebnis → Speicher
  | .zugestellt m _ _ _ => m
  | .lieferFehler _ _ => witMem

/-- Delivery reaches the witness handler offset. -/
theorem wit_liefert_rip :
    (match liefere witMem idtWitSteuer witAnfrage with
      | .zugestellt _ rip _ _ => rip
      | .lieferFehler _ _ => BitVec.ofNat 64 0) =
      BitVec.ofNat 64 8192 := by
  decide

/-- The interrupt gate clears IF. -/
theorem wit_liefert_if :
    (match liefere witMem idtWitSteuer witAnfrage with
      | .zugestellt _ _ ifNeu _ => ifNeu
      | .lieferFehler _ _ => true) = false := by
  decide

/-- Delivery reports the IST switch. -/
theorem wit_liefert_gew :
    (match liefere witMem idtWitSteuer witAnfrage with
      | .zugestellt _ _ _ gew => gew
      | .lieferFehler _ _ => false) = true := by
  decide

/-- First frame word reads back. -/
theorem wit_rahmen_ss :
    read64 (ergebnisSpeicher (liefere witMem idtWitSteuer witAnfrage))
        (BitVec.ofNat 64 16376) = some (BitVec.ofNat 64 16) := by
  decide

/-- Last frame word reads back. -/
theorem wit_rahmen_rip :
    read64 (ergebnisSpeicher (liefere witMem idtWitSteuer witAnfrage))
        (BitVec.ofNat 64 16344) = some (BitVec.ofNat 64 4660) := by
  decide

/-- Both frame cells start zeroed. -/
theorem wit_rahmen_anfang :
    witMem.bytes (BitVec.ofNat 64 16376) = BitVec.ofNat 8 0 ∧
      witMem.bytes (BitVec.ofNat 64 16344) = BitVec.ofNat 8 0 := by
  decide

/-- Both frame cells observably change. -/
theorem wit_rahmen_aendert :
    witMem.bytes (BitVec.ofNat 64 16376) ≠
        (ergebnisSpeicher (liefere witMem idtWitSteuer witAnfrage)).bytes
          (BitVec.ofNat 64 16376) ∧
      witMem.bytes (BitVec.ofNat 64 16344) ≠
        (ergebnisSpeicher (liefere witMem idtWitSteuer witAnfrage)).bytes
          (BitVec.ofNat 64 16344) := by
  decide

/-- JOINT WITNESS: checked delivery over byte-populated canonical
    memory with an observable five-word frame change. -/
theorem liefer_zeuge_gemeinsam :
    (match liefere witMem idtWitSteuer witAnfrage with
      | .zugestellt _ rip _ _ => rip
      | .lieferFehler _ _ => BitVec.ofNat 64 0) =
        BitVec.ofNat 64 8192 ∧
      (match liefere witMem idtWitSteuer witAnfrage with
        | .zugestellt _ _ ifNeu _ => ifNeu
        | .lieferFehler _ _ => true) = false ∧
      read64 (ergebnisSpeicher (liefere witMem idtWitSteuer witAnfrage))
          (BitVec.ofNat 64 16376) = some (BitVec.ofNat 64 16) ∧
      read64 (ergebnisSpeicher (liefere witMem idtWitSteuer witAnfrage))
          (BitVec.ofNat 64 16344) = some (BitVec.ofNat 64 4660) ∧
      witMem.bytes (BitVec.ofNat 64 16376) ≠
        (ergebnisSpeicher (liefere witMem idtWitSteuer witAnfrage)).bytes
          (BitVec.ofNat 64 16376) ∧
      witMem.bytes (BitVec.ofNat 64 16344) ≠
        (ergebnisSpeicher (liefere witMem idtWitSteuer witAnfrage)).bytes
          (BitVec.ofNat 64 16344) :=
  ⟨wit_liefert_rip, wit_liefert_if, wit_rahmen_ss, wit_rahmen_rip,
    wit_rahmen_aendert.1, wit_rahmen_aendert.2⟩

/- CUTS:
   Proved here, over canonical `Speicher` equations only (no new
   machine, no decoder row, no source claim):
   - control state (`Steuerstand`: IDTR/TSS windows, CPL, IF);
   - vector selection (`torAdresse`, `torImLimit`) and the two-half
     gate read (`liesTorBytes`: any unreadable half refuses);
   - 16-byte parse (`zerlegeTor`: interrupt `0xE`/trap `0xF`,
     IST/high reserved checks, DPL needs no range check);
   - check pipeline in INT-entry pseudocode order (`pruefeTor` /
     `pruefeTorKern`), software-INT DPL with the INT1 exemption
     and external bypass (`dplZugelassen`), NULL-selector and
     canonical-handler checks, downstream-owned `codeOk` explicit;
   - TSS slot lookup (`stapelSlotOffset`: IST slot wins, else the
     target-level RSP slot; `slotImLimit`) and selection
     (`waehleStapel`: no read where nothing switches);
   - fault vectors (Table 6-1), error codes (INT-entry
     `error_code` comments) and the admitted-vocabulary bridge
     (`alsArch`; #NP/#TS have no admitted member);
   - first-failure priority (`erste_pruefung_gewinnt_dpl`);
   - frame push (`schiebeRahmen`: five/six accepted `write64`
     pushes in pseudocode order) and end-to-end delivery
     (`liefere`) with checks-before-effects, stack-fault-before-
     push and both success equations;
   - joint byte-populated witness (IDT/TSS images in canonical
     memory, IST switch, IF cleared, five-word frame read-back,
     two observably changed cells) beside twelve fault/control/
     overlap probes (limit, type, absent, both reserveds, NULL
     selector, noncanonical target, DPL contrast incl. INT1,
     TSS limit, no-switch keep, dark stack, code values).
   NOT proved here, and not claimed:
   - No GDT/code-segment ownership: `codeOk` arrives as an
     explicit checked input; selector table walks, conforming
     checks and CPL changes from code DPL stay downstream (672).
   - No async completion: this layer checks descriptors and
     pushes one frame; what the handler runs, nested delivery,
     #DF escalation, TSO/store-buffer interaction and timing
     stay with 672/708 and the concurrency lanes.
   - No full 20-vector error-code table: presence is an explicit
     `Option` in the request; only the code VALUES of reached
     faults are pinned.
   - No `RSP & ...F0` masking line: the loaded pointer is the
     producer output; the pseudocode alignment mask is OPEN.
   - No shadow-stack/CET/FRED paths: the `CR4.FRED = 0` IDT
     delivery only (INT entry); task gates are refused as
     `falscherTyp`.
   - No silicon proof: field positions cite the Vol. 3 gate/TSS
     figures (outside the local txt snapshot) as stated
     architecture; every CHECK is proved from canonical-memory
     equations, and `gabbro_ziel` axioms are untouched.
-/

#print axioms torAdresse
#print axioms torImLimit
#print axioms liesTorBytes_verweigert_unten
#print axioms liesTorBytes_erfolg
#print axioms zerlegeTor_typ
#print axioms zerlegeTor_ist
#print axioms zerlegeTor_hoch
#print axioms dpl_verweigert_software
#print axioms dpl_int1_frei
#print axioms dpl_extern_frei
#print axioms pruefeTor_limit
#print axioms pruefeTor_dpl
#print axioms pruefeTor_abwesend
#print axioms pruefeTor_selektor_null
#print axioms pruefeTor_typ
#print axioms pruefeTor_reserviert_ist
#print axioms pruefeTor_reserviert_hoch
#print axioms pruefeTor_bereit
#print axioms torDetail_faelle
#print axioms waehleStapel_behalten
#print axioms waehleStapel_tss_limit
#print axioms waehleStapel_wechseln
#print axioms slot_ist_pins
#print axioms slot_rsp_pins
#print axioms alsArch_gp
#print axioms alsArch_ohne_mitglied
#print axioms erste_pruefung_gewinnt_dpl
#print axioms rahmenWorte_laenge
#print axioms schiebeRahmen_leer
#print axioms liefere_prueft_zuerst
#print axioms liefere_stapel_vor_wirkung
#print axioms liefere_rsp_nichtkanonisch
#print axioms liefere_zugestellt_wechsel
#print axioms liefere_zugestellt_behalten
#print axioms idtWit_liest
#print axioms wit_zerlegt
#print axioms wit_bereit
#print axioms wit_stapel
#print axioms neg_limit
#print axioms neg_typ
#print axioms neg_abwesend
#print axioms neg_reserviert_ist
#print axioms neg_reserviert_hoch
#print axioms neg_selektor
#print axioms neg_ziel
#print axioms neg_dpl_kontrast
#print axioms neg_tss_limit
#print axioms neg_kein_wechsel
#print axioms neg_dunkel_vektor
#print axioms neg_codes
#print axioms wit_liefert_rip
#print axioms wit_liefert_if
#print axioms wit_liefert_gew
#print axioms wit_rahmen_ss
#print axioms wit_rahmen_rip
#print axioms wit_rahmen_anfang
#print axioms wit_rahmen_aendert
#print axioms liefer_zeuge_gemeinsam

end Gabbro.Grammatik.X86
