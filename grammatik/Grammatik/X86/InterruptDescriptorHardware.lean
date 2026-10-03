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

/- CUTS:
   Skeleton only: control state, gate address and the IDT-limit
   predicate. Parsing, checks, slot lookup, selection, faults,
   priority, frame, producer interface and witnesses are OPEN.
-/

#print axioms torAdresse
#print axioms torImLimit

end Gabbro.Grammatik.X86
