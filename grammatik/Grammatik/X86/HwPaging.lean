/-
  File:      Grammatik/X86/HwPaging.lean
  Subject:   IA-32e 4-level page translation as a named hardware model.

  Lane 1283: 4-level page walk (PML4/PDPT/PD/PT, 4 KiB pages),
  present/RW/US/XD bits with AND/OR combination, CR0.WP, accessed/dirty
  updates, #PF error-code outcome on the accepted fault vocabulary
  (`HardwareFaults`, `ExceptionPriorityHardware`), canonical-address
  check (#GP), and the bridge to the flat `Speicher` permissions.
  No TLB, no timing. OS policy stays user logic.
-/
import Grammatik.X86.HardwareExecution
import Grammatik.X86.ExceptionPriorityHardware

namespace Gabbro.Grammatik.X86

/-- One IA-32e page-table entry, decoded. Bit positions per SDM Vol 3A
    §4.5 Table 4-18: P bit 0, R/W bit 1, U/S bit 2, A bit 5, D bit 6,
    PS bit 7, XD bit 63; `rahmen` is the page-frame number. -/
structure SeitenEintrag where
  vorhanden : Bool
  schreibbar : Bool
  benutzer : Bool
  gross : Bool
  zugegriffen : Bool
  schmutzig : Bool
  noExec : Bool
  rahmen : Nat
  deriving DecidableEq, Repr

/-! ## 1. Raw entry encoding.

  Table memory holds raw 64-bit words; the walk decodes them. -/

/-- Raw bit test on a 64-bit word. -/
def wortBit (w : Wort) (k : Nat) : Bool :=
  decide ((w.toNat / 2 ^ k) % 2 = 1)

/-- Decode a raw 64-bit table entry into its named bits. -/
def eintragDekodieren (w : Wort) : SeitenEintrag :=
  { vorhanden := wortBit w 0
    schreibbar := wortBit w 1
    benutzer := wortBit w 2
    gross := wortBit w 7
    zugegriffen := wortBit w 5
    schmutzig := wortBit w 6
    noExec := wortBit w 63
    rahmen := (w.toNat / 4096) % 2 ^ 40 }

/-- Encode a decoded entry in the SDM layout. Faithful only for
    `rahmen < 2 ^ 40` (the frame field is 40 bits wide). -/
def eintragKodieren (e : SeitenEintrag) : Wort :=
  BitVec.ofNat 64
    ((if e.vorhanden then 1 else 0) +
      2 * (if e.schreibbar then 1 else 0) +
      4 * (if e.benutzer then 1 else 0) +
      32 * (if e.zugegriffen then 1 else 0) +
      64 * (if e.schmutzig then 1 else 0) +
      128 * (if e.gross then 1 else 0) +
      e.rahmen * 4096 + (if e.noExec then 2 ^ 63 else 0))

/-- The present bit round-trips. -/
theorem kodieren_vorhanden (e : SeitenEintrag) :
    (eintragDekodieren (eintragKodieren e)).vorhanden = e.vorhanden := by
  cases e with
  | mk v s u g a d x f =>
    cases v <;> cases s <;> cases u <;> cases g <;> cases a <;> cases d <;>
      cases x <;>
      simp [eintragDekodieren, eintragKodieren, wortBit,
        BitVec.toNat_ofNat] <;>
      omega

/-- The R/W bit round-trips. -/
theorem kodieren_schreibbar (e : SeitenEintrag) :
    (eintragDekodieren (eintragKodieren e)).schreibbar =
      e.schreibbar := by
  cases e with
  | mk v s u g a d x f =>
    cases v <;> cases s <;> cases u <;> cases g <;> cases a <;> cases d <;>
      cases x <;>
      simp [eintragDekodieren, eintragKodieren, wortBit,
        BitVec.toNat_ofNat] <;>
      omega

/-- The U/S bit round-trips. -/
theorem kodieren_benutzer (e : SeitenEintrag) :
    (eintragDekodieren (eintragKodieren e)).benutzer = e.benutzer := by
  cases e with
  | mk v s u g a d x f =>
    cases v <;> cases s <;> cases u <;> cases g <;> cases a <;> cases d <;>
      cases x <;>
      simp [eintragDekodieren, eintragKodieren, wortBit,
        BitVec.toNat_ofNat] <;>
      omega

/-- The PS bit round-trips. -/
theorem kodieren_gross (e : SeitenEintrag) :
    (eintragDekodieren (eintragKodieren e)).gross = e.gross := by
  cases e with
  | mk v s u g a d x f =>
    cases v <;> cases s <;> cases u <;> cases g <;> cases a <;> cases d <;>
      cases x <;>
      simp [eintragDekodieren, eintragKodieren, wortBit,
        BitVec.toNat_ofNat] <;>
      omega

/-- The accessed bit round-trips. -/
theorem kodieren_zugegriffen (e : SeitenEintrag) :
    (eintragDekodieren (eintragKodieren e)).zugegriffen =
      e.zugegriffen := by
  cases e with
  | mk v s u g a d x f =>
    cases v <;> cases s <;> cases u <;> cases g <;> cases a <;> cases d <;>
      cases x <;>
      simp [eintragDekodieren, eintragKodieren, wortBit,
        BitVec.toNat_ofNat] <;>
      omega

/-- The dirty bit round-trips. -/
theorem kodieren_schmutzig (e : SeitenEintrag) :
    (eintragDekodieren (eintragKodieren e)).schmutzig = e.schmutzig := by
  cases e with
  | mk v s u g a d x f =>
    cases v <;> cases s <;> cases u <;> cases g <;> cases a <;> cases d <;>
      cases x <;>
      simp [eintragDekodieren, eintragKodieren, wortBit,
        BitVec.toNat_ofNat] <;>
      omega

/-- The XD bit round-trips below the frame-field width. -/
theorem kodieren_noExec (e : SeitenEintrag) (h : e.rahmen < 2 ^ 40) :
    (eintragDekodieren (eintragKodieren e)).noExec = e.noExec := by
  cases e with
  | mk v s u g a d x f =>
    cases v <;> cases s <;> cases u <;> cases g <;> cases a <;> cases d <;>
      cases x <;>
      simp [eintragDekodieren, eintragKodieren, wortBit,
        BitVec.toNat_ofNat] at h ⊢ <;>
      omega

/-- The frame number round-trips below its field width. -/
theorem kodieren_rahmen (e : SeitenEintrag) (h : e.rahmen < 2 ^ 40) :
    (eintragDekodieren (eintragKodieren e)).rahmen = e.rahmen := by
  cases e with
  | mk v s u g a d x f =>
    cases v <;> cases s <;> cases u <;> cases g <;> cases a <;> cases d <;>
      cases x <;>
      simp [eintragDekodieren, eintragKodieren, wortBit,
        BitVec.toNat_ofNat] at h ⊢ <;>
      omega

/-! ## 2. Request, control register state, outcome.

  Linear addresses are `Nat` (byte offsets in the 64-bit space);
  physical addresses are `Nat` too. -/

/-- One translation request: linear address, access kind. `benutzer`
    is CPL 3 (user mode); `abruf` is an instruction fetch. -/
structure SeitenAnfrage where
  linear : Nat
  schreiben : Bool
  benutzer : Bool
  abruf : Bool
  deriving DecidableEq, Repr

/-- Control state: CR3 page-table base frame, CR0.WP, CR4.SMEP/SMAP
    refusal flags, IA32_EFER.NXE. SMEP/SMAP-armed configurations are
    REFUSED by the walk (see `gangSteuer`); WP is modelled. -/
structure SeitenSteuerung where
  cr3 : Nat
  wp : Bool
  smep : Bool
  smap : Bool
  nxe : Bool
  deriving DecidableEq, Repr

/-- #PF error code, SDM Vol 3A §4.7 Table 4-7: P bit 0 (0 non-present,
    1 protection), W/R bit 1, U/S bit 2, RSVD bit 3, I/D bit 4. -/
structure PfFehlerCode where
  p : Bool
  wr : Bool
  us : Bool
  rsvd : Bool
  id : Bool
  deriving DecidableEq, Repr

/-- Pack the error code into its 5-bit value. -/
def pfCodeBits (c : PfFehlerCode) : Nat :=
  (if c.p then 1 else 0) + 2 * (if c.wr then 1 else 0) +
    4 * (if c.us then 1 else 0) + 8 * (if c.rsvd then 1 else 0) +
    16 * (if c.id then 1 else 0)

/-- Walk outcome: success names the physical byte address; a page fault
    names the faulting LINEAR address plus its error code; a
    noncanonical address is #GP; a large page (PS set where 4 KiB
    pages walk on) is refused; an armed SMEP/SMAP configuration is
    refused as a whole. -/
inductive GangErgebnis where
  | ok : Nat → GangErgebnis
  | seitenFehler : Nat → PfFehlerCode → GangErgebnis
  | gpFehler : Nat → GangErgebnis
  | grossVerweigert : Nat → GangErgebnis
  | steuerVerweigert : GangErgebnis
  deriving DecidableEq, Repr

/-- The four table indices of a linear address (bits 47:39, 38:30,
    29:21, 20:12) plus the page offset (bits 11:0). -/
def gangIndexPML4 (lin : Nat) : Nat := (lin / 2 ^ 39) % 512
def gangIndexPDPT (lin : Nat) : Nat := (lin / 2 ^ 30) % 512
def gangIndexPD (lin : Nat) : Nat := (lin / 2 ^ 21) % 512
def gangIndexPT (lin : Nat) : Nat := (lin / 2 ^ 12) % 512
def gangOffset (lin : Nat) : Nat := lin % 4096

/-- Canonical linear address at the implemented 48-bit width. -/
def istKanonischNat (lin : Nat) : Bool :=
  decide (lin < 2 ^ 47 ∨ 2 ^ 64 - 2 ^ 47 ≤ lin)

/-- The walk's canonical check IS the accepted one, on constructed
    addresses below `2 ^ 64`. -/
theorem kanonischNat_bruecke (lin : Nat) (h : lin < 2 ^ 64) :
    istKanonischNat lin = istKanonisch (BitVec.ofNat 64 lin) := by
  have hmod : lin % 2 ^ 64 = lin := by omega
  simp [istKanonischNat, istKanonisch, BitVec.toNat_ofNat, hmod]

/-- Address zero is canonical in the walk's check. -/
theorem kanonischNat_null : istKanonischNat 0 = true := by decide

/-- Bit 47 alone set is the first noncanonical walk address. -/
theorem nichtkanonischNat_bit47 :
    istKanonischNat (2 ^ 47) = false := by
  decide

/-- A noncanonical walk address faults as #GP in the accepted
    classifier too: the walk reuses `adrKlasse`, never a copy. -/
theorem gangGp_adrKlasse (lin : Nat) (h : lin < 2 ^ 64)
    (hk : istKanonischNat lin = false) :
    adrKlasse (BitVec.ofNat 64 lin) false = some .gp := by
  have hkan : istKanonisch (BitVec.ofNat 64 lin) = false := by
    rw [← kanonischNat_bruecke lin h, hk]
  simp [adrKlasse, hkan]

/- CUTS (skeleton):
   NOT proved here, and not claimed:
   - Everything in the lane task: walk, permission combination, WP,
     accessed/dirty rules, #PF error code, canonical check, flat bridge,
     adapter/extended step, witness. This skeleton only fixes the
     entry vocabulary.
-/

end Gabbro.Grammatik.X86
