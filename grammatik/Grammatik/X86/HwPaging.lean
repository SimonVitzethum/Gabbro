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

/- CUTS (skeleton):
   NOT proved here, and not claimed:
   - Everything in the lane task: walk, permission combination, WP,
     accessed/dirty rules, #PF error code, canonical check, flat bridge,
     adapter/extended step, witness. This skeleton only fixes the
     entry vocabulary.
-/

end Gabbro.Grammatik.X86
