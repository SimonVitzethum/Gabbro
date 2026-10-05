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
import Grammatik.X86.Hw.Grundlage.HardwareExecution
import Grammatik.X86.Hw.Grundlage.ExceptionPriorityHardware

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

/-! ## 3. The four-level walk over decoded entries.

  `gangEbenen` runs the walk over four already-decoded entries
  (PML4, PDPT, PD, PT). The effective rights are combined along the
  path exactly as silicon does: R/W and U/S are ANDed (every level
  must grant), XD is ORed (any level may forbid execution). -/

/-- Leaf permission check: `effRW`/`effUS`/`effXD` are the combined
    rights; `rahmen` is the leaf frame. Supervisor writes to a
    read-only leaf fault only under CR0.WP. -/
def blattPruefung (st : SeitenSteuerung) (q : SeitenAnfrage)
    (effRW effUS effXD : Bool) (rahmen : Nat) : GangErgebnis :=
  if q.abruf then
    if effXD then
      .seitenFehler q.linear ⟨true, q.schreiben, q.benutzer, false, true⟩
    else if q.benutzer && !effUS then
      .seitenFehler q.linear ⟨true, q.schreiben, true, false, true⟩
    else .ok (rahmen * 4096 + gangOffset q.linear)
  else if q.benutzer && !effUS then
    .seitenFehler q.linear ⟨true, q.schreiben, true, false, false⟩
  else if q.schreiben && !effRW then
    if q.benutzer || st.wp then
      .seitenFehler q.linear ⟨true, true, q.benutzer, false, false⟩
    else .ok (rahmen * 4096 + gangOffset q.linear)
  else .ok (rahmen * 4096 + gangOffset q.linear)

/-- The combined rights of one four-entry path: R/W ANDed, U/S ANDed,
    XD ORed. -/
def gangRechte (e3 e2 e1 e0 : SeitenEintrag) : Bool × Bool × Bool :=
  (e3.schreibbar && e2.schreibbar && e1.schreibbar && e0.schreibbar,
   e3.benutzer && e2.benutzer && e1.benutzer && e0.benutzer,
   e3.noExec || e2.noExec || e1.noExec || e0.noExec)

/-- The walk over four decoded entries. Order of checks at each
    level: present, reserved-XD (when NXE is off), large-page rule;
    then the leaf permission check. -/
def gangEbenen (st : SeitenSteuerung) (q : SeitenAnfrage)
    (e3 e2 e1 e0 : SeitenEintrag) : GangErgebnis :=
  if st.smep || st.smap then .steuerVerweigert
  else if !istKanonischNat q.linear then .gpFehler q.linear
  else if !e3.vorhanden then
    .seitenFehler q.linear ⟨false, q.schreiben, q.benutzer, false, q.abruf⟩
  else if !st.nxe && e3.noExec then
    .seitenFehler q.linear ⟨true, q.schreiben, q.benutzer, true, q.abruf⟩
  else if e3.gross then
    .seitenFehler q.linear ⟨true, q.schreiben, q.benutzer, true, q.abruf⟩
  else if !e2.vorhanden then
    .seitenFehler q.linear ⟨false, q.schreiben, q.benutzer, false, q.abruf⟩
  else if !st.nxe && e2.noExec then
    .seitenFehler q.linear ⟨true, q.schreiben, q.benutzer, true, q.abruf⟩
  else if e2.gross then .grossVerweigert q.linear
  else if !e1.vorhanden then
    .seitenFehler q.linear ⟨false, q.schreiben, q.benutzer, false, q.abruf⟩
  else if !st.nxe && e1.noExec then
    .seitenFehler q.linear ⟨true, q.schreiben, q.benutzer, true, q.abruf⟩
  else if e1.gross then .grossVerweigert q.linear
  else if !e0.vorhanden then
    .seitenFehler q.linear ⟨false, q.schreiben, q.benutzer, false, q.abruf⟩
  else if !st.nxe && e0.noExec then
    .seitenFehler q.linear ⟨true, q.schreiben, q.benutzer, true, q.abruf⟩
  else if e0.gross then
    .seitenFehler q.linear ⟨true, q.schreiben, q.benutzer, true, q.abruf⟩
  else
    blattPruefung st q (e3.schreibbar && e2.schreibbar &&
      e1.schreibbar && e0.schreibbar)
      (e3.benutzer && e2.benutzer && e1.benutzer && e0.benutzer)
      (e3.noExec || e2.noExec || e1.noExec || e0.noExec) e0.rahmen

/-- An armed SMEP refuses the whole walk. -/
theorem gangEbenen_smep (st : SeitenSteuerung) (q : SeitenAnfrage)
    (e3 e2 e1 e0 : SeitenEintrag) (h : st.smep = true) :
    gangEbenen st q e3 e2 e1 e0 = .steuerVerweigert := by
  simp [gangEbenen, h]

/-- An armed SMAP refuses the whole walk. -/
theorem gangEbenen_smap (st : SeitenSteuerung) (q : SeitenAnfrage)
    (e3 e2 e1 e0 : SeitenEintrag) (h : st.smap = true) :
    gangEbenen st q e3 e2 e1 e0 = .steuerVerweigert := by
  simp [gangEbenen, h]

/-- A noncanonical address is #GP once control state is disarmed. -/
theorem gangEbenen_gp (st : SeitenSteuerung) (q : SeitenAnfrage)
    (e3 e2 e1 e0 : SeitenEintrag) (h1 : st.smep = false)
    (h2 : st.smap = false)
    (hk : istKanonischNat q.linear = false) :
    gangEbenen st q e3 e2 e1 e0 = .gpFehler q.linear := by
  simp [gangEbenen, h1, h2, hk]

/-- A missing PML4 entry faults non-present with the access bits. -/
theorem gangEbenen_nichtvorhanden3 (st : SeitenSteuerung)
    (q : SeitenAnfrage) (e3 e2 e1 e0 : SeitenEintrag)
    (h1 : st.smep = false) (h2 : st.smap = false)
    (hk : istKanonischNat q.linear = true)
    (h : e3.vorhanden = false) :
    gangEbenen st q e3 e2 e1 e0 =
      .seitenFehler q.linear
        ⟨false, q.schreiben, q.benutzer, false, q.abruf⟩ := by
  simp [gangEbenen, h1, h2, hk, h]

/-- A missing leaf entry faults non-present with the access bits. -/
theorem gangEbenen_nichtvorhanden0 (st : SeitenSteuerung)
    (q : SeitenAnfrage) (e3 e2 e1 e0 : SeitenEintrag)
    (h1 : st.smep = false) (h2 : st.smap = false)
    (hk : istKanonischNat q.linear = true)
    (h3 : e3.vorhanden = true) (hn3 : e3.noExec = false)
    (hg3 : e3.gross = false)
    (h2v : e2.vorhanden = true) (hn2 : e2.noExec = false)
    (hg2 : e2.gross = false)
    (h1v : e1.vorhanden = true) (hn1 : e1.noExec = false)
    (hg1 : e1.gross = false)
    (hnxe : st.nxe = true)
    (h : e0.vorhanden = false) :
    gangEbenen st q e3 e2 e1 e0 =
      .seitenFehler q.linear
        ⟨false, q.schreiben, q.benutzer, false, q.abruf⟩ := by
  simp [gangEbenen, h1, h2, hk, h3, hn3, hg3, h2v, hn2, hg2, h1v, hn1,
    hg1, hnxe, h]

/-- A 1 GiB large page (PS at PDPT) is refused, not silently mapped. -/
theorem gangEbenen_gross2 (st : SeitenSteuerung) (q : SeitenAnfrage)
    (e3 e2 e1 e0 : SeitenEintrag) (h1 : st.smep = false)
    (h2 : st.smap = false)
    (hk : istKanonischNat q.linear = true)
    (h3 : e3.vorhanden = true) (hn3 : e3.noExec = false)
    (hg3 : e3.gross = false)
    (h2v : e2.vorhanden = true) (hn2 : e2.noExec = false)
    (hnxe : st.nxe = true)
    (h : e2.gross = true) :
    gangEbenen st q e3 e2 e1 e0 = .grossVerweigert q.linear := by
  simp [gangEbenen, h1, h2, hk, h3, hn3, hg3, h2v, hn2, hnxe, h]

/-- A 2 MiB large page (PS at PD) is refused, not silently mapped. -/
theorem gangEbenen_gross1 (st : SeitenSteuerung) (q : SeitenAnfrage)
    (e3 e2 e1 e0 : SeitenEintrag) (h1 : st.smep = false)
    (h2 : st.smap = false)
    (hk : istKanonischNat q.linear = true)
    (h3 : e3.vorhanden = true) (hn3 : e3.noExec = false)
    (hg3 : e3.gross = false)
    (h2v : e2.vorhanden = true) (hn2 : e2.noExec = false)
    (hg2 : e2.gross = false)
    (h1v : e1.vorhanden = true) (hn1 : e1.noExec = false)
    (hnxe : st.nxe = true)
    (h : e1.gross = true) :
    gangEbenen st q e3 e2 e1 e0 = .grossVerweigert q.linear := by
  simp [gangEbenen, h1, h2, hk, h3, hn3, hg3, h2v, hn2, hg2, h1v, hn1,
    hnxe, h]

/-- A reached leaf runs the leaf check on the AND/OR-combined rights:
    the combination is checked, not just written. -/
theorem gangEbenen_rechte (st : SeitenSteuerung) (q : SeitenAnfrage)
    (e3 e2 e1 e0 : SeitenEintrag) (h1 : st.smep = false)
    (h2 : st.smap = false)
    (hk : istKanonischNat q.linear = true)
    (h3 : e3.vorhanden = true) (hn3 : e3.noExec = false)
    (hg3 : e3.gross = false)
    (h2v : e2.vorhanden = true) (hn2 : e2.noExec = false)
    (hg2 : e2.gross = false)
    (h1v : e1.vorhanden = true) (hn1 : e1.noExec = false)
    (hg1 : e1.gross = false)
    (h0v : e0.vorhanden = true) (hn0 : e0.noExec = false)
    (hg0 : e0.gross = false)
    (hnxe : st.nxe = true) :
    gangEbenen st q e3 e2 e1 e0 =
      blattPruefung st q (gangRechte e3 e2 e1 e0).1
        (gangRechte e3 e2 e1 e0).2.1
        (gangRechte e3 e2 e1 e0).2.2 e0.rahmen := by
  simp [gangEbenen, gangRechte, h1, h2, hk, h3, hn3, hg3, h2v, hn2, hg2,
    h1v, hn1, hg1, h0v, hn0, hg0, hnxe]

/-- CR0.WP protects a read-only leaf against supervisor writes. -/
theorem blatt_wp_schuetzt (st : SeitenSteuerung) (q : SeitenAnfrage)
    (effRW effUS : Bool) (rahmen : Nat) (hwp : st.wp = true)
    (hsch : q.schreiben = true) (hben : q.benutzer = false)
    (hab : q.abruf = false) (hrw : effRW = false) :
    blattPruefung st q effRW effUS false rahmen =
      .seitenFehler q.linear ⟨true, true, false, false, false⟩ := by
  simp [blattPruefung, hwp, hsch, hben, hab, hrw]

/-- With WP off, the supervisor write to a read-only leaf succeeds. -/
theorem blatt_wp_offen_erlaubt (st : SeitenSteuerung) (q : SeitenAnfrage)
    (effUS : Bool) (rahmen : Nat) (hwp : st.wp = false)
    (hsch : q.schreiben = true) (hben : q.benutzer = false)
    (hab : q.abruf = false) :
    blattPruefung st q false effUS false rahmen =
      .ok (rahmen * 4096 + gangOffset q.linear) := by
  simp [blattPruefung, hwp, hsch, hben, hab]

/-- A user write to a read-only leaf faults whatever WP says. -/
theorem blatt_benutzer_schreibschutz (st : SeitenSteuerung)
    (q : SeitenAnfrage) (rahmen : Nat) (hsch : q.schreiben = true)
    (hben : q.benutzer = true) (hab : q.abruf = false) :
    blattPruefung st q false true false rahmen =
      .seitenFehler q.linear ⟨true, true, true, false, false⟩ := by
  simp [blattPruefung, hsch, hben, hab]

/-- A fetch through an execute-disabled path faults with I/D set. -/
theorem blatt_abruf_xd (st : SeitenSteuerung) (q : SeitenAnfrage)
    (effRW effUS : Bool) (rahmen : Nat) (hab : q.abruf = true) :
    blattPruefung st q effRW effUS true rahmen =
      .seitenFehler q.linear
        ⟨true, q.schreiben, q.benutzer, false, true⟩ := by
  simp [blattPruefung, hab]

/-- A user read of a user leaf succeeds. -/
theorem blatt_lese_ok (st : SeitenSteuerung) (q : SeitenAnfrage)
    (effRW effXD : Bool) (rahmen : Nat) (hsch : q.schreiben = false)
    (hben : q.benutzer = true) (hab : q.abruf = false) :
    blattPruefung st q effRW true effXD rahmen =
      .ok (rahmen * 4096 + gangOffset q.linear) := by
  simp [blattPruefung, hsch, hben, hab]

/-! ## 4. Table memory and accessed/dirty updates.

  Table memory holds raw entry words keyed by entry number
  (`rahmen * 512 + index`). Accessed/dirty updates set only bit 5/6;
  every other bit is preserved by the round-trip lemmas of §1. -/

/-- Table memory: raw entry words keyed by entry number. -/
def SeitenTabellen := Nat → Wort

/-- Read one decoded entry: table at frame `rahmen`, slot `idx`. -/
def seitenTabEintrag (tab : Nat → Wort) (rahmen idx : Nat) : SeitenEintrag :=
  eintragDekodieren (tab (rahmen * 512 + idx))

/-- Set the accessed bit of a raw entry word. -/
def wortZugriff (w : Wort) : Wort :=
  eintragKodieren { eintragDekodieren w with zugegriffen := true }

/-- Set the dirty bit of a raw entry word. -/
def wortSchmutzig (w : Wort) : Wort :=
  eintragKodieren { eintragDekodieren w with schmutzig := true }

/-- Setting accessed keeps the present bit. -/
theorem wortZugriff_vorhanden (w : Wort) :
    (eintragDekodieren (wortZugriff w)).vorhanden =
      (eintragDekodieren w).vorhanden := by
  unfold wortZugriff
  rw [kodieren_vorhanden]

/-- Setting accessed keeps the R/W bit. -/
theorem wortZugriff_schreibbar (w : Wort) :
    (eintragDekodieren (wortZugriff w)).schreibbar =
      (eintragDekodieren w).schreibbar := by
  unfold wortZugriff
  rw [kodieren_schreibbar]

/-- Setting accessed keeps the U/S bit. -/
theorem wortZugriff_benutzer (w : Wort) :
    (eintragDekodieren (wortZugriff w)).benutzer =
      (eintragDekodieren w).benutzer := by
  unfold wortZugriff
  rw [kodieren_benutzer]

/-- Setting accessed keeps the PS bit. -/
theorem wortZugriff_gross (w : Wort) :
    (eintragDekodieren (wortZugriff w)).gross =
      (eintragDekodieren w).gross := by
  unfold wortZugriff
  rw [kodieren_gross]

/-- Setting accessed keeps the XD bit below the frame width. -/
theorem wortZugriff_noExec (w : Wort)
    (h : (eintragDekodieren w).rahmen < 2 ^ 40) :
    (eintragDekodieren (wortZugriff w)).noExec =
      (eintragDekodieren w).noExec := by
  have h' : ({eintragDekodieren w with zugegriffen := true}).rahmen <
      2 ^ 40 := h
  unfold wortZugriff
  rw [kodieren_noExec _ h']

/-- Setting accessed keeps the frame below its field width. -/
theorem wortZugriff_rahmen (w : Wort)
    (h : (eintragDekodieren w).rahmen < 2 ^ 40) :
    (eintragDekodieren (wortZugriff w)).rahmen =
      (eintragDekodieren w).rahmen := by
  have h' : ({eintragDekodieren w with zugegriffen := true}).rahmen <
      2 ^ 40 := h
  unfold wortZugriff
  rw [kodieren_rahmen _ h']

/-- Setting accessed really sets it. -/
theorem wortZugriff_setzt (w : Wort) :
    (eintragDekodieren (wortZugriff w)).zugegriffen = true := by
  unfold wortZugriff
  rw [kodieren_zugegriffen]

/-- Setting dirty keeps the present bit. -/
theorem wortSchmutzig_vorhanden (w : Wort) :
    (eintragDekodieren (wortSchmutzig w)).vorhanden =
      (eintragDekodieren w).vorhanden := by
  unfold wortSchmutzig
  rw [kodieren_vorhanden]

/-- Setting dirty keeps the R/W bit. -/
theorem wortSchmutzig_schreibbar (w : Wort) :
    (eintragDekodieren (wortSchmutzig w)).schreibbar =
      (eintragDekodieren w).schreibbar := by
  unfold wortSchmutzig
  rw [kodieren_schreibbar]

/-- Setting dirty keeps the U/S bit. -/
theorem wortSchmutzig_benutzer (w : Wort) :
    (eintragDekodieren (wortSchmutzig w)).benutzer =
      (eintragDekodieren w).benutzer := by
  unfold wortSchmutzig
  rw [kodieren_benutzer]

/-- Setting dirty keeps the PS bit. -/
theorem wortSchmutzig_gross (w : Wort) :
    (eintragDekodieren (wortSchmutzig w)).gross =
      (eintragDekodieren w).gross := by
  unfold wortSchmutzig
  rw [kodieren_gross]

/-- Setting dirty keeps the XD bit below the frame width. -/
theorem wortSchmutzig_noExec (w : Wort)
    (h : (eintragDekodieren w).rahmen < 2 ^ 40) :
    (eintragDekodieren (wortSchmutzig w)).noExec =
      (eintragDekodieren w).noExec := by
  have h' : ({eintragDekodieren w with schmutzig := true}).rahmen <
      2 ^ 40 := h
  unfold wortSchmutzig
  rw [kodieren_noExec _ h']

/-- Setting dirty keeps the frame below its field width. -/
theorem wortSchmutzig_rahmen (w : Wort)
    (h : (eintragDekodieren w).rahmen < 2 ^ 40) :
    (eintragDekodieren (wortSchmutzig w)).rahmen =
      (eintragDekodieren w).rahmen := by
  have h' : ({eintragDekodieren w with schmutzig := true}).rahmen <
      2 ^ 40 := h
  unfold wortSchmutzig
  rw [kodieren_rahmen _ h']

/-- Setting dirty really sets it. -/
theorem wortSchmutzig_setzt (w : Wort) :
    (eintragDekodieren (wortSchmutzig w)).schmutzig = true := by
  unfold wortSchmutzig
  rw [kodieren_schmutzig]

/-! ## 5. The full walk with write-back.

  `seitenGang` looks the four entries up from table memory, runs
  `gangEbenen`, and on success writes back accessed on every touched
  entry and dirty on the leaf (for writes). Every other outcome leaves
  the tables unchanged. -/

/-- Mark accessed on the touched entry addresses, dirty on the leaf
    (for writes). Untouched entries keep their exact word. -/
def tabAD (tab : Nat → Wort) (touched : List Nat) (blatt : Option Nat) :
    Nat → Wort :=
  fun n =>
    let w1 := if n ∈ touched then wortZugriff (tab n) else tab n
    match blatt with
    | some b => if n = b then wortSchmutzig w1 else w1
    | none => w1

/-- Without a leaf mark, an untouched entry keeps its word. -/
theorem tabAD_unberuehrt_keinBlatt (tab : Nat → Wort)
    (touched : List Nat) (n : Nat) (h : n ∉ touched) :
    tabAD tab touched none n = tab n := by
  simp [tabAD, h]

/-- With a leaf mark, an entry that is neither touched nor the leaf
    keeps its word. -/
theorem tabAD_unberuehrt_blatt (tab : Nat → Wort) (touched : List Nat)
    (b n : Nat) (h1 : n ∉ touched) (h2 : n ≠ b) :
    tabAD tab touched (some b) n = tab n := by
  simp [tabAD, h1, h2]

/-- The update touches only touched entries and the leaf. -/
theorem tabAD_nur_beruehrt (tab : Nat → Wort) (touched : List Nat)
    (blatt : Option Nat) (n : Nat)
    (h : tabAD tab touched blatt n ≠ tab n) :
    n ∈ touched ∨ ∃ b, blatt = some b ∧ n = b := by
  cases blatt with
  | none =>
    refine Or.inl ?_
    by_cases hn : n ∈ touched
    · exact hn
    · exact absurd (tabAD_unberuehrt_keinBlatt tab touched n hn) h
  | some b =>
    by_cases heq : n = b
    · exact Or.inr ⟨b, rfl, heq⟩
    · refine Or.inl ?_
      by_cases hn : n ∈ touched
      · exact hn
      · exact absurd
          (tabAD_unberuehrt_blatt tab touched b n hn heq) h

/-- Table write-back for one walk outcome: only success updates. -/
def seitenGangTab (tab : Nat → Wort) (touched : List Nat)
    (blatt : Option Nat) (e : GangErgebnis) : Nat → Wort :=
  match e with
  | .ok _ => tabAD tab touched blatt
  | _ => tab

/-- A non-success outcome leaves the tables unchanged. -/
theorem seitenGangTab_nichtOk (tab : Nat → Wort) (touched : List Nat)
    (blatt : Option Nat) (e : GangErgebnis)
    (h : ¬ ∃ phys, e = .ok phys) :
    seitenGangTab tab touched blatt e = tab := by
  cases e with
  | ok phys => exact absurd ⟨phys, rfl⟩ h
  | seitenFehler a c => rfl
  | gpFehler a => rfl
  | grossVerweigert a => rfl
  | steuerVerweigert => rfl

/-- Full walk: look the four entries up from table memory, run
    `gangEbenen`, write back accessed/dirty on success. Written
    let-free so the lookup equations rewrite directly. -/
def seitenGang (st : SeitenSteuerung) (tab : Nat → Wort)
    (q : SeitenAnfrage) : GangErgebnis × (Nat → Wort) :=
  (gangEbenen st q (seitenTabEintrag tab st.cr3 (gangIndexPML4 q.linear))
    (seitenTabEintrag tab
      (seitenTabEintrag tab st.cr3 (gangIndexPML4 q.linear)).rahmen
      (gangIndexPDPT q.linear))
    (seitenTabEintrag tab
      (seitenTabEintrag tab
        (seitenTabEintrag tab st.cr3 (gangIndexPML4 q.linear)).rahmen
        (gangIndexPDPT q.linear)).rahmen
      (gangIndexPD q.linear))
    (seitenTabEintrag tab
      (seitenTabEintrag tab
        (seitenTabEintrag tab
          (seitenTabEintrag tab st.cr3 (gangIndexPML4 q.linear)).rahmen
          (gangIndexPDPT q.linear)).rahmen
        (gangIndexPD q.linear)).rahmen
      (gangIndexPT q.linear)),
   seitenGangTab tab
    [st.cr3 * 512 + gangIndexPML4 q.linear,
     (seitenTabEintrag tab st.cr3 (gangIndexPML4 q.linear)).rahmen * 512 +
       gangIndexPDPT q.linear,
     (seitenTabEintrag tab
       (seitenTabEintrag tab st.cr3 (gangIndexPML4 q.linear)).rahmen
       (gangIndexPDPT q.linear)).rahmen * 512 + gangIndexPD q.linear,
     (seitenTabEintrag tab
       (seitenTabEintrag tab
         (seitenTabEintrag tab st.cr3 (gangIndexPML4 q.linear)).rahmen
         (gangIndexPDPT q.linear)).rahmen
       (gangIndexPD q.linear)).rahmen * 512 + gangIndexPT q.linear]
    (if q.schreiben then
      some ((seitenTabEintrag tab
        (seitenTabEintrag tab
          (seitenTabEintrag tab st.cr3 (gangIndexPML4 q.linear)).rahmen
          (gangIndexPDPT q.linear)).rahmen
        (gangIndexPD q.linear)).rahmen * 512 + gangIndexPT q.linear)
     else none)
    (gangEbenen st q (seitenTabEintrag tab st.cr3 (gangIndexPML4 q.linear))
      (seitenTabEintrag tab
        (seitenTabEintrag tab st.cr3 (gangIndexPML4 q.linear)).rahmen
        (gangIndexPDPT q.linear))
      (seitenTabEintrag tab
        (seitenTabEintrag tab
          (seitenTabEintrag tab st.cr3 (gangIndexPML4 q.linear)).rahmen
          (gangIndexPDPT q.linear)).rahmen
        (gangIndexPD q.linear))
      (seitenTabEintrag tab
        (seitenTabEintrag tab
          (seitenTabEintrag tab
            (seitenTabEintrag tab st.cr3 (gangIndexPML4 q.linear)).rahmen
            (gangIndexPDPT q.linear)).rahmen
          (gangIndexPD q.linear)).rahmen
        (gangIndexPT q.linear))))

/-- A non-success walk leaves the tables unchanged. -/
theorem seitenGang_nichtOk_still (st : SeitenSteuerung) (tab : Nat → Wort)
    (q : SeitenAnfrage) (e : GangErgebnis)
    (h1 : (seitenGang st tab q).1 = e)
    (h2 : ¬ ∃ phys, e = .ok phys) :
    (seitenGang st tab q).2 = tab := by
  simp only [seitenGang] at h1 ⊢
  rw [h1]
  exact seitenGangTab_nichtOk _ _ _ _ h2

/-- The walk depends only on control bits: entries with equal
    control fields walk equally. Intermediate frames never occur in
    the outcome (only the leaf frame does), so they take no premise. -/
theorem gangEbenen_kongr (st : SeitenSteuerung) (q : SeitenAnfrage)
    (e3 e2 e1 e0 e3' e2' e1' e0' : SeitenEintrag)
    (hv3 : e3.vorhanden = e3'.vorhanden)
    (hr3 : e3.schreibbar = e3'.schreibbar)
    (hu3 : e3.benutzer = e3'.benutzer)
    (hg3 : e3.gross = e3'.gross)
    (hx3 : e3.noExec = e3'.noExec)
    (hv2 : e2.vorhanden = e2'.vorhanden)
    (hr2 : e2.schreibbar = e2'.schreibbar)
    (hu2 : e2.benutzer = e2'.benutzer)
    (hg2 : e2.gross = e2'.gross)
    (hx2 : e2.noExec = e2'.noExec)
    (hv1 : e1.vorhanden = e1'.vorhanden)
    (hr1 : e1.schreibbar = e1'.schreibbar)
    (hu1 : e1.benutzer = e1'.benutzer)
    (hg1 : e1.gross = e1'.gross)
    (hx1 : e1.noExec = e1'.noExec)
    (hv0 : e0.vorhanden = e0'.vorhanden)
    (hr0 : e0.schreibbar = e0'.schreibbar)
    (hu0 : e0.benutzer = e0'.benutzer)
    (hg0 : e0.gross = e0'.gross)
    (hx0 : e0.noExec = e0'.noExec)
    (hf0 : e0.rahmen = e0'.rahmen) :
    gangEbenen st q e3 e2 e1 e0 =
      gangEbenen st q e3' e2' e1' e0' := by
  simp only [gangEbenen]
  rw [hv3, hr3, hu3, hg3, hx3, hv2, hr2, hu2, hg2, hx2, hv1, hr1, hu1,
    hg1, hx1, hv0, hr0, hu0, hg0, hx0, hf0]

/-- The walk outcome is the four-entry walk: unfolding without
    simp equation lemmas (which loop here). -/
theorem seitenGang_fst (st : SeitenSteuerung) (tab : Nat → Wort)
    (q : SeitenAnfrage) :
    (seitenGang st tab q).1 =
      gangEbenen st q (seitenTabEintrag tab st.cr3 (gangIndexPML4 q.linear))
        (seitenTabEintrag tab
          (seitenTabEintrag tab st.cr3 (gangIndexPML4 q.linear)).rahmen
          (gangIndexPDPT q.linear))
        (seitenTabEintrag tab
          (seitenTabEintrag tab
            (seitenTabEintrag tab st.cr3 (gangIndexPML4 q.linear)).rahmen
            (gangIndexPDPT q.linear)).rahmen
          (gangIndexPD q.linear))
        (seitenTabEintrag tab
          (seitenTabEintrag tab
            (seitenTabEintrag tab
              (seitenTabEintrag tab st.cr3 (gangIndexPML4 q.linear)).rahmen
              (gangIndexPDPT q.linear)).rahmen
            (gangIndexPD q.linear)).rahmen
          (gangIndexPT q.linear)) := rfl

/-- Tables that agree on every control bit give the same walk outcome:
    the walk never consults accessed/dirty. Level addresses agree
    down the frame chain, so each side's entries meet `gangEbenen_kongr`
    directly; the giant walk body is unfolded only once, inside it. -/
theorem seitenGang_steuer_gleich (st : SeitenSteuerung)
    (tab tab' : Nat → Wort) (q : SeitenAnfrage)
    (h : ∀ n, (eintragDekodieren (tab n)).vorhanden =
          (eintragDekodieren (tab' n)).vorhanden ∧
        (eintragDekodieren (tab n)).schreibbar =
          (eintragDekodieren (tab' n)).schreibbar ∧
        (eintragDekodieren (tab n)).benutzer =
          (eintragDekodieren (tab' n)).benutzer ∧
        (eintragDekodieren (tab n)).gross =
          (eintragDekodieren (tab' n)).gross ∧
        (eintragDekodieren (tab n)).noExec =
          (eintragDekodieren (tab' n)).noExec ∧
        (eintragDekodieren (tab n)).rahmen =
          (eintragDekodieren (tab' n)).rahmen) :
    (seitenGang st tab q).1 = (seitenGang st tab' q).1 := by
  obtain ⟨hv3, hr3, hu3, hg3, hx3, hf3⟩ :=
    h (st.cr3 * 512 + gangIndexPML4 q.linear)
  obtain ⟨_, _, _, _, _, hf2o⟩ := h
    ((eintragDekodieren
      (tab (st.cr3 * 512 + gangIndexPML4 q.linear))).rahmen * 512 +
      gangIndexPDPT q.linear)
  obtain ⟨_, _, _, _, _, hf1o⟩ := h
    ((eintragDekodieren
      (tab ((eintragDekodieren
        (tab (st.cr3 * 512 + gangIndexPML4 q.linear))).rahmen * 512 +
          gangIndexPDPT q.linear))).rahmen * 512 +
      gangIndexPD q.linear)
  have a2 : (eintragDekodieren
        (tab (st.cr3 * 512 + gangIndexPML4 q.linear))).rahmen * 512 +
        gangIndexPDPT q.linear =
      (eintragDekodieren
        (tab' (st.cr3 * 512 + gangIndexPML4 q.linear))).rahmen * 512 +
        gangIndexPDPT q.linear := by rw [hf3]
  have a1 : (eintragDekodieren
        (tab ((eintragDekodieren
          (tab (st.cr3 * 512 + gangIndexPML4 q.linear))).rahmen * 512 +
            gangIndexPDPT q.linear))).rahmen * 512 +
        gangIndexPD q.linear =
      (eintragDekodieren
        (tab' ((eintragDekodieren
          (tab' (st.cr3 * 512 + gangIndexPML4 q.linear))).rahmen * 512 +
            gangIndexPDPT q.linear))).rahmen * 512 +
        gangIndexPD q.linear := by rw [hf2o, hf3]
  have a0 : (eintragDekodieren
        (tab ((eintragDekodieren
          (tab ((eintragDekodieren
            (tab (st.cr3 * 512 + gangIndexPML4 q.linear))).rahmen * 512 +
              gangIndexPDPT q.linear))).rahmen * 512 +
            gangIndexPD q.linear))).rahmen * 512 +
        gangIndexPT q.linear =
      (eintragDekodieren
        (tab' ((eintragDekodieren
          (tab' ((eintragDekodieren
            (tab' (st.cr3 * 512 + gangIndexPML4 q.linear))).rahmen * 512 +
              gangIndexPDPT q.linear))).rahmen * 512 +
            gangIndexPD q.linear))).rahmen * 512 +
        gangIndexPT q.linear := by rw [hf1o, hf2o, hf3]
  have c2 := h ((eintragDekodieren
    (tab (st.cr3 * 512 + gangIndexPML4 q.linear))).rahmen * 512 +
      gangIndexPDPT q.linear)
  rw [a2] at c2
  obtain ⟨hv2, hr2, hu2, hg2, hx2, hf2⟩ := c2
  have c1 := h ((eintragDekodieren
    (tab ((eintragDekodieren
      (tab (st.cr3 * 512 + gangIndexPML4 q.linear))).rahmen * 512 +
        gangIndexPDPT q.linear))).rahmen * 512 + gangIndexPD q.linear)
  rw [a1] at c1
  obtain ⟨hv1, hr1, hu1, hg1, hx1, hf1⟩ := c1
  have c0 := h ((eintragDekodieren
    (tab ((eintragDekodieren
      (tab ((eintragDekodieren
        (tab (st.cr3 * 512 + gangIndexPML4 q.linear))).rahmen * 512 +
          gangIndexPDPT q.linear))).rahmen * 512 +
        gangIndexPD q.linear))).rahmen * 512 + gangIndexPT q.linear)
  rw [a0] at c0
  obtain ⟨hv0, hr0, hu0, hg0, hx0, hf0⟩ := c0
  have g1 := seitenGang_fst st tab q
  have g2 := seitenGang_fst st tab' q
  rw [g1, g2]
  simp only [seitenTabEintrag]
  rw [hf3, hf2, hf1]
  exact gangEbenen_kongr st q _ _ _ _ _ _ _ _ hv3 hr3 hu3 hg3 hx3
    hv2 hr2 hu2 hg2 hx2 hv1 hr1 hu1 hg1 hx1 hv0 hr0 hu0 hg0 hx0 hf0

/-! ## 6. Witness: two mappings of one physical page.

  One shared intermediate chain at frame 16 (PML4/PDPT/PD all read
  slot 0 of the same table); PT slots 1 and 2 map linear pages 1 and 2
  onto the same frame 32, the first read-write, the second read-only.
  All other slots are absent. -/

/-- Shared intermediate-table frame. -/
def witRahmenTab : Nat := 16

/-- Shared leaf frame: both linear pages land here. -/
def witRahmenBlatt : Nat := 32

/-- Intermediate entry: present, full rights, no XD, next frame 16. -/
def witEZwischen : SeitenEintrag :=
  { vorhanden := true, schreibbar := true, benutzer := true,
    gross := false, zugegriffen := false, schmutzig := false,
    noExec := false, rahmen := 16 }

/-- Read-write leaf onto frame 32. -/
def witBlattRW : SeitenEintrag :=
  { vorhanden := true, schreibbar := true, benutzer := true,
    gross := false, zugegriffen := false, schmutzig := false,
    noExec := false, rahmen := 32 }

/-- Read-only leaf onto frame 32. -/
def witBlattRO : SeitenEintrag :=
  { vorhanden := true, schreibbar := false, benutzer := true,
    gross := false, zugegriffen := false, schmutzig := false,
    noExec := false, rahmen := 32 }

/-- Witness tables: slot 0 of frame 16 chains to itself at every
    level; PT slots 1 and 2 are the RW/RO leaves onto frame 32. -/
def witTab : Nat → Wort :=
  fun n =>
    if n = 16 * 512 + 0 then eintragKodieren witEZwischen
    else if n = 16 * 512 + 1 then eintragKodieren witBlattRW
    else if n = 16 * 512 + 2 then eintragKodieren witBlattRO
    else 0

/-- Witness control: CR3 at frame 16, WP armed, SMEP/SMAP off, NXE on. -/
def witSeitenSteuer : SeitenSteuerung :=
  { cr3 := 16, wp := true, smep := false, smap := false, nxe := true }

/-- User read of linear page 1 succeeds onto frame 32. -/
theorem wit_lese_rw_ok :
    (seitenGang witSeitenSteuer witTab ⟨4096, false, true, false⟩).1 =
      .ok 131072 := by
  decide

/-- User read of linear page 2 succeeds onto the SAME frame 32. -/
theorem wit_lese_ro_ok :
    (seitenGang witSeitenSteuer witTab ⟨8192, false, true, false⟩).1 =
      .ok 131072 := by
  decide

/-- Both mappings name the same physical page. -/
theorem wit_gleiches_blatt :
    (seitenGang witSeitenSteuer witTab ⟨4096, false, true, false⟩).1 =
      (seitenGang witSeitenSteuer witTab ⟨8192, false, true, false⟩).1 := by
  decide

/-- User write through the RW mapping succeeds. -/
theorem wit_schreibe_rw_ok :
    (seitenGang witSeitenSteuer witTab ⟨4096, true, true, false⟩).1 =
      .ok 131072 := by
  decide

/-- User write through the RO mapping faults with W/R set. -/
theorem wit_schreibe_ro_pf :
    (seitenGang witSeitenSteuer witTab ⟨8192, true, true, false⟩).1 =
      .seitenFehler 8192 ⟨true, true, true, false, false⟩ := by
  decide

/-- Supervisor write through the RO mapping faults under WP. -/
theorem wit_schreibe_ro_wp :
    (seitenGang witSeitenSteuer witTab ⟨8192, true, false, false⟩).1 =
      .seitenFehler 8192 ⟨true, true, false, false, false⟩ := by
  decide

/-- Read of the unmapped linear page 3 faults non-present. -/
theorem wit_lese_loch_pf :
    (seitenGang witSeitenSteuer witTab ⟨12288, false, true, false⟩).1 =
      .seitenFehler 12288 ⟨false, false, true, false, false⟩ := by
  decide

/-- A noncanonical linear address is #GP in the full walk. -/
theorem wit_nichtkanonisch_gp :
    (seitenGang witSeitenSteuer witTab ⟨2 ^ 47, false, true, false⟩).1 =
      .gpFehler (2 ^ 47) := by
  decide

/-- The write sets accessed on the touched intermediate entry. -/
theorem wit_zugriff_gesetzt :
    (eintragDekodieren
      ((seitenGang witSeitenSteuer witTab ⟨4096, true, true, false⟩).2
        (16 * 512 + 0))).zugegriffen = true := by
  decide

/-- The write sets dirty on the leaf entry. -/
theorem wit_schmutzig_gesetzt :
    (eintragDekodieren
      ((seitenGang witSeitenSteuer witTab ⟨4096, true, true, false⟩).2
        (16 * 512 + 1))).schmutzig = true := by
  decide

/-- An untouched entry keeps its exact word through the write-back. -/
theorem wit_unberuehrt_still :
    (seitenGang witSeitenSteuer witTab ⟨4096, true, true, false⟩).2
      (16 * 512 + 7) = witTab (16 * 512 + 7) := by
  decide

/-! ## 7. Bridge to the flat permission model.

  The flat `Speicher` is the physical memory. `FlachStimmt` is the
  proof obligation the OS (user logic) establishes when it installs
  its tables: every walk-admitted access meets its flat permission.
  The walk gives the check; the policy stays outside the model. -/

/-- Flat consistency: every walk-admitted read meets `lesbar`, every
    walk-admitted write meets `schreibbar`, at the physical byte. -/
def FlachStimmt (st : SeitenSteuerung) (tab : Nat → Wort)
    (m : Speicher) : Prop :=
  ∀ (q : SeitenAnfrage) (phys : Nat),
    (seitenGang st tab q).1 = .ok phys →
    (q.schreiben = true → m.schreibbar (BitVec.ofNat 64 phys) = true) ∧
    (q.schreiben = false → m.lesbar (BitVec.ofNat 64 phys) = true)

/-- A walk-admitted write meets the flat write permission. -/
theorem gangOk_flach_schreibbar (st : SeitenSteuerung) (tab : Nat → Wort)
    (m : Speicher) (q : SeitenAnfrage) (phys : Nat)
    (hcons : FlachStimmt st tab m)
    (h : (seitenGang st tab q).1 = .ok phys)
    (hs : q.schreiben = true) :
    m.schreibbar (BitVec.ofNat 64 phys) = true :=
  (hcons q phys h).1 hs

/-- A walk-admitted read meets the flat read permission. -/
theorem gangOk_flach_lesbar (st : SeitenSteuerung) (tab : Nat → Wort)
    (m : Speicher) (q : SeitenAnfrage) (phys : Nat)
    (hcons : FlachStimmt st tab m)
    (h : (seitenGang st tab q).1 = .ok phys)
    (hs : q.schreiben = false) :
    m.lesbar (BitVec.ofNat 64 phys) = true :=
  (hcons q phys h).2 hs

/-- The obligation is inhabited: the all-permissive flat memory meets
    every walk, so the bridge is never vacuous. -/
def allWahrSpeicher : Speicher :=
  { bytes := fun _ => BitVec.ofNat 8 0
    lesbar := fun _ => true
    schreibbar := fun _ => true
    ausfuehrbar := fun _ => false }

/-- The all-permissive memory satisfies the obligation as stated. -/
theorem flachStimmt_allwahr (st : SeitenSteuerung) (tab : Nat → Wort) :
    FlachStimmt st tab allWahrSpeicher := by
  intro q phys h
  exact ⟨fun _ => rfl, fun _ => rfl⟩

/-- Witness flat memory: exactly frame 32 is readable and writable. -/
def witFlach : Speicher :=
  { bytes := fun _ => BitVec.ofNat 8 0
    lesbar := fun a => decide (a.toNat / 4096 = 32)
    schreibbar := fun a => decide (a.toNat / 4096 = 32)
    ausfuehrbar := fun _ => false }

/-- The shared page is flat-readable. -/
theorem wit_flach_liest :
    witFlach.lesbar (BitVec.ofNat 64 131072) = true := by
  decide

/-- The shared page is flat-writable. -/
theorem wit_flach_schreibt :
    witFlach.schreibbar (BitVec.ofNat 64 131072) = true := by
  decide

/-! ## 8. Fault class consensus with the accepted vocabulary.

  Every walk page fault IS class `#PF`; every walk #GP IS class `#GP`.
  Non-present agrees with `seitenKlasse` on a dark page state, and the
  vector is the accepted Table 6-1 entry. -/

/-- The fault class of one walk outcome: page faults are `#PF`,
    noncanonical addresses are `#GP`; refusals carry no class. -/
def gangKlasse : GangErgebnis → Option ArchFehler
  | .seitenFehler _ _ => some .pf
  | .gpFehler _ => some .gp
  | _ => none

/-- A walk page fault carries class `#PF`. -/
theorem gangKlasse_pf (g : GangErgebnis) (a : Nat) (c : PfFehlerCode)
    (h : g = .seitenFehler a c) : gangKlasse g = some .pf := by
  simp [gangKlasse, h]

/-- A walk #GP carries class `#GP`. -/
theorem gangKlasse_gp (g : GangErgebnis) (a : Nat)
    (h : g = .gpFehler a) : gangKlasse g = some .gp := by
  simp [gangKlasse, h]

/-- A refusal carries no fault class. -/
theorem gangKlasse_steuer_keine (g : GangErgebnis)
    (h : g = .steuerVerweigert) : gangKlasse g = none := by
  simp [gangKlasse, h]

/-- A refused large page carries no fault class. -/
theorem gangKlasse_gross_keine (g : GangErgebnis) (a : Nat)
    (h : g = .grossVerweigert a) : gangKlasse g = none := by
  simp [gangKlasse, h]

/-- Non-present consensus: the walk's missing-entry fault and the
    accepted `seitenKlasse` on a dark page state both answer `#PF`. -/
theorem gangPf_seitenKlasse_eins (a : Adresse) :
    seitenKlasse ⟨fun _ => false⟩ a = .pf :=
  seitenKlasse_nicht_vorhanden _ a rfl

/-- The walk's page fault delivers on the accepted vector 14. -/
theorem gangPf_vektor : fehlerVektor .pf = 14 :=
  vektor_pf_vierzehn

/-- The non-present error code: P clear, RSVD clear, access bits live. -/
theorem wit_code_loch :
    pfCodeBits ⟨false, false, true, false, false⟩ = 4 := by
  decide

/-- The protection error code of the RO write: P, W/R and U/S set. -/
theorem wit_code_ro :
    pfCodeBits ⟨true, true, true, false, false⟩ = 7 := by
  decide

/-! ## 9. Machine connection: adapter plug and extended steps.

  No walk admits a `HwMaschine` successor: faults have none by
  construction (the same reason `adapterFehler1123` refuses), and
  accessed/dirty updates touch the tables, which live outside
  `HwMaschine`. Walk behaviour lives in `HwSeitenSchritt` over
  machine-plus-tables, embedding `HwSchritt` exactly. -/

/-- The paging adapter: the refused default. No walk admits a machine
    successor state. -/
def adapterSeiten : HwAdapter SeitenAnfrage := verweigertAdapter _

/-- The paging adapter admits nothing. -/
theorem adapterSeiten_verweigert (m : HwMaschine) (c : Nat)
    (q : SeitenAnfrage) :
    adapterSeiten.schritt m c q = none := rfl

/-- Paging state: the coherent machine plus control state plus tables. -/
structure SeitenZustand where
  maschine : HwMaschine
  steuer : SeitenSteuerung
  tabellen : Nat → Wort

/-- Paging events: the old events, an admitted walk, a page fault. -/
inductive SeitenEreignis where
  | alt : HwEreignis → SeitenEreignis
  | gangOk : SeitenAnfrage → Nat → SeitenEreignis
  | gangPf : SeitenAnfrage → Nat → PfFehlerCode → SeitenEreignis
  deriving DecidableEq, Repr

/-- One paging step: the embedded old step (tables kept), an admitted
    walk (tables gain accessed/dirty, machine kept), or a page fault
    (a self-loop carrying the faulting address and error code).
    Large pages, SMEP/SMAP-armed control and noncanonical addresses
    admit NO step. -/
inductive HwSeitenSchritt :
    SeitenZustand → SeitenZustand → SeitenEreignis → Prop where
  | einbettet {s : SeitenZustand} {m' : HwMaschine} {e : HwEreignis}
      (h : HwSchritt s.maschine m' e) :
      HwSeitenSchritt s ⟨m', s.steuer, s.tabellen⟩ (.alt e)
  | gang {s : SeitenZustand} {q : SeitenAnfrage} {phys : Nat}
      {tab' : Nat → Wort}
      (h : (seitenGang s.steuer s.tabellen q).1 = .ok phys)
      (ht : (seitenGang s.steuer s.tabellen q).2 = tab') :
      HwSeitenSchritt s ⟨s.maschine, s.steuer, tab'⟩ (.gangOk q phys)
  | fehler {s : SeitenZustand} {q : SeitenAnfrage} {a : Nat}
      {c : PfFehlerCode}
      (h : (seitenGang s.steuer s.tabellen q).1 = .seitenFehler a c) :
      HwSeitenSchritt s s (.gangPf q a c)

/-- FORWARD embedding: every old step is a paging step. -/
theorem hwSeitenSchritt_einbettung_vor (s : SeitenZustand)
    (m' : HwMaschine) (e : HwEreignis)
    (h : HwSchritt s.maschine m' e) :
    HwSeitenSchritt s ⟨m', s.steuer, s.tabellen⟩ (.alt e) :=
  .einbettet h

/-- BACKWARD embedding, exact: an `.alt` step comes only from the old
    step with the same event. The inversion goes through a variable
    target so no cyclic state equation ever arises. -/
theorem hwSeitenSchritt_alt_invert (s t : SeitenZustand)
    (e : HwEreignis) (h : HwSeitenSchritt s t (.alt e)) :
    ∃ m', t.maschine = m' ∧ t.tabellen = s.tabellen ∧
      HwSchritt s.maschine m' e := by
  cases h with
  | einbettet hstep => exact ⟨_, rfl, rfl, hstep⟩

/-- An `.alt` step over the reached target is the old step. -/
theorem hwSeitenSchritt_einbettung_zurueck (s : SeitenZustand)
    (m' : HwMaschine) (e : HwEreignis)
    (h : HwSeitenSchritt s ⟨m', s.steuer, s.tabellen⟩ (.alt e)) :
    HwSchritt s.maschine m' e := by
  obtain ⟨m'', hm, _, hstep⟩ := hwSeitenSchritt_alt_invert s _ e h
  subst hm
  exact hstep

/-- A walk step carries its walk equation. -/
theorem gangOk_invert (s t : SeitenZustand) (q : SeitenAnfrage)
    (phys : Nat) (h : HwSeitenSchritt s t (.gangOk q phys)) :
    (seitenGang s.steuer s.tabellen q).1 = .ok phys := by
  cases h with
  | gang h ht => exact h

/-- A fault step carries its walk equation. -/
theorem gangPf_invert (s t : SeitenZustand) (q : SeitenAnfrage) (a : Nat)
    (c : PfFehlerCode) (h : HwSeitenSchritt s t (.gangPf q a c)) :
    (seitenGang s.steuer s.tabellen q).1 = .seitenFehler a c := by
  cases h with
  | fehler h => exact h

/-- A fault step never moves the state. -/
theorem hwSeitenSchritt_fehler_still (s s' : SeitenZustand)
    (q : SeitenAnfrage) (a : Nat) (c : PfFehlerCode)
    (h : HwSeitenSchritt s s' (.gangPf q a c)) : s' = s := by
  cases h
  rfl

/-- Every paging step preserves machine well-formedness: old steps by
    the accepted preservation, walk steps because the machine is kept,
    fault steps because the state never moves. -/
theorem hwSeitenSchritt_wf (s s' : SeitenZustand)
    (e : SeitenEreignis) (h : HwSeitenSchritt s s' e)
    (hwf : HwWf s.maschine) : HwWf s'.maschine := by
  cases h with
  | einbettet hstep => exact hwSchritt_wf _ _ _ hstep hwf
  | gang h => exact hwf
  | fehler h => exact hwf

/-- A refused large page admits no paging step at all. -/
theorem seitenGross_verweigert (s s' : SeitenZustand)
    (q : SeitenAnfrage) (a phys : Nat) (a' : Nat) (c : PfFehlerCode)
    (hg : (seitenGang s.steuer s.tabellen q).1 = .grossVerweigert a) :
    ¬ HwSeitenSchritt s s' (.gangOk q phys) ∧
      ¬ HwSeitenSchritt s s' (.gangPf q a' c) := by
  refine ⟨?_, ?_⟩
  · intro hstep
    have hok := gangOk_invert s s' q phys hstep
    rw [hg] at hok
    cases hok
  · intro hstep
    have hpf := gangPf_invert s s' q a' c hstep
    rw [hg] at hpf
    cases hpf

/-- An armed SMEP/SMAP configuration admits no paging step at all. -/
theorem seitenSteuer_verweigert (s s' : SeitenZustand)
    (q : SeitenAnfrage) (phys : Nat) (a' : Nat) (c : PfFehlerCode)
    (hg : (seitenGang s.steuer s.tabellen q).1 = .steuerVerweigert) :
    ¬ HwSeitenSchritt s s' (.gangOk q phys) ∧
      ¬ HwSeitenSchritt s s' (.gangPf q a' c) := by
  refine ⟨?_, ?_⟩
  · intro hstep
    have hok := gangOk_invert s s' q phys hstep
    rw [hg] at hok
    cases hok
  · intro hstep
    have hpf := gangPf_invert s s' q a' c hstep
    rw [hg] at hpf
    cases hpf

/-- A noncanonical address admits no paging step: the #GP belongs to
    the address stage, which already owns it (`adressKandidat`). -/
theorem seitenGp_verweigert (s s' : SeitenZustand)
    (q : SeitenAnfrage) (a phys : Nat) (a' : Nat) (c : PfFehlerCode)
    (hg : (seitenGang s.steuer s.tabellen q).1 = .gpFehler a) :
    ¬ HwSeitenSchritt s s' (.gangOk q phys) ∧
      ¬ HwSeitenSchritt s s' (.gangPf q a' c) := by
  refine ⟨?_, ?_⟩
  · intro hstep
    have hok := gangOk_invert s s' q phys hstep
    rw [hg] at hok
    cases hok
  · intro hstep
    have hpf := gangPf_invert s s' q a' c hstep
    rw [hg] at hpf
    cases hpf

/-! ## 10. Joint witness: two mappings, one page, two cores.

  The paging facts (both mappings land on frame 32, the RO write
  faults with W/R set) join the accepted two-core TSO run: owner-only
  forwarding, a drain that changes actual shared memory, and the flat
  agreement on the shared page. -/

/-- JOINT WITNESS: well-formedness, both mappings onto one page, the
    RO write fault with its error class, owner-only forwarding, the
    memory-changing drain, and flat agreement. Non-degenerate: two
    mappings with different permissions, two cores, a real memory
    change. -/
theorem hwSeiten_zeuge :
    HwWf hwWitStart ∧
      (seitenGang witSeitenSteuer witTab ⟨4096, false, true, false⟩).1 =
        .ok 131072 ∧
      (seitenGang witSeitenSteuer witTab ⟨8192, false, true, false⟩).1 =
        .ok 131072 ∧
      (seitenGang witSeitenSteuer witTab ⟨8192, true, true, false⟩).1 =
        .seitenFehler 8192 ⟨true, true, true, false, false⟩ ∧
      hwWitLoadEigen = some (some (BitVec.ofNat 8 42)) ∧
      hwWitLoadFremd = some (some (BitVec.ofNat 8 0)) ∧
      hwWitNachFlush = some (some (BitVec.ofNat 8 42)) ∧
      witFlach.lesbar (BitVec.ofNat 64 131072) = true := by
  exact ⟨hwWitStart_wf, wit_lese_rw_ok, wit_lese_ro_ok,
    wit_schreibe_ro_pf, hwWit_weiterleitung, hwWit_fremd_alt,
    hwWit_spülung_aendert_speicher, wit_flach_liest⟩

/- CUTS:
   Proved here (all over the REUSED coherent machine and the REUSED
   accepted fault vocabulary -- no new machine, no new decoder row,
   no silicon re-verification):
   - entry word layout `wortBit`/`eintragDekodieren`/`eintragKodieren`
     with per-bit round-trips (P/RW/US/PS/A/D unconditionally,
     XD/frame below the 40-bit field width) (§1);
   - request/control vocabulary, the 5-bit #PF error code
     `PfFehlerCode`/`pfCodeBits`, the walk outcome `GangErgebnis`,
     level indices, and the canonical check with its bridge to the
     accepted `istKanonisch` plus #GP agreement with `adrKlasse` (§2);
   - the four-level walk `gangEbenen` over decoded entries: SMEP/SMAP
     refusal, #GP, present/RSVD/large-page rules at every level, the
     WP-aware leaf check `blattPruefung`, and the checked AND/OR
     rights combination `gangRechte` (§3);
   - table memory `seitenTabEintrag`, accessed/dirty word updates with
     preservation of every permission bit and the frame, and the set
     facts (§4);
   - the write-back `tabAD` (untouched entries keep their word; only
     touched entries and the leaf can change), the full walk
     `seitenGang`, stillness of every non-success walk, and control-bit
     determinism `seitenGang_steuer_gleich` (the walk never consults
     accessed/dirty) (§5);
   - witness: two mappings (RW + RO) of linear pages 1 and 2 onto one
     physical frame 32, the RO write fault with W/R set, the WP
     supervisor fault, the non-present hole, the noncanonical #GP,
     accessed/dirty set on exactly the touched entries (§6);
   - flat bridge: the OS obligation `FlachStimmt` with its two checked
     directions, inhabited by the all-permissive memory (never
     vacuous), and the witness flat agreement on the shared page (§7);
   - fault consensus: walk faults ARE `#PF`, walk #GP IS `#GP`,
     refusals carry no class, non-present agrees with `seitenKlasse`
     on a dark page state, vector 14, pinned error-code values (§8);
   - machine connection: the refusing adapter `adapterSeiten`, the
     extended step `HwSeitenSchritt` with the EXACT two-way embedding
     of `HwSchritt`, fault steps that never move state, wf
     preservation, and planted refusals for large pages, armed
     SMEP/SMAP and noncanonical addresses (§9);
   - joint witness: two mappings with different permissions of one
     page beside the accepted two-core memory-changing TSO run (§10).
   NOT proved here, and not claimed:
   - No hardware verification: entry bit positions (P/RW/US/A/D/PS/XD
     per Vol 3A §4.5 Table 4-18), index shifts, the error-code bit
     meanings (Vol 3A §4.7 Table 4-7) and the 48-bit canonical width
     are NAMED silicon assumptions. The supplied clone references are
     the Vol 2 instruction-set extract (which confirms #PF carries a
     fault-code error code); no Vol 3A paging table was supplied, so
     bit-level correspondence is assumed, never claimed.
   - Large pages (2 MiB/1 GiB) are REFUSED (`grossVerweigert`), never
     mapped; their fault-vs-refusal status and PAT/memory-type
     behaviour stay open.
   - CR4.SMEP/SMAP-armed configurations are REFUSED wholesale
     (`steuerVerweigert`); per-access SMEP/SMAP/AC-flag semantics
     (including the supervisor-fetches-user and AC-gated SMAP rules)
     are not modelled. CR0.WP IS modelled (supervisor writes).
   - No TLB (addressed by a separate lane): no translation caching,
     no INVLPG/MOV-to-CR3 invalidation, no TLB-coherence claim.
   - No fault DELIVERY (IDT/stack/handler/error-code push stays with
     lane 672): the fault outcome carries address plus code only.
   - `FlachStimmt` for a REAL OS is user logic (the OS establishes it
     when installing tables); only the all-permissive instance and the
     witness agreement are proved here.
   - No per-access target-to-W/GX simulation, no timing, no source
     stop-class transfer.
-/

#print axioms wortBit
#print axioms eintragDekodieren
#print axioms eintragKodieren
#print axioms kodieren_vorhanden
#print axioms kodieren_schreibbar
#print axioms kodieren_benutzer
#print axioms kodieren_gross
#print axioms kodieren_zugegriffen
#print axioms kodieren_schmutzig
#print axioms kodieren_noExec
#print axioms kodieren_rahmen
#print axioms pfCodeBits
#print axioms istKanonischNat
#print axioms kanonischNat_bruecke
#print axioms kanonischNat_null
#print axioms nichtkanonischNat_bit47
#print axioms gangGp_adrKlasse
#print axioms blattPruefung
#print axioms gangRechte
#print axioms gangEbenen
#print axioms gangEbenen_smep
#print axioms gangEbenen_smap
#print axioms gangEbenen_gp
#print axioms gangEbenen_nichtvorhanden3
#print axioms gangEbenen_nichtvorhanden0
#print axioms gangEbenen_gross2
#print axioms gangEbenen_gross1
#print axioms gangEbenen_rechte
#print axioms blatt_wp_schuetzt
#print axioms blatt_wp_offen_erlaubt
#print axioms blatt_benutzer_schreibschutz
#print axioms blatt_abruf_xd
#print axioms blatt_lese_ok
#print axioms gangEbenen_kongr
#print axioms seitenTabEintrag
#print axioms wortZugriff
#print axioms wortSchmutzig
#print axioms wortZugriff_vorhanden
#print axioms wortZugriff_schreibbar
#print axioms wortZugriff_benutzer
#print axioms wortZugriff_gross
#print axioms wortZugriff_noExec
#print axioms wortZugriff_rahmen
#print axioms wortZugriff_setzt
#print axioms wortSchmutzig_vorhanden
#print axioms wortSchmutzig_schreibbar
#print axioms wortSchmutzig_benutzer
#print axioms wortSchmutzig_gross
#print axioms wortSchmutzig_noExec
#print axioms wortSchmutzig_rahmen
#print axioms wortSchmutzig_setzt
#print axioms tabAD
#print axioms tabAD_unberuehrt_keinBlatt
#print axioms tabAD_unberuehrt_blatt
#print axioms tabAD_nur_beruehrt
#print axioms seitenGangTab_nichtOk
#print axioms seitenGang
#print axioms seitenGang_fst
#print axioms seitenGang_nichtOk_still
#print axioms seitenGang_steuer_gleich
#print axioms witTab
#print axioms witSeitenSteuer
#print axioms wit_lese_rw_ok
#print axioms wit_lese_ro_ok
#print axioms wit_gleiches_blatt
#print axioms wit_schreibe_rw_ok
#print axioms wit_schreibe_ro_pf
#print axioms wit_schreibe_ro_wp
#print axioms wit_lese_loch_pf
#print axioms wit_nichtkanonisch_gp
#print axioms wit_zugriff_gesetzt
#print axioms wit_schmutzig_gesetzt
#print axioms wit_unberuehrt_still
#print axioms witFlach
#print axioms wit_flach_liest
#print axioms wit_flach_schreibt
#print axioms FlachStimmt
#print axioms gangOk_flach_schreibbar
#print axioms gangOk_flach_lesbar
#print axioms allWahrSpeicher
#print axioms flachStimmt_allwahr
#print axioms gangKlasse
#print axioms gangKlasse_pf
#print axioms gangKlasse_gp
#print axioms gangKlasse_steuer_keine
#print axioms gangKlasse_gross_keine
#print axioms gangPf_seitenKlasse_eins
#print axioms gangPf_vektor
#print axioms wit_code_loch
#print axioms wit_code_ro
#print axioms adapterSeiten
#print axioms adapterSeiten_verweigert
#print axioms HwSeitenSchritt
#print axioms hwSeitenSchritt_einbettung_vor
#print axioms hwSeitenSchritt_alt_invert
#print axioms hwSeitenSchritt_einbettung_zurueck
#print axioms gangOk_invert
#print axioms gangPf_invert
#print axioms hwSeitenSchritt_fehler_still
#print axioms hwSeitenSchritt_wf
#print axioms seitenGross_verweigert
#print axioms seitenSteuer_verweigert
#print axioms seitenGp_verweigert
#print axioms hwSeiten_zeuge

end Gabbro.Grammatik.X86
