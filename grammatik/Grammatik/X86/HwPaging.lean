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
def tabEintrag (tab : Nat → Wort) (rahmen idx : Nat) : SeitenEintrag :=
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

/- CUTS (skeleton):
   NOT proved here, and not claimed:
   - Everything in the lane task: walk, permission combination, WP,
     accessed/dirty rules, #PF error code, canonical check, flat bridge,
     adapter/extended step, witness. This skeleton only fixes the
     entry vocabulary.
-/

end Gabbro.Grammatik.X86
