/-
  File:      Grammatik/X86/HwPagingLarge.lean
  Subject:   Large pages (2 MiB, 1 GiB) and per-access SMEP/SMAP.

  Lane 1297: follow-up of lane 1283 (`HwPaging.lean`), whose CUTS state
  no large-page mapping and no per-access SMEP/SMAP. This file LIFTS
  the accepted 4 KiB walk (`gangEbenen`, `blattPruefung`, `seitenGang`)
  unchanged: new functions equal it where it applies (proved), large
  leaves add reserved-bit/alignment rules, SMEP/SMAP+EFLAGS.AC is a
  decided per-access check, and the machine embeds `HwSchritt` exactly.
-/
import Grammatik.X86.HwPaging

namespace Gabbro.Grammatik.X86

/-- Extended control: accepted control plus the EFLAGS.AC flag. -/
structure GrossSteuerung where
  basis : SeitenSteuerung
  ac : Bool
  deriving DecidableEq, Repr

/-! ## 1. Per-access SMEP/SMAP with EFLAGS.AC.

  Named architecture rule (decided check, no silicon re-verification):
  SMEP faults a supervisor fetch from a user page; SMAP faults a
  supervisor data access to a user page while AC is clear. Fetches are
  never subject to SMAP; user-mode accesses never fault here. -/

/-- SMEP violation: supervisor fetch from a user page. -/
def smepVerletzt (st : SeitenSteuerung) (q : SeitenAnfrage)
    (effUS : Bool) : Bool :=
  st.smep && q.abruf && !q.benutzer && effUS

/-- SMAP violation: supervisor data access to a user page with AC clear. -/
def smapVerletzt (st : SeitenSteuerung) (ac : Bool) (q : SeitenAnfrage)
    (effUS : Bool) : Bool :=
  st.smap && !q.abruf && !q.benutzer && effUS && !ac

/-- With SMEP off there is never a SMEP violation. -/
theorem smepVerletzt_off (st : SeitenSteuerung) (q : SeitenAnfrage)
    (effUS : Bool) (h : st.smep = false) :
    smepVerletzt st q effUS = false := by
  simp [smepVerletzt, h]

/-- With SMAP off there is never a SMAP violation. -/
theorem smapVerletzt_off (st : SeitenSteuerung) (ac : Bool)
    (q : SeitenAnfrage) (effUS : Bool) (h : st.smap = false) :
    smapVerletzt st ac q effUS = false := by
  simp [smapVerletzt, h]

/-- A user access never violates SMEP. -/
theorem smepVerletzt_benutzer (st : SeitenSteuerung) (q : SeitenAnfrage)
    (effUS : Bool) (h : q.benutzer = true) :
    smepVerletzt st q effUS = false := by
  simp [smepVerletzt, h]

/-- A user access never violates SMAP. -/
theorem smapVerletzt_benutzer (st : SeitenSteuerung) (ac : Bool)
    (q : SeitenAnfrage) (effUS : Bool) (h : q.benutzer = true) :
    smapVerletzt st ac q effUS = false := by
  simp [smapVerletzt, h]

/-- A fetch never violates SMAP. -/
theorem smapVerletzt_abruf (st : SeitenSteuerung) (ac : Bool)
    (q : SeitenAnfrage) (effUS : Bool) (h : q.abruf = true) :
    smapVerletzt st ac q effUS = false := by
  simp [smapVerletzt, h]

/-- With AC set there is never a SMAP violation. -/
theorem smapVerletzt_ac (st : SeitenSteuerung) (q : SeitenAnfrage)
    (effUS : Bool) :
    smapVerletzt st true q effUS = false := by
  simp [smapVerletzt]

/-- Supervisor fetch from a user page violates armed SMEP. -/
theorem smepVerletzt_beispiel :
    smepVerletzt ⟨0, false, true, false, true⟩
      ⟨0, false, false, true⟩ true = true := by
  decide

/-- Supervisor data read of a user page violates armed SMAP at AC clear. -/
theorem smapVerletzt_beispiel :
    smapVerletzt ⟨0, false, false, true, true⟩ false
      ⟨0, false, false, false⟩ true = true := by
  decide

/-! ## 2. Large-page alignment and the shared leaf check.

  Named architecture rule: a 2 MiB leaf frame names 2 MiB, so its low
  9 frame bits are reserved (must be zero); a 1 GiB leaf frame names
  1 GiB, so its low 18 frame bits are reserved. A nonzero reserved
  field faults with RSVD set (the same error-code bit the 4 KiB walk
  uses for its reserved-XD rule). Bit positions are NAMED assumptions
  (see CUTS), never checked provenance. -/

/-- 2 MiB alignment: the frame is a multiple of 512 4 KiB pages. -/
def grossAusgerichtet2M (rahmen : Nat) : Bool :=
  decide (rahmen % 512 = 0)

/-- 1 GiB alignment: the frame is a multiple of 512 * 512 pages. -/
def grossAusgerichtet1G (rahmen : Nat) : Bool :=
  decide (rahmen % (512 * 512) = 0)

/-- 21-bit offset inside a 2 MiB page. -/
def grossOffset2M (lin : Nat) : Nat := lin % 2 ^ 21

/-- 30-bit offset inside a 1 GiB page. -/
def grossOffset1G (lin : Nat) : Nat := lin % 2 ^ 30

/-- Frame 512 is 2 MiB-aligned. -/
theorem ausgerichtet2M_beispiel : grossAusgerichtet2M 512 = true := by
  decide

/-- Frame 513 is not 2 MiB-aligned. -/
theorem ausgerichtet2M_gegenbeispiel :
    grossAusgerichtet2M 513 = false := by
  decide

/-- Frame 512 * 512 is 1 GiB-aligned. -/
theorem ausgerichtet1G_beispiel :
    grossAusgerichtet1G (512 * 512) = true := by
  decide

/-- Frame 512 alone is not 1 GiB-aligned. -/
theorem ausgerichtet1G_gegenbeispiel :
    grossAusgerichtet1G 512 = false := by
  decide

/-- Shared large leaf check: SMEP/SMAP first, then the ACCEPTED leaf
    check, with the caller-supplied offset replacing the 4 KiB one on
    success. The old evaluator is lifted, never redefined. -/
def grossBlatt (st : SeitenSteuerung) (ac : Bool) (q : SeitenAnfrage)
    (effRW effUS effXD : Bool) (rahmen offset : Nat) : GangErgebnis :=
  if smepVerletzt st q effUS then
    .seitenFehler q.linear ⟨true, q.schreiben, q.benutzer, false, q.abruf⟩
  else if smapVerletzt st ac q effUS then
    .seitenFehler q.linear ⟨true, q.schreiben, q.benutzer, false, q.abruf⟩
  else
    match blattPruefung st q effRW effUS effXD rahmen with
    | .ok _ => .ok (rahmen * 4096 + offset)
    | e => e

/-- Every success of the accepted leaf check names the 4 KiB frame
    address: the payload is forced by the branches. -/
theorem blatt_ok_payload (st : SeitenSteuerung) (q : SeitenAnfrage)
    (effRW effUS effXD : Bool) (rahmen phys : Nat)
    (h : blattPruefung st q effRW effUS effXD rahmen = .ok phys) :
    phys = rahmen * 4096 + gangOffset q.linear := by
  cases q with
  | mk lin sch ben abr =>
    simp only [blattPruefung] at h
    split at h
    next hcond =>
      split at h
      next hcond2 => exact nomatch h
      next hcond2 =>
        split at h
        next hcond3 => exact nomatch h
        next hcond3 => cases h; rfl
    next hcond =>
      split at h
      next hcond2 => exact nomatch h
      next hcond2 =>
        split at h
        next hcond3 =>
          split at h
          next hcond4 => exact nomatch h
          next hcond4 => cases h; rfl
        next hcond3 => cases h; rfl

/-- Without armed SMEP/SMAP and with the 4 KiB offset, the shared
    check IS the accepted leaf check. -/
theorem grossBlatt_ohne_schutz (st : SeitenSteuerung) (ac : Bool)
    (q : SeitenAnfrage) (effRW effUS effXD : Bool) (rahmen : Nat)
    (h1 : st.smep = false) (h2 : st.smap = false) :
    grossBlatt st ac q effRW effUS effXD rahmen (gangOffset q.linear) =
      blattPruefung st q effRW effUS effXD rahmen := by
  cases q with
  | mk lin sch ben abr =>
    have hs1 : smepVerletzt st ⟨lin, sch, ben, abr⟩ effUS = false :=
      smepVerletzt_off st _ effUS h1
    have hs2 : smapVerletzt st ac ⟨lin, sch, ben, abr⟩ effUS = false :=
      smapVerletzt_off st ac _ effUS h2
    simp only [grossBlatt, hs1, hs2, Bool.false_eq_true, reduceIte,
      gangOffset]
    cases h : blattPruefung st ⟨lin, sch, ben, abr⟩ effRW effUS effXD
        rahmen with
    | ok phys =>
      have hp := blatt_ok_payload st ⟨lin, sch, ben, abr⟩ effRW effUS
        effXD rahmen phys h
      simp [hp, gangOffset]
    | seitenFehler a c => simp
    | gpFehler a => simp
    | grossVerweigert a => simp
    | steuerVerweigert => simp

/-! ## 3. The large-page walks.

  Each new function maps its large leaf (with the reserved-bit and
  alignment rules of §2) and DEFERS to the accepted 4 KiB walk
  `gangEbenen` wherever its leaf does not apply -- proved below. The
  4 KiB path keeps the per-access SMEP/SMAP check through
  `grossBlatt`, so armed control is enforced at every leaf. -/

/-- 2 MiB walk: PD with PS maps; a PS at PDPT stays refused (the 1 GiB
    function's job); without a PD large page the walk is the accepted
    4 KiB walk with the per-access check at the leaf. -/
def gangGross2M (gst : GrossSteuerung) (q : SeitenAnfrage)
    (e3 e2 e1 e0 : SeitenEintrag) : GangErgebnis :=
  if !istKanonischNat q.linear then .gpFehler q.linear
  else if !e3.vorhanden then
    .seitenFehler q.linear ⟨false, q.schreiben, q.benutzer, false, q.abruf⟩
  else if !gst.basis.nxe && e3.noExec then
    .seitenFehler q.linear ⟨true, q.schreiben, q.benutzer, true, q.abruf⟩
  else if e3.gross then
    .seitenFehler q.linear ⟨true, q.schreiben, q.benutzer, true, q.abruf⟩
  else if !e2.vorhanden then
    .seitenFehler q.linear ⟨false, q.schreiben, q.benutzer, false, q.abruf⟩
  else if !gst.basis.nxe && e2.noExec then
    .seitenFehler q.linear ⟨true, q.schreiben, q.benutzer, true, q.abruf⟩
  else if e2.gross then .grossVerweigert q.linear
  else if !e1.vorhanden then
    .seitenFehler q.linear ⟨false, q.schreiben, q.benutzer, false, q.abruf⟩
  else if !gst.basis.nxe && e1.noExec then
    .seitenFehler q.linear ⟨true, q.schreiben, q.benutzer, true, q.abruf⟩
  else if e1.gross then
    if !grossAusgerichtet2M e1.rahmen then
      .seitenFehler q.linear
        ⟨true, q.schreiben, q.benutzer, true, q.abruf⟩
    else grossBlatt gst.basis gst.ac q
      (e3.schreibbar && e2.schreibbar && e1.schreibbar)
      (e3.benutzer && e2.benutzer && e1.benutzer)
      (e3.noExec || e2.noExec || e1.noExec)
      e1.rahmen (grossOffset2M q.linear)
  else if !e0.vorhanden then
    .seitenFehler q.linear ⟨false, q.schreiben, q.benutzer, false, q.abruf⟩
  else if !gst.basis.nxe && e0.noExec then
    .seitenFehler q.linear ⟨true, q.schreiben, q.benutzer, true, q.abruf⟩
  else if e0.gross then
    .seitenFehler q.linear ⟨true, q.schreiben, q.benutzer, true, q.abruf⟩
  else grossBlatt gst.basis gst.ac q
    (e3.schreibbar && e2.schreibbar && e1.schreibbar && e0.schreibbar)
    (e3.benutzer && e2.benutzer && e1.benutzer && e0.benutzer)
    (e3.noExec || e2.noExec || e1.noExec || e0.noExec)
    e0.rahmen (gangOffset q.linear)

/-- 1 GiB walk: PDPT with PS maps; a PS at PD stays refused (the 2 MiB
    function's job); without a PDPT large page the walk is the accepted
    4 KiB walk with the per-access check at the leaf. -/
def gangGross1G (gst : GrossSteuerung) (q : SeitenAnfrage)
    (e3 e2 e1 e0 : SeitenEintrag) : GangErgebnis :=
  if !istKanonischNat q.linear then .gpFehler q.linear
  else if !e3.vorhanden then
    .seitenFehler q.linear ⟨false, q.schreiben, q.benutzer, false, q.abruf⟩
  else if !gst.basis.nxe && e3.noExec then
    .seitenFehler q.linear ⟨true, q.schreiben, q.benutzer, true, q.abruf⟩
  else if e3.gross then
    .seitenFehler q.linear ⟨true, q.schreiben, q.benutzer, true, q.abruf⟩
  else if !e2.vorhanden then
    .seitenFehler q.linear ⟨false, q.schreiben, q.benutzer, false, q.abruf⟩
  else if !gst.basis.nxe && e2.noExec then
    .seitenFehler q.linear ⟨true, q.schreiben, q.benutzer, true, q.abruf⟩
  else if e2.gross then
    if !grossAusgerichtet1G e2.rahmen then
      .seitenFehler q.linear
        ⟨true, q.schreiben, q.benutzer, true, q.abruf⟩
    else grossBlatt gst.basis gst.ac q
      (e3.schreibbar && e2.schreibbar)
      (e3.benutzer && e2.benutzer)
      (e3.noExec || e2.noExec)
      e2.rahmen (grossOffset1G q.linear)
  else if !e1.vorhanden then
    .seitenFehler q.linear ⟨false, q.schreiben, q.benutzer, false, q.abruf⟩
  else if !gst.basis.nxe && e1.noExec then
    .seitenFehler q.linear ⟨true, q.schreiben, q.benutzer, true, q.abruf⟩
  else if e1.gross then .grossVerweigert q.linear
  else if !e0.vorhanden then
    .seitenFehler q.linear ⟨false, q.schreiben, q.benutzer, false, q.abruf⟩
  else if !gst.basis.nxe && e0.noExec then
    .seitenFehler q.linear ⟨true, q.schreiben, q.benutzer, true, q.abruf⟩
  else if e0.gross then
    .seitenFehler q.linear ⟨true, q.schreiben, q.benutzer, true, q.abruf⟩
  else grossBlatt gst.basis gst.ac q
    (e3.schreibbar && e2.schreibbar && e1.schreibbar && e0.schreibbar)
    (e3.benutzer && e2.benutzer && e1.benutzer && e0.benutzer)
    (e3.noExec || e2.noExec || e1.noExec || e0.noExec)
    e0.rahmen (gangOffset q.linear)

/-- Combined walk: a PDPT large page maps through the 1 GiB walk,
    otherwise the 2 MiB walk decides (mapping a PD large page, else
    the 4 KiB walk). The two functions agree on every earlier check,
    so the priority is exact. -/
def gangGross (gst : GrossSteuerung) (q : SeitenAnfrage)
    (e3 e2 e1 e0 : SeitenEintrag) : GangErgebnis :=
  if e2.gross then gangGross1G gst q e3 e2 e1 e0
  else gangGross2M gst q e3 e2 e1 e0

/-- A PDPT large page walks through the 1 GiB function. -/
theorem gangGross_bei_1G (gst : GrossSteuerung) (q : SeitenAnfrage)
    (e3 e2 e1 e0 : SeitenEintrag) (h : e2.gross = true) :
    gangGross gst q e3 e2 e1 e0 = gangGross1G gst q e3 e2 e1 e0 := by
  simp [gangGross, h]

/-- Without a PDPT large page the combined walk is the 2 MiB walk. -/
theorem gangGross_bei_2M (gst : GrossSteuerung) (q : SeitenAnfrage)
    (e3 e2 e1 e0 : SeitenEintrag) (h : e2.gross = false) :
    gangGross gst q e3 e2 e1 e0 = gangGross2M gst q e3 e2 e1 e0 := by
  simp [gangGross, h]

/-- Without a PD large page and with disarmed SMEP/SMAP, the 2 MiB
    walk IS the accepted 4 KiB walk. -/
theorem gangGross2M_gleich (gst : GrossSteuerung) (q : SeitenAnfrage)
    (e3 e2 e1 e0 : SeitenEintrag)
    (h1 : gst.basis.smep = false) (h2 : gst.basis.smap = false)
    (hg1 : e1.gross = false) :
    gangGross2M gst q e3 e2 e1 e0 =
      gangEbenen gst.basis q e3 e2 e1 e0 := by
  simp [gangGross2M, gangEbenen, h1, h2, hg1, grossBlatt_ohne_schutz]

/-- Without a PDPT large page and with disarmed SMEP/SMAP, the 1 GiB
    walk IS the accepted 4 KiB walk (a PD large page refuses on both
    sides). -/
theorem gangGross1G_gleich (gst : GrossSteuerung) (q : SeitenAnfrage)
    (e3 e2 e1 e0 : SeitenEintrag)
    (h1 : gst.basis.smep = false) (h2 : gst.basis.smap = false)
    (hg2 : e2.gross = false) :
    gangGross1G gst q e3 e2 e1 e0 =
      gangEbenen gst.basis q e3 e2 e1 e0 := by
  simp [gangGross1G, gangEbenen, h1, h2, hg2, grossBlatt_ohne_schutz]

/-- Without any large page and with disarmed SMEP/SMAP, the combined
    walk IS the accepted 4 KiB walk. -/
theorem gangGross_gleich (gst : GrossSteuerung) (q : SeitenAnfrage)
    (e3 e2 e1 e0 : SeitenEintrag)
    (h1 : gst.basis.smep = false) (h2 : gst.basis.smap = false)
    (hg2 : e2.gross = false) (hg1 : e1.gross = false) :
    gangGross gst q e3 e2 e1 e0 =
      gangEbenen gst.basis q e3 e2 e1 e0 := by
  rw [gangGross_bei_2M gst q e3 e2 e1 e0 hg2]
  exact gangGross2M_gleich gst q e3 e2 e1 e0 h1 h2 hg1

/-! ## 4. Fault behaviour of the new causes.

  A misaligned large leaf faults with RSVD set (the same error-code
  bit the 4 KiB walk uses for its reserved rules); a SMEP/SMAP
  violation faults as protection (P set, RSVD clear) with the access
  bits live. With AC set, SMAP never fires: the check falls through
  to the accepted leaf outcome. -/

/-- A misaligned 2 MiB leaf faults with RSVD set. -/
theorem gangGross2M_fehlaligniert (gst : GrossSteuerung)
    (q : SeitenAnfrage) (e3 e2 e1 e0 : SeitenEintrag)
    (hk : istKanonischNat q.linear = true)
    (h3 : e3.vorhanden = true) (hn3 : e3.noExec = false)
    (hg3 : e3.gross = false)
    (h2v : e2.vorhanden = true) (hn2 : e2.noExec = false)
    (hg2 : e2.gross = false)
    (h1v : e1.vorhanden = true) (hn1 : e1.noExec = false)
    (hnxe : gst.basis.nxe = true)
    (hg1 : e1.gross = true)
    (hm : grossAusgerichtet2M e1.rahmen = false) :
    gangGross2M gst q e3 e2 e1 e0 =
      .seitenFehler q.linear
        ⟨true, q.schreiben, q.benutzer, true, q.abruf⟩ := by
  simp [gangGross2M, hk, h3, hn3, hg3, h2v, hn2, hg2, h1v, hn1, hnxe,
    hg1, hm]

/-- A misaligned 1 GiB leaf faults with RSVD set. -/
theorem gangGross1G_fehlaligniert (gst : GrossSteuerung)
    (q : SeitenAnfrage) (e3 e2 e1 e0 : SeitenEintrag)
    (hk : istKanonischNat q.linear = true)
    (h3 : e3.vorhanden = true) (hn3 : e3.noExec = false)
    (hg3 : e3.gross = false)
    (h2v : e2.vorhanden = true) (hn2 : e2.noExec = false)
    (hnxe : gst.basis.nxe = true)
    (hg2 : e2.gross = true)
    (hm : grossAusgerichtet1G e2.rahmen = false) :
    gangGross1G gst q e3 e2 e1 e0 =
      .seitenFehler q.linear
        ⟨true, q.schreiben, q.benutzer, true, q.abruf⟩ := by
  simp [gangGross1G, hk, h3, hn3, hg3, h2v, hn2, hnxe, hg2, hm]

/-- Supervisor fetch from a user 2 MiB page faults under armed SMEP. -/
theorem gangGross2M_smep (gst : GrossSteuerung) (q : SeitenAnfrage)
    (e3 e2 e1 e0 : SeitenEintrag)
    (hk : istKanonischNat q.linear = true)
    (h3 : e3.vorhanden = true) (hn3 : e3.noExec = false)
    (hg3 : e3.gross = false)
    (h2v : e2.vorhanden = true) (hn2 : e2.noExec = false)
    (hg2 : e2.gross = false)
    (h1v : e1.vorhanden = true) (hn1 : e1.noExec = false)
    (hnxe : gst.basis.nxe = true)
    (hg1 : e1.gross = true)
    (hal : grossAusgerichtet2M e1.rahmen = true)
    (hsmep : gst.basis.smep = true)
    (hab : q.abruf = true) (hben : q.benutzer = false)
    (hus : (e3.benutzer && e2.benutzer && e1.benutzer) = true) :
    gangGross2M gst q e3 e2 e1 e0 =
      .seitenFehler q.linear
        ⟨true, q.schreiben, q.benutzer, false, true⟩ := by
  simp [gangGross2M, grossBlatt, smepVerletzt, hk, h3, hn3, hg3, h2v,
    hn2, hg2, h1v, hn1, hnxe, hg1, hal, hsmep, hab, hben, hus]

/-- Supervisor data access to a user 2 MiB page faults under armed
    SMAP while AC is clear (fetches never reach SMAP). -/
theorem gangGross2M_smap (gst : GrossSteuerung) (q : SeitenAnfrage)
    (e3 e2 e1 e0 : SeitenEintrag)
    (hk : istKanonischNat q.linear = true)
    (h3 : e3.vorhanden = true) (hn3 : e3.noExec = false)
    (hg3 : e3.gross = false)
    (h2v : e2.vorhanden = true) (hn2 : e2.noExec = false)
    (hg2 : e2.gross = false)
    (h1v : e1.vorhanden = true) (hn1 : e1.noExec = false)
    (hnxe : gst.basis.nxe = true)
    (hg1 : e1.gross = true)
    (hal : grossAusgerichtet2M e1.rahmen = true)
    (hsmap : gst.basis.smap = true) (hac : gst.ac = false)
    (hab : q.abruf = false) (hben : q.benutzer = false)
    (hus : (e3.benutzer && e2.benutzer && e1.benutzer) = true) :
    gangGross2M gst q e3 e2 e1 e0 =
      .seitenFehler q.linear
        ⟨true, q.schreiben, q.benutzer, false, false⟩ := by
  simp [gangGross2M, grossBlatt, smepVerletzt, smapVerletzt, hk, h3,
    hn3, hg3, h2v, hn2, hg2, h1v, hn1, hnxe, hg1, hal, hsmap, hac,
    hab, hben, hus]

/-- With AC set, SMAP never fires: the check falls through to the
    accepted leaf outcome with the caller offset. -/
theorem grossBlatt_ac_gleich (st : SeitenSteuerung) (q : SeitenAnfrage)
    (effRW effUS effXD : Bool) (rahmen offset : Nat)
    (hsmep : st.smep = false) :
    grossBlatt st true q effRW effUS effXD rahmen offset =
      match blattPruefung st q effRW effUS effXD rahmen with
      | .ok _ => .ok (rahmen * 4096 + offset)
      | e => e := by
  have hs1 : ∀ (u : Bool), smepVerletzt st q u = false := by
    intro u
    exact smepVerletzt_off st q u hsmep
  simp [grossBlatt, hs1, smapVerletzt_ac]

/-- Error code of a misaligned user read: P, U/S and RSVD set. -/
theorem code_fehlaligniert_lese :
    pfCodeBits ⟨true, false, true, true, false⟩ = 13 := by
  decide

/-- Error code of a SMEP supervisor fetch: P and I/D set. -/
theorem code_smep_abruf :
    pfCodeBits ⟨true, false, false, false, true⟩ = 17 := by
  decide

/-- Error code of a SMAP supervisor write: P and W/R set. -/
theorem code_smap_schreib :
    pfCodeBits ⟨true, true, false, false, false⟩ = 3 := by
  decide

/-! ## 5. The full walk over table memory with write-back.

  The four entries are looked up exactly as in the accepted
  `seitenGang`; the outcome runs the combined walk `gangGross`. On
  success only the touched entries gain accessed (the leaf gains
  dirty for writes): two entries for a 1 GiB page, three for a
  2 MiB page, four otherwise. Every other outcome leaves the tables
  unchanged, through the accepted `seitenGangTab`. -/

/-- Full walk: the accepted lookups, the combined outcome, and the
    touched-only write-back. Written let-free so the lookup equations
    rewrite directly, as in `seitenGang`. -/
def seitenGangGross (gst : GrossSteuerung) (tab : Nat → Wort)
    (q : SeitenAnfrage) : GangErgebnis × (Nat → Wort) :=
  (gangGross gst q (seitenTabEintrag tab gst.basis.cr3 (gangIndexPML4 q.linear))
    (seitenTabEintrag tab
      (seitenTabEintrag tab gst.basis.cr3 (gangIndexPML4 q.linear)).rahmen
      (gangIndexPDPT q.linear))
    (seitenTabEintrag tab
      (seitenTabEintrag tab
        (seitenTabEintrag tab gst.basis.cr3 (gangIndexPML4 q.linear)).rahmen
        (gangIndexPDPT q.linear)).rahmen
      (gangIndexPD q.linear))
    (seitenTabEintrag tab
      (seitenTabEintrag tab
        (seitenTabEintrag tab
          (seitenTabEintrag tab gst.basis.cr3 (gangIndexPML4 q.linear)).rahmen
          (gangIndexPDPT q.linear)).rahmen
        (gangIndexPD q.linear)).rahmen
      (gangIndexPT q.linear)),
   seitenGangTab tab
    (if (seitenTabEintrag tab
        (seitenTabEintrag tab gst.basis.cr3 (gangIndexPML4 q.linear)).rahmen
        (gangIndexPDPT q.linear)).gross then
       [gst.basis.cr3 * 512 + gangIndexPML4 q.linear,
        (seitenTabEintrag tab gst.basis.cr3 (gangIndexPML4 q.linear)).rahmen *
          512 + gangIndexPDPT q.linear]
     else if (seitenTabEintrag tab
        (seitenTabEintrag tab
          (seitenTabEintrag tab gst.basis.cr3 (gangIndexPML4 q.linear)).rahmen
          (gangIndexPDPT q.linear)).rahmen
        (gangIndexPD q.linear)).gross then
       [gst.basis.cr3 * 512 + gangIndexPML4 q.linear,
        (seitenTabEintrag tab gst.basis.cr3 (gangIndexPML4 q.linear)).rahmen *
          512 + gangIndexPDPT q.linear,
        (seitenTabEintrag tab
          (seitenTabEintrag tab gst.basis.cr3 (gangIndexPML4 q.linear)).rahmen
          (gangIndexPDPT q.linear)).rahmen * 512 + gangIndexPD q.linear]
     else
       [gst.basis.cr3 * 512 + gangIndexPML4 q.linear,
        (seitenTabEintrag tab gst.basis.cr3 (gangIndexPML4 q.linear)).rahmen *
          512 + gangIndexPDPT q.linear,
        (seitenTabEintrag tab
          (seitenTabEintrag tab gst.basis.cr3 (gangIndexPML4 q.linear)).rahmen
          (gangIndexPDPT q.linear)).rahmen * 512 + gangIndexPD q.linear,
        (seitenTabEintrag tab
          (seitenTabEintrag tab
            (seitenTabEintrag tab gst.basis.cr3 (gangIndexPML4 q.linear)).rahmen
            (gangIndexPDPT q.linear)).rahmen
          (gangIndexPD q.linear)).rahmen * 512 + gangIndexPT q.linear])
    (if q.schreiben then
       some (if (seitenTabEintrag tab
           (seitenTabEintrag tab gst.basis.cr3 (gangIndexPML4 q.linear)).rahmen
           (gangIndexPDPT q.linear)).gross then
          (seitenTabEintrag tab gst.basis.cr3 (gangIndexPML4 q.linear)).rahmen *
            512 + gangIndexPDPT q.linear
        else if (seitenTabEintrag tab
           (seitenTabEintrag tab
             (seitenTabEintrag tab gst.basis.cr3 (gangIndexPML4 q.linear)).rahmen
             (gangIndexPDPT q.linear)).rahmen
           (gangIndexPD q.linear)).gross then
          (seitenTabEintrag tab
            (seitenTabEintrag tab gst.basis.cr3 (gangIndexPML4 q.linear)).rahmen
            (gangIndexPDPT q.linear)).rahmen * 512 + gangIndexPD q.linear
        else
          (seitenTabEintrag tab
            (seitenTabEintrag tab
              (seitenTabEintrag tab gst.basis.cr3
                (gangIndexPML4 q.linear)).rahmen
              (gangIndexPDPT q.linear)).rahmen
            (gangIndexPD q.linear)).rahmen * 512 + gangIndexPT q.linear)
      else none)
    (gangGross gst q (seitenTabEintrag tab gst.basis.cr3 (gangIndexPML4 q.linear))
      (seitenTabEintrag tab
        (seitenTabEintrag tab gst.basis.cr3 (gangIndexPML4 q.linear)).rahmen
        (gangIndexPDPT q.linear))
      (seitenTabEintrag tab
        (seitenTabEintrag tab
          (seitenTabEintrag tab gst.basis.cr3 (gangIndexPML4 q.linear)).rahmen
          (gangIndexPDPT q.linear)).rahmen
        (gangIndexPD q.linear))
      (seitenTabEintrag tab
        (seitenTabEintrag tab
          (seitenTabEintrag tab
            (seitenTabEintrag tab gst.basis.cr3 (gangIndexPML4 q.linear)).rahmen
            (gangIndexPDPT q.linear)).rahmen
          (gangIndexPD q.linear)).rahmen
        (gangIndexPT q.linear))))

/-- The walk outcome is the combined walk on the looked-up entries. -/
theorem seitenGangGross_fst (gst : GrossSteuerung) (tab : Nat → Wort)
    (q : SeitenAnfrage) :
    (seitenGangGross gst tab q).1 =
      gangGross gst q (seitenTabEintrag tab gst.basis.cr3 (gangIndexPML4 q.linear))
        (seitenTabEintrag tab
          (seitenTabEintrag tab gst.basis.cr3 (gangIndexPML4 q.linear)).rahmen
          (gangIndexPDPT q.linear))
        (seitenTabEintrag tab
          (seitenTabEintrag tab
            (seitenTabEintrag tab gst.basis.cr3 (gangIndexPML4 q.linear)).rahmen
            (gangIndexPDPT q.linear)).rahmen
          (gangIndexPD q.linear))
        (seitenTabEintrag tab
          (seitenTabEintrag tab
            (seitenTabEintrag tab
              (seitenTabEintrag tab gst.basis.cr3 (gangIndexPML4 q.linear)).rahmen
              (gangIndexPDPT q.linear)).rahmen
            (gangIndexPD q.linear)).rahmen
          (gangIndexPT q.linear)) := rfl

/-- Without large pages in the tables and with disarmed SMEP/SMAP,
    the full walk IS the accepted 4 KiB walk. -/
theorem seitenGangGross_gleich (gst : GrossSteuerung) (tab : Nat → Wort)
    (q : SeitenAnfrage)
    (h1 : gst.basis.smep = false) (h2 : gst.basis.smap = false)
    (hg2 : (seitenTabEintrag tab
        (seitenTabEintrag tab gst.basis.cr3 (gangIndexPML4 q.linear)).rahmen
        (gangIndexPDPT q.linear)).gross = false)
    (hg1 : (seitenTabEintrag tab
        (seitenTabEintrag tab
          (seitenTabEintrag tab gst.basis.cr3 (gangIndexPML4 q.linear)).rahmen
          (gangIndexPDPT q.linear)).rahmen
        (gangIndexPD q.linear)).gross = false) :
    (seitenGangGross gst tab q).1 = (seitenGang gst.basis tab q).1 := by
  rw [seitenGangGross_fst, seitenGang_fst]
  exact gangGross_gleich gst q _ _ _ _ h1 h2 hg2 hg1

/-- A non-success walk leaves the tables unchanged. -/
theorem seitenGangGross_nichtOk_still (gst : GrossSteuerung)
    (tab : Nat → Wort) (q : SeitenAnfrage) (e : GangErgebnis)
    (h1 : (seitenGangGross gst tab q).1 = e)
    (h2 : ¬ ∃ phys, e = .ok phys) :
    (seitenGangGross gst tab q).2 = tab := by
  simp only [seitenGangGross] at h1 ⊢
  rw [h1]
  exact seitenGangTab_nichtOk _ _ _ _ h2

/-! ## 6. Machine connection: adapter plug and extended steps.

  No walk admits a `HwMaschine` successor: faults have none by
  construction, and accessed/dirty updates touch the tables, which
  live outside `HwMaschine`. Walk behaviour lives in
  `HwGrossSchritt` over machine-plus-tables, embedding `HwSchritt`
  exactly. -/

/-- The large-page adapter: the refused default. No walk admits a
    machine successor state. -/
def adapterGross : HwAdapter SeitenAnfrage := verweigertAdapter _

/-- The large-page adapter admits nothing. -/
theorem adapterGross_verweigert (m : HwMaschine) (c : Nat)
    (q : SeitenAnfrage) :
    adapterGross.schritt m c q = none := rfl

/-- Paging state: the coherent machine plus extended control plus
    tables. -/
structure GrossZustand where
  maschine : HwMaschine
  steuer : GrossSteuerung
  tabellen : Nat → Wort

/-- Paging events: the old events, an admitted walk, a page fault. -/
inductive GrossEreignis where
  | alt : HwEreignis → GrossEreignis
  | gangOk : SeitenAnfrage → Nat → GrossEreignis
  | gangPf : SeitenAnfrage → Nat → PfFehlerCode → GrossEreignis
  deriving DecidableEq, Repr

/-- One large-paging step: the embedded old step (tables kept), an
    admitted walk (tables gain accessed/dirty, machine kept), or a
    page fault (a self-loop carrying the faulting address and error
    code). A noncanonical address admits NO step. -/
inductive HwGrossSchritt :
    GrossZustand → GrossZustand → GrossEreignis → Prop where
  | einbettet {s : GrossZustand} {m' : HwMaschine} {e : HwEreignis}
      (h : HwSchritt s.maschine m' e) :
      HwGrossSchritt s ⟨m', s.steuer, s.tabellen⟩ (.alt e)
  | gang {s : GrossZustand} {q : SeitenAnfrage} {phys : Nat}
      {tab' : Nat → Wort}
      (h : (seitenGangGross s.steuer s.tabellen q).1 = .ok phys)
      (ht : (seitenGangGross s.steuer s.tabellen q).2 = tab') :
      HwGrossSchritt s ⟨s.maschine, s.steuer, tab'⟩ (.gangOk q phys)
  | fehler {s : GrossZustand} {q : SeitenAnfrage} {a : Nat}
      {c : PfFehlerCode}
      (h : (seitenGangGross s.steuer s.tabellen q).1 = .seitenFehler a c) :
      HwGrossSchritt s s (.gangPf q a c)

/-- FORWARD embedding: every old step is a large-paging step. -/
theorem hwGrossSchritt_einbettung_vor (s : GrossZustand)
    (m' : HwMaschine) (e : HwEreignis)
    (h : HwSchritt s.maschine m' e) :
    HwGrossSchritt s ⟨m', s.steuer, s.tabellen⟩ (.alt e) :=
  .einbettet h

/-- BACKWARD embedding, exact: an `.alt` step comes only from the old
    step with the same event. -/
theorem hwGrossSchritt_alt_invert (s t : GrossZustand)
    (e : HwEreignis) (h : HwGrossSchritt s t (.alt e)) :
    ∃ m', t.maschine = m' ∧ t.tabellen = s.tabellen ∧
      HwSchritt s.maschine m' e := by
  cases h with
  | einbettet hstep => exact ⟨_, rfl, rfl, hstep⟩

/-- An `.alt` step over the reached target is the old step. -/
theorem hwGrossSchritt_einbettung_zurueck (s : GrossZustand)
    (m' : HwMaschine) (e : HwEreignis)
    (h : HwGrossSchritt s ⟨m', s.steuer, s.tabellen⟩ (.alt e)) :
    HwSchritt s.maschine m' e := by
  obtain ⟨m'', hm, _, hstep⟩ := hwGrossSchritt_alt_invert s _ e h
  subst hm
  exact hstep

/-- A walk step carries its walk equation. -/
theorem grossGangOk_invert (s t : GrossZustand) (q : SeitenAnfrage)
    (phys : Nat) (h : HwGrossSchritt s t (.gangOk q phys)) :
    (seitenGangGross s.steuer s.tabellen q).1 = .ok phys := by
  cases h with
  | gang h ht => exact h

/-- A fault step carries its walk equation. -/
theorem grossGangPf_invert (s t : GrossZustand) (q : SeitenAnfrage)
    (a : Nat) (c : PfFehlerCode)
    (h : HwGrossSchritt s t (.gangPf q a c)) :
    (seitenGangGross s.steuer s.tabellen q).1 = .seitenFehler a c := by
  cases h with
  | fehler h => exact h

/-- A fault step never moves the state. -/
theorem hwGrossSchritt_fehler_still (s s' : GrossZustand)
    (q : SeitenAnfrage) (a : Nat) (c : PfFehlerCode)
    (h : HwGrossSchritt s s' (.gangPf q a c)) : s' = s := by
  cases h
  rfl

/-- Every large-paging step preserves machine well-formedness: old
    steps by the accepted preservation, walk steps because the
    machine is kept, fault steps because the state never moves. -/
theorem hwGrossSchritt_wf (s s' : GrossZustand)
    (e : GrossEreignis) (h : HwGrossSchritt s s' e)
    (hwf : HwWf s.maschine) : HwWf s'.maschine := by
  cases h with
  | einbettet hstep => exact hwSchritt_wf _ _ _ hstep hwf
  | gang h ht => exact hwf
  | fehler h => exact hwf

/-- A noncanonical address admits no large-paging step: the #GP
    belongs to the address stage, which already owns it. -/
theorem grossSeitenGp_verweigert (s s' : GrossZustand)
    (q : SeitenAnfrage) (a phys : Nat) (a' : Nat) (c : PfFehlerCode)
    (hg : (seitenGangGross s.steuer s.tabellen q).1 = .gpFehler a) :
    ¬ HwGrossSchritt s s' (.gangOk q phys) ∧
      ¬ HwGrossSchritt s s' (.gangPf q a' c) := by
  refine ⟨?_, ?_⟩
  · intro hstep
    have hok := grossGangOk_invert s s' q phys hstep
    rw [hg] at hok
    cases hok
  · intro hstep
    have hpf := grossGangPf_invert s s' q a' c hstep
    rw [hg] at hpf
    cases hpf

/-! ## 7. Witness: a 2 MiB page, a 1 GiB page, and their faults.

  Tables at frames 40/41/42: PML4[0] chains to frame 41, PDPT[0]
  chains to frame 42, PD[0] is an aligned 2 MiB leaf onto frame 512,
  PD[1] is a MISALIGNED 2 MiB leaf (frame 513), and PDPT[1] is an
  aligned 1 GiB leaf onto frame 512 * 512. All other slots are
  absent. -/

/-- Witness control: CR3 at frame 40, WP armed, SMEP/SMAP off. -/
def witGrossBasis : SeitenSteuerung :=
  { cr3 := 40, wp := true, smep := false, smap := false, nxe := true }

/-- Witness extended control: AC clear. -/
def witGrossSteuer : GrossSteuerung := ⟨witGrossBasis, false⟩

/-- Witness control with SMEP armed. -/
def witGrossSteuerSmep : GrossSteuerung :=
  ⟨{ witGrossBasis with smep := true }, false⟩

/-- Witness control with SMAP armed and AC clear. -/
def witGrossSteuerSmap : GrossSteuerung :=
  ⟨{ witGrossBasis with smap := true }, false⟩

/-- Witness control with SMAP armed but AC set: access is allowed. -/
def witGrossSteuerAc : GrossSteuerung :=
  ⟨{ witGrossBasis with smap := true }, true⟩

/-- Intermediate entry chaining to the next frame. -/
def witGrossZwischen (rahmen : Nat) : SeitenEintrag :=
  { vorhanden := true, schreibbar := true, benutzer := true,
    gross := false, zugegriffen := false, schmutzig := false,
    noExec := false, rahmen := rahmen }

/-- Aligned 2 MiB leaf onto frame 512. -/
def witGross2M : SeitenEintrag :=
  { vorhanden := true, schreibbar := true, benutzer := true,
    gross := true, zugegriffen := false, schmutzig := false,
    noExec := false, rahmen := 512 }

/-- Misaligned 2 MiB leaf: frame 513 breaks the 512-alignment. -/
def witGross2MFehl : SeitenEintrag :=
  { vorhanden := true, schreibbar := true, benutzer := true,
    gross := true, zugegriffen := false, schmutzig := false,
    noExec := false, rahmen := 513 }

/-- Aligned 1 GiB leaf onto frame 512 * 512. -/
def witGross1G : SeitenEintrag :=
  { vorhanden := true, schreibbar := true, benutzer := true,
    gross := true, zugegriffen := false, schmutzig := false,
    noExec := false, rahmen := 512 * 512 }

/-- Witness tables: the 40/41/42 chain, the two large leaves, and the
    misaligned twin. -/
def witGrossTab : Nat → Wort :=
  fun n =>
    if n = 40 * 512 + 0 then eintragKodieren (witGrossZwischen 41)
    else if n = 41 * 512 + 0 then eintragKodieren (witGrossZwischen 42)
    else if n = 41 * 512 + 1 then eintragKodieren witGross1G
    else if n = 42 * 512 + 0 then eintragKodieren witGross2M
    else if n = 42 * 512 + 1 then eintragKodieren witGross2MFehl
    else 0

/-- User read of linear page 0 lands on the 2 MiB page at frame 512. -/
theorem wit_gross2M_ok :
    (seitenGangGross witGrossSteuer witGrossTab
      ⟨0, false, true, false⟩).1 = .ok 2097152 := by
  decide

/-- User read of linear 1 GiB lands on the 1 GiB page: identity. -/
theorem wit_gross1G_ok :
    (seitenGangGross witGrossSteuer witGrossTab
      ⟨2 ^ 30, false, true, false⟩).1 = .ok (2 ^ 30) := by
  decide

/-- User read through the misaligned leaf faults with RSVD set. -/
theorem wit_gross_fehl_rsvd :
    (seitenGangGross witGrossSteuer witGrossTab
      ⟨2 ^ 21, false, true, false⟩).1 =
      .seitenFehler (2 ^ 21) ⟨true, false, true, true, false⟩ := by
  decide

/-- Supervisor fetch from the user large page faults under SMEP. -/
theorem wit_gross_smep :
    (seitenGangGross witGrossSteuerSmep witGrossTab
      ⟨0, false, false, true⟩).1 =
      .seitenFehler 0 ⟨true, false, false, false, true⟩ := by
  decide

/-- Supervisor data read of the user large page faults under SMAP. -/
theorem wit_gross_smap :
    (seitenGangGross witGrossSteuerSmap witGrossTab
      ⟨0, false, false, false⟩).1 =
      .seitenFehler 0 ⟨true, false, false, false, false⟩ := by
  decide

/-- With AC set, the same SMAP-armed access succeeds onto frame 512. -/
theorem wit_gross_ac_erlaubt :
    (seitenGangGross witGrossSteuerAc witGrossTab
      ⟨0, false, false, false⟩).1 = .ok 2097152 := by
  decide

/-- A noncanonical address is #GP in the large walk. -/
theorem wit_gross_nichtkanonisch_gp :
    (seitenGangGross witGrossSteuer witGrossTab
      ⟨2 ^ 47, false, true, false⟩).1 = .gpFehler (2 ^ 47) := by
  decide

/-- The write sets accessed on the touched PML4 entry. -/
theorem wit_gross_zugriff_gesetzt :
    (eintragDekodieren
      ((seitenGangGross witGrossSteuer witGrossTab
        ⟨0, true, true, false⟩).2 (40 * 512 + 0))).zugegriffen = true := by
  decide

/-- The write sets dirty on the 2 MiB leaf entry. -/
theorem wit_gross_schmutzig_gesetzt :
    (eintragDekodieren
      ((seitenGangGross witGrossSteuer witGrossTab
        ⟨0, true, true, false⟩).2 (42 * 512 + 0))).schmutzig = true := by
  decide

/-- An untouched entry keeps its exact word through the write-back. -/
theorem wit_gross_unberuehrt_still :
    (seitenGangGross witGrossSteuer witGrossTab
      ⟨0, true, true, false⟩).2 (40 * 512 + 7) =
      witGrossTab (40 * 512 + 7) := by
  decide

/-- JOINT WITNESS: well-formedness, the 2 MiB and 1 GiB mappings, the
    misalignment/SMEP/SMAP faults with their classes, beside the
    accepted two-core run: owner-only forwarding and the
    memory-changing drain (0 becomes 42, observed from both cores).
    Non-degenerate: large pages with different sizes, two cores, a
    real memory change. -/
theorem hwGross_zeuge :
    HwWf hwWitStart ∧
      (seitenGangGross witGrossSteuer witGrossTab
        ⟨0, false, true, false⟩).1 = .ok 2097152 ∧
      (seitenGangGross witGrossSteuer witGrossTab
        ⟨2 ^ 30, false, true, false⟩).1 = .ok (2 ^ 30) ∧
      (seitenGangGross witGrossSteuer witGrossTab
        ⟨2 ^ 21, false, true, false⟩).1 =
        .seitenFehler (2 ^ 21) ⟨true, false, true, true, false⟩ ∧
      (seitenGangGross witGrossSteuerSmep witGrossTab
        ⟨0, false, false, true⟩).1 =
        .seitenFehler 0 ⟨true, false, false, false, true⟩ ∧
      (seitenGangGross witGrossSteuerSmap witGrossTab
        ⟨0, false, false, false⟩).1 =
        .seitenFehler 0 ⟨true, false, false, false, false⟩ ∧
      hwWitLoadEigen = some (some (BitVec.ofNat 8 42)) ∧
      hwWitLoadFremd = some (some (BitVec.ofNat 8 0)) ∧
      hwWitNachFlush = some (some (BitVec.ofNat 8 42)) := by
  exact ⟨hwWitStart_wf, wit_gross2M_ok, wit_gross1G_ok,
    wit_gross_fehl_rsvd, wit_gross_smep, wit_gross_smap,
    hwWit_weiterleitung, hwWit_fremd_alt,
    hwWit_spülung_aendert_speicher⟩

/- CUTS:
   Proved here (all over the REUSED coherent machine, the REUSED
   accepted fault vocabulary and the REUSED 4 KiB walk -- no new
   machine, no new decoder row, no silicon re-verification):
   - extended control `GrossSteuerung` (accepted control plus
     EFLAGS.AC) and the decided per-access SMEP/SMAP checks
     `smepVerletzt`/`smapVerletzt` with their off/user/fetch/AC
     shape lemmas (§1);
   - large-page alignment `grossAusgerichtet2M/1G` (frame multiples of
     512 / 512*512) with examples and counterexamples, the 21/30-bit
     offsets, and the shared leaf check `grossBlatt` that runs the
     ACCEPTED `blattPruefung` after the SMEP/SMAP gate, with
     `blatt_ok_payload` and `grossBlatt_ohne_schutz` (§2);
   - the 2 MiB walk `gangGross2M` (PD with PS maps, PDPT with PS
     stays refused), the 1 GiB walk `gangGross1G` (PDPT with PS maps,
     PD with PS stays refused), and the dispatcher `gangGross` (PDPT
     large pages through 1G, else 2M), each EQUAL to the accepted 4
     KiB walk where it applies (`gangGross2M_gleich`,
     `gangGross1G_gleich`, `gangGross_gleich`, `gangGross_bei_1G/2M`)
     (§3);
   - fault behaviour: misaligned leaves fault with RSVD set
     (2M and 1G), SMEP/SMAP violations fault as protection with live
     access bits, AC-set access falls through to the accepted leaf
     (`grossBlatt_ac_gleich`), and the pinned error-code values
     13/17/3 (§4);
   - the full walk `seitenGangGross` over the accepted lookups with
     touched-only write-back (2 entries for 1 GiB, 3 for 2 MiB, 4
     otherwise), its outcome equation, its agreement with the
     accepted walk without large pages (`seitenGangGross_gleich`),
     and stillness of every non-success walk (§5);
   - machine connection: the refusing adapter `adapterGross`, the
     extended step `HwGrossSchritt` with the EXACT two-way embedding
     of `HwSchritt`, fault steps that never move state, wf
     preservation, and the planted noncanonical refusal (§6);
   - witness: a 2 MiB page and a 1 GiB page mapped, the misaligned
     RSVD fault, the SMEP/SMAP faults and the AC-set allowance, the
     noncanonical #GP, accessed set on touched entries and dirty on
     the large leaf (§7);
   - joint witness `hwGross_zeuge`: large mappings and faults beside
     the accepted two-core memory-changing TSO run (owner-only
     forwarding, drain 0 to 42 observed from both cores).
   NOT proved here, and not claimed:
   - No hardware verification: entry bit positions (P/RW/US/A/D/PS/XD
     per Vol 3A §4.5 Table 4-18), the 512/512*512 alignment rules,
     the SMEP/SMAP/AC rule shape, index shifts, the error-code bit
     meanings (Vol 3A §4.7 Table 4-7) and the 48-bit canonical width
     are NAMED silicon assumptions. No Vol 3A paging text was
     supplied to this lane, so bit-level correspondence is assumed,
     never claimed.
   - No TLB, no PAT/memory-type behaviour on large pages, no fault
     DELIVERY (IDT/stack/handler/error-code push stays with its
     lane): fault outcomes carry address plus code only.
   - The 1 GiB/2 MiB choice of reserved-bit STATUS (RSVD fault vs
     refusal) follows the 4 KiB walk's reserved-XD precedent; the
     silicon's exact reserved-bit reporting on large leaves stays a
     named assumption.
   - No per-access target-to-W/GX simulation, no timing, no source
     stop-class transfer.
-/

#print axioms GrossSteuerung
#print axioms smepVerletzt
#print axioms smapVerletzt
#print axioms grossAusgerichtet2M
#print axioms grossAusgerichtet1G
#print axioms grossBlatt
#print axioms blatt_ok_payload
#print axioms grossBlatt_ohne_schutz
#print axioms gangGross2M
#print axioms gangGross1G
#print axioms gangGross
#print axioms gangGross2M_gleich
#print axioms gangGross1G_gleich
#print axioms gangGross_gleich
#print axioms gangGross2M_fehlaligniert
#print axioms gangGross1G_fehlaligniert
#print axioms gangGross2M_smep
#print axioms gangGross2M_smap
#print axioms grossBlatt_ac_gleich
#print axioms seitenGangGross
#print axioms seitenGangGross_gleich
#print axioms seitenGangGross_nichtOk_still
#print axioms adapterGross
#print axioms adapterGross_verweigert
#print axioms HwGrossSchritt
#print axioms hwGrossSchritt_einbettung_vor
#print axioms hwGrossSchritt_alt_invert
#print axioms hwGrossSchritt_einbettung_zurueck
#print axioms grossGangOk_invert
#print axioms grossGangPf_invert
#print axioms hwGrossSchritt_fehler_still
#print axioms hwGrossSchritt_wf
#print axioms grossSeitenGp_verweigert
#print axioms witGrossTab
#print axioms wit_gross2M_ok
#print axioms wit_gross1G_ok
#print axioms wit_gross_fehl_rsvd
#print axioms wit_gross_smep
#print axioms wit_gross_smap
#print axioms wit_gross_ac_erlaubt
#print axioms hwGross_zeuge

end Gabbro.Grammatik.X86
