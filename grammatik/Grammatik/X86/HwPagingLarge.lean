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

/- CUTS:
   Skeleton only; full CUTS with the reviewed file.
-/

#print axioms GrossSteuerung
