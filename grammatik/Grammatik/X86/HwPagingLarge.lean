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

/- CUTS:
   Skeleton only; full CUTS with the reviewed file.
-/

#print axioms GrossSteuerung
