module

public import Core.Beobachtung.SchrankenBeweise.Ressourcen.StartByteHandoff

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine
open Ast.Semantik (Zustand)

inductive RessourcenLadefehler where
  | bildUngueltig
  | regionVoll

/-- Check the footprint of the actual grants before installing their canonical byte booking.
    An open ceiling accepts the handoff at any size. -/
def ladeStartbuchung (P : Plattform) (u : UnitMitSchranken) (a : AussenStart) (p : Ladung) :
    Except RessourcenLadefehler Zustand :=
  match (einheitMitSchranken P u).laden a p with
  | none => .error .bildUngueltig
  | some s =>
    if u.deklaration.speicher.any (fun n => decide (n < handoffByteFootprint a.regions)) then
      .error .regionVoll
    else
      .ok { s with buchung := handoffBooking 1 a.regions s.buchung }

/-- A valid image and an overfull handoff force the named refusal. -/
theorem ladeStartbuchung_regionVoll (P : Plattform) (u : UnitMitSchranken) (a : AussenStart)
    (p : Ladung) {s : Zustand} {n : Nat}
    (bild : (einheitMitSchranken P u).laden a p = some s)
    (grenze : u.deklaration.speicher = some n) (voll : n < handoffByteFootprint a.regions) :
    ladeStartbuchung P u a p = .error .regionVoll := by
  simp only [ladeStartbuchung, bild, grenze, Option.any, decide_eq_true voll, if_true]

/-- Every successful handoff retains the loaded frames and charges exactly the bytes of its
    grants. A finite declaration bounds that charge. -/
theorem ladeStartbuchung_erfolg (P : Plattform) (u : UnitMitSchranken) (a : AussenStart)
    (p : Ladung) {s : Zustand} (geladen : ladeStartbuchung P u a p = .ok s) :
    ∃ roh : Zustand, (einheitMitSchranken P u).laden a p = some roh ∧
      s.lokal = roh.lokal ∧ (LebendeZellen s).encard = handoffByteFootprint a.regions ∧
      UnterGrenze u.deklaration.speicher (handoffByteFootprint a.regions) := by
  unfold ladeStartbuchung at geladen
  cases bild : (einheitMitSchranken P u).laden a p with
  | none =>
    rw [bild] at geladen
    cases geladen
  | some roh =>
    rw [bild] at geladen
    split at geladen
    · cases geladen
    · rename_i passt
      cases geladen
      refine ⟨roh, ?_, rfl, ?_, ?_⟩
      · first | exact bild | rfl
      · apply handoffBooking_byte_encard
        intro slot valid
        exact (geladeneRegion_lebt_leer P u a p bild slot valid).1
      · intro n grenze
        apply Nat.le_of_not_gt
        intro voll
        exact passt (by simp only [grenze, Option.any, decide_eq_true voll])

/-- The same valid one-byte handoff fits exactly under ceiling one and is rejected under
    ceiling zero. The successful state contains one live booked cell. -/
theorem ladeStartbuchung_erfuellbar (P : Plattform) (u : UnitMitSchranken) :
    let passend : UnitMitSchranken := { u with deklaration := { u.deklaration with speicher := some 1 } }
    let voll : UnitMitSchranken := { u with deklaration := { u.deklaration with speicher := some 0 } }
    ∃ (a : AussenStart) (p : Ladung), a.regions = [⟨0, 1⟩] ∧
      (∃ s : Zustand, ladeStartbuchung P passend a p = .ok s ∧ (LebendeZellen s).encard = 1) ∧
      ladeStartbuchung P voll a p = .error .regionVoll := by
  intro passend voll
  let a : AussenStart := ⟨0, fun i => if i = 0 then some 0 else none,
    [⟨0, 1⟩], fun _ => none, .leer⟩
  let p := Ast.Semantik.bild.lade
  let d := Ast.Semantik.startdaten (Ast.Semantik.programm u.baum).eingang
    (Ast.Semantik.programm u.baum).eintritte (a.assignment 0) P a.regions
  let roh := Maschine.Zustand.start d.lokal d.status d.kerne d.rechte
    (Ast.Semantik.programm u.baum).speicher.initial (.leer (Ast.Semantik.startmedium a))
  have bild : (einheitMitSchranken P u).laden a p = some roh := rfl
  have footprint : handoffByteFootprint a.regions = 1 := rfl
  have passt : ladeStartbuchung P passend a p =
      .ok { roh with buchung := handoffBooking 1 a.regions roh.buchung } := by
    have bild' : (einheitMitSchranken P passend).laden a p = some roh := bild
    have cap : passend.deklaration.speicher = some 1 := rfl
    have notFull : ¬ (1 : Nat) < 1 := Nat.lt_irrefl _
    simp only [ladeStartbuchung, bild', cap, Option.any, footprint, decide_eq_false notFull,
      Bool.false_eq_true, if_false]
  obtain ⟨_, _, _, count, _⟩ := ladeStartbuchung_erfolg P passend a p passt
  rw [footprint] at count
  refine ⟨a, p, rfl, ⟨_, passt, count⟩, ?_⟩
  have bild' : (einheitMitSchranken P voll).laden a p = some roh := bild
  exact ladeStartbuchung_regionVoll P voll a p bild' rfl (footprint.symm ▸ Nat.zero_lt_one)

end Gabbro.Core.Beobachtung
