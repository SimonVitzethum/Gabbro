/-
  File:      core/Core/Beobachtung/SchrankenBeweise/BindungRessourcenEndlich.lean
  Subject:   THE RESOURCE PROTOCOL DUTY OF BOUND UNITS (M9, MK-12). The bare
              `ressourcenProtokollAussage` is false: a crash can install recovery
              data outside the declared bounds. Its missing premise is the
              recovery start-data discipline (`ressourcenProtokoll_unterWiederanlauf`).
              For bound units the premise holds unconditionally: the elaborated
              restart data is the loader start data with the identity clearing,
              so the cleared entry has depth zero and the durable booking is
              empty. This closes the protocol resource family of
              `SchrankenbindungOffenAussage` over bound units. The per-form
              family still needs the class footprints, and the checker row the
              simulation match; both stay open findings.
-/
module

public import Core.Beobachtung.SchrankenBeweise.RessourcenEinheit
public import Core.Beobachtung.SchrankenBeweise.Bindung

@[expose] public section

namespace Gabbro.Core.Beobachtung

open Katalog Maschine Annahme
open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- The elaborated restart data clears nothing: entry data keeps its frame. -/
theorem einrichtung_verwerfen_id (scope : Scope) (eintritte : Kontext → Option Nat)
    (plan : Speicherplan) (r : Rahmen) :
    (einrichtung scope eintritte plan).wiederanlauf.verwerfen r = r :=
  rfl

/-- The elaborated restart entry starts with an empty continuation stack. -/
theorem einrichtung_daten_tiefe (scope : Scope) (eintritte : Kontext → Option Nat)
    (plan : Speicherplan) (m : Nat → UInt8) (c : Kontext) :
    ((einrichtung scope eintritte plan).wiederanlauf.daten m).lokal c |>.fortsetzungen.length =
      0 :=
  rfl

/-- The booking after a crash reset is empty, whatever the pre-state and the
    installed rights are: the reset builds a start state, whose booking
    defaults to empty. -/
theorem wiederanlauf_umfang_leer {s : Zustand Nat Zelle Int Nat Rahmen PUnit}
    {w : Wiederanlauf Zelle Int Nat Rahmen PUnit} {t : Nat} {p : PersistZustand}
    {r : Rechte} {i : Nat} :
    ({ s.wiederanlauf w t p with rechte := r } : Zustand Nat Zelle Int Nat Rahmen PUnit).buchung.umfang
        i =
      [] :=
  rfl

/-- The resource protocol duty of every bound unit: answers and interrupts keep
    both bounds by the generic preservation facts, and the crash case meets the
    recovery start-data discipline because the cleared entry has depth zero
    and books nothing. -/
theorem bindungRessourcenProtokoll_endlich (P : Katalog.Plattform)
    (u : UnitMitSchranken) :
    ressourcenProtokollAussage (einheitMitSchranken P u) := by
  apply ressourcenProtokoll_unterWiederanlauf
  intro t s p c
  have hverw : ∀ r : Rahmen,
      (einheitMitSchranken P u).einrichtung.wiederanlauf.verwerfen r = r :=
    fun r => einrichtung_verwerfen_id _ _ _ r
  have htiefe : ∀ (m : Nat → UInt8) (d : Kontext),
      (((einheitMitSchranken P u).einrichtung.wiederanlauf.daten m).lokal d).fortsetzungen.length =
        0 :=
    fun m d => einrichtung_daten_tiefe _ _ _ m d
  refine ⟨?_, ?_⟩
  · rw [einheitMitSchranken_tiefe, hverw _, htiefe _ _]
    exact fun _ _ => Nat.zero_le _
  · intro z hz
    simp only [LebendeZellen, Set.mem_setOf_eq] at hz
    obtain ⟨_, hlen⟩ := hz
    have humfang : ({ s.wiederanlauf (einheitMitSchranken P u).einrichtung.wiederanlauf t p
      with rechte :=
        ((einheitMitSchranken P u).einrichtung.wiederanlauf.daten p.dauerhaft).rechte } :
      Zustand Nat Zelle Int Nat Rahmen PUnit).buchung.umfang z.1 = [] :=
      wiederanlauf_umfang_leer
    rw [humfang, List.length_nil] at hlen
    exact Nat.not_lt_zero _ hlen

end Gabbro.Core.Beobachtung
