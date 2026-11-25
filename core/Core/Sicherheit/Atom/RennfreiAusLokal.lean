/-
  File:      core/Core/Sicherheit/Atom/RennfreiAusLokal.lean
  Subject:   THE RACE LEG FROM THE LOCK DISCIPLINE (MK-04). The race leg of the implementation's safety
             (`Sicherheit.Rennfrei`, first conjunct `RennenImGraph`) says that conflicting real accesses of one RC11
             prefix, one of which is plain, are ordered by happens-before. `RennfreiAusLokalAussage`: every prefix
             whose graph satisfies the lock discipline of `Speicher.Atom.Abschnitte` has this property. It is
             proved from the order argument `rennfrei_aus_abschnitten`; `RennenImGraph` IS the race freedom of the
             real accesses of `g.graph` (`AusgefuehrterZugriff`: the initial writes are no accesses).
             What this does NOT claim, and why: that every reachable prefix of the machine satisfies the discipline.
             The checker's lock rule must give every plain access of a guarded location a window; the machine's lock
             protocol must give the windows their hand-over. The second part has a FINDING for MK-05: the machine
             records the hand-off of a lock to the next ticket holder as ONE update event of the RELEASING context
             (`Maschine/Ereignisse.sperrE`: `some c`, `some d` with `c ≠ d` is `[⟨.rmw, ort, .ra, v, v⟩]` appended by
             `c`), and the new owner `d` never records an acquire event, because `SperrZustand.Nimmt` only takes a
             FREE lock. After a hand-off nothing in the program order of `d` reads the lock word, so the release of
             `c` does not synchronise with `d`'s section, and `RennenImGraph` fails for lock-protected plain data
             handed over by a hand-off. The discipline `Abschnitte.ausschluss` needs the acquire of the new owner;
             MK-05 must either record the hand-off as a release write of `c` plus an acquire read of `d` (when `d`
             resumes), or free the lock at a release and let the head of the queue take it.
-/
module

public import Core.Sicherheit.Rennen
public import Core.Speicher.Atom.Abschnitte

@[expose] public section

namespace Gabbro.Core.Sicherheit

open Maschine Katalog

/-- **The race leg follows from the lock discipline.** For every RC11 prefix `g` and every guard map `schloss`, if the
    real accesses of `g` stand in lock windows as `Abschnitte` demands, the prefix is race free. -/
def RennfreiAusLokalAussage : Prop :=
  ∀ (Ort Wert : Type) (schloss : Ort → Option Ort) (g : SpeicherGraph Ort Wert),
    g.graph.Abschnitte schloss (AusgefuehrterZugriff g) → RennenImGraph g

/-- **The race leg from the lock discipline** (the proof of `RennfreiAusLokalAussage`). -/
theorem rennfreiAusLokal : RennfreiAusLokalAussage := by
  intro Ort Wert schloss g d i j konflikt
  obtain ⟨hne, hi, hj, hort, hw, hna⟩ := konflikt
  exact Speicher.Graph.rennfrei_aus_abschnitten d i j hi hj ⟨hne, hort, hw⟩ hna

end Gabbro.Core.Sicherheit
