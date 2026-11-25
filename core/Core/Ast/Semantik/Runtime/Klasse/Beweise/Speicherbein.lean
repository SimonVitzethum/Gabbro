/-
  File:      core/Core/Ast/Semantik/Runtime/Klasse/Beweise/Speicherbein.lean
  Subject:   THE MEMORY LEG OF EVERY EFFECT CLASS (MK-03). `KlassenSpeicherbeinAussage` is proved for all
             eleven effect classes by assembling the case proofs already established in this folder: the
             private classes (`lokal`, `ruf`, `frage`) and the lifecycle classes (`starte`, `beende`,
             `verbinde`, `wechsle`) have no memory event to book; the three memory classes (`lesen`,
             `schreiben`, `rmw`) book the one access of their trace through `Speicherfolge`; and the lock
             class closes the statement vacuously, because the premise `beruehrtSperrwort = false` is
             contradictory for a lock action. The lock word's own authority is the separate, excluded
             statement `KlassenSperrwortbeinAussage`; nothing here changes a pinned statement or weakens
             a guard.
-/
module

public import Core.Ast.Semantik.Runtime.Klasse.Beweise.Sicherheit

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog

/-- **Booking and releases, for every effect class** (`KlassenSpeicherbeinAussage`). The proof has no
    per-program content: it only selects the case proof of the class. The lock class is discharged by its
    impossible premise; the machine-level gap behind that premise is the MK-05 finding recorded in
    `Klasse/Sicherheit`. -/
theorem klassenSpeicherbein (k : Wirkungsklasse) : KlassenSpeicherbeinAussage k := by
  cases k with
  | lokal => exact klassenSpeicherbein_privat .lokal (Or.inl rfl)
  | ruf => exact klassenSpeicherbein_privat .ruf (Or.inr (Or.inl rfl))
  | frage => exact klassenSpeicherbein_privat .frage (Or.inr (Or.inr (Or.inl rfl)))
  | verbrauche => exact klassenSpeicherbein_privat .verbrauche (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  | zaun m => exact klassenSpeicherbein_privat (.zaun m) (Or.inr (Or.inr (Or.inr (Or.inr ⟨m, rfl⟩))))
  | lesen m => exact klassenSpeicherbein_zugriff (.lesen m) m (Or.inl rfl)
  | schreiben m => exact klassenSpeicherbein_zugriff (.schreiben m) m (Or.inr (Or.inl rfl))
  | rmw m => exact klassenSpeicherbein_zugriff (.rmw m) m (Or.inr (Or.inr rfl))
  | sperre a =>
      intro h
      change true = false at h
      cases h
  | starte => exact klassenSpeicherbein_faden .starte (Or.inl rfl)
  | beende => exact klassenSpeicherbein_faden .beende (Or.inr (Or.inl rfl))
  | verbinde => exact klassenSpeicherbein_faden .verbinde (Or.inr (Or.inr (Or.inl rfl)))
  | wechsle => exact klassenSpeicherbein_faden .wechsle (Or.inr (Or.inr (Or.inr rfl)))

end Gabbro.Core.Ast.Semantik
