/-
  File:      core/Core/Ast/Semantik/Runtime/Klasse/Beweise/Sicherheit.lean
  Subject:   THE CLASS-DETERMINED SAFETY LEGS, TOGETHER (MK-03). `KlassenSicherheitAussage` is the conjunction
             of the four legs fixed by the effect class alone: booking and releases, the authority of pending
             questions, device authority and committed outside operations. Three legs hold for every class
             (`klassenFragenbein`, `klassenRegisterbein`, `klassenCommitbein`). The booking leg is split by
             class: `klassenSpeicherbein_privat` for `lokal`, `ruf` and `frage`, `klassenSpeicherbein_zugriff`
             for `lesen`, `schreiben` and `rmw`. For `sperre` the booking leg is vacuous, because the premise
             `beruehrtSperrwort = false` is contradictory: a lock action changes the lock owner and the machine
             records that as an event on the lock word; `ZugriffGebucht` would ask for a handle that
             `Zustand.griff` has no way to give. That gap is recorded as a finding for MK-05 in
             `Klasse/Sicherheit`; nothing is weakened here and no statement is changed.
-/
module

public import Core.Ast.Semantik.Runtime.Klasse.Sicherheit
public import Core.Ast.Semantik.Runtime.Klasse.Beweise.SpeicherPrivat
public import Core.Ast.Semantik.Runtime.Klasse.Beweise.Speicherfolge
public import Core.Ast.Semantik.Runtime.Klasse.Beweise.Fragen
public import Core.Ast.Semantik.Runtime.Klasse.Beweise.RegisterCommit

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog

/-- **The four class-determined safety legs of one class** (`KlassenSicherheitAussage`). Only the booking leg
    needs a case split. The lock class closes it vacuously, through the contradictory premise
    `beruehrtSperrwort = false`; the machine-level gap behind that premise is the MK-05 finding in
    `Klasse/Sicherheit`. -/
theorem klassenSicherheit (k : Wirkungsklasse) : KlassenSicherheitAussage k := by
  refine ⟨?_, klassenFragenbein k, klassenRegisterbein k, klassenCommitbein k⟩
  cases k with
  | lokal => exact klassenSpeicherbein_privat .lokal (Or.inl rfl)
  | ruf => exact klassenSpeicherbein_privat .ruf (Or.inr (Or.inl rfl))
  | frage => exact klassenSpeicherbein_privat .frage (Or.inr (Or.inr (Or.inl rfl)))
  | verbrauche => exact klassenSpeicherbein_privat .verbrauche (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  | zaun m =>
    exact klassenSpeicherbein_privat (.zaun m) (Or.inr (Or.inr (Or.inr (Or.inr ⟨m, rfl⟩))))
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
