module

public import Core.Sicherheit.Einheit

@[expose] public section

namespace Gabbro.Core.Sicherheit

open Maschine Katalog
open Gabbro.Core.Speicher (Etikett)

variable {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]

/-- A read-modify-write requires both rights. An address is resolved only through the recorded
    capability, and the allocation table is read before the step can change it. -/
def Speicherzugriff (s : Maschine.Zustand L Ort Wert Raum Lok Grund) (c : Kontext)
    (l : Etikett Ort Wert) (a : Adresse) : Prop :=
  s.rechte.Gueltig a.griff ∧
    (s.buchung.umfang a.griff.objekt)[a.offset]? = some l.ort ∧
    (l.art.liest → s.buchung.haelt c a.griff .lesen) ∧
    (l.art.schreibt → s.buchung.haelt c a.griff .schreiben)

/-- The synthetic RC11 initial write is the initial value of the triggering real access.
    Its location must have that access in the same transition. -/
def ZugriffGebucht (vor nach : Maschine.Zustand L Ort Wert Raum Lok Grund)
    (spur : SchrittSpur Ort Wert) : Prop :=
  ∀ (i : Nat) (actor : SpeicherAkteur Ort) (l : Etikett Ort Wert), spur.speicher[i]? = some (actor, l) → l.art ≠ .aussen →
    match actor with
    | .kontext c =>
      ∃ a, nach.buchung.adresse (vor.graph.ev.length + i) = some a ∧ Speicherzugriff vor c l a
    | .initial x =>
      x = l.ort ∧ ∃ c access, (.kontext c, access) ∈ spur.speicher ∧
        access.art ≠ .aussen ∧ access.ort = x
    | .aussen => False

def Wirkung.freigabeObjekt : Wirkung → Option Nat
  | .freigabe _ g => some g.objekt
  | .aussen _ => none

/-- The release ledger detects even a denied, repeated or foreign release whose state update
    would otherwise be invisible. It also accounts for all allocations lost by a program step. -/
def FreigabenGueltig (vor nach : Maschine.Zustand L Ort Wert Raum Lok Grund)
    (hw : HwLauf) (t : Nat) (spur : SchrittSpur Ort Wert) (neu : List Wirkung) : Prop :=
  (neu.filterMap Wirkung.freigabeObjekt).Nodup ∧
    (∀ c g, Wirkung.freigabe c g ∈ neu →
      KannSchreiten hw t c vor ∧
      vor.rechte.Gueltig g ∧ vor.buchung.haelt c g .freigeben ∧
        nach.rechte.lebt g.objekt = false ∧ vor.rechte.gen g.objekt < nach.rechte.gen g.objekt) ∧
    (¬ Absturz spur → ∀ o, vor.rechte.lebt o = true → nach.rechte.lebt o = false →
      ∃ c g, Wirkung.freigabe c g ∈ neu ∧ g.objekt = o)

/-- All concrete memory events and releases are safe, including events before a crash.
    A loaded state begins before the first event and with an empty effects ledger. -/
def Speichersicher (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (_H : Umgebung) (ρ : Lauf E) : Prop :=
  (∀ s, ρ.zeit.zustand 0 = some s → s.graph.ev = [] ∧ s.buchung.wirkungen = []) ∧
    ∀ t vor spur nach, Uebergang E ρ t vor spur nach →
      ZugriffGebucht vor nach spur ∧
        ∃ neu, NeueWirkungen vor nach spur neu ∧
          FreigabenGueltig vor nach ρ.hw t spur neu

end Gabbro.Core.Sicherheit
