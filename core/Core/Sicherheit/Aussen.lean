module

public import Core.Sicherheit.Einheit
public import Core.Aussen.Bindung

@[expose] public section

namespace Gabbro.Core.Sicherheit

open Maschine Katalog

variable {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]

/-- A successful reply commits its operation. An error reply has no committed effect. -/
def ErfolgreicherCommit (e : Katalog.Ereignis) (a : AntwortEreignis) : Prop :=
  e = .antwort a ∧ a.reply.result.isOk = true

/-- Replay the previously observed answers, including errors, against the alternative total
    policy. Catalogue start data and the offered hardware schedule remain those of the run. -/
def Vorgeschichte (H : Umgebung) (verlauf : AussenVerlauf) : Prop :=
  ∀ i t q a, verlauf[i]? = some (t, .antwort q a) →
    H.politik.antwort t (verlauf.take i) q = .antwort a

def AussenHistorie (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (ρ : Lauf E) (H : Umgebung) (verlauf : AussenVerlauf) : Prop :=
  Hardware E.maschine.katalog H ∧ E.maschine.ZulStart H ρ.start ∧
    (∀ t, AngebotGueltig E.maschine.katalog H (ρ.hw.angebot t)) ∧ Vorgeschichte H verlauf

/-- A raw effect must also satisfy the operation-specific precondition of the row. -/
def CommitBedingungen (p : Plattform) (s : AussenSicht) (q : Frage) : Prop :=
  ∃ a, atomar p s q = .antwort a ∧ a.result.isOk = true

def EigeneGriffe (s : Zustand L Ort Wert Raum Lok Grund) (c : Kontext) (q : Frage) : Prop :=
  ∀ z ∈ q.zugriffe, s.buchung.aussengriff c z.handle z.right

/-- Each committed operation holds the handles it uses and validates in its own commit view.
    A mediated operation can fail under another admissible policy. An unmediated commit has
    no such atomic failure branch, so its authorisation must survive every admissible view. -/
def CommitImSchritt (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (H : Umgebung) (ρ : Lauf E) (t : Nat) (vor : Zustand L Ort Wert Raum Lok Grund)
    (spur : SchrittSpur Ort Wert) (nach : Zustand L Ort Wert Raum Lok Grund) : Prop :=
    (∀ e ∈ spur.aussen, ∀ a, ErfolgreicherCommit e a →
      (∃ c, c.nummer = a.context ∧ EigeneGriffe vor c a.question) ∧
      Aussen.GueltigBeiCommit E.maschine.katalog.plattform (H.politik.sicht t vor.verlauf) a.question ∧
      ∀ H', AussenHistorie E ρ H' vor.verlauf →
        H'.politik.antwort t vor.verlauf a.question = .antwort a.reply →
        Aussen.GueltigBeiCommit E.maschine.katalog.plattform
          (H'.politik.sicht t vor.verlauf) a.question) ∧
    ∃ neu, NeueWirkungen vor nach spur neu ∧
      ∀ e, Wirkung.aussen e ∈ neu →
        KannSchreiten ρ.hw t e.kontext vor ∧ EigeneGriffe vor e.kontext e.frage ∧
        E.maschine.katalog.enthaelt (.endpoint e.frage.endpoint) ∧
        Aussen.GueltigBeiCommit E.maschine.katalog.plattform (H.politik.sicht t vor.verlauf) e.frage ∧
        CommitBedingungen E.maschine.katalog.plattform (H.politik.sicht t vor.verlauf) e.frage ∧
        ∀ H', AussenHistorie E ρ H' vor.verlauf →
          Aussen.GueltigBeiCommit E.maschine.katalog.plattform (H'.politik.sicht t vor.verlauf) e.frage ∧
          CommitBedingungen E.maschine.katalog.plattform (H'.politik.sicht t vor.verlauf) e.frage

/-- Check commits in every implementation transition, including unmediated effects. -/
def ToctouFrei (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (H : Umgebung) (ρ : Lauf E) : Prop :=
  (∀ s, ρ.zeit.zustand 0 = some s → s.buchung.wirkungen = []) ∧
  ∀ t vor spur nach, Uebergang E ρ t vor spur nach → CommitImSchritt E H ρ t vor spur nach

end Gabbro.Core.Sicherheit
