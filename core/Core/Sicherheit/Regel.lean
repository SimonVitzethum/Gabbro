module

public import Core.Sicherheit.Speicher
public import Core.Sicherheit.Invarianten
public import Core.Sicherheit.Rennen

@[expose] public section

namespace Gabbro.Core.Sicherheit

open Maschine Katalog

variable {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]
variable (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)

/-- M7S checks ordinary concrete context steps here. Loader, hardware arrival,
    interruption and crash have their own cases in the run induction. -/
structure SchrittSicherheit (H : Umgebung) (ρ : Lauf E) (t : Nat)
    (vor nach : Zustand L Ort Wert Raum Lok Grund) (spur : SchrittSpur Ort Wert) : Prop where
  speicher : ZugriffGebucht vor nach spur ∧
    ∃ neu, NeueWirkungen vor nach spur neu ∧ FreigabenGueltig vor nach ρ.hw t spur neu
  invarianten : InvariantenAmSchnitt E vor → InvariantenAmSchnitt E nach
  sperrwechsel : ¬ Absturz spur → InvariantenBeimWechsel E vor nach
  rennen : RennenImGraph vor.graph → RennenImGraph nach.graph
  register : RegisterImSchritt ρ.hw t vor spur nach
  toctou : CommitImSchritt E H ρ t vor spur nach

/-- The per-form premise for the four safety theorems, checked directly
    against each executed implementation rule and its recorded effects. -/
def RegelSicher : Form → Prop := fun f =>
  ∀ H ρ t c w vor zwischen nach plan spur,
    E.maschine.system.kopf vor c = some f →
    (E.maschine.system.regel f).impl c vor w [plan] zwischen →
    FuehrtSchrittAus E.maschine.einrichtung t c vor zwischen plan spur nach →
    SchrittSicherheit E H ρ t vor nach spur

end Gabbro.Core.Sicherheit
