module

public import Core.Sicherheit.Aussen

@[expose] public section

namespace Gabbro.Core.Sicherheit

open Maschine Katalog

variable {L Ort Wert Raum Lok Grund Bedingung Wahl Form : Type} [DecidableEq L]

/-- Lazy initial values participate in reads-from and coherence as M3 prescribes.
    They do not count as accesses performed by an executing context. -/
def AusgefuehrterZugriff (g : SpeicherGraph Ort Wert) (i : Fin g.ev.length) : Prop :=
  (g.graph.liest i ∨ g.graph.schreibt i) ∧
    match (g.ev[i.val]'i.isLt).kontext with
    | .initial _ => False
    | .kontext _ | .aussen => True

def Konflikt (g : SpeicherGraph Ort Wert) (i j : Fin g.ev.length) : Prop :=
  i ≠ j ∧ AusgefuehrterZugriff g i ∧ AusgefuehrterZugriff g j ∧
    g.graph.ort i = g.graph.ort j ∧ (g.graph.schreibt i ∨ g.graph.schreibt j) ∧
    (g.graph.na i ∨ g.graph.na j)

def Registerzugriff : AussenOperation → Prop
  | .registerRead _ | .registerWrite _ _ | .waitRegister _ _ => True
  | .read | .write _ | .resolve _ | .firmware _ _ | .exchange _ => False

/-- A device object has one owner in the authority state. Access requires its unloaned
    authority at the transition, including when the register access is a synchronous reply. -/
def RegisterErlaubt (s : Maschine.Zustand L Ort Wert Raum Lok Grund) (c : Nat) (q : Frage) : Prop :=
  Registerzugriff q.operation →
    ∃ owner, owner.nummer = c ∧ s.buchung.geraet q.objekt = some (owner, .frei)

/-- Conflicting real accesses in one memory prefix are ordered. -/
def RennenImGraph (g : SpeicherGraph Ort Wert) : Prop :=
  ∀ i j, Konflikt g i j → g.graph.hb i j ∨ g.graph.hb j i

/-- A device access needs exclusive authority at the transition that uses it. -/
def RegisterImSchritt (hw : HwLauf) (t : Nat)
    (vor : Zustand L Ort Wert Raum Lok Grund) (spur : SchrittSpur Ort Wert)
    (nach : Zustand L Ort Wert Raum Lok Grund) : Prop :=
    (∀ e ∈ spur.aussen,
      (∀ q : FrageEreignis, e = .frage q → RegisterErlaubt vor q.context q.question) ∧
      ∀ a, ErfolgreicherCommit e a → RegisterErlaubt vor a.context a.question) ∧
    ∃ neu, NeueWirkungen vor nach spur neu ∧
      ∀ e, Wirkung.aussen e ∈ neu →
        KannSchreiten hw t e.kontext vor ∧ RegisterErlaubt vor e.kontext.nummer e.frage

/-- Every RC11 prefix and every device transition is checked, including epochs
    later discarded by crashes. -/
def Rennfrei (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (_H : Umgebung) (ρ : Lauf E) : Prop :=
  (∀ (t : Maschine.Schnitt E.maschine ρ) s, ρ.zeit.zustand t.val = some s → RennenImGraph s.graph) ∧
  ∀ t vor spur nach, Uebergang E ρ t vor spur nach → RegisterImSchritt ρ.hw t vor spur nach

end Gabbro.Core.Sicherheit
