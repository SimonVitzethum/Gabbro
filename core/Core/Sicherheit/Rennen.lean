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

/-- Race freedom is checked in each RC11 graph prefix, including prefixes of epochs
    later discarded by crashes. The same cut checks authority for device operations. -/
def Rennfrei (E : Einheit L Ort Wert Raum Lok Grund Bedingung Wahl Form)
    (_H : Umgebung) (ρ : Lauf E) : Prop :=
  (∀ (t : Maschine.Schnitt E.maschine ρ) (s : Maschine.Zustand L Ort Wert Raum Lok Grund),
    ρ.zeit.zustand t.val = some s →
    ∀ i j, Konflikt s.graph i j → s.graph.graph.hb i j ∨ s.graph.graph.hb j i) ∧
  ∀ t vor spur nach, Uebergang E ρ t vor spur nach →
    (∀ e ∈ spur.aussen,
      (∀ q : FrageEreignis, e = .frage q → RegisterErlaubt vor q.context q.question) ∧
      ∀ a, ErfolgreicherCommit e a → RegisterErlaubt vor a.context a.question) ∧
    ∃ neu, NeueWirkungen vor nach spur neu ∧
      ∀ e, Wirkung.aussen e ∈ neu →
        KannSchreiten ρ.hw t e.kontext vor ∧ RegisterErlaubt vor e.kontext.nummer e.frage

end Gabbro.Core.Sicherheit
