module

public import Core.Ast.Semantik.Runtime.Regeln
public import Mathlib.Computability.PartrecCode

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar

open Ast.Semantik

/-- Ein Einzelschritt über einem Befehlsprogramm: holt den Befehl am Programmzeiger
    und wertet ihn aus. Kein Befehl am Zeiger (Programmende, Sprung ins Leere):
    kein Nachfolger. Die Funktion ist total und deterministisch. -/
def Schritt (prog : List Befehl) : Option Rahmen → Option Rahmen
  | none => none
  | some r =>
    match prog[r.pc]? with
    | none => none
    | some b => some (b.auswerten r)

/-- Erreichbarkeit in endlich vielen Schritten ab einem Startrahmen. -/
def Erreicht (prog : List Befehl) (start : Rahmen) (r : Rahmen) : Prop :=
  ∃ k, (Schritt prog)^[k] (some start) = some r

/-- Nat-Ausgabe eines Laufzeitwerts: ganze Zahl, nichtnegativ, als Nat gelesen.
    Negative oder nicht-ganze Werte sind keine Nat-Ausgabe. -/
def NatAusgabe (d : Ast.Dynamisch) : Option Nat :=
  match alsGanzzahl d with
  | none => none
  | some g => if 0 ≤ g.zahl.wert then some g.zahl.wert.toNat else none

/-- Das Programm hält ab `start` mit Ausgabe `a`: ein erreichbarer Rahmen, dessen
    Rückgabe `a` als Nat-Ausgabe trägt. -/
def HaeltMit (prog : List Befehl) (start : Rahmen) (a : Nat) : Prop :=
  ∃ r, Erreicht prog start r ∧ r.rueckgabe.bind NatAusgabe = some a

/-- Das offene Fragment: der Startrahmen trägt keine Schranken an den
    Temporärslots (`obergrenzen slot = none` für alle Slots). Zusammen mit den
    unbeschränkten `Int`-Werten der `Zahl`-Semantik (`wert : Int`, kein
    Maschinenwort-Zwang im Modell) ist dies die Quelle des unbeschränkten
    Zustands, den die Simulation braucht:
    - `Rahmen.obergrenzen` default `none` (Frame.lean),
    - `Schrankendaten` default `none` = offen (Messdaten.lean),
    - offene Regionen ohne Obergrenze bleiben zulässig (AGENTS.md §2).
    Ein Fragment mit überall endlichen Schranken UND Maschinenwort-Werten ist
    ein endlicher Automat (siehe Befund unten) und gehört nicht hierher. -/
def OffenesFragment (r : Rahmen) : Prop :=
  ∀ slot, r.obergrenzen slot = none

/-- Das Simulationssubstrat: alles, was Hy2/Hy4 liefern müssen, in einer
    Struktur. Der Prüfer sieht nur Gabbro-Programme — über ihre Kodierung
    (`kodiere`) als natürliche Zahlen; kein Prädikat spricht je über den
    μ-rekursiven Code `c` als Prüfgegenstand, und der Startrahmen hängt nur
    von der Eingabe `n` ab (`startVon`), nie vom Code:
    - `programm` bildet jeden μ-rekursiven Code auf ein Befehlsprogramm ab;
    - `kodiere`/`dekodiere` ist die berechenbare Kodierung ℕ ↔ Programm
      (statt einer `Primcodable`-Instanz für `Befehl`: erststufig, ohne
      Funktionsanteile — die konkrete Gödel-Nummerierung baut Hy2/Hy4);
    - `komposition_berechenbar` verlangt `Computable (kodiere ∘ programm)`
      — das braucht nur `Primcodable Code` und `Primcodable ℕ`, und genau
      diese Funktion ist die Reduktionsfunktion;
    - `treue`: Auswertung trifft Haldung mit gleicher Ausgabe.
    Die Schleifen der Simulation (`springe`, `springeWenn`, `zurueckSprung`)
    und die Nat-Arithmetik (`literal`, `binaer`, `vergleichen`) sind die
    unbeschränkten Bausteine aus dem Kernmodell. -/
structure SimulationsSubstrat where
  programm : Nat.Partrec.Code → List Befehl
  kodiere : List Befehl → ℕ
  dekodiere : ℕ → Option (List Befehl)
  startVon : ℕ → Rahmen
  komposition_berechenbar : Computable (fun c => kodiere (programm c))
  dekodiere_links : ∀ p, dekodiere (kodiere p) = some p
  start_offen : ∀ n, OffenesFragment (startVon n)
  treue : ∀ c n a, (Nat.Partrec.Code.eval c n = Part.some a ↔
    HaeltMit (programm c) (startVon n) a)

/-- Die pinnierte Grundaussage: ein solches Substrat existiert. Der
    Existenzbeweis (Kodierung + Compiler + Treuebeweis) ist Arbeit von
    Hy2/Hy4; die Reduktions- und Rice-Sätze bauen bedingt darauf auf. -/
def SubstratAussage : Prop :=
  Nonempty SimulationsSubstrat

/-- Aus der Linksinversen folgt die Injektivität der Kodierung: verschiedene
    Programme erhalten verschiedene Nummern. -/
theorem kodiere_injektiv (s : SimulationsSubstrat) :
    Function.Injective s.kodiere := by
  intro p₁ p₂ h
  have h1 := s.dekodiere_links p₁
  have h2 := s.dekodiere_links p₂
  rw [h] at h1
  have h3 : some p₁ = some p₂ := h1.symm.trans h2
  exact Option.some_inj.mp h3

theorem erreicht_refl (prog : List Befehl) (r : Rahmen) : Erreicht prog r r :=
  ⟨0, rfl⟩

theorem erreicht1 {prog : List Befehl} {r r' : Rahmen}
    (hs : Schritt prog (some r) = some r') : Erreicht prog r r' :=
  ⟨1, by simpa using hs⟩

theorem erreicht_trans {prog : List Befehl} {r₀ r₁ r₂ : Rahmen}
    (h₁ : Erreicht prog r₀ r₁) (h₂ : Erreicht prog r₁ r₂) :
    Erreicht prog r₀ r₂ := by
  obtain ⟨k₁, hk₁⟩ := h₁
  obtain ⟨k₂, hk₂⟩ := h₂
  exact ⟨k₁ + k₂, by rw [Nat.add_comm k₁ k₂, Function.iterate_add_apply, hk₁, hk₂]⟩

theorem erreicht_schritt {prog : List Befehl} {r₀ r r' : Rahmen}
    (h : Erreicht prog r₀ r) (hs : Schritt prog (some r) = some r') :
    Erreicht prog r₀ r' :=
  erreicht_trans h (erreicht1 hs)

theorem haeltMit_erreicht {prog : List Befehl} {r₀ r₁ : Rahmen} {a : Nat}
    (h : Erreicht prog r₀ r₁) (hh : HaeltMit prog r₁ a) : HaeltMit prog r₀ a := by
  obtain ⟨r, hr, hout⟩ := hh
  exact ⟨r, erreicht_trans h hr, hout⟩

/- Befund (kein Satz, zur Entscheidung durch Lead mit Owner): das vollständig
    beschränkte Fragment — alle Werte Maschinenwörter (endlicher Wertebereich),
    alle Regionen mit Obergrenze, alle Schranken endlich — hat nur endlich viele
    verschiedene Maschinenzustände. Terminierung ist dort entscheidbar
    (Zustandswiederholung: ein Lauf, der länger als die Zustandszahl Schritte
    macht, wiederholt einen Zustand und läuft wegen deterministischem `Schritt`
    nie mehr in einen haltenden Zustand, den er nicht schon erreicht hätte).
    Für dieses Fragment gilt also KEIN Unentscheidbarkeitssatz; was dort die
    Nutzerpflicht (Terminierungs- oder Schrankenargument) rechtfertigt, wäre eher
    eine Härte-Aussage (z. B. PSPACE-Härte des beschränkten Halteproblems)
    als ein Unentscheidbarkeitsbeweis. Ob und in welcher Form eine solche
    Aussage pinniert wird, entscheiden Lead mit Owner. -/

end Gabbro.Core.Beobachtung.Unentscheidbar
