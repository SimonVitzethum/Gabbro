module

public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.Interferenz
public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.InterferenzAllgemein.T1.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}

/-- **Allgemeine Stabilitaet der Invarianten (N Faeden).** Wo `Q` die Invariante selbst
    ist, faellt die geteilte Erhaltpraemisse weg: jeder Schritt -- fremd wie eigen --
    wird vom Kontext getragen (`invErhalt_aus_Kontext`), die Kette faltet wie gehabt
    (`kette_erhaelt` via `allgemeinStabil`). `hDeck` wird getragen, nicht verbraucht:
    es beurkundet die Disziplin, unter der der Rest -- beliebiges rahmenlokales `Q`
    ueber geteilten Traegern -- weiter anzunehmen ist (G3); `atomic`-Globale und
    `publishes`/`awaits`-Paare bleiben ausserhalb (G4). -/
theorem allgemeinStabil_invariant (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (I : TraegerInv (D := D)) (c : D.Tab ⊕ D.Glob)
    (hInv : InvariantenKontext Nb J I)
    (hDeck : GeteiltGedeckt Nb J)
    (hAb : ∀ (f : Faden), f ∈ J.faeden →
      HaengtAb (D.schreibt (J.code f)) (D.gschreibt (J.code f)) (I.inv c))
    (hInit : ∀ (f : Faden), f ∈ J.faeden → ∀ (σ₀ : World D),
      J.welten[0]? = some σ₀ → I.inv c σ₀) :
    ∀ (σ : World D), J.welten.getLast? = some σ → ∀ (f : Faden), f ∈ J.faeden → I.inv c σ := by
  have hErhalt : ∀ (k : Nat) (g : Faden) (vor nach : World D),
      J.schrittFaden[k]? = some g → J.welten[k]? = some vor → J.welten[k + 1]? = some nach →
        (I.inv c vor ↔ I.inv c nach) := by
    intro k g vor nach _ hkv hkn
    exact invErhalt_aus_Kontext Nb J I hInv c vor nach
      (List.mem_of_getElem? hkv) (List.mem_of_getElem? hkn)
  refine allgemeinStabil Nb J I (fun _ => I.inv c) hInv hDeck hAb hInit ?_ ?_
  · intro f hf k g vor nach _ _ hkg hkv hkn
    exact .inr (hErhalt k g vor nach hkg hkv hkn)
  · intro f hf k vor nach hkg hkv hkn
    exact hErhalt k f vor nach hkg hkv hkn

#print axioms Gabbro.Grammatik.stabilSchritt_gilt
#print axioms Gabbro.Grammatik.stabilKette_gilt
#print axioms Gabbro.Grammatik.kette_erhaelt
#print axioms Gabbro.Grammatik.allgemeinStabil
#print axioms Gabbro.Grammatik.schuldnerHaelt_gilt
#print axioms Gabbro.Grammatik.eintrittHeldIn_aus_Passt
#print axioms Gabbro.Grammatik.invSichtHaelt_aus_Eintritt
#print axioms Gabbro.Grammatik.fremdDisziplin_gilt
#print axioms Gabbro.Grammatik.fremdErhalt_disjunkt_aus_Disziplin
#print axioms Gabbro.Grammatik.invErhalt_aus_Kontext
#print axioms Gabbro.Grammatik.allgemeinStabil_invariant

/-! ## 12. Gabelmodell: Erzeugung und Vereinigung als Gestalt (G6) -/

/-- Ein Erzeugungseintrag: der Elternfaden `eltern` gibt dem Kindfaden `kind` an der
    Kettenstelle `k` seine Eintrittswelt -- die Welt der Kette an eben dieser Stelle. -/
def SpawnEintrag : Type := Faden × Faden × Nat

/-- Ein Vereinigungseintrag: der Elternfaden `eltern` nimmt den Kindfaden `kind` an der
    Kettenstelle `k` zurueck -- die Welt der Kette an eben dieser Stelle. -/
def JoinEintrag : Type := Faden × Faden × Nat

/-- Die Eintrittswelt des Kindfadens aus der Erzeugung: die Kettenwelt an der
    eingetragenen Stelle. Keine eigene Eintrittswelt mehr -- der Gabeleintrag nennt sie. -/
def KindEintrittAusSpawn (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (s : SpawnEintrag) : Option (World D) :=
  J.welten[s.2.2]?

/-- Die Rueckkehrwelt des Kindfadens aus der Vereinigung: die Kettenwelt an der
    eingetragenen Stelle. -/
def KindEintrittAusJoin (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (j : JoinEintrag) : Option (World D) :=
  J.welten[j.2.2]?

/-- Die Eintrittswelt eines Kindfadens aus der ganzen Erzeugungsliste: der erste Eintrag,
    der ihn als Kind nennt, bestimmt die Stelle; ohne Eintrag gibt es keine Welt. -/
def KindEintrittAusGabel (Nb : Nebeneinander) (J : GemeinsamerLauf (D := D) Nb)
    (spawns : List SpawnEintrag) (kind : Faden) : Option (World D) :=
  match spawns.find? (fun s => decide (s.2.1 = kind)) with
  | none => none
  | some s => J.welten[s.2.2]?

/-! ## 13. Ausnahmen neben der geteilten Deckung: Atomar und Paarung als Gestalt (G4) -/

/-- Atomare Ausnahme: der Traeger ist ein `atomic`-Global -- seine Zugriffe ordnet die
    Maschine (A10), nicht die gemeinsame Sperre. -/
def AtomarAusgenommen (c : D.Tab ⊕ D.Glob) : Prop :=
  ∃ g : D.Glob, c = .inr g ∧ D.atomar g = true

/-- Paarungsausnahme: der Traeger ist Nutzlast einer Veroeffentlichung -- die Paarung von
    `publishes` und `awaits` ueber `D.nutzlast` ordnet, nicht die gemeinsame Sperre. -/
def PaarungAusgenommen (c : D.Tab ⊕ D.Glob) : Prop :=
  ∃ a p : D.Glob, c = .inr p ∧ p ∈ D.nutzlast a ∧ D.atomar a = true


end Gabbro.Grammatik
