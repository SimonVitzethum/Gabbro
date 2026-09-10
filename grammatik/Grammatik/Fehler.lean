/-
  Datei:      Grammatik/Fehler.lean
  Gegenstand: **Der Fehlerausgang als PARALLELES Modell** -- neben `Semantik.lean`, nicht
              darin. Nichts an `eval`, `exec` oder `Ausgang` aendert sich; diese Datei legt
              daneben, was ein benannter Fehler waere, und in welcher Form die Ueberein-
              stimmung stuende, faellt er nicht.

    `Fehlerklasse` -- die vier benannten Fehler: `index` (Index ausserhalb), `ueberlauf`
                      (Ablage ausserhalb der erklaerten Breite), `nenner` (Nenner null),
                      `gestalt` (Gestalt passt nicht).
    `ErgebnisF`    -- der parallele Ausgang eines Ausdrucks: `wert` oder `fehler`.
    `evalF`        -- die parallele Auswertung: `State -> Expr -> Wert plus Fehlerklasse`
                      als Gestalt (`World D -> Expr D Γ Λ τ -> ErgebnisF D τ`, mit
                      Eintrittswelt und Sichtbereich als Argumenten wie bei `eval`).
    `evalF_ok` / `evalF_stimmt`
                   -- die Uebereinstimmungsform als `Prop`-Definitionen: kein Fehler
                      heisst, `eval` stimmt zu.
    `IndexFalle` / `FehlerFall`
                   -- die Geschenk-Falsifizierer als DATEN, nicht als Beweise: ein Index
                      ausserhalb seines Bereichs erreicht `fehler .index` per Definition.

  Warum `evalF` heute nie fehlt -- und das ist die Aussage, kein Mangel: ein
  `Expr.slot`-Index hat den Typ `.index (D.count t)` und traegt seinen Bereichsbeweis
  bei sich; ausserhalb ist nicht schreibbar. Der Fehlerarm ist nur ueber ROHE Daten
  (`IndexFalle`: Tabelle plus nacktes `Int`) erreichbar -- genau die Stelle, an der
  der Pruefer heute den Bereich haelt (`S3-FEHLER-ENTWURF.md`).

  BEWUSST AUSSERHALB (Entscheidung, keine Luecke):
    Durch `execStmt`/`execBlock` faedelt kein Fehler: die Fortpflanzung (`evalAll`,
    Schrittfolge, Schleifendurchgang) stuende erst mit dem Anschluss an `exec` da,
    und der Anschluss ist Schnitt, nicht Fassade (Schnitt S1 unten). Ebenso faellt
    `finalState` hier aus: ohne Postzustand gibt es nichts abzubilden.

  Vorausgesetzt (vertraut, nicht bewiesen):
    P1  `eval` aus `Semantik.lean` ist die Bedeutung: `evalF` ruft es auf, statt es
        nachzubauen. Zwei Auswerter waeren zwei Bedeutungen.
    P2  Rohe Indizes kommen von aussen (`Orakel`, Maschine): `IndexFalle.k` ist ein
        Datum, kein Term der Grammatik.

  Schnitte (gebucht, nicht versteckt):
    S1  Kein Anschluss an `exec`: `ErgebnisF` lebt auf Ausdruecken; der Anweisungs-
        ausgang `Ausgang` bekommt keinen `fehler`-Fall. Die Fortpflanzungslemmata
        (`evalAll`, Schritt, Schleife) sind damit benannt, nicht gebaut.
    S2  `evalF` reicht jeden Aufruf an `eval` durch und meldet `wert`: die Fehler-
        arme sind erreichbar nur ueber die Fallen-Daten, nicht ueber Terme.
    S3  Nicht in `Grammatik.lean` verdrahtet: die Bahnbreite verbietet den
        Indexeingriff; pruefen allein mit `lake env lean Grammatik/Fehler.lean`.

  Kein `mathlib`, kein `sorry`, kein `axiom`, kein Import aus `programmlogik/`.
-/
import Grammatik.Semantik

namespace Gabbro.Grammatik

variable {D : Deklaration}
variable {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}

/-- Die vier benannten Fehler -- die Aufzaehlung neben den Ausgaengen, nicht darin. -/
inductive Fehlerklasse where
  | index
  | ueberlauf
  | nenner
  | gestalt
  deriving DecidableEq, Repr

/-- Der parallele Ausgang eines Ausdrucks: ein Wert seines Typs oder ein benannter
    Fehler. Daneben `Ausgang` aus `Semantik.lean`, der unveraendert bleibt. -/
inductive ErgebnisF (D : Deklaration) (τ : Ty) where
  | wert (v : Wert D τ)
  | fehler (k : Fehlerklasse)

/-- Die parallele Auswertung: `State -> Expr -> Wert plus Fehlerklasse` als Gestalt.
    Heute immer `wert`, per P1 durch `eval` hindurch -- der Fehlerarm wartet auf den
    Anschluss (Schnitt S1), nicht auf einen zweiten Auswerter. -/
def evalF (σ₀ σ : World D) (ρ : Env D Γ) (e : Expr D Γ Λ τ) : ErgebnisF D τ :=
  .wert (eval σ₀ e σ ρ)

/-- Kein Fehler: das Ergebnis traegt einen Wert. Die Voraussetzung der
    Uebereinstimmung, als `Prop`-Definition, nicht als Satz. -/
def evalF_ok : ErgebnisF D τ → Prop
  | .wert _ => True
  | .fehler _ => False

/-- Die Uebereinstimmungsform: faellt kein Fehler, stimmt `eval` zu. Als `Prop`-
    Definition hingelegt; der Beweis stuende erst mit dem Anschluss (Schnitt S1). -/
def evalF_stimmt (σ₀ σ : World D) (ρ : Env D Γ) (e : Expr D Γ Λ τ) (v : Wert D τ) : Prop :=
  evalF σ₀ σ ρ e = .wert v → eval σ₀ e σ ρ = v

/-- Ein Index ausserhalb als DATUM: die Tabelle und das nackte `Int` -- ohne
    Bereichsbeweis, denn mit Beweis waere es kein Falsifizierer, sondern ein Term. -/
structure IndexFalle (D : Deklaration) where
  tab : D.Tab
  k : Int

/-- Ein Index ausserhalb erreicht `fehler .index` -- per Definition, nicht per Beweis. -/
def indexFalleErgebnis {τ : Ty} (_ : IndexFalle D) : ErgebnisF D τ :=
  .fehler .index

/-- Ein benannter Fehlerfall als Datum: die Klasse plus die Beschreibung, woher das
    rohe Datum kam (Orakel, Maschine, Prueferstelle). -/
structure FehlerFall where
  klasse : Fehlerklasse
  beschreibung : String

/-- Jeder benannte Fall erreicht seinen Fehler -- per Definition. -/
def fehlerFallErgebnis {τ : Ty} (f : FehlerFall) : ErgebnisF D τ :=
  .fehler f.klasse

#print axioms Gabbro.Grammatik.evalF
#print axioms Gabbro.Grammatik.evalF_ok
#print axioms Gabbro.Grammatik.evalF_stimmt
#print axioms Gabbro.Grammatik.indexFalleErgebnis
#print axioms Gabbro.Grammatik.fehlerFallErgebnis

end Gabbro.Grammatik
