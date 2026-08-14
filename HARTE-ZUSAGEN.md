# Harte Zusagen im Code — und die eine Bedingung, an der alles haengt

**2026-08-14.** Die Frage: kann die Sprache dem Programmierer **Zusagen abverlangen**, so dass
Induktion nicht mehr geraten, sondern **zusammengesetzt** wird?

**Antwort: ja — aber nur, wenn die erzwungene Zusage eine Aussage ueber EINEN SCHRITT ist.**

---

## Warum Induktion heute Heuristik ist

Ein Loeser muss drei Dinge raten: **welches** Schema, an **welcher** Variablen, mit **welcher**
Verallgemeinerung. `by induction over <domain>` nimmt ihm das erste ab. Die anderen zwei bleiben —
und damit bleibt „uebersetzt es" teilweise Loeserglueck, was gegen den ganzen Zuschnitt steht
(M1–M4 sind Typen, keine Loeser).

---

## Die Zerlegung, die es aufloest

| | Aussage | braucht Induktion? | pruefbar? |
|---|---|---|---|
| **Schrittzusage** | *„`delete_leaf` entfernt genau einen Knoten und erhaelt die Verkettung der uebrigen"* | **nein** — eine Aussage ueber **eine** Operation | **ja**, gegen die **erzeugte** Mutation |
| **Gesamtaussage** | *„nach `revoke` gibt es keine Abkoemmlinge"* | **ja** | durch **Zusammensetzung** der Schrittzusagen |

> **Wenn der Code die Schrittzusage machen MUSS, setzt das Schema die Gesamtaussage zusammen,
> statt sie zu raten.** Die Verallgemeinerung ist dann die Invariante (schon da), die Variable ist
> das Mass (deklariert), das Schema kommt aus der Struktur. **Nichts bleibt zu erraten.**

---

## Die Form: eine Zeile je ERZEUGTER Operation, nicht je Aufrufstelle

```gabbro
table CapSpace {
    slot { … }
    invariant cdt_wellformed  cost O(n) runs online : … ;

    ops insert, remove, relabel, delete_leaf;

    op delete_leaf shrinks descendants by 1 maintains cdt_wellformed;
    op insert      grows   descendants by 1 maintains cdt_wellformed;
    op relabel     keeps   descendants      maintains cdt_wellformed;
}
```

**Vier Operationen, vier Zeilen.** Nicht vier je Beweispflicht, nicht vier je Aufrufstelle.

---

## Die Bedingung, an der alles haengt — und sie ist scharf

**Eine erzwungene Zusage ist entweder geprueft oder ein Axiom. Ein drittes gibt es nicht.**

| Fall | Folge |
|---|---|
| **geprueft** | dann ist sie eine **Pflicht**. Braeuchte ihre Pruefung selbst Induktion, waere die Sache **zirkulaer** |
| **ungeprueft** | dann ist sie ein **Axiom je Operation** — und die Axiomschicht waechst von ~130 auf eins-je-Operation. Das ist Abbruchbedingung 5 |

**Der Ausweg ist genau die Lokalitaet:** eine Schrittzusage ist ueber **einer** Operation
formuliert, und die Operation ist **erzeugt** (Zuschnitt (c)). **Der Erzeuger weiss, was er
emittiert hat** — er prueft die Zusage gegen seine eigene Emission, ohne Induktion. Weder
zirkulaer noch Axiom.

> **Damit steht die Entwurfsregel, und sie ist neu:**
> **Eine Zusage, die der Code machen MUSS, darf nur eine Aussage ueber EINEN Schritt sein.
> Alles Globale ist Beweis oder Axiom — niemals Zusage.**

---

## Was es kostet

| | |
|---|---|
| **Zeilen** | **eine je erzeugter Operation.** Bei `CapSpace` vier. Sie zaehlen als Spezifikation (Quelle, vor der Codeerzeugung geloescht) |
| **Neue Woerter** | drei: `op`, `shrinks`/`grows`/`keeps`, `by` (vorhanden) |
| **Vorhersagbarkeit** | **wiederhergestellt** — nichts wird geraten, also haengt „uebersetzt es" nicht mehr am Loeser |
| **Vertrauensbasis** | **unveraendert** — die Zusage ist geprueft, nicht geglaubt |

---

## Was es NICHT tut — sonst waere es Ueberschreibung Nummer achtzehn

**Es hebt die Decke nicht.** Erreichbar bleibt: *Eigenschaften, die sich durch wohlfundierten
Abstieg ueber eine **deklarierte** Struktur beweisen lassen.* Was die Form nicht hat, hat sie auch
mit Zusagen nicht:

* Eigenschaften ueber **nicht deklarierten** Strukturen (Maschinenzustand),
* alles, was **Ablaeufe** quantifiziert (Lebendigkeit, D8),
* funktionale Korrektheit, deren Argument **kein Abstieg** ist (der IPC-Fastpath: eine Aussage
  ueber **Werte**, nicht ueber eine schrumpfende Menge).

> **Der Gewinn ist nicht Hoehe, sondern Sicherheit des Erreichens:** die Decke wird
> **automatisch** statt heuristisch erreicht. Das ist weniger, als die Frage hofft — und mehr,
> als der heutige Stand hat.

- [ ] **Die Zahl fehlt weiterhin, und sie ist dieselbe:** wieviele der 17 gemessenen
      Logik-Pflichten sind **Abstiegsaussagen** (dann greift das hier), wieviele sind
      **Wertaussagen** (dann nicht)? **Ohne diese Aufteilung ist auch dieser Entwurf eine
      Behauptung.**
