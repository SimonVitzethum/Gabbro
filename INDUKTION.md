# Induktion — was sie braucht, und was sie am Nutzen kostet

**2026-08-14.** Anschluss an die Berichtigung in [`BEWEISER.md`](BEWEISER.md): Induktion ist nicht
unmoeglich, sondern durch drei Entwurfsregeln verboten. **Was braeuchte man, und was kostet es?**

---

## Drei Stufen, und nur die erste behaelt die Sprache

| | Stufe | der Anwender schreibt | die Linie |
|---|---|---|---|
| **A** | **Erzeugte Schemata** — das Induktionsprinzip folgt aus der `table`-Deklaration | **nichts Neues** (oder eine Zeile, s. u.) | **haelt** |
| **B** | **Rekursive `spec fn` mit `decreases`** | je rekursive Spezifikation ein Abstiegsmass | **wandert** — die Spezifikationssprache bekommt eigene Terminierungspflichten |
| **C** | **Handgeschriebene Lemmata** mit Beweisschritten | Beweise | **weg** — das ist Verus/Dafny, und dann waere die ehrliche Frage: warum nicht Verus |

---

## Was Stufe A technisch braucht — drei Dinge, zwei davon mechanisch

**1. Eine wohlfundierte Relation aus der Deklaration.** Eine `table` mit
`parent`/`first_child`/`next_sibling` legt „ist Abkoemmling von" nahe. **Aber sie ist nur
wohlfundiert, wenn die Struktur azyklisch ist — und das ist die Invariante, die man beweisen will.**

Aufloesung (Standard, nicht neu): die Induktion laeuft ueber ein **Mass** (Zahl der Abkoemmlinge),
und die Invariante ist **Voraussetzung**, nicht Ergebnis. Die Deklaration muss also **nennen**,
welche Invariante die Wohlfundiertheit traegt:

```gabbro
invariant acyclic cost O(n) runs offline: … ;
```

**2. Das Schema erzeugen.** Mechanisch, aus der Deklaration — **wie Isabelle und Coq es aus einer
Datentypdeklaration ableiten.** Es ist eine **Schablone** im Sinne von L3, geht also **einmal nach
Isabelle** und **verkleinert die Vertrauensbasis**, statt sie zu vergroessern. *(Das ist der Grund,
warum Stufe A in den vorhandenen Entwurf passt statt ihn zu sprengen.)*

**3. Das Schema ANWENDEN — und hier sitzt die ganze Schwierigkeit.** Welches Schema, an welcher
Variable, mit welcher Verallgemeinerung? **Das ist eine Heuristik**, und Heuristiken sind die
Stelle, an der Automatisierung ausfaellt.

---

## Der Preis ist nicht die Zeilenzahl, sondern die VORHERSAGBARKEIT

**Das ist die eigentliche Antwort auf „wieviel schwerer im Nutzen".**

Wenn der Uebersetzer das Schema **raet**, haengt „uebersetzt es" an Loeserglueck: **dasselbe
Programm geht heute durch und morgen nicht**, weil eine Zeitschranke anders faellt. Gabbros ganzer
Zuschnitt war das Gegenteil — **M1 bis M4 sind Typen, keine Loeser.**

> **Und der Riss ist schon da:** [`NARROW-GEMESSEN.md`](NARROW-GEMESSEN.md) hat gemessen, dass
> **M1 an vier Stellen ein Loeser ist**, und [`LOGIK-KLEMPNEREI.md`](LOGIK-KLEMPNEREI.md), dass
> **54 relationale Faelle** dazukommen. Induktion mit geratener Anwendung **verbreitert** ihn.

### Die Aufloesung: das Schema wird GENANNT, nicht geraten

```gabbro
ensures  descendants(s) is empty
    by   induction on descendants(s)
```

| | |
|---|---|
| **kein Lemma** | keine Beweisschritte, kein Beweiskoerper |
| **keine rekursive `spec fn`** | die Linie bleibt, wo sie ist |
| **kein Raten** | der Uebersetzer waehlt nichts; er wendet an, was dasteht |
| **faellt vorhersagbar** | entlaedt das genannte Schema die Pflicht nicht, sagt der Fehler **welches** und **wo** — nicht „unklar" |

**Ein neues Wort** (`induction`), **eine Produktion**, **eine Zeile beim Anwender — und nur dort, wo
Induktion noetig ist.**

---

## Was es am Nutzen kostet, ehrlich beziffert

| | Stufe A mit `by induction on` |
|---|---|
| **Zeilen** | **1 je Beweispflicht, die Induktion braucht.** Wieviele das sind, ist **ungemessen** — die Zahl liefert dieselbe Messung, die als Falsifikator der L3-Entscheidung ohnehin ansteht (17 Logik-Pflichten einordnen) |
| **Begriffe, die ein Anwender lernen muss** | **einer**: ueber welche Struktur die Induktion laeuft. Er muss **nicht** wissen, was ein Induktionsprinzip ist — er nennt eine Domaene, die er ohnehin deklariert hat |
| **Vorhersagbarkeit** | **erhalten**, weil genannt statt geraten |
| **Vertrauensbasis** | **schrumpft** — das Schema ist eine Schablone, geht einmal nach Isabelle |
| **Was es NICHT gibt** | Induktion ueber irgendetwas, das nicht als Struktur deklariert ist; ueber benutzerdefinierte rekursive Funktionen; ueber Programmablaeufe |

**Stufe B kostet mehr als eine Zeile:** wer rekursive `spec fn` schreibt, schreibt Spezifikationen
**mit eigener Terminierungspflicht** — eine andere Faehigkeit, und die Fehlerbilder werden
haeufiger. **Stufe C kostet die Identitaet der Sprache.**

---

## Die Decke verschiebt sich damit — aber nicht bis Gold

Mit Stufe A ist erreichbar: **Sicherheitshuelle + deklarierte Invarianten + induktive Eigenschaften
ueber deklarierten Strukturen.** Das deckt den gemessenen Fall (`revoke`s Nachordnungslemma) und
vermutlich `cdt_wellformed`.

**Es deckt nicht** — und das ist die verbleibende Decke:

* Eigenschaften ueber Strukturen, die **nicht** deklariert sind (der Maschinenzustand, ein
  Zeiger-Bitfeld-PTE),
* alles, was **Ablaeufe** quantifiziert (Lebendigkeit),
* funktionale Korrektheit, deren Argument **nicht** die Form einer Induktion ueber eine deklarierte
  Struktur hat.

- [ ] **Die Zahl fehlt, und sie entscheidet alles:** wieviele der 17 gemessenen Logik-Pflichten
      braeuchten `by induction on`, wieviele kaemen ohne aus, wieviele braeuchten Stufe B oder C?
      **Ein einziger Fall in der letzten Spalte setzt die Decke wieder tiefer.**
