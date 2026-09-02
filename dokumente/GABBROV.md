# GabbroV — der Prüfer für die Logikpflichten

Status: Entwurf. Keine Zahl gemessen. Zitate aus `SPRACHE.md` und `PFLICHTEN.md` sind
belegt, alles andere ist Vorschlag.

> **Hinweis zur Sprache:** `CLAUDE.md` setzt seit dem 2026-09-01 Englisch für alle
> `.md`-Dokumente im Gabbro-Baum. Dieses Dokument ist deutsch, weil es Gespräch ist. Landet
> es im Baum, gehört es vorher übersetzt — und die Wächtermuster zuerst, nicht danach.

---

## 1. Was Gabbro bereits erledigt, und woher wir das wissen

`SPRACHE.md` §0 sagt es selbst:

> **Gabbro proves everything except logic.**

| | wer | wie |
|---|---|---|
| **Klempnerei** — index, overflow, alias, frame, lock, race, **termination**, phase, leafness, publication | Gabbro | M1–M4, erzeugte Schemata. *No SMT, no solver, no heuristic* |
| **Logik** — *diese* Funktion tut *das Richtige* | der Programmierer | Gabbro **gibt** jede offene Logikpflicht ins Manifest aus |
| **Klempnerei, die auf Logik ruht** (§8.3) | gemischt | fällt konstruktiv, **wird aber als Logik gebucht** |

Terminierung steht in Zeile eins. `M4` verlangt ein Abstiegsmaß, `divergent fn` ist die
ausgesprochene Ausnahme, `by unvisited` und `decreases expr` sind die Notation, und §5.4
hält fest, dass beim `walk` die Tiefe M1-beschränkt ist und die Terminierung des Abstiegs
**konstruktiv** fällt — kein Variant, kein Beweis.

Invarianten ebenso: `table … invariant`, `group`, `maintains`. Sie werden deklariert und vom
Prüfer getragen, nicht von einem Löser gesucht.

**Damit ist der Zuschnitt von GabbroV eng und klar: nur Logik und Annahmen.**

Größenordnung, gemessen an `PFLICHTEN.md` über die zehn Fragmente: **164 K gegen 66 L.**
Rund ein Viertel der Pflichten landet überhaupt bei GabbroV. Die Zahl gilt für dieses
Korpus, nicht allgemein.

---

## 2. Die Schnittstelle existiert schon

`SPRACHE.md` §15 beschreibt das Pflichtenmanifest, das der Compiler je Übersetzungseinheit
ausgibt — und nennt als Adressaten ausdrücklich *„the programmer **or an external tool**"*.

```
obligation revoke.functional   "ensures !exists k in descendants of s: k.used"  offen
assumption vtd_te_effective    falsifiziert(probe_vtd_te)
closed     consuming.schablone "Ordnungserhaltung descendants"                  Fundstelle
```

**GabbroV liest nicht das Gabbro-Programm. Es liest das Manifest.**

Das ist der wichtigste Unterschied zu einem gewöhnlichen Verifizierer und der Grund, warum
das Werkzeug klein bleiben kann: es muss keine Programmsemantik nachbauen, keine
Verifikationsbedingungen aus Kontrollfluss erzeugen, keinen Speicher modellieren. GabbroC
hat die Pflichten bereits ausgerechnet und benannt.

Drei Klassen, drei Aufgaben:

| Manifestklasse | GabbroV |
|---|---|
| `obligation` | gegen die Lean-Spezifikation prüfen — die eigentliche Arbeit |
| `assumption` | Erfüllbarkeit der Annahmenmenge, Vakuität, Probenlage (§5) |
| `closed` | nichts; Fundstelle nur nachhalten |

Der Aufruf ist damit: **Manifest + Lean-Spezifikation → bestanden / widerlegt /
unentschieden.**

---

## 3. Die eine Ausnahme, und sie ist real

§8.3 nennt die dritte Klasse: *„if a plumbing obligation falls only via a logic invariant,
it is booked as logic."* Ohne diese Regel würde *„fällt konstruktiv"* zur bequemen Buchung —
der `depleted_count`-Streit ist genau daran entschieden worden.

Praktisch heißt das: „Gabbro regelt Terminierung und Invarianten" gilt, **außer** wo das
Abstiegsmaß oder die Wiederherstellung auf einer Logikinvariante ruht. Ein `breaking`-Block,
der nicht mit einer erzeugten Operation schließt, erzeugt eine `obligation` — und die landet
bei GabbroV.

Das ist kein Einwand gegen deinen Zuschnitt, sondern seine Präzisierung: GabbroV bekommt
genau das, was das Manifest als Logik bucht, und die Buchungsregel steht bereits fest.

Und §8.3.1 nennt, was `D013` **nicht** prüft: dass die Invariante hier wirklich ruht, dass
der Block sie wiederherstellt, dass `requires I`/`maintains I` darin gesperrt sind. *Ein
`breaking` auf der falschen, aber existierenden Invariante besteht weiterhin.* Wenn GabbroV
irgendwo Wert schafft, der über Bequemlichkeit hinausgeht, dann hier.

---

## 4. Drei Ausgänge, niemals zwei

Automatische Verifikation ist im Allgemeinen unentscheidbar. Ein Werkzeug mit nur bestanden
und nicht bestanden muss im Zweifel raten.

| Ausgang | |
|---|---|
| **bestanden** | Die Pflicht ist erfüllt. Geprüft, nicht vermutet. |
| **widerlegt** | Sie ist es nicht — mit Gegenbeispiel als konkretem Zustand. |
| **unentschieden** | GabbroV kommt nicht durch. Mit Pflichtname und Grund. |

Unentschieden ist derselbe Griff wie „anhalten statt schätzen". Der Ausgang schreibt die
Pflicht als `offen` ins Manifest zurück — der Zustand, in dem sie schon war. Der Ratschen-
mechanismus über Namen läuft weiter, nur mit einem Bearbeiter mehr.

**Solide, nicht vollständig.** Bestanden muss immer stimmen; unentschieden darf oft
vorkommen. Jede Optimierung, die diese Asymmetrie antastet, ist ein Fehler.

---

## 5. Annahmen — der stille Ausfallweg

Die Axiomschicht hat bereits eine Falsifikationsdisziplin: `falsifiziert(probe_…)` gegen
echte Hardware, `unfalsifizierbar("qemu64 hat kein x2APIC")` mit Begründung.

Das prüft die Annahme gegen die Welt. Es prüft sie **nicht gegen sich selbst**, und das ist
eine andere Frage:

**Widerspruch.** Sind die Annahmen untereinander unverträglich, ist jede Pflicht beweisbar.
Alles besteht, nichts sieht falsch aus, und es meldet sich nie. Gegenmittel: für die
Annahmenmenge ein Modell suchen lassen. Kein Modell heißt Ablehnung der Menge, nicht
Benutzung.

**Vakuität.** Auch widerspruchsfreie Annahmen können eine Vorbedingung unerfüllbar machen —
dann gilt die Nachbedingung trivial und die Prüfung sagt nichts.

Beides ist billig und nur früh einbaubar. Es gehört zur selben Klasse wie `W16` und der
abbrechende Messlauf: ein Werkzeug, das plausibel aussieht und nichts misst.

---

## 6. Wer prüft — die Zertifikatsfrage

Automatische Prüfung läuft über SMT. Damit steht sofort: wenn Z3 das Urteil fällt, wozu
dann Lean?

| | |
|---|---|
| **A** — Lean nur Notation, Z3 entscheidet | einfach; aber Z3 steht in der Vertrauensbasis |
| **B** — Lean entscheidet mit Taktiken | saubere Basis, schwache Automatisierung |
| **C** — Z3 sucht, Lean rechnet nach | Automatisierung von A, Basis von B |

**C.** Der Löser liefert ein Zertifikat, Leans Kern rechnet es nach. Kein Zertifikat heißt
unentschieden; ein falsches fällt beim Nachrechnen auf. Z3 steht damit nicht auf der
Vertrauensliste.

Das passt zur Hauslinie: §0 sagt über die Klempnerei *„it compiles" is a function of the
source, not of solver luck*. Für die Logik lässt sich Löserglück nicht ganz vermeiden — aber
man kann verhindern, dass es **geglaubt** wird.

Weil die Klempnerei komplett wegfällt, landen die Formeln in Bitvektor- und linearer
Arithmetik statt in quantorenlastigem Speicherkram. Das sind genau die Theorien mit der
besten Zertifikatslage. Dein Zuschnitt macht C überhaupt erst realistisch.

---

## 7. Die Spezifikationssprache ist ein Fragment von Lean 4

Beliebiges Lean 4 ist abhängige Typtheorie höherer Ordnung; daran scheitert jeder SMT-Löser
sofort. Spezifikationen sind deshalb Lean-Terme eines bestimmten Typs, mit umrissenen
Mitteln: Prädikate über Werten, Ganzzahl- und Bitvektorarithmetik mit Überlaufverhalten,
Aggregation über Tabellendomänen, reine Hilfsfunktionen im übersetzbaren Teil.

Eine Spezifikation außerhalb des Fragments wird **abgelehnt**, nicht approximiert. Der
häufigste Weg, wie solche Werkzeuge unsolide werden, ist eine Übersetzung, die etwas nicht
versteht und es weglässt.

**Ein Bedarf steht schon fest.** «B13» hängt an Aggregation: `refcount == count(s in slots :
s.object == o)` ist die Kernbuchhaltung des Capability-Systems und lässt sich in `pred` nicht
sagen. Auf der Lean-Seite ist Aggregation selbstverständlich — das Fragment muss sie tragen,
sonst wandert dieselbe Lücke nur eine Ebene weiter.

---

## 8. Die eine Semantik

GabbroV prüft Pflichten, die GabbroC erzeugt hat, gegen eine Bedeutung von Gabbro. GabbroCs
Korrektheitsbeweis benutzt ebenfalls eine. **Es muss dieselbe sein.**

Sind es zwei Formalisierungen, die man für gleich hält, ist bestanden gültig in GabbroVs
Modell und die Übersetzung korrekt in GabbroCs Modell, und ein Fehler in der Differenz ist
von beiden unsichtbar.

Weil das Manifest die Schnittstelle ist, verengt sich die Frage angenehm: es muss nicht die
ganze Sprachsemantik übereinstimmen, sondern die **Bedeutung der Pflichttexte**. Das ist ein
kleinerer, schärfer umrissener Gegenstand — und der erste konkrete Arbeitsschritt ist, ihn
für eine Handvoll echter Manifestzeilen aufzuschreiben.

---

## 9. Vertrauensbasis

`SPRACHE.md` §0 benennt die heutige: *„The checker is unverified; the trust sits at three
named places: checker, syntax-directed lowering, one `iasm` emission site."*

GabbroV **ergänzt** diese Liste, es ersetzt sie nicht:

| # | Element | Anmerkung |
|---|---|---|
| 1–3 | Prüfer, syntaxgeleitete Absenkung, die eine `iasm`-Stelle | heutiger Stand, aus §0 |
| 4 | M1–M4 als Träger der Klempnereipflichten | trägt §1; ohne sie ist GabbroV still unsolide |
| 5 | Bedeutung der Pflichttexte im Manifest | klein, durchsehbar, unbeweisbar |
| 6 | Übersetzung Lean-Fragment → SMT | klein halten; Ablehnung statt Approximation |
| 7 | Lean-4-Kern | extern |
| 8 | Die Annahmenmenge | Proben gegen Hardware, Erfüllbarkeit gegen sich selbst |

**Z3 steht nicht darauf** — das ist der Zweck von §6C.

Punkt 4 ist der, den man leicht übersieht. GabbroV darf Alias, Rennen und Terminierung nur
deshalb ignorieren, weil M1–M4 sie tragen. Solange der Prüfer unverifiziert ist, ist
*bestanden* eine Aussage unter der Annahme, dass er stimmt.

---

## 10. Stufen und Tore

| Stufe | Inhalt | Tor |
|---|---|---|
| V0 | Bedeutung der Pflichttexte für eine Handvoll Manifestzeilen festschreiben | schriftlich, gegen echte Zeilen aus `PFLICHTEN.md` |
| V1 | Lean-Fragment, Übersetzung, Ablehnung außerhalb | die 66 L-Pflichten der zehn Fragmente ausdrückbar — oder benannt, welche nicht |
| V2 | Annahmenprüfung: Erfüllbarkeit, Vakuität | Annahmenmenge der zehn Fragmente hat ein Modell |
| V3 | Zertifikatsprüfung in Lean | Anteil mit nachgerechnetem Zertifikat gemessen |
| V4 | Rücklauf ins Manifest, Ratsche über Namen | eine echte `obligation` von `offen` auf `bestanden` |

V1 vor allem anderen, weil es die einzige Stufe ist, die scheitern kann, ohne dass man
Werkzeug baut: wenn sich die vorhandenen 66 Logikpflichten nicht im Fragment sagen lassen,
ist der Zuschnitt falsch, und zwar bevor eine Zeile Code entsteht.

---

## 11. Falsifikatoren

| ID | Bedingung | Folge |
|---|---|---|
| G1 | Ein nennenswerter Teil der 66 L-Pflichten ist im Fragment nicht sagbar | Zuschnitt falsch; Fragment oder Erwartung neu |
| G2 | Zertifikatsabdeckung bleibt niedrig | §6C trägt nicht; Wahl zwischen Z3 in der Basis und schwacher Automatisierung |
| G3 | Anteil *unentschieden* bleibt hoch | kein Knopfdruckwerkzeug, sondern ein Vorsortierer |
| G4 | Eine bestandene Pflicht erweist sich als falsch | Solidität gebrochen: Pflichtbedeutung, Übersetzung oder M1–M4 |
| G5 | Die Annahmenmenge hat kein Modell | alle bisher bestandenen Pflichten sind ungeprüft |

G4 ist der, der nicht von allein auffällt — dieselbe Klasse wie der abbrechende Messlauf und
wie `W16`. Er braucht Stichproben gegen echtes Verhalten, nicht gegen das Werkzeug.

---

## 12. Offene Fragen

1. Wie viele der 66 L-Pflichten sind im Fragment sagbar? **Das ist die erste Messung und sie
   braucht kein Werkzeug** — die Pflichttexte stehen in `PFLICHTEN.md`, man kann sie einzeln
   in Lean aufschreiben und zählen, wie weit man kommt.
2. Trägt das Fragment Aggregation? «B13» hängt daran.
3. Wie verhält sich die Bedeutung der Pflichttexte zu dem, was die Isabelle-Beweise
   annehmen? Entscheidet §8.
4. Welche Caprock- und Velve-Einheiten bekommen GabbroV, welche nicht? Produktentscheidung.
