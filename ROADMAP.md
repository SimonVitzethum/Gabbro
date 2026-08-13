# Gabbro — Fahrplan

**Ein** Plan. Bis zum 2026-08-13 standen hier zwei nebeneinander — die Phasen eines engen
Formaterzeugers und die V-Phasen der Vollsprache — ohne Aussage, welcher gilt. Das ist behoben:
gültig ist der unten, die alten Phasen sind darin aufgegangen.

**Jede Phase liefert eine Zahl, die über die nächste entscheidet.** Eine Phase ohne Tor wird nicht
gebaut. Die ersten drei kosten **keinen Übersetzer**.

---

## P0 — Papier. Drei Fragen, jede kann die These töten

Zusammen ein bis zwei Tage, kein Code. **Das ist der billigste Punkt des ganzen Vorhabens.**

### P0.1 — `revoke` in den Konstrukten ausdrücken

`decrement requires` ist eine Vorbedingung **auf einem Feld**. Die Korrektheitsbedingung von
`revoke` ist **strukturell**: ein Teilbaum verschwindet, und dass danach `kind_zeigt_zurueck` und
die Kettenendlichkeit noch gelten, ist eine Aussage über Baumform.

> **Tor:** Geht es, ist Zuschnitt (c) tragfähig und die 0,8 : 1-Vorhersage hält ihre riskanteste
> Annahme. Geht es nicht, bleibt die **gefährlichste** Mutation handgeschrieben — dann kehrt die
> Invariantenerhaltung als Beweisposten zurück, **und die Kennzahl fällt mit ihr**.

### P0.2 — `vtd.rs` als `device`-Block

1 448 Zeilen Rust gegen eine Beschreibung derselben Einheit.

> **Tor:** Faktor ≥ 5 kleiner. Sonst ist die Knappheitsthese widerlegt, und mit ihr der
> Deklarationsgewinn an jeder Stelle.

### P0.3 — `space.rs` zweimal hinschreiben

Als Gabbro-Quelle **und** mit dem, was ein Beweiser darüber hinaus bräuchte. Der richtige Fall, weil
er beides enthält: beschreibende Struktur **und** algorithmisches `revoke`.

> **Tor:** die erste echte Zahl für die Kennzahl, nach dem Protokoll unten. Über 2 : 1 ⇒ Abbruch.

- [ ] **Dazu, unabhängig und ebenfalls Papier: die Basisrate zählen.** Wie viele Formate hat Caprock
      wirklich, wie oft ändern sie sich, wie viele Fehler dieser Klasse sind pro Jahr entstanden
      (aus `done.md` auszählbar)? Fällt sie klein aus, ist das ehrlichste Ergebnis nicht „es geht",
      sondern „die Falle ist zu selten für eine Sprache".

---

## P1 — `check` als Rust-Makrobibliothek, ohne Sprache

Das einzige Konstrukt ohne Vorbild, und es braucht **keinen Übersetzer**. Rückwirkend gegen die 33
Messdisziplin-Fallen gehalten, jede mit Mutation.

> **Tor:** **≥ 5 der 33** rückwirkend gefangen, mit Mutation belegt. Darunter ist `check` Ergonomie
> — und mit ihm fällt die einzige Begründung, die Gabbro allein gehört.

**Nützlich auch dann, wenn Gabbro nie entsteht.** Das ist der Grund, warum diese Phase vor allen
anderen steht.

---

## P2 — Der Kern als PRÜFER, ohne Codeerzeugung

M1 (Bereichstypen) + M2 (lineare, auch geisterhafte Werte) + M4 (kein ungeprüfter Index) als
Typprüfer über einer minimalen Sprache. Noch kein C.

> **Tor:** S1a und S1b sind **nicht formulierbar**, und zwar mit **0 Zeilen** Annotation. Braucht es
> welche, ist Gabbro an dieser Stelle nur ein umständlicheres Verus.

Zusätzlich hier zu zeigen, weil es der einzige Mechanismus ohne vorhandenes Werkzeug ist:

> **Tor 2:** die **Bootphasen-Marke** trägt — eine `roh`-Funktion nach `boot_ende` übersetzt nicht,
> und ein Versuch, die Marke zu kopieren oder herzustellen, ebenso wenig.

---

## P3 — Absenkung nach C, syntaxgesteuert

Ein Modul durch bis zum C, nicht optimierend, plus Differenztest gegen die Rust-Fassung.

> **Tor:** Differenztest grün (gleiche Eingaben, gleiche Ausgaben, gleiche **Absagecodes**) **und**
> Zyklen je Aufruf gegen die handgeschriebene Referenz gemessen. „Dauerhaft langsamer und die
> Ursache nicht behebbar" ist eine Abbruchbedingung.

---

## P4 — M3 und `device`

Adressräume und Zugriffsrechte am Zeiger; `vtd.rs` übersetzt.

> **Tor:** die DMA-Suite bleibt grün, **und vier Mutationen übersetzen NICHT** — die bezahlten
> Fallen 1 (`STE.S1STALLD`), 2 (CD ohne `R`), 4 (`GCMD` als RMW), 5 (x2APIC `EN`+`EXTD`).

---

## P5 — Axiomschicht und Eintritt

Je privilegiertem Befehl ein erklärter Effekt; ein Syscall-Eintritt ohne handgeschriebenen
Assembler.

> **Tor:** die Axiommenge ist **aufgezählt und beziffert** (Ratsche, darf nur fallen), jedes Axiom
> hat einen `falsifier` oder einen benannten Grund, warum keiner fahrbar ist. **Ohne die Zahl ist
> „speichersicher unter A1…An" eine Form ohne Inhalt.**

---

## P6 — `spec fn` / `impl fn` und die erzeugte Verfeinerungspflicht

Der Gold-Mechanismus.

> **Tor:** die Kennzahl an **zwei** Modulen gemessen, beide berichtet (bester und schlechtester
> Fall). Auslösung: bester > 1 : 1 oder schlechtester > 2 : 1.

---

## P7 — Rennfreiheit

Datenrennen aus M2/M3; **Protokollrennen** über lineare Phasen.

> **Tor:** die **D0-Form** ist nicht formulierbar — ein Thread, der lauffähig wird, bevor er seine
> Autorität hat, übersetzt nicht. Das ist der Fall, den jeder Datenrennen-Prüfer der Welt
> durchgelassen hätte.

---

## P8 — Umstellung nach Strangler-Muster

Modul für Modul, **beide Fassungen gleichzeitig lebendig**, Differenztest dazwischen. Nie ein
grosser Schnitt.

> **Abnahme, dreiteilig:** (A) die 14-Punkte-Reihe grün, beide Architekturen, alle RAM-Grössen ·
> (B) Differenztest gegen die Rust-Fassung, Modul für Modul · (C) Wiederholungsmessung mit
> Quervergleich, Nullbefunde mit Stichprobengrösse.
>
> **(B) ist nicht optional:** über die Behebungen von D8, D9 und D10 hinweg blieb die x86-Signatur
> **byte-identisch** (500 Läufe je Stand). Drei echte Kernfehler, keiner ausgelöst.

**Die Prüfsuite ist der LETZTE Umzug, nicht der erste.** Sie ist 15,7 % des Codes und besteht aus
`check`-Zusagen; sie bleibt in Rust, bis die Gabbro-Fassung **gegen sie** bewiesen ist. Wer sein
Messgerät zuerst umbaut, misst den Umbau mit dem Umbau.

---

## Später, ausdrücklich nicht jetzt

* **Binärverifikation** (seL4-Art, erzeugtes C gegen Maschinencode). Der Weg existiert, ist aber ein
  eigenes Projekt — und er ist der einzige, der die Absenkung aus der Vertrauensbasis nimmt.
* **Wiederverwendbare Spezifikationstheorien** (Fähigkeitssystem, Seitentabellen). Sie helfen dem
  **zweiten** Projekt, nicht dem ersten — deshalb dürfen sie in keiner Kostenrechnung mitgezählt
  werden, solange es nur einen Kernel gibt.
* **~~Rust-Ausgabe~~, ~~Ada-Ausgabe~~** — gestrichen am 2026-08-13. Sie waren nur nötig, solange ein
  *fremder* Beweiser den Beweis führen sollte.
* **Seitentabellen-Beschreiber.** Verlockend (das fehlende `US` auf der Zwischenebene wäre nicht
  formulierbar gewesen), aber Seitentabellen sind Hardwareverträge; ein falscher Beschreiber erzeugt
  einen beweisbar korrekten falschen Kernel.

---

## Die Abbruchbedingungen — hier, damit sie nicht verhandelt werden

Gabbro endet, wenn **eines** davon eintritt:

1. **Die Basisrate ist zu klein** (P0) — zu wenige Formate, zu wenige Fehler dieser Klasse.
2. **`check` fängt rückwirkend weniger als 5 der 33 Fallen** (P1). Dann fällt die einzige
   Begründung, die Gabbro allein gehört.
3. **Rust + Verus + Loom decken einen Mechanismus bereits ab.** Für M2 am Sperrbeleg und für M1
   ist das am 2026-08-13 **eingetreten**; übrig bleibt echte Linearität. Tritt es für die auch ein,
   ist der Kern leer.
4. **Die Kennzahl verfehlt ihre Schwellen** (P6): bester Fall > 1 : 1 oder schlechtester > 2 : 1.
5. **Der erzeugte Code ist dauerhaft langsamer** als die handgeschriebene Referenz und die Ursache
   ist nicht behebbar (P3).
6. **Eine Kernel-Logik lässt sich nur ausdrücken, indem die Axiomschicht wächst.** Die Ratsche darf
   nur fallen. Wächst sie, um ein Sprachdefizit zu decken, wird „speichersicher unter A1…An" jedes
   Mal etwas weniger wert — und niemand merkt es, weil die Zusage formal weiter gilt.
7. **Die Umstellung erzwingt einen grossen Schnitt** (P8). Ein Vorhaben, das die Abnahmereihe
   abschaltet, um sich selbst zu bauen, hat keinen Prüfer mehr — und dieses Projekt hat gemessen,
   was dann passiert: zehn Tage rot, ohne dass es jemand sah.

Ein Ordner, der seine eigenen Abbruchbedingungen nicht nennt, wird nie beendet — nur vergessen.

---

## Das Messprotokoll zur Kennzahl — vorab, weil es sonst die Wunschzahl liefert

Die Regeln stehen hier **vor** der Messung, aus demselben Grund, aus dem die IPC-Schwelle von
2000 Zyklen vorab feststeht: eine Schwelle, die man nach dem Ergebnis wählt, ist keine.

**1. Zwei Module, beide berichtet — die Wahl entscheidet sonst das Ergebnis.**

| | Modul | erwartet |
|---|---|---|
| **bester Fall** | der **Manifest-Leser** (`format`) | nahe am Ziel — hier *ist* der Beschreiber die Spezifikation |
| **schlechtester Fall** | ein **(c)-Mutationsmodul** am Cap-Space | deutlich darüber — Schleifeninvarianten, Ghost-Code, Hilfslemmata |

**Nur den ersten zu berichten ist die Manipulation**, und sie braucht keine Absicht: man misst das
Modul, das fertig ist.

**2. Zählregel für den Zähler — Beweiscode IST Spezifikation.** Was der nachgelagerte Beweiser
zusätzlich braucht, zählt mit: **Schleifeninvarianten, Ghost-Code, Hilfslemmata, `assert`-Ketten,
ACSL-Annotationen**. Wer nur den Gabbro-Beschreiber zählt, misst die halbe Last — und genau die
Hälfte, die bei (c) explodiert.

**3. Zählregel für den Nenner — GABBRO-CODE.** Nicht die handgeschriebene Rust-Referenz: gemessen
wird, ob ein **in Gabbro geschriebener** Kernel billig zu verifizieren ist; Rust kommt darin nicht
vor. **Die Trennlinie ist die Laufzeitwirkung:** was der Übersetzer vor der Codeerzeugung löscht,
ist Spezifikation; was im erzeugten C ankommt, ist Code. Gezählt wird in **Anweisungen**, nicht in
Zeilen — sonst gewinnt geschwätziger Code. Und wer eine Eigenschaft zur Laufzeit **prüft** statt
sie zu beweisen, verschiebt Zeilen nach unten: erlaubt, aber die Laufzeitmessung gehört daneben.

**4. Die Stufe steht dabei.** Ob Sicherheitshülle, deklarierte Invarianten oder funktionale
Korrektheit gemessen wurde, gehört neben die Zahl — die 20 : 1 von seL4 ist eine Zahl für die
**stärkste** Stufe. Ein Verhältnis ohne Stufe vergleicht über eine Kluft.

**5. Der Beweisweg IST entschieden** (2026-08-13): Gabbro prüft selbst, Ausgabe ist C + iasm, kein
nachgelagerter Beweiser. Damit fällt die ACSL-Last aus dem Zähler und die Entsprechungspflicht weg.
**Was stattdessen in den Zähler gehört:** `spec fn`-Zeilen und die Verfeinerungsannotationen — und
das ist bei einem Kernel der Boden, der die 1 : 1 unerreichbar macht (§3c dort).

**Auslösung:** Liegt der beste Fall über 1 : 1 **oder** der schlechteste über 2 : 1, ist die
Gold-These widerlegt. Diese zwei Zahlen stehen hier, damit sie nicht später gewählt werden — und sie
sind **schärfer** als die früheren (2 : 1 / 5 : 1), weil der Boden jetzt hergeleitet ist statt
geraten.
