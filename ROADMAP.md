# Gabbro — Fahrplan

**Jede Phase liefert eine ZAHL, und die Zahl entscheidet über die nächste.** Nicht der Vorsatz.
Wer eine Phase ohne ihre Kennzahl abschließt, hat sie nicht abgeschlossen.

Stand: 2026-08-13. **Phase 0 hat noch nicht begonnen.**

---

## Phase −1 — Die zwei Fragen, die VOR Phase 0 stehen

Sie stehen hier, weil Phase 0 sonst die falsche Frage tötet.

**Kennzahl A: die Basisrate.** Wie viele Formate hat Caprock, wie oft ändern sie sich, **wie viele
Fehler dieser Klasse sind pro Jahr wirklich entstanden** — auszählbar aus `done.md`.

- [ ] Zählen, nicht schätzen. „Fünfmal dieselbe Falle" ist bisher **ungezählt** und widerspricht
      der Disziplin, auf die dieser Ordner sich beruft.
- [ ] **Tor:** Fällt die Zahl klein aus (etwa sechs stabile Formate, wenige Fehler), ist das
      ehrlichste Ergebnis **„die Falle ist zu selten für eine Sprache"** — und der Ordner endet
      hier, mit einem Beleg statt mit einem Gefühl.

**Kennzahl B: der Schnitt bei `table`.** Erzeugt Gabbro (a) nur den Prüfer, (b) auch Zugriff,
(c) auch **Mutation**?

- [ ] Entscheiden **und aufschreiben**. Bei (a) fallen S1a und S1b als Abnahmekriterien weg, und
      Phase 4 verliert ihre schärfste Rechtfertigung. Bei (c) besitzt das erzeugte C die
      Datenstruktur — ein Schnittstelleneingriff unter dem Kern-Lock, dessen Aufwand **in keiner
      Phase steht** und geschätzt werden muss, bevor er zugesagt wird.
- [ ] **Und die Folge für Phase 0:** EverParse deckt **ausschliesslich `format`** ab. Liegt der
      Wert bei `table`, kann Phase 0 Gabbro **nicht** erledigen — nur die halbe
      Daseinsberechtigung streichen. Das ist dann in Phase 0 so zu protokollieren, statt als
      Freispruch gelesen zu werden.

**Kennzahl B2: der Zuschnitt hängt am Kostenmodell — beide Fragen sind EINE.**

- [ ] Eine vollständige Invariantenprüfung ist naiv **O(n · Kettenlänge)** über 80 256 Slots;
      `colors.rs` gilt heute mit **42 Ticks** als Schuldposten. Also: **offline** (Diagnostik, kein
      Schutz) oder **inkrementell** — und inkrementell setzt voraus, dass der Prüfer das **Delta**
      kennt, das **nur der Mutator** kennt. **Wer Invarianten im heissen Pfad will, hat (c) schon
      gewählt.** Diese Ableitung gehört in die Entscheidung, nicht daneben.

**Kennzahl C (nur falls das Kernel-Fernziel verfolgt wird): was bietet Gabbro über
Rust-heute und Verus hinaus?** — **nicht** über Low\*; das ist der übernächste Gegner.

- [ ] **Rust, heute**: ein Newtype ohne `Drop`/`Copy` mit versiegeltem Konsumpfad erzwingt für
      diese eine Ressource lineares Verhalten zu **null Sprachkosten** — so ist `Parked` gebaut,
      und es hat eine fünfte Stelle gefunden, die das Gegenlesen übersah.
- [ ] **Verus**: Beweise direkt auf Rust, SMT **ohne** F\*-Kette, keine C-Extraktion nötig —
      **zwei der drei geforderten Belege bei einem vorhandenen Werkzeug**, und lineare
      Ghost-Permissions für Ressourcen-Invarianten.
- [ ] **Verus an `Parked` ausprobieren, bevor der Zweig ein Entwurf wird.** Phase-0-Logik für den
      Zweig: *der nächste Verwandte ist gebaut, der Ordner nicht.*

---

## Phase 0 — Die Vorfrage: gibt es das schon?

**Kennzahl:** eine Ja/Nein-Antwort mit Beleg, nicht mit Eindruck.

**EverParse** (Microsoft Research, F\*) erzeugt verifizierte Parser aus Beschreibern und wird im
Windows-Netzwerkstapel eingesetzt. Es ist der nächste Verwandte, und es ist gebaut, während Gabbro
ein Ordner mit drei Dateien ist.

- [ ] EverParse an **einem echten Caprock-Format** ausprobieren — dem Manifest-Eintrag, weil er
      Versionskopf, reservierte Bytes und eine `where`-Bedingung auf einmal hat.
- [ ] Drei Fragen beantworten: Erzeugt es `no_std`-taugliches C? Sind die Absagen **benannt** oder
      ein gemeinsamer Formfehler? Wie groß ist die Werkzeugkette (F\*-Abhängigkeit im Bauweg)?
- [ ] **Trägt es, ist dieser Ordner erledigt** — und das wäre das beste Ergebnis. Trägt es nicht,
      steht in `TODO.md`, an welchem der drei Punkte es scheiterte, und *das* ist die
      Daseinsberechtigung von Gabbro.

> Diese Phase steht zuerst, weil dieses Projekt einmal einen halben Tag an eine Lücke verloren hat,
> die es nicht gab (`Kani` deckte `sync` längst ab, nur die CI beschrieb sich falsch).

---

## Phase 1 — Ein Format, von Hand, als Maßstab

**Kennzahl:** Zyklen je Aufruf und `.text`-Größe der **handgeschriebenen** Referenz.

Bevor irgendetwas erzeugt wird, muss feststehen, wogegen gemessen wird.

- [ ] Den Manifest-Leser in C von Hand schreiben, so wie ein guter Systemprogrammierer ihn
      schriebe — mit allen Prüfungen, die Gabbro später erzwingen soll.
- [ ] Zyklen je Aufruf messen (Median, ruhige Maschine, TSC), dazu `.text`.
- [ ] **Diese Zahl ist der Maßstab für alles Weitere.** Ein Erzeuger, der 30 % langsamer ist,
      ist gescheitert, auch wenn sein Erzeugnis bewiesen ist — die Alternative wäre dann
      handgeschriebener Code plus Prüfer.

---

## Phase 2 — Der kleinste Übersetzer, der etwas Echtes kann

**Kennzahl:** erzeugtes C gegen Phase 1 — Zyklen **und** Bytes, beide Richtungen genannt.

Umfang bewusst winzig: **nur `format`**, keine Tabellen, keine Aufzählungen.

- [ ] Übersetzer in sicherem Rust (`forbid(unsafe_code)`, benannte Abhängigkeitsliste — dieselbe
      Regel, die Caprock für Handler-Module durchsetzt).
- [ ] Feste Breiten, ausgesprochene Bytereihenfolge, `reserved`-Felder, `where` auf Feldern,
      Versionskopf mit **benannter** Absage je Grund.
- [ ] Erzeugt: C-Header + Quelle, `no_std`-tauglich, ohne Allokation.
- [ ] **Gegen Phase 1 messen.** Ist es langsamer, sagen **warum** — und ob es behebbar ist.
- [ ] Ein **Differenztest** gegen den handgeschriebenen Leser: dieselben Bytes rein, dasselbe
      Urteil raus, über zufällige und über bösartig gewählte Eingaben.

**Tor:** Ist der erzeugte Code langsamer als die Referenz **und** die Ursache nicht behebbar,
endet Gabbro hier. Das wäre ein Ergebnis, kein Scheitern.

---

## Phase 3 — Die Eigenschaft, für die es das alles gibt

**Kennzahl:** Anzahl der Eigenschaften, die **per Konstruktion** gelten, gegen die Anzahl, die
noch eine Prüfung braucht.

- [ ] **Totalität**: kein erzeugter Leser kann endlos laufen. Belegt durch die Grammatik, nicht
      durch einen Test.
- [ ] **Bereichssicherheit**: jeder Versatz steht gegen eine Länge im Geltungsbereich.
- [ ] **Absage statt Deutung**: für jeden Abweisungsgrund ein eigener Code; kein Vorgabezweig.
- [ ] Nachweis, dass die Bereichsprüfungen im erzeugten C **entfernbar** sind (`-O2`-Ausgabe
      lesen, nicht hoffen).
- [ ] **Eine Mutationsprobe je Eigenschaft**: Eigenschaft im Erzeuger absichtlich brechen, prüfen,
      dass genau die zugehörige Zeile fällt. Ein Erzeuger, der nur den gesunden Zustand kennt,
      belegt nichts.

---

## Phase 4 — Das zweite Muster: Tabellen mit Invarianten

**Kennzahl:** Findet der erzeugte Prüfer die zwei bekannten Cap-Space-Fehler?

Das ist die schärfste denkbare Abnahme, weil die Antwort schon feststeht:

- [ ] `table` mit `index into`, `option index`, `chain … bounded by` und `invariant`.
- [ ] Den Cap-Space als Beschreiber ausdrücken.
- [ ] **S1a** — die ungeprüfte `first_child`-Indizierung — **muss** unformulierbar sein.
- [ ] **S1b** — `refcount -= 1` ohne Bedingung — **muss** eine Absage oder ein ausgesprochenes
      `wrapping` verlangen.
- [ ] **S2d** — `priority: u8` gegen `[ListHead; 8]` — **muss** an der Bereichsprüfung scheitern.
- [ ] Findet er sie nicht, ist der Sprachentwurf zu schwach, und das gehört in `TODO.md`.

---

## Phase 5 — Einbau in Caprock, an genau einer Stelle

**Kennzahl:** die Abnahme-Reihe bleibt grün, und die Prüfzeilen sind **byte-identisch**.

- [ ] Ein Format ersetzen — der Manifest-Eintrag, weil er die meisten Absagen hat.
- [ ] Der erzeugte Leser muss dieselben Fehlercodes liefern wie der heutige; die Suiten dürfen
      keinen Unterschied sehen.
- [ ] `tools/eingeschlossenheit.py` muss das erzeugte Modul akzeptieren, ohne dass jemand die
      Regel lockert.
- [ ] **Tor:** Verlangt der Einbau eine Ausnahme in einem Wächter, ist der Entwurf falsch, nicht
      der Wächter.

---

## Später, ausdrücklich nicht jetzt

* **~~DER KERNEL-ZWEIG~~ — ÜBERHOLT am 2026-08-13, und die Zahl, die ihn hier festhielt, ist
  gefahren.** Er stand hier, weil er als einziger „keine Allzwecksprache" aufweichte und am
  weitesten von einer Kennzahl entfernt war. **Sein Tor ist gefahren und er hat es nicht
  bestanden:** Verus drückt „der Aufrufer hält den Lock" heute aus. *Trotzdem* ist der Zweig auf
  Anforderung die **Hauptrichtung** geworden — s. [`VOLLDECKUNG.md`](VOLLDECKUNG.md).
  **Damit ist die Zusage „keine Allzwecksprache" aufgegeben**, ausdrücklich und nicht nebenbei;
  die Abbruchbedingungen dort sind ihr Ersatz.

* **Aufzählungen mit `exhaustive`** — nützlich, aber die kleinste Ersparnis.
* **Seitentabellen-Beschreiber.** Verlockend (das fehlende `US` auf der Zwischenebene wäre nicht
  formulierbar gewesen), aber Seitentabellen sind Hardwareverträge; ein falscher Beschreiber
  erzeugt einen beweisbar korrekten falschen Kernel.
* **~~Rust-Ausgabe~~, ~~Ada-Ausgabe~~ — beide GESTRICHEN am 2026-08-13.** Sie waren nur nötig,
  solange ein *fremder* Beweiser den Beweis führen sollte. **Ausgabe ist C + Inline-Assembler,
  genau eine**; der Beweis liegt auf der Quelle. Damit entfällt die Entsprechungspflicht („bewiesen
  in Rust, ausgeliefert in C"), die hier vorher als offener Konflikt stand.
* **Binärverifikation** (seL4-Art, erzeugtes C gegen Maschinencode). Der Weg existiert, aber er
  ist ein eigenes Projekt.

---

## Die Abbruchbedingungen — hier, damit sie nicht verhandelt werden

Gabbro endet, wenn **eines** davon eintritt:

0. **Die Basisrate ist zu klein** (Phase −1) — zu wenige Formate, zu wenige Fehler dieser Klasse.
   Diese Bedingung steht zuerst, weil sie am billigsten zu prüfen ist und am ehesten zutrifft.
0b. **Das Spezifikationsverhältnis verfehlt sein Ziel deutlich** — *Zeilen Spezifikation je Zeile
   Code*, seL4 als Vergleich **20 : 1** — davon rund **0,5 : 1 abstrakte Spezifikation** und
   **19,5 : 1 Beweis**. Der Boden ist die Spezifikation, nicht 5 : 1. Ziel **≤ 1 : 1**, Vorhersage
   **0,8 : 1**, Auslösung bei **2 : 1** (Herleitung in `VOLLDECKUNG.md` §3c). **Ohne das Protokoll darunter liefert
   diese Bedingung die Wunschzahl**, und zwar ohne dass jemand schummelt.
1. **EverParse trägt** (Phase 0) — **aber nur, wenn der Schnitt bei `table` auf (a) gefallen ist.**
   Bei (b)/(c) deckt EverParse die Frage gar nicht ab, und ein grünes Phase-0-Ergebnis wäre kein
   Freispruch.
2. **Der erzeugte Code ist dauerhaft langsamer** als die handgeschriebene Referenz und die Ursache
   ist nicht behebbar (Phase 2).
3. **Der erzeugte Prüfer findet die drei bekannten Fehler nicht** (Phase 4).

Ein Ordner, der seine eigenen Abbruchbedingungen nicht nennt, wird nie beendet — nur vergessen.

---

## Das Messprotokoll zu 0b — vorab, weil es sonst die Wunschzahl liefert

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
