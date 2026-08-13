# Gabbro

**Eine eigene Sprache, die seL4-Beweise leicht macht.** Ausgabe: **C + Inline-Assembler**, genau
eine. Übersetzer in **sicherem Rust** (`forbid(unsafe_code)`).

Der Zweck ist nicht, eine weitere Sprache zu haben. Er ist, einen **Kernel darin zu schreiben und
ihn dann billig formal zu verifizieren** — Caprock vollständig, mit grüner Abnahmereihe.

## Drei Zusagen, drei verschiedene Stärken

Die Unterscheidung ist die ganze Ehrlichkeit dieses Ordners.

| | Zusage | Status |
|---|---|---|
| **1** | **Speichersicherheit** — kein Zugriff ausserhalb, kein Gebrauch nach Freigabe, kein Alias, der eine Zusicherung bricht | **Gabbro beweist es selbst** — unter benannten **Hardware-Annahmen** und unter Vertrauen in Prüfer und Absenkung |
| **1b** | **Unsicherer Bootcode läuft nach dem Boot nie wieder** | **beweisbar, zweistufig**: eine **lineare** Marke (nicht kopierbar — das kann Rust nicht) *und* der `.boot`-Abschnitt wird im selben Zug abgebildet. Falsifizierbar: eine Sonde dorthin muss faulten |
| **2** | **Rennfreiheit** — Datenrennen **und** Protokollrennen | **später, aber JETZT eingeplant.** Nachträglich ändert sich jede Signatur, die geteilten Zustand anfasst |
| **3** | **Funktionale Korrektheit (Gold)** | **Gabbro beweist sie NICHT — es macht sie billig.** Der Mechanismus ist die These des Ordners |

> **Zusage 1 gilt nur relativ.** „Speichersicher" heisst für einen Kernel notwendigerweise
> *speichersicher, WENN die MMU tut, was ihr Modell sagt* — der Kernel schreibt seine eigenen
> Seitentabellen. Deshalb ist die Annahmenmenge **Teil des Satzes**: das Erzeugnis trägt
> „**speichersicher unter A1…An**", maschinenlesbar.

## Die Kennzahl, an der alles hängt

*Zeilen Spezifikation je Zeile **Gabbro**-Code* — Spezifikation ist, **was keine Laufzeitwirkung
hat**; alles, was im erzeugten C ankommt, ist Code.

| | |
|---|---|
| seL4 (Isabelle über C) | **20 : 1** — davon rund **0,5 : 1 abstrakte Spezifikation**, **19,5 : 1 Beweis** |
| **Boden** (nimmt keine Sprache weg) | **≈ 0,5 : 1** |
| **ZIEL** | **0,5 : 1 — der Boden.** Das heisst nicht „wenig Beweis", sondern **kein handgeschriebener Beweis**: geschrieben wird die abstrakte Spezifikation, sonst nichts |
| **Abbruch** (etwas ganz anderes) | **> 3 : 1** — dort ist der Beweis wieder der dominierende Posten, und die Prämisse „billig" ist widerlegt |

**Das Ziel ist bewusst der theoretische Boden, nicht ein erreichbarer Kompromiss.** Damit misst die
Kennzahl den **Abstand** statt zu urteilen: jede Zehntelstelle über 0,5 ist ein benennbarer
Beweisposten, der noch von Hand geschrieben wird. Eine Zahl, die man treffen kann, sagt „bestanden";
eine Zahl am Boden sagt, **was noch fehlt**.

**Die Rechnung ist unbarmherzig:** braucht auch nur 5 % des Kernels handgeschriebene funktionale
Beweise zu 5 : 1, sind das allein +0,25. Daraus folgt der ganze Entwurfsauftrag — Invarianten an der
Struktur statt an der Schleife, algorithmische Rümpfe als Traversierungen, und der Rest
verschwindend klein. Herleitung und Messprotokoll in [`PLAN.md`](PLAN.md).

Stand: 2026-08-13. **Nichts davon ist gebaut.** Was gemessen ist, steht als gemessen da; alles
andere ist ausdrücklich Absicht.

---

## Wo was steht

| Datei | Inhalt |
|---|---|
| `README.md` | dies — Zweck, Zusagen, Kennzahl, Stand, Einstieg |
| [`SYNTAX.md`](SYNTAX.md) | **die Schreibweise**: Grammatik, geschlossener Wortschatz, fünf Entscheidungen, was es absichtlich nicht gibt |
| [`SPRACHE.md`](SPRACHE.md) | **die Mechanismen**: vier Mechanismen, zwei Deklarationsregeln, Bootphase, Rennfreiheit, Kernel-Vollständigkeit — und die Bibliotheksschicht darüber |
| [`PLAN.md`](PLAN.md) | **der Plan**: was 0,5 : 1 verlangt, die Evidenz, acht Phasen mit Toren, Messprotokoll, Abnahme, Abbruchbedingungen |
| [`TODO.md`](TODO.md) | **ausschliesslich Offenes** |
| [`HISTORIE.md`](HISTORIE.md) | **was an diesem Entwurf schon falsch war**, mit Lehre |
| [`P0-2-3-DEVICE-UND-SPACE.md`](P0-2-3-DEVICE-UND-SPACE.md) | **beide Tore gefallen** — `device` deckt 21 % von `vtd.rs` und ist dort 2× knapper, nicht 15×; und **65,1 % des Kernels brauchen handgeschriebene Spezifikation, nicht 10 %** |
| [`P0-1-REVOKE.md`](P0-1-REVOKE.md) | **das erste gefahrene Papiertor.** `revoke` ist ausdrückbar — mit einem Konstrukt, das fehlte; und es hat einen Fehler in der Zählregel gefunden |
| `pruefe-syntax.sh` | hält alle Beispiele gegen die geschlossene Wortliste, mit Sprechprobe |
| [`fallen-klassifikation.tsv`](fallen-klassifikation.tsv) | die 100 bezahlten Caprock-Fallen, einzeln klassifiziert; `./zaehle-fallen.sh` leitet die Zahlen ab |

> **Berichtigungen stehen bewusst vor allem Weiteren.** Zwei Überschreibungen („per Konstruktion
> beweisbar", „Gold-Beweis billig"), ein falscher Nenner, ein zu hoher Boden, zwanzig Konstrukte
> statt vier Mechanismen — alle samt Lehre in [`HISTORIE.md`](HISTORIE.md). Der Ordner behält seine
> widerlegten Fassungen, weil er sonst aussähe, als hätte er von Anfang an recht gehabt.

---

## Der Stand — was gemessen ist, und was es sagt

**Gegen Gabbro:**

* **Verus findet S1a und S1b am echten Cap-Space, für 0 Zeilen Annotation** (2026-08-13). Ein
  Schalter; das Delta über die ganze Datei sind 24 Zeilen, davon 21 Attribute und **kein
  Funktionsrumpf**. Die These „SPARK fand etwas, das Verus nicht kann" ist damit erledigt: es war
  die **Voreinstellung**, nicht die Sprache.
* **„Der Aufrufer hält den Lock" ist in Verus ausdrückbar** — `tracked`-Zeuge, drei Aufrufer, drei
  verschiedene Ausgänge, `no_std`, kein Byte im Erzeugnis. Der schwerste Einzelposten der
  Kernel-Liste, und er ist **kein Alleinstellungsmerkmal mehr**.
* **Die sieben Konstrukte der Bibliotheksschicht decken ≤ 9 % von Caprock** (hart 4,6 %).

**Für Gabbro:**

* **`tracked` ist affin, nicht linear.** Wer den Zeugen fallenlässt, kommt durch — SPARKs
  automatische Leckprüfung hat Verus nicht, Rust auch nicht. **Echte Linearität ist der einzige
  Mechanismus, den kein vorhandenes Werkzeug liefert**, und an ihm hängen die Bootphase, `Parked`
  und die lineare Prüfpflicht.
* **Von 100 bezahlten Caprock-Fallen sind 36 % sprachlich adressierbar, 36 % Messdisziplin.** Das
  stärkste Einzelkonstrukt ist **`check` mit 33 getöteten Fallen** — und es hat in Rust, SPARK,
  Verus, F\* und ATS **kein Vorbild**.
* **15,7 % von Caprock sind Prüf- und Berichtsgerüst** — der Teil, der die Fehler gefunden hat, und
  keine dieser Sprachen sagt etwas darüber.

**Daraus die Reihenfolge in [`PLAN.md`](PLAN.md):** zuerst Papier, dann `check` **ohne
Sprache**, dann der Kern. Nichts davon kostet einen Übersetzer, und jedes kann die These töten.

---

## Warum der Name

**Gabbro ist der plutonische Zwilling des Basalts**: dieselbe Zusammensetzung, langsam abgekühlt —
grosse, regelmässige Kristalle statt feinem Gefüge. Das Wort ist in Deutsch und Englisch identisch
und passt zu Caprock (beides magmatisch); *Basalt*, der erste Vorschlag, ist bereits von einem
Übersetzer belegt.

- [ ] **Nachprüfen, nicht glauben.** „Ich habe nichts gefunden" ist ein Nullbefund ohne Grösse. Vor
      der ersten Veröffentlichung eine Suche über Paketregister, GitHub und Sprachlisten — mitsamt
      dem, was gefunden wurde.

---

## Warum C + Inline-Assembler als Ziel

* **Zwei Verbraucher ohne Umweg**: Rust bindet C über FFI, SPARK ebenso.
* **Binärverifikation existiert als Weg**: seL4 beweist den *übersetzten* Code gegen das C.
* **Vorhersagbarer Codegen** — geradliniger Code, keine Halde, keine versteckte Kontrolle.
* **Der Inline-Assembler ist keine Schwäche des Ziels, sondern die Bedingung dafür, dass es EINES
  bleibt.** Der Eintrittspfad (`iretq`/`eret`, Registerabdruck) ist in C nicht ausdrückbar; ohne
  `iasm` bräuchte es eine zweite Ausgabe für genau ihn.

### Damit löst sich eine Entsprechungspflicht auf

Eine frühere Fassung nannte **drei** Beweiswege (Frama-C über dem C, Verus über einer Rust-Ausgabe,
GNATprove über Ada) und handelte sich damit **zwei Ausgaben** ein: bewiesen die eine, ausgeliefert
die andere. Mit „Gabbro prüft selbst, Ausgabe ist C + iasm" gibt es **eine**. Der Beweis liegt auf
der **Quelle**, das C ist Codeerzeugung — die Low\*-Anordnung, und sie ist billiger.

Das Vertrauen verschwindet nicht, es **wandert an benannte Stellen**:

| | |
|---|---|
| **Der Prüfer** | Gabbros Typprüfer ist selbst unverifiziert. „Bewiesen" heisst „bewiesen unter Vertrauen in ihn" — wie bei jedem Typsystem |
| **Die Absenkung** | **syntaxgesteuert und nicht optimierend**, sonst ist die Entsprechung Quelle↔C wieder offen. Zugleich die Bedingung dafür, dass ein Gold-Beweis billig wird |
| **Die Axiomschicht** | je privilegiertem Befehl ein erklärter Effekt. **Der grösste unbewiesene Posten der ganzen Sprache**, grösser als der Übersetzer |
| **Der `iasm`-Anteil** | aus einer Beschreibung emittiert, nicht je Fundstelle geschrieben: **eine Emissionsstelle statt 161** |

### Leistung ist ein Entwurfsziel, kein Nachgedanke

Keine Allokation · Bereichsprüfungen, die der C-Übersetzer entfernen kann, weil jeder Versatz gegen
eine Länge im Geltungsbereich steht · `restrict` aus der Struktur · geradlinig statt schleifend, wo
die Länge konstant ist · **und jede erzeugte Einheit bringt eine Messzeile mit** (Zyklen je Aufruf
gegen eine handgeschriebene Referenz). Ohne die Gegenzahl ist „schnell" ein Gefühl.

**Der Preis steht daneben:** eine nicht optimierende Absenkung verschiebt die Optimierung in den
C-Übersetzer, und die ist dann **nicht** Teil der Zusage — dieselbe Grenze, an der seL4 die
Binärverifikation ansetzt.

---

## Der Übersetzer — und der Kanal für den Wunschform-Beweis

**In sicherem Rust**, `#![forbid(unsafe_code)]`, ohne Abhängigkeiten ausserhalb einer benannten
Liste — dieselbe Regel, die Caprock für seine Handler-Module durchsetzt. Ein Erzeuger, der selbst
ausbrechen kann, macht die Eigenschaft seines Erzeugnisses wertlos. **Kein Selbst-Hosting:** ein
Erzeuger, der sich selbst übersetzt, verliert seinen unabhängigen Prüfer.

> **Der Erzeuger emittiert nicht nur Code, sondern auch die Verträge, die geprüft werden.** Ein
> Erzeuger, der versehentlich abgeschwächte Verträge ausgibt, liefert einen **grünen Beweis über
> eine schwächere Aussage** — wörtlich „ein Beweis, der die Wunschform beweist".

| Mutation im Erzeuger | wer fängt sie |
|---|---|
| **Code** abgeschwächt, Vertrag bleibt | die **Prüfung** fällt |
| **Vertrag** abgeschwächt, Code bleibt | nur eine **Mutationsprobe auf der Annotationsemission** |
| **beide** stimmig abgeschwächt | **kein Beweis** — nur der **Differenztest gegen die Handschrift** |

Damit hat der Differenztest eine benannte Aufgabe statt der Rolle eines allgemeinen Netzes: **er ist
das einzige, was einen stimmig abgeschwächten Erzeuger fängt.**

---

## Was Gabbro **nicht** löst

* **Falsche Beschreiber.** Gabbro zeigt, dass der Code dem Beschreiber entspricht — nicht, dass der
  Beschreiber der Wirklichkeit entspricht. Wer die Bytereihenfolge falsch aufschreibt, bekommt einen
  makellosen falschen Leser; wer ein Registerhandbuch falsch liest, einen makellosen falschen
  Treiber.
* **Hardware-Zusagen.** `assume`/`falsifier` macht sie **zählbar**, nicht wahr. Eine bestandene
  Sonde prüft *diese* Maschine, *diese* Konfiguration, *diesen* Augenblick.
* **Fortschritt.** Aushungern und Lebendigkeit (Caprocks D8) fallen unter **keinen** Mechanismus.
* **Werkzeug und Prozess.** Gemessen **18 %** der bezahlten Fallen: CI im Format des falschen
  Servers, `.git/info/exclude`, `grep -q` unter `pipefail`, zwei Suiten mit verschiedenem Aufbau.
* **Bedeutung.** Gemessen **10 %**: ein fehlendes `US`-Bit auf der Zwischenebene, „unten zuerst" als
  Zufall der Grössenrelation, eine Wachseite, die einen Farbstreifen sprengt. **Fehler über
  Bedeutung, nicht über Form** — gefunden hat die alle die Messdisziplin.

**Die Obergrenze für den Sprachanteil ist damit 72 %, nicht 100 %.**

---

## Verwandtschaft — und der eigene Vergleich, gefahren statt behauptet

| Projekt | was es kann | was hier fehlt |
|---|---|---|
| **F\*/Low\*** | Gold, extrahiert nach C, in HACL\* ausgeliefert | Allzwecksprache — die Spezifikationslast bleibt |
| **Verus** | Beweise auf Rust, `no_std`, Geisterwerte ohne Laufzeitkosten | **echte Linearität** (`tracked` ist affin); Werkzeugreife (vier Abstürze, versiegelte vstd-Schnittstelle, fehlende Iterator-Spezifikationen) |
| **GNATprove/SPARK** | jede Indizierung und Arithmetik als Pflicht, **automatische** Leckprüfung | keine Ausdrucksform für „der Aufrufer hält den Lock"; dynamische Strukturen schwach; Linearität hängt an einer **Allokation** |
| **EverParse, Kaitai, P4** | Parser aus Beschreibern | nur die `format`-Hälfte |
| **ATS** | lineare Typen + Beweise, kompiliert nach C | der nächste Verwandte für den Kern — und **ungeprüft**, s. `TODO.md` |

**Der Verus-Vergleich ist gefahren und ging gegen diesen Ordner aus** (2026-08-13, oben unter
„Stand"). Was übrig bleibt, ist keine Ausdrucksfrage, sondern **echte Linearität plus
Werkzeugreife** — und Reife bezahlt man mit Beiträgen an Verus, nicht mit einer Sprache. **Diese
Frage steht offen und ist die teuerste des Ordners.**

---

## Wie es weitergeht

[`PLAN.md`](PLAN.md) — acht Phasen, jede mit einem Tor. Die ersten drei kosten
**keinen Übersetzer** und können die These jeweils töten:

1. ~~**`revoke` auf Papier**~~ — **gefahren 2026-08-13**, [`P0-1-REVOKE.md`](P0-1-REVOKE.md):
   bedingt bestanden, Bedingung ist ein fehlendes Konstrukt. **Kein weiterer Entwurfstext vor 2.**
2. ~~**`vtd.rs` als `device`-Block**~~ — **gefahren, GEFALLEN**: Faktor 2,0 auf dem gedeckten Teil.
3. ~~**`space.rs` zweimal**~~ — **gefahren, über der Abbruchmarke**: 3,6–6 : 1 ausgeschrieben.
4. **`check` als Rust-Makrobibliothek**, rückwirkend gegen die 33 Messdisziplin-Fallen gehalten —
   **der einzige Posten, der die Messungen von heute überlebt hat.**
