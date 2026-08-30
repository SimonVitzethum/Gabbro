# Der Verifikationspfad als eigenständiges Werkzeug

*Geschrieben am 2026-08-28. **Ausgeplant, nicht gebaut** — kein Schritt hieraus ist ausgeführt.*

> **Der Gegenstand in einem Satz:** ein Werkzeug, das ein **beliebiges** Gabbro-Programm und eine
> **von Hand geschriebene Lean-4-Spezifikation** nimmt und entscheidet, ob die Logik des
> Programms der Spezifikation entspricht — **unabhängig von Übersetzer und Prüfer.**

Das ist ein anderes Erzeugnis als der Prüfer, und es ist heute keines: es ist ein Unterbefehl.
*Der Unterschied zwischen beidem ist der ganze Inhalt dieses Plans.*

---

## 0. Zwei Kanäle, die verwechselt werden

**Es gibt heute zwei Wege nach Lean, und sie werden regelmäßig füreinander gehalten.** Sie haben
verschiedene Gegenstände, verschiedene Zahlen und verschiedene Zukunft.

| | **Kanal A** | **Kanal B** |
|---|---|---|
| Befehl | `gabbro pflichten --lean` | `gabbro lean a.gab b.gab` |
| Was gesagt wird | Gabbros **eigene** `ensures`/`requires` | eine **Lean-Spezifikation von Hand** |
| Wer sagt es | die Sprache | ein Mensch, in Leans Mitteln |
| Stand | ~~71 Pflichten, **4 Sätze**, 67 abgesagt~~ **75 Pflichten, 9 Sätze, 66 abgesagt** (2026-08-30) | 4 Rümpfe, **5 Spezifikationen**, 5 Giftproben |
| Wächter | `pruefe-lean-beweis.sh` | `pruefe-lean-programm.sh` |

**Dieser Plan handelt ausschließlich von Kanal B.** Kanal A bleibt, was er ist — ein Maß dafür,
wie viel die Sprache über sich selbst sagen kann. *Er kann nicht mehr sagen als die Sprache
kennt, und genau darum ist er nicht der Verifikationspfad.*

Der Beleg dafür steht in `programmlogik/beispiel/Spec.lean` und ist mit einer Zeile abzulesen:
**Spezifikation 2 ist ein Quantor** — *„`raeumen` fasst KEIN anderes Fach an"* —, und eine
`spec fn` in Gabbro kann das nicht ausdrücken. **Die Rahmenbedingung ist der Grund, warum es
Kanal B gibt.**

---

## 1. Der Stand, gegen den geplant wird

Alles am 2026-08-28 gemessen, jede Zahl mit dem Befehl daneben.

```
$ ./instrumente/pruefe-lean-programm.sh
   @program 1  units 2  routines 4  bodies 4  refused 0  places 4
   eine handgeschriebene Spezifikation geht durch:  ja  (5 Saetze)
   jede vergiftete faellt:                          ja  (5 von 5)
   ein nicht erklaerter Ort wird benannt:           ja  ->  Faecher.gewicht
== LEAN PROGRAM: 4 bodies from 2 files, 5 hand-written specifications, LEAN GREEN ==

$ for f in beispiele/*.gab messung/*/*.gab; do ./target/debug/gabbro lean "$f"; done | …
   routines 277   bodies 89   refused 188        -> 32 %
   ohne die 93 Fremdruempfe:  89 von 184         -> 48 %
```

**Der Mechanismus ist fertig und in beide Richtungen belegt. Was fehlt, ist Reichweite und
Unabhängigkeit** — und die zweite ist die, die niemand gemessen hat.

---

## 2. Was „unabhängig" heißt — und was heute dagegen steht

Drei Abhängigkeiten. Die erste ist die härteste, und sie ist keine Reichweitenfrage.

### 2.1 Der Export ist an das Urteil des Prüfers gebunden

`lean.rs` liegt in `crates/gabbro-check` (1834 Zeilen); der Unterbefehl steht in
`crates/gabbro-cli/src/main.rs`:246. Und `zaehle-lean.py`:135 sagt die Regel:

> *„A unit with errors carries no register."* — **23 von ~~70~~ 93 Einheiten**
> (nachgezogen 2026-08-30: die **23** stimmt weiter, der Nenner war die Zahl der
> Einheiten von damals).

> **Ein Verifizierer, der nur verifiziert, was der Prüfer schon durchgelassen hat, verifiziert
> das Falsche.** Der Prüfer ist damit eine *Vorbedingung* geworden, wo er eine *unabhängige
> zweite Meinung* sein sollte. Dieselbe Klasse wie W7, nur in der Zeit statt im Raum: zwei
> Register über derselben Sache, hintereinandergeschaltet statt nebeneinander.

*Der schärfste Fall ist der, für den man einen Verifizierer überhaupt will:* ein Programm, bei
dem der Prüfer und die Spezifikation **uneins** sind. Heute kommt es nicht bis zur Frage.

### 2.2 Ein Teil der Absagen ist Prüferwissen, nicht Sprachlücke

Die Absageliste vermengt zwei Sorten, und die Zahlen unten sind darum **noch nicht** die
Arbeitsmenge:

| Sorte | Absagen | |
|---|---|---|
| **echte Sprachlücke** | `loop` 24 · `call-not-compositional` 17 · `non-local-exit` 2 · `result-in-ensures` 1 | die Semantik kennt die Form nicht |
| **Prüferwissen** | `carrier-not-a-table` 15 · `no-shape-for-field` 6 · `spec-not-an-expression` 0 | Typ- und Gestaltwissen, das aus den Pässen kommt |
| **noch zu sortieren** | `narrow` 6 · `match-not-option` 5 · `let-else` 5 · `call-in-expression` 5 · `other-value` 2 · `observe` 2 · `float` 2 | |

**Die Einteilung ist eine Vermutung und wird gemessen, nicht übernommen** (W10). Sie ist der
erste Schritt, weil jede folgende Zahl an ihr hängt.

### 2.3 `foreign-body` (93) ist in einem unabhängigen Verifizierer **keine Absage**

**Das ist die größte Einzelbewegung dieses Plans, und sie kostet keinen Beweiser.**

`Spec.lean` zeigt die Form schon, in Spezifikation 5: die Umgebung `ρ` ist ein **Parameter** des
Satzes und keine Definition — *„eine festgelegte Umgebung wäre der Erzeuger, der entscheidet, was
ein Gerufener tut."* Der Rufer wird aus dem **Vertrag** bewiesen, ohne den Rumpf je anzusehen.

Damit ist ein fremder Rumpf nicht *„nicht verifizierbar"*, sondern *„verifizierbar unter einem
benannten Vertrag, den der Mensch hinschreibt."*

> **93 Absagen werden zu 93 benannten Annahmen** — und der Unterschied ist nicht kosmetisch:
> **eine benannte Annahme steht im Zeugnis, eine Absage nicht.** Wer das Ergebnis liest, sieht,
> worauf es ruht. Genau das ist die Bewegung, die `Table_Absenkung.thy` an seiner Zeile 36
> *nicht* macht.

**Und der Riegel dazu, sonst ist es ein Rückschritt:** ein Vertrag ist eine **Hypothese**,
niemals ein Axiom. Wer ihn in die Umgebung einträgt statt in die Voraussetzung des Satzes, hat
einen Beweiser gebaut, der jeden Unsinn schließt, sobald ein Vertrag falsch ist. `Body.lean`:391
sagt es an genau dieser Stelle über fremden Code.

---

## 3. Die vertrauenswürdige Basis — heute nirgends aufgeschrieben

Damit ein grünes Ergebnis etwas heißt, muss man **vier** Dingen trauen:

| | | Umfang |
|---|---|---|
| 1 | der **Parser** — Quelle → Baum | `crates/gabbro-syntax` |
| 2 | der **Export** — Baum → Datum von `Gabbro.Body` | `lean.rs`, 1834 Zeilen |
| 3 | die **Semantik** | `programmlogik/Gabbro/Body.lean`, 642 Zeilen |
| 4 | der **Lean-Kern** | fremd, und das ist in Ordnung |

**Und ausdrücklich NICHT: die Pässe des Prüfers.** Heute stimmt das nicht (2.1), und **die Liste
hat nie jemand hingeschrieben.** Ein Verifizierer ohne aufgeschriebene vertrauenswürdige Basis
verkauft eine Zusage, deren Preis niemand kennt.

**Zeile 2 ist die unbewiesene.** *Dass das exportierte Datum das Programm IST, steht in keinem
Satz* — wörtlich dieselbe Lücke wie bei der Absenkung, nur eine Ebene höher und mit einem
**viel kleineren Gegenstand**: 1834 Zeilen gegen eine Sprachdefinition.

Und dieselben **drei** Formen stehen zur Wahl wie dort:

* **beweisen** — den Export gegen Parser und Semantik verifizieren;
* **ersetzen** — den Export so klein machen, dass er zu lesen ist;
* **Zeugenpaare** — je Lauf ein wegwerfbarer Beleg, dass Export und Quelle dasselbe sagen.

*Hier ist die dritte Form voraussichtlich die richtige, und der Grund ist die Größe:* ein
Rückübersetzer, der aus dem Datum wieder Gabbro schreibt, und ein Vergleich gegen die Quelle sind
zusammen kleiner als der Beweis — **und sie fallen laut.**

---

## 4. Die Schritte

**V1 — Die Absageliste zerlegen.** *Reine Messung, kein Bau.* Je Absagegrund: kommt er aus der
Semantik oder aus dem Prüfer? **Zuerst, weil jede folgende Zahl daran hängt.** Ergebnis ist eine
Tabelle, kein Code.

**V2 — Den Export vom Prüferurteil lösen.** Ein Programm mit Prüferfehlern muss ein Register
bekommen. Die 23 Einheiten sind die Messgröße; sie muss auf 0 fallen, **oder der Rest muss
benannt sein** (z. B. ein Programm, das nicht parst — *dort ist die Abhängigkeit echt*).
*Die Grenze zwischen „parst nicht" und „gefällt dem Prüfer nicht" ist der ganze Schritt.*

**V3 — `foreign-body` von der Absage zur benannten Annahme.** Der Mensch schreibt den Vertrag,
das Werkzeug führt ihn **im Zeugnis**. Riegel: Hypothese, nie Axiom (2.3). *Größter Zugewinn an
Reichweite im ganzen Plan, und er braucht keine neue Sprachform.*

**V4 — Die vertrauenswürdige Basis aufschreiben**, mit Zeilenzahlen und mit dem, was **nicht**
dazugehört. *Ein Absatz, der heute fehlt und ohne den keine Zahl aus diesem Kanal zitierbar ist.*

**V5 — Die Treue des Exports.** Zeugenpaare nach §3: Rückübersetzung und Vergleich. **Erst nach
V2**, sonst misst man die Treue eines Exports, den es so nicht mehr gibt.

**V6 — Den Wächter in die Abnahme.** `pruefe-lean-programm.sh` und `pruefe-lean-beweis.sh` laufen
heute in **keinem** Sammellauf; §1.7 des autonomen Plans führt sie nicht, und sie können dort so
nicht stehen, weil die Abnahme auf `ki-pc-fisch-101` läuft und **Lean nur lokal liegt**.
Entweder eine `elan`-Kette auf den Server, oder eine ausgeschriebene Zeile, dass dieser Pfad
außerhalb der Abnahme steht. *Solange keins von beidem gilt, ist ein Rückschritt hier für jeden
Schritt unsichtbar.*

**V7 — Eine Spezifikation über einer Korpusdatei**, die **nicht** für diesen Kanal geschrieben
wurde. Heute stehen die fünf über `beispiel/lager.gab` und `beispiel/betrieb.gab` — `refused 0`,
und das ist kein Zufall: *die zwei Dateien wurden für ihn geschrieben.* **Das ist Falle 80 eine
Ebene tiefer**, dieselbe Struktur wie beim zweiten Korpus. Bedingung, unter der V7 zählt: die
Datei war vorher da.

**Reihenfolge und Abhängigkeit:** V1 → V2 → {V3, V5} → V7. V4 und V6 hängen an nichts und sind
die billigsten; **V6 ist der billigste Posten mit der größten Wirkung**, weil er verhindert, dass
die anderen still verfallen.

*Keine Tagesschätzung.* V1, V4 und V6 sind Messen und Schreiben; V2 und V3 sind Bauten mit
bekanntem Gegenstand; V5 ist ein zweites Werkzeug; V7 hängt an einer Bedingung, die nicht in
Arbeitszeit gemessen wird.

---

## 5. Was dieser Weg NICHT kauft

* **Keine Aussage über das erzeugte C.** Der Verifikationspfad endet am Gabbro-Programm. Die
  Absenkung (§7 des autonomen Plans) bleibt vollständig unberührt — *ein verifiziertes Gabbro-
  Programm und ein korrektes C-Erzeugnis sind zwei Zusagen, und dieser Plan kauft die erste.*
* **Keine Aussage darüber, ob die Spezifikation sagt, was gemeint war.** Ein Tippfehler von einem
  **erklärten** Feld auf ein anderes beweist eine wahre Aussage über den falschen Ort. Das
  Ortsverzeichnis begrenzt die Gefahr; es nimmt sie nicht weg — *und das steht im Wächter selbst,
  benannt statt versteckt.*
* **Keinen Ersatz für den Prüfer.** Er sagt Dinge, die keine Spezifikation sagt: Kosten,
  Wirkungen, Linearität, Phasen. **Unabhängig heißt nebeneinander, nicht anstelle.**
* **Kein `K100.4 stark`.** Ein Zeugenpaar je Lauf ist kein maschinengeprüftes Zeugnis je
  Übersetzung.
