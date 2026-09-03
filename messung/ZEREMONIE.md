# Die Zeremonie des Korpus — Ziel 3 bekommt seine erste Zahl

**Von den vier Zielen hatte „möglichst gut nutzbar" als einziges keine Zahl.** Ohne eine ist
es eine Meinung — und *„keine Klempnerei beim Endnutzer"* ist eine Nutzbarkeitsaussage.

```
$ ./instrumente/zaehle-zeremonie.py
74 Dateien gemessen, 1 abgelehnt
  ableitbar       86        A1  4 · A4 82
  redundant        0
  tragend       1215
86 von 1301 Stellen dürfen sinken

> **Am 2026-09-01 stand hier für eine Stunde 1111, und das war eine Fehlmessung.** Der Lauf
> zählt alle `.gab` des Baums — und in diesem Baum schrieb gleichzeitig eine zweite Spur.
> Drei Läufe hintereinander sagen jetzt übereinstimmend `77 + 1067 = 1144`; eine Stunde vorher
> sagten sie ebenso übereinstimmend `1111`. **Nicht der Korpus hat sich bewegt, sondern der
> Zeitpunkt.**
>
> *Eine korpusweite Zählung, die genommen wird, während ein anderer Schreiber den Baum hält,
> misst den Schreiber und nicht den Korpus.* Innerhalb eines Augenblicks ist sie stabil, und
> genau das macht sie glaubwürdig aussehen.
```

> **~~1156~~ 1181 am 2026-09-02, and every one of the 25 is a site that was on disk all
> along.** Nothing was written into the corpus; `zeremonie.rs::geraet()` stopped at the top
> level of a `device` and two kinds of site were below it. The report's own header says
> *"Every clause and annotation"*, so the miss was in the census and not in the corpus:
>
> | | Lehrkorpus | | real code |
> |---|---|---|---|
> | `T3` `transition … requires` | **+12** | `02`:3 · `09`:1 · `20`:2 · `45`:1 · `F02`:5 | **+1** (`virtio-net`) |
> | `T10` a register inside a `bank` | **+13** | `02`:2 · `F02`:4 · `F04`:7 | 0 |
> | | `T3` 85 → 97, `T10` 60 → 73 | | 109 → 110 |
>
> **The delta is named site by site and not estimated** — the two columns add to exactly the
> 25 the headline moved, and to exactly the 1 the real-code count moved. *A number that grows
> without a per-site account is a number nobody can check a second time.*
>
> Found by counting the ASSUMPTION TIER, not by reading the function: `beispiele/02-geraet.gab`
> carries three `transition … requires`, and `gabbro zeremonie --je-stelle` listed **none** of
> them. **The direction of that error is the dangerous one** — ceremony undercounted reads as
> ceremony not incurred, and this counter is the only number goal 3 has.
>
> *It is `T3` and not a new rule.* `T3` reads *"`requires` / `ensures` that no other clause
> repeats"*, the `reg` half has stood under it since the function existed, and a rule of its
> own would have been the second register over one matter.

> **~~1028~~ 1050 in der Nacht auf den 2026-09-01, und der NENNER ist zurückgekommen.**
> `messung/fragmente/F06.gab` war die fünfte abgelehnte Datei: `N043` wies
> `measures eich.leer, …` ab, einen Träger, den der eingefrorene Ausschnitt nennt und
> nirgends deklariert — **und eine Datei mit Fehlern zählt hier nicht mit.** Mit
> `type EichMarke` + `static eich` prüft sie wieder sauber, und ihre **22 Stellen (1
> ableitbar, 21 tragend)** sind zurück in der Grundgesamtheit.
>
> *Dieselbe Bewegung wie bei `F05` weiter unten, nur andersherum* — dort verließ eine Datei
> die Messung, hier kommt eine zurück. **Nichts ist nutzbarer geworden und nichts weniger;
> die Grundgesamtheit hat sich bewegt.** Und die Zeilen `ableitbar 64 / tragend 986` im
> Block darüber standen schon vorher so da: sie summierten sich zu 1050, während die
> Schlusszeile 1028 sagte. *Ein Block, dessen Spalten nicht auf seine Summe gehen, ist
> sechzehn Tage lang nicht nachgerechnet worden* (W10) — er geht seit heute wieder auf.

> **~~1008~~ ~~1050~~ 1028 am Abend des 2026-08-31, und diesmal ist der ZÄHLER mitgestiegen.**
> `beispiele/55`–`57` sind drei neue Dateien (die Quantorendomänen `chain`, `queue`,
> `threads`, `QUANTORENDOMAENEN.md`): +42 Stellen, davon +4 ableitbar. *Die Quote bleibt
> damit fast stehen, und das ist die ehrliche Auskunft — drei annotationsschwere Programme
> verschieben sie nicht.*

> **~~1035~~ 1008 seit dem 2026-08-31, und der Nenner ist gefallen, nicht der Zähler.**
> `messung/fragmente/F05.gab` ist die vierte abgelehnte Datei: `N041` weist `extern fn exit()`
> ab, ein Name, den C schon vergeben hat, und **eine Datei mit Fehlern zählt hier nicht mit**
> (*„has errors -- no count"*). Ihre 27 Stellen sind aus der Grundgesamtheit heraus.
>
> *Eine Quote, deren Nenner sich bewegt, ist zweimal zu lesen* — die 60 ableitbaren stehen
> unverändert, die Prozentzahl steigt trotzdem. **Nichts ist nutzbarer geworden;** eine Datei
> hat die Messung verlassen. `messung/C-NAMEN.md`, `messung/F05-UNERREICHBAR.md`

## Die zwei Achsen, und warum sie getrennt bleiben

Ein Nutzbarkeitsmaß wird sofort zum Optimierungsziel. Fällt es **unkalibriert**, fällt als
erstes das Billigste — `effects`, `costs`, die Paarungsklauseln. *Genau der Gegenstand der
Sprache.* Deshalb trägt `gabbro zeremonie` seine Kalibrierung mit:

| | | |
|---|---|---|
| **Achse 1** | *gemessen* | steht diese Tatsache ein **zweites Mal** in dieser Einheit? |
| **Achse 2** | *erklärt* | darf die Zahl sinken? — je Regel ein Ja/Nein **mit Grund** |

> **Achse 1 ist mechanisch, Achse 2 ist eine Entscheidung — und steht als eine da.** Das ist
> die Lehre aus `N_ritus` (W19), einen Stock höher angewandt: die urteilsfreie Hälfte wird
> gezählt, die geurteilte wird benannt. `gabbro zeremonie --tafel` druckt beide nebeneinander.

**`ableitbar` heißt: dieselbe Tatsache steht mechanisch lesbar an einer zweiten Stelle dieser
Einheit — und das Register nennt welche.** Es heißt *nicht* „weg damit". Deshalb kann eine
Regel `ableitbar` sein und trotzdem nicht fallen dürfen; genau dafür gibt es zwei Achsen.

## Und der eigentliche Befund ist der Vergleich zweier Korpora

Die Beispiele sind **für die Sprache** geschrieben; `messung/treiber/` und `messung/caprock/`
sind **echter Code** gegen `../caprock-messbasis`. Eine Quote über beiden zusammen verstünde
die Frage falsch — Ziel 3 fragt, was ein *Nutzer* schreiben muss, nicht was ein Beispiel
vorführt. Also getrennt (W11: jede Quote nennt ihr N):

| | dürfen sinken | Stellen / Zeilen | Dichte |
|---|---|---|---|
| **Lehrkorpus** *(53 Beispiele + 7 Fragmente)* | 58 von 1006 — **5,8 %** | 1006 / 6682 | 15,1 je 100 Z. |
| **echter Code** *(virtio-net · kapraum · planer)* | 14 von 109 — **12,8 %** | 109 / 519 | 21,0 je 100 Z. |

> **Im echten Code ist der ableitbare Anteil mehr als doppelt so hoch — und er besteht
> ausschließlich aus `A4`.** *Ein Beispiel ruft wenig; ein Treiber ruft ständig.* Damit ist
> die A4-Frage nicht mehr eine unter zwanzig, sondern **die** Frage dieses Maßes: 14 von 14
> ableitbaren Stellen im echten Code sind Wirkungszeilen, die ein Gerufener ohnehin erklärt.

Und die Dichte geht in dieselbe Richtung: echter Code trägt **ein Drittel mehr** Klauseln je
Zeile. *Beides zusammen heißt: die Beispiele unterschätzen, was ein Nutzer schreibt.*

## Was die Zahl sagt

**Der Korpus ist mager: 58 von 1006 Stellen (5,8 %) dürfen sinken.** Die Klempnerei liegt
*nicht* in den Klauseln — 948 Stellen tragen eine Aussage, die nirgends sonst steht.

Und der größte Einzelposten ist `A4` mit 47: **eine Wirkungszeile, die ein Gerufener dieses
Rumpfes ohnehin erklärt.** Sie darf sinken, aber nur auf **eine** Weise — die Liste des Rufers
wird *gerechnet* und gedruckt (`gabbro abi`) statt weggelassen. *Sie einfach zu streichen
machte `E008` rückgängig, den Posten, der `effects` am 2026-08-15 erst kompositional gemacht
hat.*

## Null redundante Stellen — und warum das hier keine Freisprechung ist

`redundant = 0` ist entweder ein sauberer Korpus oder ein blindes Werkzeug, und **von außen
ist der Unterschied nicht zu sehen** (W17, *Erfolg ohne Arbeit*). Die Sprechprobe ist deshalb
schärfer als sonst:

> **Eine Regel der Tafel, die nirgends einen Treffer hat, ist selbst ein Befund.**

Was der Korpus nicht auslöst, löst eine absichtlich schlecht geschriebene Probe aus:
**20 Regeln, 14 vom Korpus, 6 von der Probe, keine stumm.** Erst damit heißt „0 redundant"
*gemessen* und nicht *ungesehen*.

## Vier Befunde, und zwei davon korrigieren diesen Ordner

**1. Eine Annotation mit zwei Lesern, von denen nur einer sie las.** `beispiele/21` schrieb
`let c : Completion = fertig(k, 7);` mit dem Kommentar, der Erzeuger rate keinen Typ. Er
*liest* ihn längst ab — und das Weglassen deckte auf, dass `verbundlokale` es **nicht** tut:
das erzeugte C wurde `c->len` auf einem Verbundwert.

> **`gabbro emit` gab 0 zurück, und `cc` lehnte ab.** Gefunden nicht von einem Pass, sondern
> von der Frage, *ob eine Zeile nötig ist*. Dieselbe Klasse wie W7: zwei Register über
> derselben Sache, und das schwächere entschied.

**2. Der nachgebildete Korpus erbt das Alter seiner Vorlage.** `messung/fragmente/F05.gab`
sagt, `forever` habe keinen Ausgang. **Es hat einen**: `leave <marke>` steht in der Grammatik
(`SYNTAX.md`:658), prüft mit 0 Fehlern und senkt zu `goto marke_ende;` ab — nachgerechnet am
2026-08-20. Was fehlt, ist ein Ausgang, der einen **Grund** trägt; `leaves` heißt in Gabbro
etwas anderes (die linearen Werte, die den Bereich verlassen). *«B11» schrumpft von „die
Dienstschleife ist nicht schreibbar" auf „ihr Austritt ist unbenannt".*

> **Und das Bemerkenswerte ist, wie der Satz dorthin kam.** `TODO.md` führte längst, dieser
> Grund sei „zu dem Zeitpunkt längst nicht mehr wahr". F5 entstand am selben Tag und trug den
> Wortlaut des **eingefrorenen** Berichts vom 2026-08-14 mit. *Ein Korpus, der einen Bericht
> nachbildet, vervielfältigt dessen Alter, wenn niemand auf den Gegenstand sieht* — die Regel
> des Ordners („nachgebildet, nicht übersetzt — und ausdrücklich gesagt") deckt die Zeilen, sie
> deckt nicht die **Sätze über Gabbro** daneben.

**3. `S006` schweigt nicht mehr.** Der TODO-Eintrag hielt fest, `on_exceeded DeviceSilent`
falle durch, weil der Pass „Reason-Variante" nicht von „unbekannter Name" unterscheiden könne.
`S007` — der dritte Zustand, gebaut am 2026-08-19 — meldet es. *Der fünfte Eintrag binnen
einer Woche, der zu pessimistisch dastand.*

**4. Und dieser Bericht ist der Beleg für die Diagnose selbst:** die Buchführung schönt nicht,
sie **veraltet**. Zwei der vier Punkte dieser Stufe waren beim Nachsehen schon zu.

## Die drei Entscheidungen dieser Stufe

**Kein `?`.** Gemessen statt argumentiert: **21 `let … else`-Stellen, 15 verschiedene Rümpfe,
26 von 5569 Korpuszeilen (0,5 %).** Die sechs, die wie Kopien aussehen, unterscheiden sich
genau in der Fehlerkennung — *und die ist das Einzige, was `?` löschen würde.* D11 sagt
„benannt statt still"; ein Operator, der den Namen frisst, ist die Gegenrichtung.

**`on_exceeded` behält `-> never`.** Der Wachhund ist die Stelle, an der die Schranke ihre
Wirklichkeit berührt — kehrte er zurück, wäre die Schranke eine Zahl ohne Folge (`S006`). Der
Fehlerkanal `-> T or R` ist eine **Rückgabe**konvention; eine überschrittene Schranke ist keine
Rückgabe, sondern die Aussage, dass das Programm den Bereich verlassen hat, in dem seine
Kostenzusage gilt. *Der Grund gehört an den Austritt, nicht an den Wachhund* — und der Austritt
ist Befund 2.

**Die Pässe halten nach einer Leserabsage NICHT an — aber sie sagen es.** `gabbro pruefe`
druckt seit heute, wie viele spätere Meldungen Folgen sein können. *Anhalten hieße, ein `P001`
im dritten Item verdeckt einen echten `M101` im ersten: Rauschen gegen Schweigen getauscht,
und dieser Ordner hält Schweigen für das teurere.* Dieselbe Bauart wie `E009` und `S007`.

## Was hier ausdrücklich NICHT gezählt wird

Steht in `gabbro zeremonie --tafel`, je Zeile mit Grund: `module`/`use`/`pub`, `section`/
`arch`/`when`, die Fälle eines `reason`, `entrust`/`boot`/`entry`, die `by`-Beweishinweise und
die Typdeklarationen selbst. **Was ein Werkzeug nicht misst, muss es sagen** — sonst sieht
ungemessenes Schweigen wie eine Null aus (W11).

*Und die Doktrinzeile, wie bei den drei anderen Zählern:* **was 0 Befunde hat, ist nicht
nutzbar, sondern ungemessen.**

> **1050 → 1079 am 2026-09-01, und wieder ist es der NENNER.** `beispiele/58` und drei
> Giftproben kamen mit dem Blockgeltungsbereich dazu; `ableitbar` steigt von 64 auf 68,
> `tragend` von 986 auf 1011. *Die Quote bewegt sich nicht, weil jemand nachlässiger
> geworden wäre, sondern weil der Korpus gewachsen ist* — und genau darum steht der Nenner
> hier und nicht nur der Zähler (W11).

> **1110 → 1137 am 2026-09-01, und wieder ist es der NENNER.** Fünf saubere Beispiele und
> neun Giftproben kamen mit `~`, `w1c` und der Verdrahtungsbahn dazu; `ableitbar` steigt
> 68 → 76, `tragend` 1011 → 1061. *Die Quote bewegt sich, weil der Korpus wächst — und darum
> steht der Nenner hier und nicht nur der Zähler* (W11).
