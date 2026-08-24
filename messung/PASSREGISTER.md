# Das Passregister — 54 Sätze über zwölf Pässe

*Angelegt 2026-08-21 (PL.1 + PL.2). Jede Zahl unten nennt den Befehl, der sie nachrechnet.*

> **Der Befund, mit dem das anfing:** `struct Pass` hatte kein Feld für einen Satz. Zwölf
> Pässe entscheiden über jedes Programm, 191 Absagekennungen — und **null Sätze**. Ohne die
> Sätze ist *„Gabbro formal verifiziert"* nicht einmal **formulierbar**: man wüsste nicht,
> was zu beweisen wäre.

## Der Stand, in Zahlen

```bash
cargo build -q --bin gabbro && ./target/debug/gabbro paesse          # das Register
./instrumente/pruefe-saetze.py                                       # der zweite Zahn
```

| | | Befehl |
|---|---:|---|
| Sätze im Register | **54** | `gabbro paesse` |
| davon `measured` | **46** | ein Giftprobenfall oder eine gefangene Mutation |
| davon **`ARGUED`** | **2** | ein Korrektheitsargument ist aufgeschrieben — [`K001`](K001.md), [`H006`](H006.md). *Das erste fand eine Unterzählung um Faktor 3; der dritte Versuch ([`V2`](V2.md)) fand statt einer Messung den [Nichtdeterminismus](DETERMINISMUS.md) und blieb `CONJECTURED`* |
| davon `CONJECTURED` | **6** | nichts misst sie |
| davon `PROVED` | **0** | **das ist die Zahl, um die es in PL.2 geht** |
| Pässe mit mindestens einem Satz | **12 von 12** | `gabbro paesse` |
| Kennungen im Prüfer | **191** | `./pruefe-kennungen.py` |
| davon von einem Satz beansprucht | **156** | `./instrumente/pruefe-saetze.py` |
| **Kennungen ohne Satz — die Ratsche** | **45** | `./instrumente/pruefe-saetze.py` |

**Die Schätzung im Plan war ~22 Sätze; es sind 43 geworden.** Der Grund ist kein
Fleiß, sondern eine Messung: mehrere Pässe halten **zwei Aussagen verschiedener Stärke**,
und sie in einen Satz zu schreiben hätte die schwächere unter der stärkeren versteckt.
`kosten` ist das Beispiel — siehe unten.

## Die 45 ohne Satz sind kein Vergessen, sondern eine gezogene Linie

```
parse.rs   37     lex.rs   7     emit.rs   1
```

**Alle 45 liegen außerhalb der `passliste()`**: der Parser ist kein Prüfpass, der Erzeuger
auch nicht. *Trotzdem stehen sie als offen und nicht als wegdefiniert* — ein Absagetext des
Parsers behauptet genauso etwas über ein Programm wie einer des Kostenpasses.

> **Was nicht geht, ist die Zahl kleiner zu machen, indem man die Frage ändert.** Wer sie auf
> null bringen will, schreibt die 45 Sätze — oder das Register bekommt eine zweite Spalte für
> „kein Pass", und *das* ist dann eine Entscheidung mit einem Datum.

## Was die Zahl 43 NICHT sagt

> **Ein aufgeschriebener Satz ist kein bewiesener.** Das ist der ganze Vorbehalt, und er ist
> größer als die Leistung.

1. **`PROVED` ist leer.** Keiner der 54 Sätze war je in Isabelle. Was das Register liefert,
   ist die **Liste der zu beweisenden Aussagen** — der Gegenstand von PL.2, nicht sein
   Ergebnis.
2. **`measured` misst die UMSETZUNG, nicht die REGEL.** Eine fallende Giftprobe zeigt, dass
   der Rust in *diesem* Fall so entscheidet, wie der Satz sagt. Sie zeigt nicht, dass er es
   überall tut, und schon gar nicht, dass die Regel richtig ist (PLAN.md PL.3, Weg (c)).
3. **Der Wächter zählt ZUORDNUNGEN, er liest die Sätze nicht.** Ein falscher Satz zählt wie
   ein richtiger; ein Satz, der weniger sagt als sein Pass leistet, fällt gar nicht auf (W10).
4. **20 der 146 beanspruchten Kennungen haben KEINE Giftprobe** — davon sind 5 Hinweise, die
   restlichen **15 sind echte Absagen, die niemand misst**:
   ```
   A002 A003 E004 H004 H008 K004 L105 M106 M107 M110 M114 U001 U002 U004 U005
   ```
   *Der Satz darüber steht trotzdem auf `measured`, weil andere Kennungen desselben Satzes
   gemessen sind. Das ist die Vergröberung dieses Registers, und sie steht hier statt in
   einer Fußnote.*

## Die Vorbedingung über allen 54 Sätzen: ein Hinweis ist keine Absage

`Stufe::Hinweis` zählt nicht als Fehler, und nur `Stufe::Fehler` lässt den Übersetzer
scheitern. **Fünf Kennungen sind Hinweise: `E003`, `E009`, `V003`, `S007`, `N026`.**

> **Ein Programm, das „ohne Absage" durchgeht, kann Funktionen enthalten, deren Rahmen- oder
> Paarungsaussage der Prüfer AUSDRÜCKLICH für unentscheidbar erklärt hat.** `E009` ist der
> ehrliche dritte Zustand (R16) — sichtbar, nicht grün. **Jeder Satz dieses Registers ist um
> genau diesen Betrag schwächer**, und deshalb steht die Zeile im Kopf von `gabbro paesse`.

## Die drei mit der größten Traglast (PL.2)

### `K001` — die Summation, und ihr gemessener Fehler steht IM Satz

**Der Satz wurde geteilt, weil die zwei Hälften verschieden stark sind:**

| | Stand | |
|---|---|---|
| `kosten.summation` | **measured** | Anweisungen addieren; Zweig = Maximum; was hinter einem immer verlassenden `if` steht, zählt einmal; verglichen wird bei der **kleinsten Belegung** |
| `kosten.domaenenschranke` | **CONJECTURED** | `traverse` kostet Rumpf × Schranke — *und nichts prüft, dass die gelesene Zahl die Mächtigkeit der Domäne IST* |

> **Der Fehler, sichtbar gemacht statt überschrieben:** für `mappings of` las der Pass
> `Ebenen × Knotenlänge` = **2 048**, wo die Domäne die **Blattmenge** ist,
> `Knotenlänge ^ Ebenen` = 512⁴ = **68 719 476 736**. **Sieben Größenordnungen, drei Tage
> getragen** — und gefunden, weil der **Erzeuger** hineinlief, nicht weil ein Test fiel.
>
> Er ist korrigiert (`umgebung.rs::walkschranken`). **Der Satz steht trotzdem auf
> `CONJECTURED`**, denn `K003` hat zwei Giftproben und die messen, dass eine **fehlende**
> Schranke abgelehnt wird — nicht, dass eine **vorhandene** stimmt. *Genau in diesem
> Unterschied hat der Fehler drei Tage gelebt, und jede andere Domänenschranke des Passes hat
> dieselbe Bauart und dieselbe Prüfung: keine.*

### `H006` — die Rangordnung

`sperren.rangordnung` ist **measured**, und der Satz trägt den klassischen Schluss: *jede
Sperre hat einen zur Übersetzungszeit festen Rang, auf jedem Pfad wird nur unter einem echt
kleineren Rang genommen, also ist kein zirkuläres Warten möglich.* **Drei Bedingungen, die
der Satz braucht und der Pass nicht voll liefert**, stehen im `vorbehalt`: die
Interprozeduralität gibt es erst seit 2026-08-19, über einer **unvollständigen Hülle** wird
nicht abgesagt (R16), und gedeckt sind nur **deklarierte** Sperren.

### V2 — die relationale Verengung: der Satz mit der größten Last und der geringsten Messung

**`v2.relationale-verengung` steht auf `CONJECTURED`, und der Grund ist strukturell:**

> **V2 hat keine eigene Kennung.** Die Regel **erweitert**, was durchgeht; wo sie nicht
> trägt, kommt die Absage als `M104`/`M101` aus einem anderen Satz. *Damit lässt sie sich
> nicht vergiften* — eine Probe müsste ein **Paar** zeigen (ohne Fakt fällt, mit Fakt geht
> durch), und dafür hat das Geschirr heute keine Form.

54 relationale Fundstellen der 102 flusssensitiven hängen daran. **Das ist der erste Satz,
den PL.3 kaufen sollte.**

## Was das Aufschreiben gekostet und was es GEFUNDEN hat

*Der häufigste Einzelbefund war nicht ein fehlender Satz, sondern ein **Modulkopf, der mehr
behauptet als sein Code einlöst** — fünfmal, in fünf Dateien, zweimal schlicht veraltet.*

| Fund | Datei | Was |
|---|---|---|
| **die K-Bedingung wird nicht durchgesetzt** | `kbedingung.rs` | `k_haelt()` verlangt `breaking.is_empty()`; der Pass meldet nur Handschrift. **`breaking` wird gesammelt, gezählt, gedruckt — und nie abgesagt.** Ein Programm, das Pass 2 passiert, erfüllt die K-Bedingung **nicht notwendig** |
| **`N028`/`N029` schlüsseln verschieden** | `namen.rs` | Karte unter dem **Kurznamen**, Nachschlag unter dem **vollen Pfad**. `m::f()` trifft nie: `N029` schweigt, `N028` schlägt **falsch** an |
| **die Paarung ist global, nicht transitiv** | `paarung.rs` | Der Kopf sagt „transitive Menge", der Code vereinigt über **alle** Funktionen des Baums. Ein `publishes` in Modul A paart mit einem `awaits` in Modul B **ohne jede Aufrufbeziehung** |
| ~~**der Adressraum wird nirgends geprüft**~~ **— gebaut 2026-08-24 (`R008`)** | `m3.rs` | Außer `R001` gab es **keinen** Test auf einen Raum; ein `ptr<normal, rw>` erreichte einen `ptr<mmio, rw>`-Parameter mit null Fehlern. *Jetzt muss der Raum am Rufort ÜBEREINSTIMMEN* — für Argumente, die ein blanker Parameter sind. **`code`, `boot`, `port` prüft weiter nichts, und `Typ` verliert `Raum` bei der Typbildung** |
| **`melden` ist toter Code** | `phasen.rs` | Der Schalter, der „ein Rumpf ohne eigene `advances`-Zeile meldet nicht" unterscheiden sollte, wird durch sechs Rufstellen gereicht und **nie gelesen** |
| **`O004` schweigt bei leerem Rumpf** | `phasen.rs` | Eine Funktion mit `advances roh -> mmu` und leerem Rumpf gibt **null Fehler**. *„Eine Strecke, die unterwegs aufhört, ist keine Strecke" — eine, die nie anfängt, ist stumm* |
| **rekursive Funktionen: keine Rahmenprüfung** | `wirkungen.rs` | Am Zyklus wird `E009` (ein **Hinweis**) gesetzt und **vor jeder `E008`-Prüfung zurückgekehrt**. Und der Grund propagiert nach oben: **eine** unauflösbare Kante tief unten entwertet `E008` für die ganze Rufkette darüber |
| **`U005` fällt falsch** | `gruppe.rs` | Ein nicht auswertbarer Rang wird **0**; zwei davon sind damit „gleich" |
| **`by unvisited`/`by consuming`: keine Abstiegsprüfung** | `schleifen.rs` | Für diese zwei Formen sagt Pass 6 über Terminierung **nichts** |

> **Keiner dieser neun Funde ist von einem Werkzeug gemeldet worden.** Sie sind aufgefallen,
> weil jemand den Satz aufschreiben musste und dafür nachsehen, was der Pass wirklich tut.
> *Das ist die Leistung dieser Übung, und sie ist größer als die Liste selbst.*

## Der zweite Zahn, und wie er misst

```bash
./instrumente/pruefe-saetze.py [--je-satz] [--ohne-satz]
```

**Zwei Richtungen, und die zweite ist die schärfere:**

| | | |
|---|---|---|
| (a) | Kennung im Prüfer, kein Satz | die **Ratsche** — Marke **45**, sie darf fallen, nicht steigen |
| (b) | Kennung im Satz, nicht im Prüfer | **immer rot, ohne Marke** — ein Satz über einer Regel, die es nicht gibt |

**Beide Richtungen sind von außen gemessen, nicht nur in der Sprechprobe** (R14/W17):

```
Kennung "Z999" in kosten.rs eingefügt   -> RC 1, „46 Kennungen ohne Satz, gebucht sind 45"
Kennung "Z998" in einen Satz eingefügt  -> RC 1, „steht in einem Satz und wird von KEINER Datei vergeben"
sauberer Baum                           -> RC 0
```

> **Die zweite Probe hat beim ersten Lauf einen Fehler im Wächter selbst gefunden**: die
> Kennungserhebung las auch `saetze.rs`, also fand sich die erfundene Kennung dort wieder und
> galt als vorhanden. *Ein Wächter, der sich selbst mitzählt, kann in dieser Richtung nie rot
> werden.* Behoben durch dieselbe Ausnahme, die `tests/` schon hatte — **und derselbe Fehler
> steckte in `pruefe-kennungen.py`**, das nach dem Anlegen des Registers 146 Doppelbelegungen
> meldete, von denen keine eine war.
