# Der Abstiegswächter: sechs von sieben waren richtig, einer war ein Fehler

**Gemessen am 2026-08-30.** `instrumente/pruefe-abstieg.py` endete seit mindestens dem
2026-08-28 bei jedem Lauf mit `rc=1`, über einem Inhalt, der sich nicht bewegte:

```
  m2::endet                OHNE ABSTIEG in: Bricht, Exchange, LetSonst, Narrow,
                                            Observiert, Schleife, Sperrt
  emit::rumpf_als_wert     weigert sich benannt (8 Arten)
== ABSTIEG: 1 Paesse mit Luecke ==
```

> **Ein Wächter, dessen roter Ausgang der Normalzustand ist, unterscheidet einen neuen Befund
> nicht von dem alten.** Er ist damit kein Wächter mehr, sondern eine Anzeige.

Die Frage war zuerst, **ob die Lücke echt ist**. Die Antwort ist geteilt, und die Teilung ist
das Ergebnis.

---

## 1. `m2::endet` ist kein Abstieg, sondern ein Prädikat

`crate::unterbloecke(&Stmt) -> Vec<&Block>` fragt: *welche Blöcke enthält diese Anweisung?*
Ein Pass, der jeden Block **besuchen** muss, schuldet dafür neun Arme — genau das misst der
Wächter, und für einen solchen Pass misst er richtig.

**`m2::endet` besucht keinen einzigen davon.** Es liest `b.anweisungen.last()` und fragt eine
andere Frage: *verlässt die Steuerung diesen Block endgültig?* `if` und `match` stehen darin,
weil ihr Enden sich über ihre Zweige zusammensetzt — nicht, weil abgestiegen würde.

Die sieben gemeldeten Arten zerfallen damit in drei Gruppen:

| Art | `false` ist … | warum |
|---|---|---|
| `narrow … else`, `let … else`, `exchange`-`update` | **richtig** | ihr Block ist der ANDERE Weg; der Hauptweg läuft daran vorbei |
| `locks`, `observes` | **konservativ und folgenlos** | sie enden nur, indem sie ein `return` enthalten — und ein Wert, der in einem zurückkehrenden Zweig unverbraucht bleibt, ist ein Leck, ob das Prädikat das Enden sieht oder nicht |
| `breaking <m>` | **konservativ** | ein `leave m` von irgendwo darin springt hinter den Block; das Enden ist eine Frage über Marken |
| **`forever` ohne Ausgang** | **FALSCH** | eine solche Schleife fällt nicht durch, sie DIVERGIERT |

---

## 2. Die eine echte Lücke — an einem Programm gemessen

```gabbro
impl fn abschluss(m : Marke, ist_dienst : bool) -> u64
    effects { consumes m, diverges }
{
    if ist_dienst {
        forever dienst per_pass bounded 16 ops on_exceeded watchdog_schlug_an
            effects { pure } progress zeitgeber_tickt
        { tue(); }
    } else {
        nimm(m);
    }
    return 0;
}
```

```
$ gabbro pruefe probe-endet.gab        (vor der Berichtigung)
Fehler: [L103] :15:5:  `m` is not treated the same on every path
Fehler: [L101] :12:11: `m` is listed under `consumes` but is consumed on no path
```

**Der divergierende Zweig kann `m` nicht lecken: er kehrt nie zurück.** Die Zusage
`consumes m` gilt für jeden Weg, der normal endet — und das sagt die Notiz unter `L103`
wörtlich:

> *„a branch that diverges or returns does not count — not every path has to consume, only
> every path that ends normally"*

**Das Prädikat darunter kannte nur die zurückkehrende Hälfte.** Eine falsche Ablehnung eines
richtigen Programms, dieselbe Klasse wie `U005` und wie der Fund vom 2026-08-25 in derselben
Funktion — *ein Programmierer, der hier ankommt, kann nichts reparieren, weil nichts kaputt
ist.*

### Berichtigt, und in beide Richtungen nachgemessen

`m2::endet` beantwortet `Schleife` jetzt einzeln: `traverse` endet durch die Menge, `retry`
durch eine Zahl — beide fallen durch. Ein `forever` endet **genau dann**, wenn kein
`leave <seine Marke>` in seinem Rumpf steht; ein `forever` ohne Marke kann von nichts
verlassen werden, weil `StmtArt::Leave` immer eine Marke trägt.

```
$ gabbro pruefe beispiele/54-divergenz-leckt-nicht.gab
… 0 Fehler, 0 Hinweise                            (vorher: L103 + L101)

$ gabbro pruefe beispiele/gift/407-forever-mit-ausgang-faellt-durch.gab
Fehler: [L103] :23:5: `m` is not treated the same on every path
```

**Die Giftdatei ist byteweise dieselbe Schleife plus `leave dienst`.** Damit fällt sie durch,
`m` lebt auf diesem Weg weiter, und `L103` gehört hierher. *Ohne sie könnte die Verfeinerung
jeden `forever` für divergent halten und hätte eine echte Absage mitgenommen.*

Die Suche nach dem `leave` ist absichtlich grob: ein gleichnamiges `leave` in einer
GESCHACHTELTEN Schleife, die die Marke verdeckt, zählt hier mit — und die Antwort ist dann
„fällt durch", also die alte. *Ein Suchlauf, der nur in Richtung „fällt durch" irrt, kann
keine falsche Annahme erzeugen; er kann nur eine Verfeinerung aufgeben.*

Und `endet` matcht seither **erschöpfend, ohne `_`-Zweig** — dieselbe Bauform, die
`unterbloecke` schon trägt: eine neue `StmtArt` erzwingt eine Entscheidung statt eine Lücke
zu vererben.

---

## 3. Der Wächter bekommt drei Antworten statt zwei

`m2::endet` steigt jetzt vollständig ab, und `pruefe-abstieg.py` ist grün. **Das allein
genügt nicht:** die nächste begründete Lücke macht ihn wieder zur Daueranzeige. Er bekommt
darum die Form seines Zwillings `pruefe-konstrukte.py`, den seine eigene erste Zeile nennt —
**eine Buchung mit geschriebenem Grund je Eintrag**, und drei Ausgänge:

| Lage | Ausgabe | `rc` |
|---|---|---|
| gar keine Lücke | `ALL PASS -- jeder Pass erreicht jeden Unterblock` | 0 |
| Lücke, **nicht** gebucht | `N NEUE Paesse mit Luecke` | 1 |
| dieselbe Lücke, **gebucht** | `N gebucht, KEINE neue` + der Grund je Zeile | 0 |
| Buchung, deren Lücke **weg** ist | `DIE BUCHUNG IST VERALTET` | 1 |
| **doppelter Abstieg** | nie buchbar | 1 |

Ein doppelter Abstieg bleibt außerhalb der Buchung: er ist keine Deckungslücke, sondern eine
Laufzeit von 2^Tiefe — gemessen 1,88 s bei 26 geschachtelten `if` und über anderthalb Minuten
bei 50. *Es gibt keine Weltlage, in der das ein Rückstand ist, den jemand hinnimmt.*

**Die Buchung steht heute LEER**, und das ist eine Messung und kein Versehen: der einzige
Eintrag, den sie getragen hätte, war ein echter Fehler und ist am selben Tag berichtigt.
*Eine leere Buchung ist der einzige ehrliche Anfangszustand — was hineinkommt, muss begründet
werden.*

### Die Sprechprobe, an einer Kopie des Baumes gefahren

Die Entscheidung liegt in `einordne(luecken, tisch)`, einer eigenen Funktion — **damit die
Probe SIE laufen lässt statt einer Abschrift.** *Ein Wächter, dessen Probe die Regel
nachbaut, beweist, dass die Abschrift funktioniert.* Zusätzlich zur Probe im Wächter selbst
wurde von Hand gefahren, auf einer Wegwerfkopie von `crates/gabbro-check/src`:

```
(0) unveraendert                              -> ALL PASS                        rc=0
(1) `StmtArt::Schleife` in `endet` verstellt  -> 1 NEUE Paesse mit Luecke        rc=1
(2) dieselbe Luecke, in GEBUCHT eingetragen   -> 1 gebucht, KEINE neue           rc=0
(3) Buchung bleibt, Quelle wiederhergestellt  -> DIE BUCHUNG IST VERALTET        rc=1
```

**Der echte Baum wurde dabei nicht angefasst.**

---

## 4. Zwei Wächter, die die neuen Korpusdateien mitgenommen haben

Die zwei Dateien aus §2 haben zwei Buchungen bewegt, und die zweite ist ein eigener Befund.

**`pruefe-emission.sh`, Stufe 9** — *„JEDE Datei, die durch `emit` kommt, MUSS `cc -Werror`
bestehen"* — zählte 53 statt der gebuchten 52 emittierenden Dateien und meldete das:

```
  FUND: 53 statt 52 emittierende Dateien -- die Marke gehoert
        nachgezogen (der gute Fall, und trotzdem ein Befund).
```

*Die Marke ist eine Ratsche, die steigen darf und nicht fallen* — sie steht jetzt auf 53,
mit der Begründung daneben. **Der Wächter hat sich selbst gemeldet, und das ist der Zweck.**

**`pruefe-todo.py` dagegen hat sich NICHT gemeldet, obwohl er rot druckte.** Seine
Sprechprobe für die `DONE.md`-Korpuszahlen trug den Maßstab als Literal:

```python
d_sauber = "**53 clean examples, 310 poison probes** —\n"
```

Mit 54 Beispielen und 311 Giftdateien fiel die Richtung *„die richtige Zahl bleibt frei"* —
also **eine Sprechprobe, die an einer RICHTIGEN Zahl scheitert.** Sie druckte
`GESCHEITERT (erwartet 0)`, und der Wächter endete mit 0.

> **Zwei Fehler übereinander, und der zweite ist der teure.** Das Literal ist die Klasse, die
> im Absatz drei Zeilen tiefer schon steht — *„die Sprechprobe muss die HEUTIGE Zahl
> verstellen, nicht eine von gestern"*, dort für die README-Hälfte behoben und für die
> DONE-Hälfte stehen geblieben. **Der zweite Fehler ist, dass ihr Ergebnis nicht im `return`
> stand:** `sprechprobe()` gab `len(b_gift) >= 5 and not b_sauber and bool(getroffen) and not
> r_sauber` zurück, und die drei DONE-Zeilen wurden gedruckt und nicht gezählt.
>
> *Eine Sprechprobe, deren Scheitern nichts ändert, ist eine Verzierung* (R11) — und diese
> war seit dem Tag ihrer Entstehung eine.

Beides berichtigt: die Literale werden aus `n_b`/`n_g` abgeleitet, und `d_ok` steht im
`return`. Nachgemessen in beide Richtungen — mit verstelltem Maßstab `rc=1`, zurückgestellt
`rc=0`, die Datei danach byteidentisch (`md5sum`).

---

## 5. Was NICHT gebaut wurde

* **Kein Sammellauf über die 26 Wächter, und kein Eintrag in `dokumente/PLAN-AUTONOM.md`** —
  daran arbeitet eine andere Kette. Der Beitrag hier ist, dass `pruefe-abstieg.py` in einem
  solchen Lauf überhaupt eine sinnvolle Antwort geben kann.
* **Keine Buchung für `emit::rumpf_als_wert`.** Die Zeile *„weigert sich benannt (8 Arten)"*
  ist keine Lücke und war nie eine: der Erzeuger nennt jede Anweisungsart, die er in einem
  `update`-Rumpf nicht kann, beim Namen. Sie steht weiter in der Ausgabe und zählt weiter
  nicht mit.
* **Keine Verfeinerung für `breaking <m>`.** Sie bräuchte dieselbe Markensuche wie `forever`
  — und im Gegensatz zu `forever` gibt es dafür heute **kein Programm, das sie falsch
  ablehnt**. Regel A: der Bedarf wird gemessen, nicht vermutet.
* **Keine Mutation im Katalog von `mutiere-pruefer.py`.** Die Berichtigung an `m2::endet` ist
  von zwei Korpusdateien gedeckt, und eine davon ist eine Giftdatei, die genau an dieser
  Unterscheidung fällt. *Eine Mutation gehört dorthin, wo keine Probe steht.*
