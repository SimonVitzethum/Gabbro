# Das Tor vor `K003` — die Wurzel unter sechs Zellen, und was es kostet, sie zu ziehen

> **Dies ist eine Rechnung und keine Entscheidung.** Die Frage, ob Gabbro einen Ruf auf einen
> Namen annimmt, den niemand deklariert hat, ist eine Sprachentscheidung des Ordners — dieselbe
> Sorte wie die vier offenen Zellen der Grammatiktafel. *Was hier steht, ist das, ohne das sie
> niemand treffen kann: welche Formen daran hängen, warum genau sie durchkommen, welche Formen
> es gäbe, und was jede davon an Programmen kostet, die heute durchgehen.*

**Gemessen am 2026-08-31** auf `ki-pc-fisch-101`, mit einem Binärprogramm, das aus dem Stand
`9c0a3fa` dieses Zweiges gebaut wurde. Grundgesamtheit: **418 `.gab`-Dateien** (alle im Baum,
ohne `target/`, `.claude/`, `.lake/`) — dieselbe Menge, die `messung/ABSAGEFORMEN.md`:61 fährt.
**92 davon prüfen mit 0 Fehlern**; der Rest sind überwiegend Giftproben, die fallen sollen.

---

## 1. Die sechs Zellen

Sie stehen in [`messung/ABSAGEFORMEN.md`](ABSAGEFORMEN.md) §2.1 als U10–U15:

| Zelle | Form | Probe | die `C001`-Stelle im Erzeuger |
|---|---|---|---|
| **U10** | `match` über einen Ruf, den diese Einheit nicht deklariert | `messung/fragmente/F05.gab` | `emit.rs`:6802 |
| **U11** | `let` ohne auflösbaren Typ | `messung/proben/probe-unbekannter-ruf.gab` | `emit.rs`:5197 |
| **U12** | `state` | `messung/proben/probe-vier-zellen.gab` | `emit.rs`:1940 |
| **U13** | `queue` | dito | `emit.rs`:6506 |
| **U14** | `chain in` | dito | `emit.rs`:6537 |
| **U15** | `threads` | dito | `emit.rs`:6539 |

**Zwei Tafeln, ein Schnittpunkt.** U12–U15 sind die vier Terminale, die
`pruefe-grammatiktafel.py` aus der GRAMMATIK heraus als `UNGEDECKT` benannt hat
(`GRAMMATIKTAFEL.md`:135–138) — die Grammatiktafel rechnet Terminal × Zuständigkeit. U10 und U11
sind **keine Terminale**; sie sind Absageformen des ERZEUGERS und stehen darum nur in der
Absageformentafel. *Die „vier" der einen und die „sechs" hier widersprechen einander nicht — sie
sind zwei Schnitte durch dieselbe Wurzel.*

**Was ihnen gemeinsam ist, ist eine einzige Zeile Code**, und sie steht nicht in `emit.rs`,
sondern im Prüfer. Das Kriterium für jede der sechs ist dasselbe (`ABSAGEFORMEN.md`:43):

> **0 Prüferfehler + mindestens ein `C001` ⟹ `UNGEDECKT`** — und es ist ein PROGRAMM, kein
> Argument.

Der Prüfer nimmt an, der Erzeuger sagt ab. **`K003` ist die einzige Regel, die dazwischen
steht** — und sie kommt nicht zum Zug.

---

## 2. Was `K003` verlangt

Der ganze Pass steht in `crates/gabbro-check/src/kosten.rs` (Pass 9, `costs`). Es gibt **genau
eine** `K003`-Absagestelle im Baum, `kosten.rs`:364–382:

```rust
Kosten::Unbekannt(grund, span) => {
    z.offen += 1;
    if let Some(span) = span {
        absagen.schiebe(
            Absage::fehler("K003", span,
                format!("`{}` promises costs, but {grund}", f.name.text))
            .mit_notiz("a cost promise over an unknown quantity is a promise nobody \
                        can check"),
        );
    }
}
```

**Der Text ist zusammengesetzt, und darin steckt der ganze Inhalt.** `{grund}` kommt aus acht
Erzeugern von `Kosten::Unbekannt`, und sie sind nicht dieselbe Sorte Aussage:

| `kosten.rs` | Grund | was er sagt |
|---|---|---|
| :622 | *a `forever` loop has no total cost — its promise is `per_pass`, not `costs`* | **planmäßig** unbekannt |
| :786 | *the call to `X` declares no `costs`* | der Gerufene verspricht nichts |
| :791 | *`X` is not declared here* | den Gerufenen gibt es nicht |
| :602 | *the domain `D` of the traversal has no bound from a declaration* | die Menge ist offen |
| :615 | *the `bounded` bound of the `retry` is not fixed* | die Schranke ist nicht konstant |
| :698 | *the indirect call through `X` has no constant `costs` bound* | Funktionszeiger |
| :706 | *`X` is not a function pointer here* | Formfehler |
| :420 | *the cost calculation overflows* | die Zahl passt nicht mehr |

*Dass diese acht in EINER Kennung zusammenlaufen, ist der Grund, warum die Frage „greift `K003`
auch ohne Kostenzusage?" keine einzelne Antwort hat.* §5 nimmt sie auseinander.

### 2.1 Das Tor

`kosten.rs`:296–298, unmittelbar nach `K002`, `K006`/`K007` und `K008`/`K009`:

```rust
let Some(zusage_expr) = &f.costs else {
    return;
};
```

**Ohne `costs`-Zeile endet die Bearbeitung dieser Funktion hier.** `r.block(b)` wird dann nie
gerufen; es entsteht kein `Kosten::Unbekannt`, kein Grund, keine Absage. Die drei Regeln davor
hängen jede an ihrer *eigenen* Zusage (`held`, `bounded`, `decreases`) und sind davon unberührt.

> **`K003` ist ein Nachsatz zu einer Zusage. Ohne Zusage gibt es keinen Satz, zu dem er
> Nachsatz sein könnte.** Das ist keine Lücke im Pass — es ist seine Bauform: er prüft nicht,
> *ob* etwas berechenbar ist, sondern *ob eine Zahl hält*.

---

## 3. Warum es bei `divergent fn` nicht greift — und warum das KEINE Ausnahme ist

**Im Kostenpass kommt das Wort `divergent` nicht vor.** `grep -rn "FnKlasse::Divergent"
crates/gabbro-check/src/*.rs` liefert genau zwei Treffer, beide woanders (`wirkungen.rs`:844 für
`E003`, `schleifen.rs`:165 zum Einsammeln der Namen). **Es gibt keine geschriebene Ausnahme.**

Die Grammatik erlaubt einem `divergent fn` eine Kostenzusage ausdrücklich: `SYNTAX.md`:739–782
führt EINE `fndecl`-Regel für alle Klassen, und `costs <= expr ops` steht auf :778 ohne
Klassenbedingung.

**Gemessen, in beide Richtungen** (`messung/proben/` daneben, dieselbe Datei zweimal):

```gabbro
divergent fn schleife(w : u64) -> never
    effects { diverges }
    costs <= 4 ops                       -- <<< nur diese Zeile ist der Unterschied
{
    let x = niemand_hat_mich_erklaert(w);
    nichts();
}
```

```
MIT  der Zeile:   Fehler:  [K003] :7:13: `schleife` promises costs, but
                           `niemand_hat_mich_erklaert` is not declared here
                  -> 1 Fehler, 1 Hinweise
OHNE der Zeile:   Hinweis: [E009] :3:14: the call effects of `schleife` are undecidable
                  -> 0 Fehler, 1 Hinweise
```

> **`K003` greift bei einem `divergent fn` tadellos.** Es greift nur nie, weil **kein einziges
> `divergent fn` im Baum eine Kostenzusage trägt**: 15 Vorkommen von `divergent fn` in
> `.gab`-Dateien, **null** davon mit `costs`. *Die Ausnahme ist keine Regel des Prüfers, sondern
> eine Gewohnheit des Korpus — und sie hat einen guten Grund.*

**Der gute Grund steht im Pass selbst**, `kosten.rs`:620–626: der typische Rumpf eines
`divergent fn` ist eine `forever`-Schleife, und die hat keine Gesamtkosten. Gemessen:

```
divergent fn dienst() effects { pure } costs <= 4 ops {
    forever schleife per_pass bounded 2 ops on_exceeded wachhund effects { pure } { }
}
-> Fehler: [K003] `dienst` promises costs, but a `forever` loop has no total cost --
           its promise is `per_pass`, not `costs`
```

*Eine Kostenzusage über einem Dienst, der nicht endet, ist selbst der Fehler.* Genau deshalb
schreibt niemand sie hin — und genau deshalb steht das Tor offen.

---

## 4. Was der Prüfer stattdessen sagt

**Bei einem unbekannten Namen: `E009`, und das ist ein HINWEIS.**
`wirkungen.rs`:972–985; `Absage::hinweis` setzt `Stufe::Hinweis` (`diag.rs`:39–41), und
`fehler_zahl()` zählt nur `Stufe::Fehler` (`diag.rs`:74–77). `saetze.rs`:33–37 führt es als
Vorbedingung über allen Sätzen: *„Fünf Kennungen sind Hinweise: `E003`, `E009`, `V003`, `S007`,
`N026`."*

**Bei einer unbeschränkten Domäne: gar nichts.** `probe-vier-zellen.gab` — drei `divergent fn`
mit `queue`, `threads` und `chain in` — prüft mit **0 Fehlern und 0 Hinweisen**, `M1` sieht 100 %
der Ausdrücke. Erst `gabbro emit` sagt viermal `C001`. *Die Wirkungshülle ist vollständig; nur
die Schranke fehlt, und für eine fehlende Schranke gibt es ohne Kostenzusage keinen Leser.*

---

## 5. Gäbe es eine Form, die auch ohne Kostenzusage greift?

**Ja — drei, und sie sind DREI VERSCHIEDENE REGELN.** Der Unterschied ist nicht die Schärfe,
sondern der Gegenstand: die erste fragt nach einem RUMPF, die zweite und dritte nach einer
STELLE. *Wer sie für Abstufungen einer Regel hält, wird bei der Preisrechnung überrascht.*

### 5.1 Die Rechnung läuft heute schon ohne Tor — nur liest sie niemand

`kosten.rs`:988 (`pub fn bericht`, angebunden als `gabbro kosten` in `crates/gabbro-cli/src/main.rs`:92) benutzt
**denselben `Rechner`, aber kein Tor**: die Zusage ist dort nur eine Spalte (:1052). Gefahren
über die beiden Proben, ohne eine einzige `costs`-Zeile in den Dateien:

```
$ gabbro kosten messung/proben/probe-vier-zellen.gab
schlange_leeren   OFFEN  --  -- the domain `queue` of the traversal has no bound …
faeden_zaehlen    OFFEN  --  -- the domain `threads` of the traversal has no bound …
kette_gehen       OFFEN  --  -- the domain `chain(…) in` of the traversal has no bound …
-- 0 bodies computed, 3 open.

$ gabbro kosten messung/proben/probe-unbekannter-ruf.gab
schleife          OFFEN  --  -- `niemand_hat_mich_erklaert` is not declared here
-- 0 bodies computed, 1 open.
```

**Exakt die vier `K003`-Gründe, die den Zellen fehlen.** Was fehlt, ist nicht die Rechnung,
sondern der Leser. *Ein Werkzeug, das die Antwort druckt, und ein Wächter, der nicht hinsieht.*

### 5.2 Die drei Formen

| | Regel | Gegenstand |
|---|---|---|
| **α** | jeder Rumpf, dessen Gesamtkosten `OFFEN` sind, wird abgewiesen | ein RUMPF |
| **β** | wie α, aber `forever` bleibt erlaubt (es ist planmäßig offen) | ein RUMPF |
| **γ** | `E009` mit dem Grund *„`X` is unknown to the graph"* wird ein FEHLER | eine STELLE |

γ hat mit Kosten gar nichts mehr zu tun — die Rechnung dafür steht schon im Aufrufgraphen
(`aufrufgraph.rs`:398), und sie ist heute nur nicht als Absage gebucht.

---

## 6. Die Rechnung: was jede Form kostet

**Über alle 418 Dateien**, mit den 92 fehlerfreien als Preisbasis:

```
Rumpfe gerechnet (alle Dateien):   487
Rumpfe OFFEN     (alle Dateien):    37
Rumpfe OFFEN in sauberen Dateien:   14   in 9 Dateien
```

| Grund des `OFFEN` | alle | in sauberen Dateien |
|---|---:|---:|
| `forever` (Dienstschleife) | 13 | **8** |
| Gerufener ohne `costs` | 9 | **2** |
| Domäne ohne Schranke | 6 | **3** |
| Gerufener nicht deklariert | 6 | **1** |
| indirekter Ruf | 2 | 0 |
| kein Funktionszeiger | 1 | 0 |

### α — jeder offene Rumpf fällt: **9 Dateien, 14 Absagen**

```
  2  beispiele/04-schleifen.gab            dienstschleife, manifest_pruefen   (forever)
  2  beispiele/39-auftragsdienst.gab       abarbeiten, dienst                 (forever)
  2  beispiele/41-handschlag.gab           uebertragen_lassen, kern_starten   (forever)
  1  beispiele/42-zaehlwerk.gab            sammeldienst                       (forever)
  1  beispiele/54-divergenz-leckt-nicht.gab abschluss                         (forever)
  1  messung/fragmente/F05.gab             run     -- `signal` ohne `costs`
  1  messung/fragmente/F06.gab             messen_benutzt -- `unberuehrt` ohne `costs`
  1  messung/proben/probe-unbekannter-ruf.gab schleife -- Name unbekannt
  3  messung/proben/probe-vier-zellen.gab  queue / threads / chain in
```

**Acht von vierzehn sind FALSCH.** `forever` hat keine Gesamtkosten, und die Sprache hat dafür
schon eine Antwort (`per_pass`) — α würde die Dienstschleife abschaffen, also genau die Form,
für die `divergent fn` gebaut wurde. *Fünf Beispiele des Korpus fielen, und keines davon hat
eine Lücke.*

### β — `forever` bleibt erlaubt: **4 Dateien, 6 Absagen**

`F05`, `F06`, `probe-unbekannter-ruf`, `probe-vier-zellen`.

**Und hier steht der Preis, der weh tut:** `F06` fällt, weil `messen_benutzt` die Funktion
`unberuehrt` ruft und **keine der beiden eine `costs`-Zeile trägt**. β heißt damit nicht „eine
Lücke wird geschlossen", sondern **`costs` wird transitiv zur Pflicht** — jeder Rumpf, der
irgendetwas ruft, muss die Kette bis unten deklariert haben. *Genau das Fragment, dessen
Absenkungspflicht heute Nacht durch Ausführung eingelöst wurde (`H` fiel von 5 auf 4), wäre
danach kein gültiges Programm mehr.*

### γ — `E009 unknown to the graph` wird ein Fehler: **2 Dateien, 2 Absagen**

`E009` trägt **fünf** verschiedene Gründe, und nur einer davon ist eine Lücke. Gemessen:

| Grund von `E009` | alle | in sauberen Dateien |
|---|---:|---:|
| *`X` is unknown to the graph* | 9 | **2** — `F05`, `probe-unbekannter-ruf` |
| *cycle over `X`* (Rekursion) | 7 | 3 — alle in `beispiele/33-rekursion.gab` |
| *the callee at `t->f` is not statically known* | 4 | 0 |
| *an argument of the call … is not a place* | 2 | 0 |

**γ kostet über 418 Dateien genau zwei Programme, und beide sind die Proben, die die Zellen
sichtbar machen.** Null Kollateralschaden.

> **Aber `E009` als GANZES zum Fehler zu machen, wäre falsch**, und das ist derselbe Fund eine
> Ebene tiefer: `beispiele/33-rekursion.gab` trägt drei `E009` mit dem Grund *cycle over* — das
> ist gewöhnliche Rekursion, keine Lücke. *Eine Kennung mit fünf Gründen ist wie `K003` mit
> acht: wer sie im Ganzen anfasst, trifft vier Dinge, die er nicht meinte.*

---

## 7. Was KEINE der drei erreicht: `state` (U12)

`kosten.rs`:259–264:

```rust
crate::fuer_jedes_item_im_modul(baum, &mut |item, modul| {
    let ItemArt::Funktion(f) = &item.art else { return; };
    let FnRumpf::Block(b) = &f.rumpf else { return; };
```

**Ein `state`-Item ist keine Funktion und hat keinen Block.** Der Kostenpass sieht es nie — nicht
mit Tor und nicht ohne. Von den sechs Zellen sind damit **fünf** über `K003`-Bauformen
erreichbar (U11, U13, U14, U15 unmittelbar; U10 mit dem Vorbehalt unten) und **eine nicht**:
*U12 braucht eine Regel an einer anderen Stelle, oder sie bleibt eine Erzeugerabsage.*

### 7.1 Der Vorbehalt bei U10, und er ist gemessen

`Kosten::Unbekannt` **kurzschließt**: `plus` (:402), `schleife` (:594) und `groesser` (:966)
geben den ERSTEN unbekannten Grund weiter. Was der Bericht je Rumpf nennt, ist damit die erste
Ursache und nicht die einzige.

Für `F05` heißt das: gemeldet wird *„the call to `signal` declares no `costs`"* (Klasse β).
Nachgemessen an einer Kopie, in der `signal` und `exit` eine Zusage bekommen:

```
run  OFFEN  --  -- a `forever` loop has no total cost -- its promise is `per_pass`, not `costs`
```

> **`F05`s `run` IST eine Dienstschleife**, und der undeklarierte `decode_op` steht darin.
> **Keine Form von `K003`, die `forever` respektiert, kann ihn je sehen** — der Weg zur
> Gesamtzahl endet vorher, planmäßig. *U10 ist über den Kostenweg nicht erreichbar; über γ
> ist er es, weil γ nach einer STELLE fragt und nicht nach einem Rumpf.*

**Und daraus folgt die Vorsicht für jede Zahl in §6:** die Aufteilung nach Gründen ist eine
untere Schranke für die späteren Klassen. Wer die frühen Ursachen entfernt, bekommt neue Gründe
zu sehen, die heute hinter ihnen liegen.

---

## 8. Die Übersicht, und was danach noch offen bleibt

| | α | β | γ |
|---|---|---|---|
| Dateien, die heute durchgehen und dann fielen | **9** | **4** | **2** |
| davon zu Unrecht | 5 (`forever`) | 2 (`F05`, `F06` — `costs` würde Pflicht) | 0 |
| U10 (`match` über unbekannten Ruf) | — *(hinter `forever`)* | — *(hinter `forever`)* | **zu** |
| U11 (`let` ohne Typ) | zu | zu | **zu** |
| U12 (`state`) | — *(kein Funktionsrumpf)* | — | — |
| U13/U14/U15 (`queue`/`chain in`/`threads`) | zu | zu | — *(kein Name fehlt)* |

**Keine einzelne Form schließt alle sechs.** Die günstigste Deckung, die diese Messung findet,
ist **γ für U10/U11 und β-ohne-`forever`-und-ohne-„Gerufener ohne `costs`" für U13–U15** — also
eine Regel, die nur *„die Domäne hat keine Schranke aus der Deklaration"* zum Fehler macht.
Deren Preis über die 418 Dateien: **eine Datei**, `probe-vier-zellen.gab`, die genau dafür
geschrieben wurde. **U12 bleibt in jedem Fall übrig.**

*Ob das getan wird, ist nicht Gegenstand dieses Dokuments.* Der Plan kennt für eine
`UNGEDECKT`-Zelle zwei volle Ausgänge — absenken oder **im Prüfer** absagen
(`PLAN-VOLLSTAENDIGKEIT.md`:142–151) —, und *„der Erzeuger sagt es benannt"* ist keiner von
beiden. **Was NICHT geht, ist die Zelle offen zu lassen.** Welcher der beiden Ausgänge je Zelle
gegangen wird, ist eine Aussage darüber, was Gabbro sein soll, und sie gehört dem Ordner.

### Was diese Rechnung NICHT sagt

* **Sie sagt nicht, dass γ billig ist.** Zwei Dateien sind der Preis *im heutigen Korpus*, und
  der ist nach Schwierigkeit gewählt und mit den Sprachdokumenten daneben geschrieben
  (Falle 80). Ein zweiter Korpus kann jede dieser Zahlen vervielfachen.
* **Sie sagt nichts über die Richtigkeit der Schranke.** `saetze.rs`:1228–1265 führt
  `kosten.domaenenschranke` als **`VERMUTET`** mit dem eigenen Vorbehalt: *„`K003` has 2 probes,
  and they measure that a MISSING bound is refused — not that a PRESENT one is right."* Eine
  Regel schärfer zu machen, deren Rechnung `VERMUTET` ist, verschiebt das Vertrauen und schafft
  es nicht.
* **Sie ist mit EINEM Binärprogramm gemessen** (`9c0a3fa`, gebaut auf `fisch`). Die zweite Bahn
  arbeitet am selben Abend an `kosten.rs`, `umgebung.rs` und `domaene.rs`; nach dem
  Zusammenführen gehören die Zahlen aus §6 nachgefahren, bevor jemand auf sie baut.
