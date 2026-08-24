# Der Prüfer war nicht deterministisch — gefunden beim Versuch, `V2` zu messen

*Gemessen am 2026-08-24 auf `ki-pc-fisch-101`. Der Fund kam aus einer Übung, die etwas
anderes wollte.*

> **Derselbe Quelltext, zwanzigmal im selben Prozess geprüft:**
>
> ```
> ZEHNMAL DASSELBE PROGRAMM:  leer=13  mit-Absage=7
> ZEHNMAL DASSELBE PROGRAMM:  leer=8   mit-Absage=12
> ZEHNMAL DASSELBE PROGRAMM:  leer=9   mit-Absage=11
> ```
>
> **Ein Prüfer, dessen Urteil ein Münzwurf ist, ist schlimmer als einer, der falsch liegt:**
> er ist grün in der Prüfkette und rot auf dem Tisch, bei byteidentischen Quellen.

---

## 1. Wie er gefunden wurde, und das ist die Lehre

Er wurde **nicht** von einem Werkzeug gemeldet. Er fiel an, weil ich für
[`V2.md`](V2.md) ein Paar bauen wollte — zwei Programme, die sich in einer Zeile
unterscheiden — und die zwei Hälften **einander widersprachen**:

| Weg | Urteil |
|---|---|
| `gabbro pruefe beispiele/gift/257-…gab` (Kommandozeile) | `M104` + `M101` — **dreimal hintereinander** |
| derselbe Code im Testrahmen, byteidentische Datei (md5 verglichen) | **keine einzige Absage** |

*Zwei Urteile über einem Gegenstand — dieselbe Klasse wie `W16`, wie der `rsync -a`-Fund und
wie die `.claude/worktrees`-Zählung von heute früh.* **Diesmal lag es nicht am Werkzeug,
sondern am Prüfer selbst.**

Die Zwischenschritte, weil sie alle in die Irre führten und das dazugehört: der Dateiname
(nein), der Pfad (nein), eine veraltete Übersetzung (nein), globaler Zustand im Prüfer (es gibt
keinen). **Erst die Wiederholung im selben Prozess zeigte es.**

---

## 2. Die Ursache, soweit sie GEMESSEN ist

```rust
// umgebung.rs, sammle()
let namen: Vec<String> = u.roh_typen.keys().cloned().collect();
for n in namen { … u.typen.insert(n, u.typ_aufloesen(…)); }
```

`HashMap::keys()` iteriert in einer Reihenfolge, die Rust **je Kartenexemplar zufällig**
setzt. Die Auflösungsreihenfolge der Typdeklarationen wechselt damit von Lauf zu Lauf.

**Behoben durch Sortieren**, an beiden Stellen (`roh_konst` und `roh_typen`). Danach: zwanzig
von zwanzig Läufen gleich, dreimal wiederholt.

> **Und was hier NICHT gemessen ist: der Mechanismus.** `typ_aufloesen` steigt bei einem
> unaufgelösten Namen in `roh_typen` ab, *sollte* also reihenfolgeunabhängig sein. Warum die
> Reihenfolge trotzdem durchschlägt, habe ich **nicht** aufgeklärt. *Die Sortierung beseitigt
> den Münzwurf; ob sie die Ursache trifft oder nur verdeckt, ist offen* — und das gehört als
> offener Posten gebucht und nicht als behobener.

---

## 3. Der zweite Befund, und er ist der unangenehmere

**Sortiert steht das Urteil fest — und es lautet: keine Absage.**

Das geprüfte Programm war:

```gabbro
type Zahl = u32 in 0 .. 1000;
type Paar = { a : Zahl, b : Zahl, };

impl fn abstand(p : ptr<normal, rw> Paar, q : ptr<normal, rw> Paar) -> Zahl … {
    if p->a >= p->b {
        q->b = 1000;            -- kann DASSELBE Wort sein: keine Aliasanalyse
        return p->a - p->b;     -- Unterlauf, wenn es dasselbe war
    }
    return 0;
}
```

`M104` bleibt aus. **Damit ist offen, ob M1 hier überhaupt einen Bereich hat** — und wenn
nicht, prüft der Bereichspass an dieser Stelle nichts, statt etwas Falsches zu prüfen.

> *Sortiert löst `Paar` vor `Zahl` auf — alphabetisch. Ob das der Grund ist, ist genau die
> Frage aus §2, die offen bleibt.*

**Der bestehende Korpus ist NICHT betroffen**, und das ist gemessen: sechs Läufe der ganzen
Testsammlung auf dem Stand `97b0574` (ohne die Sortierung), **null Fehlschläge**; fünf Läufe
mit der Sortierung, ebenso. *Der Defekt ist latent, nicht aktiv* — die Form, die ihn auslöst
(ein Verbund über einem benannten Bereichstyp, hinter einem Zeiger), stand bis heute in keiner
Datei.

---

## 4. Was das über die anderen Zahlen sagt

**„186 Tests bestehen" war eine Aussage über den Zufallswert EINES Laufs.** Sie war nicht
falsch — der Korpus trifft die Form nicht —, aber sie war schwächer, als sie klang, und
niemand konnte das wissen.

Dasselbe gilt für jede Zahl dieses Ordners, die aus einem Prüferlauf kommt: die 283/286/287
Mutationen, die 255 Giftproben, `50 von 50` in der Emission. **Sie sind heute wieder das, was
sie zu sein behaupten** — vorher waren sie es nur mit einer Wahrscheinlichkeit, die niemand
gemessen hat.

> **Und die Prüfkette konnte es nicht sehen.** Ein Wächter, der einmal läuft, misst einen
> Münzwurf. *Was fehlt, ist eine Probe, die denselben Gegenstand ZWEIMAL prüft und die
> Ergebnisse vergleicht* — genau die Bauart, die `pruefe-emission.sh` für die Emission schon
> hat (`1b. zweitlauf: ok (bitgleich)`) und die dem PRÜFER fehlte.

---

## 5. Was daraus folgt, geordnet

| | |
|---|---|
| **gebaut** | die Sortierung an beiden Auflösungsschleifen |
| **offen, und es ist der eigentliche Posten** | **warum** die Reihenfolge durchschlägt, obwohl `typ_aufloesen` absteigt |
| **offen** | `pruefe-emission.sh` prüft die EMISSION auf Bitgleichheit im Zweitlauf. **Der Prüfer hat diese Probe nicht** — sie ist billig und sie hätte das hier am ersten Tag gefunden |
| **zurückgezogen** | die Messung in [`V2.md`](V2.md) §5. Sie ruhte auf der einen Seite des Münzwurfs |

**Und ein Satz zum Verfahren, weil er das Teuerste an diesem Fund ist:** die Übung, die ihn
gebracht hat, war *„schreibe den Korrektheitsbeweis auf"*. Sie hat in zwei Sätzen zwei Fehler
gefunden, gegen die 287 Mutationen und 256 Giftproben blind waren — **nicht weil die Proben
schlecht sind, sondern weil niemand die Frage gestellt hatte, die sie beantworten müssten.**
