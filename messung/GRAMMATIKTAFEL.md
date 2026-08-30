# FORM × ZUSTÄNDIGKEIT aus der GRAMMATIK — und `UNGEDECKT` fiel von 13 auf 4

*Bahn V, Schritte V-2 und V-5 des `dokumente/PLAN-VOLLSTAENDIGKEIT.md`. Gemessen und gebaut
am 2026-08-31. Werkzeug: `./instrumente/pruefe-grammatiktafel.py`.*

> **Der Unterschied zu `gabbro blindstellen` ist die Grundgesamtheit, und darin liegt alles.**
> Jenes rechnet FORM × POSITION über einem **Korpus** und sagt von sich selbst: *der Korpus
> ist von der Sprache nach außen geschrieben.* **Falle 80.** Hier ist die Grundgesamtheit die
> **Grammatik**: `dokumente/SYNTAX.md` führt 154 Regeln und **219 Terminale**, und das ist
> die Menge, die „beliebig" meint.

---

## 1. Die vier Zustände, und wie jeder gemessen wird

```
gesenkt       ein Programm mit diesem Wort emittiert C -- OHNE eine einzige Absage
abgesagt      der Erzeuger sagt es benannt ab, und ein PRUEFERFEHLER nennt es auch
vom Pruefer   nur ein Prueferfehler nennt es; der Erzeuger sieht die Form nie
UNGEDECKT     keines davon
```

**`gesenkt` ist ein LAUF und keine Lesung.** Ein Wort gilt genau dann als abgesenkt, wenn es
in einer `.gab`-Datei steht, die **vollständig emittiert**: null Prüferfehler *und* null
`C001`. Dann ist alles, was in dieser Datei steht, durch den Erzeuger gegangen — das Wort
eingeschlossen.

**Und das trägt, weil der Wortschatz geschlossen ist.** `kw.rs` führt 213 der 222 Wörter als
`res` — reserviert, nirgends ein Bezeichner. *Ein Vorkommen IST damit ein Schlüsselwort.* Die
sechs verbleibenden `ctx`-Wörter (`child`, `observed`, `occupied`, `parent`, `sibling`,
`tree`) können ein Bezeichner sein; sie stehen neben dem Urteil, statt still mitzulaufen.

### Drei Register, gelesen statt kopiert (W7)

| was | woher |
|---|---|
| die 219 Terminale | `pruefe-wortschatz.py` — es hält sie schon gegen die EBNF |
| die 130 Absageformen | `zaehle-absagen.py` — 139 Stellen in `emit.rs` |
| die Prüferfehler | `Absage::fehler(…)` in jeder `gabbro-check/src/*.rs` **außer** `emit.rs` |

*Ein zweites Register über derselben Sache läuft weg* — dieser Ordner hat das oft genug
bezahlt, dass es keine dritte Kopie der Terminalliste gibt. **`Absage::hinweis` zählt
ausdrücklich nicht:** ein Hinweis weist nichts ab. `beispiele/gift/166` trägt `S007` als
Hinweis, prüft mit null Fehlern und fällt erst am `C001` — *ein Wächter, der Hinweise als
Absagen zählt, liest seine eigene Nachsicht als Deckung.*

---

## 2. Der erste Lauf: 13 UNGEDECKT — und neun davon waren nur ungeschrieben

```
gesenkt       205
abgesagt        0
vom Pruefer     1
UNGEDECKT      13
```

| Wort | wo es in der Grammatik steht | Befund |
|---|---|---|
| `i8` `i16` `i32` `i64` | `intty` (`SYNTAX.md`:356) | **kein Programm des Baumes schrieb je einen vorzeichenbehafteten Typ** |
| `f32` | `floatty` (:357) | dito — `f64` steht in zwei Dateien, `f32` in keiner |
| `and` | `accdecl … merge` (:283) | die fünfte Faltung; `max`, `min`, `add` sind geschrieben, `or` und `and` nicht |
| `port` | `space` (:463) | ein Adressraum ohne einen einzigen Zeiger |
| `rc` | `regklasse` (:1288) | *read to clear* — nie an einem Register geschrieben |
| `seq` | Ordnung am `atomic` (:1375) | `acquire`, `release`, `relaxed` sind geschrieben, `seq` nicht |
| `chain` `queue` `state` `threads` | Domänen und ein Item | **der Erzeuger sagt sie benannt ab, und der Prüfer nimmt sie an** |

> **Neun der dreizehn waren keine Lücke im Erzeuger, sondern eine im KORPUS** — und genau das
> ist der Satz, den `blindstellen` über sich selbst schreibt: *was 0 Fundstellen hat, ist
> nicht geprüft, sondern unerreichbar.* Eine Absenkung, die nie gelaufen ist, ist eine
> Vermutung mit einem Namen.

---

## 3. Die Antwort darauf: zwei Programme, aus der Grammatik geschrieben

`messung/grammatik/` — **von der Grammatik nach innen, nicht von einer Absicht nach außen.**

| Datei | schließt |
|---|---|
| `zahlbreiten.gab` | `i8`, `i16`, `i32`, `i64`, `f32`, `merge and` |
| `geraeteworte.gab` | `port`, `rc`, `seq` |

Beide prüfen mit **0 Fehlern**, emittieren und übersetzen unter `cc -Werror` (`-O0` und
`-O2`, Stufe 9). Damit fällt die Tafel:

```
gesenkt       214        UNGEDECKT   4
abgesagt        0        vom Pruefer 1   (`masked`)
```

**Und die neun Absenkungen, die dabei zum ersten Mal gelaufen sind, haben ZWEI Befunde
abgeworfen.** Das ist der eigentliche Ertrag; die Zahl ist nur die Buchhaltung.

### Befund 1 — ein `f32`-Ausdruck rechnet in `double`

`gleitkommatext` (`emit.rs`) schreibt `f64::from_bits(bits)` ohne Suffix hin. In C ist ein
Literal ohne `f` ein **`double`**:

```c
static float zehntel(float x) {
    return x * 0.1;          /* float * double -> double, und erst die Rueckgabe rundet */
}
```

Gemessen in reinem C über 200 000 Werten:

```
(float)(v * 0.1)  !=  v * 0.1f     in 39 974 von 200 000 Faellen
```

**Der Prüfer nimmt das Programm mit 100 % Typdeckung an, und das erzeugte C rechnet etwas
anderes, als dasteht.** Die Probe steht als `messung/proben/probe-f32-literal.gab` im Baum;
der Posten ist in `TODO.md` gebucht. *Er wird hier nicht nebenbei entschieden* — welche
Breite ein Literal in einem `f32`-Ausdruck hat, ist eine Aussage über das Zahlmodell, und
`dokumente/MEMO-GLEITKOMMA.md` führt die Doppelrundung bereits als Landmine.

### Befund 2 — der Adressraum `port` verschwindet in der Absenkung

`ptr<port, r> Stand` wird `const Stand *restrict p`, und `p.bereit` wird ein gewöhnlicher
Ladebefehl. **`ctyp` liest `z.raum` überhaupt nicht** — für einen Zeiger ist der Raum eine
Prüfertatsache und im C nicht sichtbar. Bei `mmio` fängt das der Geräteweg auf (`volatile` an
`basis + Versatz`); bei `port` fängt es nichts auf.

> *Ob das ein Fehler ist, hängt daran, was `port` verspricht* — auf x86_64 ist Portraum kein
> Speicher, sondern `in`/`out`. Die Frage steht in `TODO.md`, mit der Messung daneben und
> ohne Antwort: **eine Entscheidung über einen Adressraum gehört nicht in einen Nebensatz.**

---

## 4. Was offen bleibt: vier Zellen, und alle vier dieselbe Bauart

```
! GRAMMATIKTAFEL ROT: 4 von 219 Terminalen sind UNGEDECKT.
    chain            der Erzeuger sagt ab, der Pruefer nicht
    queue            der Erzeuger sagt ab, der Pruefer nicht
    state            der Erzeuger sagt ab, der Pruefer nicht
    threads          der Erzeuger sagt ab, der Pruefer nicht
```

**Der Prüfer nimmt jede der vier Formen an, und erst der Erzeuger sagt ab.** Das ist genau
der Zustand, den der Plan verbietet — und der Ausgang steht dort auch: *im PRÜFER absagen,
dann wandert die Zelle nach `vom Pruefer`.* **Eine Sprache, die eine Form nicht hat, ist
vollständig, solange sie das sagt.**

*Das ist eine Entscheidung über die SPRACHE und keine über den Erzeuger* — vier Formen fallen
damit aus Gabbro heraus. Sie gehört dem Ordner und der Bahn, die am Prüfer arbeitet, und
steht darum hier als Arbeitsmenge und nicht als erledigt.

---

## 5. Die Sprechprobe — in beide Richtungen, und beide waren gefordert

```
ok   entfernte Absenkung `acquire` faellt als UNGEDECKT
ok   und im sauberen Lauf ist `acquire` gesenkt
ok   erfundene Grammatikregel `zztafelprobe` faellt als UNGEDECKT
ok   und sie steht nicht schon in der echten Grammatik
```

Die zweite Richtung läuft über eine **Kopie von `SYNTAX.md`** mit einer eingeschobenen Regel
— also durch dieselbe Extraktion, die auch die echten 219 liefert, und nicht durch eine
zweite. Die erste unterdrückt die Korpusbelege für ein Wort, das heute allein durch die
Absenkung gedeckt ist. *Ein Werkzeug, das über die Sprache urteilt und selbst ungeprüft ist,
ist die teuerste Sorte Wächter.*

**Und der Lauf bricht ab, bevor er urteilt, wenn die Probe fällt** — Rücklaufwert 2, nicht 1:
ein Wächter, der nichts gemessen hat, ist kein Befund.

---

## 6. Was diese Tafel NICHT sagt

1. **Eine besetzte Zelle heißt, dass es eine Absenkung GIBT — nicht, dass sie richtig ist.**
   `messung/fragmente/F06.gab` emittierte 161 Zeilen, die `cc -Werror` zurückwies, und diese
   Tafel hätte sein Wort als `gesenkt` geführt. Die Gegenprobe dafür ist **Stufe 9** von
   `pruefe-emission.sh`, und sie läuft seit heute auch über `messung/`.
2. **Ein Terminal ist nicht dasselbe wie eine Form.** `SYNTAX.md` führt 154 Regeln; diese
   Tafel steht über den 219 **Wörtern**. Eine Regel, die aus lauter gedeckten Wörtern eine
   ungedeckte Kombination baut, fällt hier nicht auf — *das ist genau die Klasse, für die
   `gabbro blindstellen` über dem Korpus gebaut wurde*, und die zwei Werkzeuge decken
   einander nicht ab, sondern ergänzen sich.
3. **Für die sechs `ctx`-Wörter ist `gesenkt` eine OBERE Schranke.** Ein Vorkommen kann ein
   Bezeichner sein. Sie werden bei jedem Lauf genannt.
