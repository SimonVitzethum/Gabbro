# Die Ordnungsstichprobe — das Protokoll steht VOR der ersten gelesenen Stelle

*Geschrieben am 2026-08-28, **bevor** eine einzige Stelle angesehen wurde. Das ist keine
Förmlichkeit: entscheidet man die Fächer erst beim Lesen, wandert jede unbequeme Stelle in das
weichste Fach, und die Stichprobe bestätigt sich selbst.*

> **Was gemessen wird:** ob §1 der Ergänzung (`SPRACHE.md` Teil II) über den 2 231
> `Ordering::`-Stellen von Caprock trägt. **Die Messung ist ZWEISEITIG** — sie kann §1
> bestätigen, und sie kann ihn widerlegen. Ein Zeitplan, der beide Ausgänge mit einer Zahl
> belegt, ist keine Schätzung.

---

## 1. Die drei erlaubten Ausgänge — und der vierte

§1 sagt es selbst; hier steht es als Zählregel, damit niemand es beim Lesen neu erfindet.

| | Fach | **Prüffrage, wörtlich** |
|---|---|---|
| **P** | **Paarung** | Trägt der Zugriff eine NUTZLAST, die ein anderer Kern nach diesem Zugriff lesen darf? Also: Botschaftsübergabe, Erzeuger→Verbraucher, Besitzübergabe, Flagge mit Nutzlast. **Ein `publishes`/`awaits`-Paar wäre schreibbar.** |
| **Z** | **Zähler** | Trägt er KEINE Nutzlast — eine Statistik, eine Kennzahl, ein Erzeugungszähler? `relaxed` mit `publishes nothing`, kein `awaits`. |
| **S** | **benannter `seq`-Fall** | Hängt die Korrektheit an einer **globalen Ordnung über MEHRERE Atomics**? |
| **X** | **der VIERTE Ausgang** | Alles, was in keines der drei passt. **Ein einziges X widerlegt §1** und ist der wertvollste Fund dieser Messung. |

### Die Schärfung, an der alles hängt: was **S** NICHT ist

> **`SeqCst` allein macht keinen `seq`-Fall.** §1 sagt wörtlich: *„Algorithms whose correctness
> hangs on a **global** seq order over **several** atomics."* Eine `SeqCst`-Stelle, die in
> Wahrheit eine Nutzlast überträgt, ist eine **P**, und die Ordnungsstärke ist dort nur zu
> stark gewählt.

**Zwei Bedingungen, beide nötig, sonst ist es kein S:**

1. die Korrektheit hängt an der **Reihenfolge**, nicht an der Sichtbarkeit einer Nutzlast, **und**
2. sie hängt an einer Ordnung über **mindestens zwei verschiedenen** Atomics.

*Ohne diese zwei Zeilen ist **S** das Fach, in das jede unbequeme Stelle wandert — und dann
misst die Stichprobe ihre eigene Nachsicht.* §1s Vermutung lautet „einstellig"; sie steht als
Vermutung da und wird hier geprüft, nicht bestätigt.

## 2. Die Wegfälle — sie gehören in die Zählregel, nicht in die Überraschung

`AN-CAPROCK.md` führt sie seit dem 2026-08-16 als **Wegfälle, nicht als Widerlegungen**. Wer sie
erst beim Lesen einordnet, bekommt sie als Befund serviert und ordnet sie dann ein — genau
verkehrt herum.

| | Wegfall | Fach |
|---|---|---|
| **K1** | die Stelle steht **unter einer Sperre**, die sie ohnehin ordnet — in Gabbro fällt das Atomic weg | **W** (Wegfall), kein X |
| **K2** | die Stelle liegt **im Inneren eines Konstrukts** (`lock`, `accumulates`, `rcu`): sie zählt zur Schablonenfläche, nicht zur Stichprobe | **W** |
| **K3** | `accumulates` mit einem Verbund deckt sie **strikt besser** als das Original (`caprock-sync:572-592`) | **W** |
| **K4** | die Stelle steht in **Mess- und Selbsttestgerüst** (`fuzz.rs`, `*mark.rs`, `selftest`, `bringup`-Diagnose): in Gabbro `check … when TESTBUILD`, im ausgelieferten C nicht vorhanden | **W** |

**Ein W ist kein Ausgang, sondern ein Ausschluss** — es wird gezählt und aus dem Nenner
genommen, und die Zahl der W steht im Bericht neben der Zahl der P/Z/S.

## 3. Die Schichtung — gleichverteilt, nicht proportional

```
2 231 Stellen in 36 Dateien:
  threads/mod.rs 872 (39 %) · bringup.rs 390 (17 %) · system.rs 184 (8 %) · fuzz.rs 112 (5 %)
  -> die vier groessten tragen 70 %
```

**Eine proportionale Ziehung wäre zu 39 % eine Messung über EINER Datei.** Also:

| Schicht | Dateien | je Datei | Summe |
|---|---|---|---|
| **A** — ≥ 100 Stellen | 4 | **5** | 20 |
| **B** — 10 … 99 Stellen | alle | **1** | ~11 |
| **C** — 1 … 9 Stellen | die 5 mit den meisten | **1** | 5 |
| | | | **≈ 36 ≥ 30** |

**Der Zug ist DETERMINISTISCH und nachziehbar**, nicht zufällig: in jeder Datei werden die
`Ordering::`-Stellen in Quellreihenfolge nummeriert (1..N), und gezogen wird an den Positionen
`round(k * N / (m+1))` für `k = 1..m`. *Wer die Messung nachrechnen will, bekommt dieselben
Stellen.* Eine zufällige Ziehung wäre hier nicht ehrlicher, nur unwiederholbar.

## 4. Was der Bericht enthalten muss

Je gezogener Stelle **eine Zeile**: `datei:zeile · Ordering-Wort · Fach (P/Z/S/W) · ein Satz
Begründung, der die Prüffrage aus §1 beantwortet.` Dazu die Summe je Fach, die Zahl der W mit
ihrem K-Grund, und — falls vorhanden — **jedes X ausgeschrieben, mit vollem Kontext.**

> **Und was diese Messung NICHT sagt:** dass §1 über den restlichen 2 195 Stellen trägt. Sie ist
> eine Stichprobe mit 36 Stellen, geschichtet gegen die Klumpung, deterministisch gezogen.
> *Sie kann §1 widerlegen; bestätigen kann sie ihn nur für ihren eigenen Umfang.*
