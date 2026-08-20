# Der vervollständigte Fragmentkorpus

**Dies sind dieselben zehn Fragmente wie in [`dokumente/FRAGMENTE.md`](../../dokumente/FRAGMENTE.md) — byteidentisch, plus genau die Zeilen, die sie zu Programmen machen.**

## Warum es diesen Ordner gibt

K100s Absenkungspflicht lautet: *„das erzeugte C rechnet, was das Fragment sagt"* — **an der Ausführung gemessen.** Sieben der zehn erfüllten sie nicht, und am 2026-08-20 wurde nachgezählt, woran das liegt:

```
41 Stellen nennen 20 Namen, die niemand deklariert
   (MAX_POLL · EP_BADGE · SYSNO_RESULT · Fehler · NTFN · IpcResult · …)
 9 `let … else` rufen Rümpfe, die diese Einheit nicht kennt
 6 Bitlagen sind unbenannt
 1 Tabelle nennt kein `tree`, 1 Gerufener kein `or <reason>`
```

**Jedes der sieben trug mindestens einen korpusseitigen Riegel.** F4 — das reinste — brauchte genau eine Zeile: `MAX_POLL`. Ohne sie nennt die `bounded`-Klausel nichts.

Damit fiel die Absenkungsspalte **um keinen Punkt**, solange `FRAGMENTE.md` unangetastet bleibt — und die Datei trägt ihren Einfriersatz: *„ein Bericht vom 2026-08-14, und er bleibt unangetastet."*

> **Ein Ausschnitt lässt sich nicht ausführen.** Die sieben zu schließen hieße, eine eingefrorene Datei zu ändern — das ist nicht das Schließen einer Pflicht, sondern das Verschieben des Maßstabs.

## Die Regel dieses Ordners

**Je Datei steht im Kopf, was ergänzt wurde — und was nicht.** Es ist derselbe Zug wie bei «K2»: *nachgebildet, nicht übersetzt, und ausdrücklich gesagt.* Wer die Zahl liest, sieht daneben, welcher Teil gemessen und welcher geschrieben ist.

Ergänzt werden **nur** Deklarationen, die der Ausschnitt ruft und nicht nennt. Nichts wird umgeschrieben, nichts weggelassen, keine Absage wegdefiniert. **Wo ein Fehler nach der Vervollständigung stehen bleibt, gehört er Gabbro** — und genau das ist der Ertrag.

## Der Stand

```
$ ./zaehle-fragmente.py
7 von 10 prüfen sauber        (vorher: 5)
4 von 10 senken ab            (vorher: 3)
```

| | ergänzt | was danach noch fällt |
|---|---|---|
| **F1** | `reason Fehler` | `Fehler::Buchfuehrung` — **ein `reason`-Wert hat keinen Erzeuger** |
| **F2** | fünf `reserved`-Felder | — *prüft sauber, senkt ab, übersetzt* |
| **F3** | vier Konstanten, `or EpVoll` an `enqueue` | 3× `IpcResult::…`, `M101` Optionssonderwert, `H011` `locks SCHEDS` nie genommen |
| **F4** | `MAX_POLL`, `assume`, `on_exceeded`-Ziel | — *prüft sauber*; Absenkung an der `dma`-Barriere |
| **F5** | neun Konstanten, fünf `extern fn` mit Kanal, ein `assume` | 3× `Status::…` — derselbe Befund wie F1 |
| **F6** | zwei Konstanten, `IrqMarke`+`static irq`, zwei Kanäle, ein Tor | — *prüft sauber*; Absenkung an «B12» `elems of` |
| **F7 F8 F10** | nichts | — *waren schon Programme* |
| **F9** | zwei `reserved`-Felder | — *prüft sauber*; drei Gabbro-Absagen, siehe Kopf der Datei |

## Der Ertrag: drei Befunde, die der eingefrorene Korpus nicht zeigen konnte

**1. `A::B` parst und wird nie aufgelöst.** `path = ident { "::" ident }` steht in der Grammatik; der Namenspass liest die **erste Silbe** und schlägt sie als Wert nach. `IpcResult::Ok` fällt als `M119`, gleichgültig ob `IpcResult` ein `module`, ein `reason` oder ein Variantentyp ist — alle drei geprüft.

**2. Ein `reason`-Wert hat keinen Erzeuger.** `primary` (`SYNTAX.md`:405) kennt keine Produktion dafür. **Jede `-> T or R`-Signatur im Korpus steht an einem `extern fn`** — an einem Rumpf, den Gabbro nie sieht. *Keine einzige Gabbro-Funktion erzeugt je einen Grund.*

> **Dieselbe Gestalt wie «B9» bei `fnptr`:** eine Form, die man deklarieren und nicht herstellen kann. Erst der Erzeuger, dann der Vertrag.

**4. Nachgetragen am 2026-08-20 (Stufe 2): «B11» ist veraltet, und die Korrektur steht im
Kopf von F5.** `forever` hat sehr wohl einen Ausgang — `leave <marke>` steht in der Grammatik
(`SYNTAX.md`:658), prüft mit 0 Fehlern und senkt zu `goto marke_ende;` ab. Was fehlt, ist ein
Ausgang, der einen **Grund** trägt; `leaves` heißt in Gabbro etwas anderes (die linearen Werte,
die den Bereich verlassen). *«B11» schrumpft von „die Dienstschleife ist nicht schreibbar" auf
„ihr Austritt ist unbenannt".*

> **Der Wortlaut des Ausschnitts bleibt trotzdem stehen**, und die Korrektur steht daneben mit
> Datum. Ein Ausschnitt vom 2026-08-14 ist ein Bericht von diesem Tag — ihn zu überschreiben
> hieße, den Maßstab zu verschieben statt die Pflicht zu schließen.

**3. Und eine Zeile, die ich selbst ergänzt habe, senkt nicht ab:** `static irq : IrqMarke = IrqMarke(…)` in F6 — ein `static` eines Verbunds mit gewöhnlichem Anfangswert. *Das steht hier, statt die Zeile wegzulassen.*
