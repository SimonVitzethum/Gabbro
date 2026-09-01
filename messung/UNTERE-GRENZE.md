# Die untere Grenze festziehen — **2 von 94, und die Absage steht**

*Gemessen am 2026-09-01, lokal (`free -g`: 31 GB gesamt, 14 verfügbar, 20 Kerne;
`ki-pc-fisch-101` nicht angefasst). Die Messung ist eine Zeilenspur über drei Wächter und
kostet **unter zwei Sekunden** — sie ist billiger als der Satz, den sie prüft.*

`messung/ABNAHME-STELLEN.md` hat am selben Tag ein Intervall statt eines Adverbs gebaut und
daneben geschrieben, was **nicht** gebaut wurde:

> **Keine Zeilenspur, die die untere Grenze festzieht.** `zaehle-probenzweige.py` führt
> bereits eine; sie könnte sagen, welche Funktion ein Lauf überhaupt betreten hat. **Heute
> wären das zwei Stellen von 94.** Regel A: der Bedarf wird gemessen, nicht vermutet.

**Die Zahl stimmt. Der Grund darunter war falsch.** Beides ist jetzt gemessen und nicht
gelesen.

---

## Was gemessen wurde

`abnahme.unsichere_stellen()` nennt die Wächter, deren gefährliche Stellen als *besucht*
gebucht sind, ohne dass der Lauf sie erreicht haben kann. Heute sind das zwei, beide aus
`SCHNELL_TEIL` (halb gefahren); `pruefe-englisch.py`, das in `ABNAHME-STELLEN.md` noch mit
zwei abgeschnittenen Stellen dabeisteht, endet inzwischen mit `0` und ist damit gar nicht
mehr unsicher.

Jeder der drei lief unter `sys.settrace`. Für jede gefährliche Stelle — die Definition ist
die von `pruefe-waechter.schnitt_stellen()`, kein zweites Register — wurde zweierlei
gefragt:

```
nach FUNKTION   ist die Funktion, in der die Stelle steht, betreten worden?
nach ZEILE      ist die Zeile gelaufen, die ueber die Stelle ENTSCHEIDET
                (der Kopf der innersten `if`/`for`/`try`, in der sie haengt)?
```

| Wächter | Stellen | nach Funktion | **nach Zeile** |
|---|---:|---:|---:|
| `mutiere-pruefer.py --anker` | 5 | 5 | **2** |
| `zaehle-probenzweige.py --anker` | 2 | 2 | **0** |
| *(nachrichtlich)* `pruefe-englisch.py` — heute grün, nicht mehr unsicher | 2 | 2 | 2 |
| **unsicher heute** | **7** | **7** | **2** |

Die zwei, die `mutiere-pruefer.py --anker` wirklich erreicht, sind die Wache über einer
unbekannten Emissionsfläche und die über den toten Ankern; die anderen drei
(*Anker im vollen Lauf*, *Nullmutation*, *Giftmutation*) stehen hinter der
Betriebsartweiche. **Genau das, was `ABNAHME-STELLEN.md` behauptet hat — jetzt gemessen
statt gelesen.**

## Der Befund: die Absage nannte das falsche Werkzeug

**Alle sieben unsicheren Stellen stehen im Rumpf von `main`.** Eine Spur, die nach der
*Funktion* fragt, findet also für jede von ihnen „betreten" und meldet **7 von 7 erreicht**.
Damit fiele die Unsicherheit auf null, und `spanne()` druckte:

```
gebaut waere:   47 von 94 gefaehrlichen Stellen besucht -- 50 %
ehrlich ist:    zwischen 40 und 47 von 94 -- 43 bis 50 %
```

> **Das grob gemessene Ergebnis ist nicht ungenauer als das Adverb, es ist dieselbe
> Behauptung in neuer Schrift.** Ein Werkzeug, das die Unsicherheit auf null misst, weil
> seine Auflösung gröber ist als der Gegenstand, liest sich wie eine Verbesserung und ist
> eine Rücknahme.

Nur die ZEILENgenaue Frage — *lief der Wachkopf, der über diese Stelle entscheidet?* — gibt
die 2. **Die Zahl in der Absage war richtig; das Werkzeug, das sie erzeugt hätte, war es
nicht.** Der Satz in `abnahme.unsichere_stellen()` ist entsprechend berichtigt.

## Die Absage — und sie bleibt eine

```
Ertrag       untere Grenze 40 -> 42 von 94        +2 Stellen, +2,1 Punkte
Kosten       eine Zeilenspur um JEDEN Waechterlauf der Abnahme
```

Drei Gründe, und der dritte ist der, der es entscheidet:

1. **Regel A.** 2 von 94 ist der gemessene Bedarf. Die Vorgängerbahn hat für denselben
   Bruch einen Hebel von **+45 Stellen** ausgerechnet und ihn liegen lassen, weil er nur die
   obere Grenze hebt. Zwei ist eine Größenordnung darunter.
2. **Der Preis ist nicht die Spur, sondern ihr Ort.** `abnahme.py` ruft die Wächter als
   eigene Prozesse. Eine Zeilenspur je Lauf hieße: jeden Wächter unter `runpy` statt unter
   `subprocess` fahren, wie `zaehle-probenzweige.py` es tut — und dessen Lauf über 43
   Instrumente kostet **322 s** gegen die **~220 s**, die der ganze Schnelllauf heute
   braucht. *Die Messung wäre teurer als das Gemessene.*
3. **62 der 94 Stellen stehen in Schalenwächtern**, die eine Python-Zeilenspur überhaupt
   nicht sieht. Der Aufwand läge zum zweiten Mal dort, wo die Wirkung nicht ist.

> **Eine Bahn, die eine Zahl misst und daraufhin nichts baut, hat gemessen.** Was hier
> gebaut wurde, ist eine Zeile Text in einer Absage — die Stelle, an der `zwei von 94` jetzt
> mit dem Werkzeug dasteht, das die Zwei erzeugt, und nicht mit dem, das Sieben erzeugt
> hätte.

## Was diese Messung NICHT sieht

1. **Drei Wächter, nicht 52.** Gemessen wurde die Menge, die `unsichere_stellen()` heute
   nennt. Wird morgen ein anderer Wächter abgeschnitten, ist die Zahl eine andere — *und
   dann kann sie auch größer sein als zwei.* Die Absage gilt für den heutigen Stand und
   nennt ihn.
2. **`erreicht` heißt „der Wachkopf lief", nicht „die Wache hätte feuern können".** Eine
   Bedingung, die aus einem anderen Grund immer falsch ist, zählt hier als erreicht. *Die
   Richtung ist die sichere: sie überschätzt den Ertrag der Spur und damit den Bedarf.*
3. **Die Schalenwächter.** Für sie ist die Zahl kein Wert, nicht null — dieselbe
   Einschränkung wie in `PROBENZWEIGE.md`, und sie trägt hier 62 von 94.
4. **Der erste Lauf lief neben einem Mutationslauf**, der in `crates/` schreibt. Das ändert
   den Rücklaufwert von `mutiere-pruefer.py --anker` (tote Anker, die keine sind), **nicht
   aber die gemessenen Wachköpfe**: beide erreichten Stellen hängen an `if`-Zeilen, die vor
   jeder Verzweigung laufen. Nachgemessen auf ruhendem Baum: dieselben Zahlen.
