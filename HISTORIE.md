# Gabbro — die Berichtigungen

Diese Datei hält fest, **was an diesem Entwurf schon falsch war**. Sie steht getrennt, weil das
`README` sonst als Sediment aus Berichtigungsschichten wächst — bei 658 Zeilen war es das bereits,
und die Ortsangabe „diese Berichtigung steht in Zeile 3" war schon verrottet, bevor jemand sie las.

**Der dokumentarische Wert ist der Punkt.** Ein Entwurfsordner, der seine widerlegten Fassungen
löscht, sieht am Ende so aus, als hätte er von Anfang an recht gehabt.

---

## Die zwei Überschreibungen — dieselbe Klasse, zwei Wochen auseinander

Beide standen in **Zeile 3**, beide waren das stärkste Wort an der Stelle mit der schwächsten
Deckung, und die zweite entstand beim **Berichtigen der ersten**.

| | Fassung | was daran falsch war |
|---|---|---|
| **Ü1** | „per Konstruktion **beweisbar**" | Gabbro beweist nichts. Es erzeugt nach Regeln; die Korrektheit hängt an einem **unverifizierten Übersetzer**. EverParse beweist seine Parser tatsächlich, in F\*. Gabbro liefert „korrekt unter Vertrauen in den Erzeuger, plus Differenztest" |
| **Ü2** | „Programme, deren **GOLD**-Beweis billig ist" | Gold heisst funktionale Korrektheit. Die sieben Konstrukte liefern ausdrücklich **keine** allgemeinen Nachbedingungen — was daraus folgt, ist eine **Sicherheitshülle plus deklarierte Invarianten**. Nur bei `format` ist der Beschreiber die vollständige funktionale Spezifikation |

**Ü2 ist die lehrreichere.** Sie entstand als *Berichtigung* von Ü1 und war eine Stufe leiser —
nicht mehr „Gabbro beweist", sondern „Gabbros Erzeugnis ist billig zu beweisen". Der Fehler wanderte
vom Verb zum Objekt. Das ist die Form, in der eine Überschreibung eine Korrektur überlebt: sie wird
schwächer formuliert, ohne schwächer zu **werden**.

> Der Satz „ein Beweis, der die Wunschform beweist, ist schlechter als keiner" gilt auch für Wörter
> in Überschriften — und offenbar auch für Wörter in Berichtigungen von Überschriften.

---

## Die übrigen, kürzer

| Was | Fassung, die fiel | was stattdessen gilt |
|---|---|---|
| **`format` = `table`** | die erste Fassung behandelte beide gleich | ein Format ist eine **reine Funktion**, eine Tabelle **mutierter Zustand**. Der Unterschied entscheidet den Wert des ganzen Ordners, und aus ihm folgt der Zuschnitt (a)/(b)/(c) |
| **Der Vergleichsgegner** | der Kernel-Zweig wurde an **Low\*** gemessen | die billigeren Gegner stehen näher: **Rust-heute** und **Verus**. Low\* ist der übernächste |
| **`Parked` als Argument** | wurde als Beleg **für** den Zweig geführt | es zählt **dagegen**: Rust-heute hat die fünfte Stelle gefunden, **ohne dass es Gabbro gab**. Wer den Erfolg der Grundlinie anführt, führt einen Grund an, sie **nicht** zu ersetzen |
| **„63 von 63 gemessen"** | die `Depends`-Messung galt als Beleg für Gabbros `touches` | die Messung ist echt, die **Übertragbarkeit** ist angenommen — SPARK prüft vorhandenen Code, Gabbro erzeugt ihn. Eine halbe Stufe zu stark |
| **`restrict`** | die Tabellenzeile klang allgemein | es trägt **nur an den Parametergrenzen** erzeugter Funktionen; innerhalb eines Traversierungskörpers in (c) sagt es nichts |
| **Die Linie bricht an `insert`** | so stand es zuerst | sie bricht an **`revoke`** — dessen Korrektheitsbedingung ist strukturell (Baumform, Induktion), also genau die ausgeschlossenen Quantoren |
| **Der SPARK-Fund** | „SPARK fand zwei Fehler, die Verus nicht fand ⇒ eine eigene Sprache bringt etwas" | der Gewinn kam aus einer **Voreinstellung**, nicht aus Adas Sprachvermögen. `refcount` steht im Verus-Modell als `nat` und kann die Frage **nicht einmal stellen**. Übrig bleibt die prüfbare Fassung: *Vorgabe schlägt Fähigkeit* |
| **„steht bewusst in Zeile 3"** | eine Ortsangabe im Fliesstext | veraltet beim ersten Einschub darüber. Aussagen über die **Reihenfolge** halten, Zeilennummern nicht |

| **„weder SPARK noch Rust"** | „der Aufrufer hält den Lock" galt als **grösster Einzelposten** und als Ausdruckslücke aller vorhandenen Werkzeuge | **gemessen 2026-08-13: Verus kann es**, als `tracked`-Zeuge, `no_std`, ohne Byte im Erzeugnis. Der Satz war wahr für SPARK und Rust und wurde stillschweigend auf „alle" erweitert — und **Verus stand in der Verwandtschaftstabelle mit „beweist, was jemand modelliert hat" abgetan.** Wer den nächsten Verwandten abwertet, statt ihn zu fahren, behält seine Begründung länger, als sie hält |

| **Zwanzig Konstrukte** | die erste Fassung von `VOLLDECKUNG.md` führte je Fehlerklasse ein Schlüsselwort — `device`, `lock`, `atomic`, `barrier`, `bitfeld`, `einheit`, `menge`, `recht`, `platzierung`, … | **das ist ein Katalog, keine Sprache**, und er wächst mit jedem Fund. Die naheliegende Ableitung aus einer Fallenliste ist der falsche Schluss. Es sind **vier Mechanismen** (Bereichstypen · lineare, auch geisterhafte Werte · Adressräume mit Rechten · kein ungeprüfter Index) und **zwei Deklarationsregeln**; die zwanzig fallen daraus als Bibliothek heraus. Die schönste Ableitung ist `check`: eine **lineare Pflicht**, kein Prüf-Schlüsselwort |

| **Ü2 ist ZURÜCKGEKEHRT** | „Gold billig machen" stand als widerlegt in dieser Datei | **und steht seit dem 2026-08-13 wieder im `README`** — das gehört hierher, sonst sieht eine stillschweigend zurückgenommene Korrektur wie eine nie gemachte aus. Der Unterschied zur widerlegten Fassung ist zweifach: es gibt jetzt einen **Mechanismus** (Invarianten an der Struktur · syntaxgesteuerte Absenkung · `spec`/`impl` in einer Sprache, `VOLLDECKUNG.md` §3c) und ein **gesenktes Ziel** (5 : 1 für Kernelcode statt 1 : 1). **Eine Behauptung darf zurückkehren — aber nur mit Mechanismus und mit Zahl** |
| **„keine Allzwecksprache"** | stand als Zusage im `README` und in `ROADMAP.md` | **aufgegeben am 2026-08-13**, auf Anforderung und ausdrücklich. Der Ersatz sind die fünf Abbruchbedingungen in `VOLLDECKUNG.md` — eine aufgegebene Zusage ohne Ersatz wäre nur ein vergessener Satz |

| **Der falsche Nenner** | die Kennzahl maß Spezifikationszeilen gegen die **handgeschriebene Rust-Referenz** | der Nenner ist **Gabbro-Code** — gefragt ist, ob ein *in Gabbro geschriebener* Kernel billig zu verifizieren ist; Rust kommt darin nicht vor. Die falsche Fassung ergab „für Caprock als Ganzes: nein", die richtige „bedingt ja". **Ein Nenner ist eine Frage, keine Formalie** — mit dem falschen beantwortet man sauber die Frage, die niemand gestellt hat |
| **5 : 1 als Boden** | galt als hergeleitete Untergrenze für Kernelcode | die 20 : 1 von seL4 sind **kein einzelner Posten**: rund 0,5 : 1 abstrakte Spezifikation, rund 19,5 : 1 Beweis. Nur der erste ist unantastbar. **Der Boden ist ≈ 0,5 : 1**, und die 5 : 1 kamen daher, dass der Beweisaufwand als unteilbar behandelt wurde |

---

## Die Form, die sich wiederholt

Sechs der neun Einträge sind dieselbe Bewegung: **ein Satz, der wahr wäre, wenn der Geltungsbereich
nicht stillschweigend erweitert würde.** `format` → alles; Parametergrenze → überall; eine Messung
am Mechanismus → die Übertragung; Silber → Gold.

Das ist kein Flüchtigkeitsfehler, sondern das, was ein Entwurfstext von selbst tut, solange niemand
den Geltungsbereich **hinschreibt**. Deshalb trägt jede Aussage im `README` und in `DESIGN.md` jetzt
einen — und wo keiner steht, ist das ein Befund.
