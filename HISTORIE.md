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

| **Zwanzig Konstrukte** | die erste Fassung von der Plandatei führte je Fehlerklasse ein Schlüsselwort — `device`, `lock`, `atomic`, `barrier`, `bitfeld`, `einheit`, `menge`, `recht`, `platzierung`, … | **das ist ein Katalog, keine Sprache**, und er wächst mit jedem Fund. Die naheliegende Ableitung aus einer Fallenliste ist der falsche Schluss. Es sind **vier Mechanismen** (Bereichstypen · lineare, auch geisterhafte Werte · Adressräume mit Rechten · kein ungeprüfter Index) und **zwei Deklarationsregeln**; die zwanzig fallen daraus als Bibliothek heraus. Die schönste Ableitung ist `check`: eine **lineare Pflicht**, kein Prüf-Schlüsselwort |

| **Ü2 ist ZURÜCKGEKEHRT** | „Gold billig machen" stand als widerlegt in dieser Datei | **und steht seit dem 2026-08-13 wieder im `README`** — das gehört hierher, sonst sieht eine stillschweigend zurückgenommene Korrektur wie eine nie gemachte aus. Der Unterschied zur widerlegten Fassung ist zweifach: es gibt jetzt einen **Mechanismus** (Invarianten an der Struktur · syntaxgesteuerte Absenkung · `spec`/`impl` in einer Sprache, der Plandatei §3c) und ein **gesenktes Ziel** (5 : 1 für Kernelcode statt 1 : 1). **Eine Behauptung darf zurückkehren — aber nur mit Mechanismus und mit Zahl** |
| **„keine Allzwecksprache"** | stand als Zusage im `README` und im Fahrplan | **aufgegeben am 2026-08-13**, auf Anforderung und ausdrücklich. Der Ersatz sind die fünf Abbruchbedingungen in der Plandatei — eine aufgegebene Zusage ohne Ersatz wäre nur ein vergessener Satz |

| **Der falsche Nenner** | die Kennzahl maß Spezifikationszeilen gegen die **handgeschriebene Rust-Referenz** | der Nenner ist **Gabbro-Code** — gefragt ist, ob ein *in Gabbro geschriebener* Kernel billig zu verifizieren ist; Rust kommt darin nicht vor. Die falsche Fassung ergab „für Caprock als Ganzes: nein", die richtige „bedingt ja". **Ein Nenner ist eine Frage, keine Formalie** — mit dem falschen beantwortet man sauber die Frage, die niemand gestellt hat |
| **5 : 1 als Boden** | galt als hergeleitete Untergrenze für Kernelcode | die 20 : 1 von seL4 sind **kein einzelner Posten**: rund 0,5 : 1 abstrakte Spezifikation, rund 19,5 : 1 Beweis. Nur der erste ist unantastbar. **Der Boden ist ≈ 0,5 : 1**, und die 5 : 1 kamen daher, dass der Beweisaufwand als unteilbar behandelt wurde |

| **Zwei Wege im Ordner** | ein enger Formaterzeuger als „Rückfallzuschnitt" **und** der Kernel als Hauptrichtung, dazu zwei Pläne nebeneinander | **gestrichen am 2026-08-13.** Ein Ordner mit einem Rückfall hat kein Tor — man fällt zurück, statt abzubrechen. Der Formaterzeuger ist die **Bibliotheksschicht** der Sprache, kein eigener Weg; es gibt einen Plan und ein Ziel |
| **Ziel mit Schwelle verwechselt** | 0,5 : 1 stand als **Auslösung** („darüber ist die These widerlegt“) | es ist das **Ziel** — der theoretische Boden. Eine Schwelle sagt „bestanden“, ein Ziel am Boden sagt **was noch fehlt**: jede Zehntelstelle darüber ist ein benennbarer, noch handgeschriebener Beweisposten. Abgebrochen wird bei **> 3 : 1**, wo der Beweis wieder dominiert |
| **0,8 : 1 als Vorhersage** | rechnete mit 10 % des Kernels zu 5 : 1 | **unvereinbar mit dem Ziel 0,5 : 1**, das der Boden ist. 0,5 : 1 heisst **kein handgeschriebener Beweis** — schon 5 % zu 5 : 1 wären +0,25 |

| **B2: „der Löser bekommt die Invariante geschenkt"** | stand als Bedingung für 0,5 : 1 | **Überschreibung Nr. 3.** Geschenkt ist die **Sicherheitshülle**; funktionale Schleifeninvarianten schreibt weiterhin jemand hin. Wahr für die Hülle, stillschweigend auf Gold erweitert — **exakt die Form, die diese Datei als Muster führt**, und diesmal trug sie das Kennzahlziel |
| **Die Zählregel** | „Spezifikation ist, was keine Laufzeitwirkung hat" | erzeugter Geistercode hat keine — er hätte **in den Zähler** gezählt, und damit hätte der Gold-Mechanismus die Kennzahl verschlechtert, je besser er wirkt. Richtig: **was ein MENSCH schreibt** und gelöscht wird |

---

## Die Trajektorie — das Muster über den Einzelfehlern

**Jedes gefallene Tor hat dieser Ordner durch Neugründung überlebt**, und das harte Tor ist dabei
hinter den Übersetzer gewandert:

| Tor | Ausgang | Antwort |
|---|---|---|
| EverParse | deckt nur die `format`-Hälfte | **umgangen** |
| Basisrate / Deckung | ≤ 9 % gemessen | nicht „zu klein", sondern **Plan für die anderen 91 %** |
| Verus × 2 | **beide gefallen** | nicht Ende, sondern **Vereinigung zu einer Sprache** |
| Rückfallzuschnitt | war die billige, verteidigbare Fassung | **gestrichen**, damit die teure die einzige ist |

Das Argument dafür — *„ein Ordner mit einem Rückfall hat kein Tor"* — ist scharf und **schneidet in
beide Richtungen**. Der alte Satz „der Weg, auf dem ein Formaterzeuger unbemerkt zur Sprachfamilie
wird" ist eingetreten: **nicht unbemerkt, sondern bemerkt, dokumentiert — und trotzdem.**

Die harte Marke ist jetzt `> 3 : 1`, **gewählt statt hergeleitet** und messbar erst, wenn ein
Übersetzer existiert. Die drei billigen Tore davor waren durch drei Umbauten hindurch benannt und
**ungefahren**, während an einem Tag rund 2000 Zeilen Entwurfstext entstanden. **Der
Korrekturkreislauf lief schneller als der Messkreislauf** — „measure before building", auf der
Meta-Ebene invertiert.

**Gegenmassnahme, seit dem 2026-08-13:** P0.1 ist gefahren ([`P0-1-REVOKE.md`](P0-1-REVOKE.md)) und
hat sofort einen Fehler in der Zählregel gefunden, den drei Umbauten Gegenlesen nicht fanden. **Kein
weiterer Entwurfstext vor P0.2 und P0.3.**

---

## Die Form, die sich wiederholt

Sechs der neun Einträge sind dieselbe Bewegung: **ein Satz, der wahr wäre, wenn der Geltungsbereich
nicht stillschweigend erweitert würde.** `format` → alles; Parametergrenze → überall; eine Messung
am Mechanismus → die Übertragung; Silber → Gold.

Das ist kein Flüchtigkeitsfehler, sondern das, was ein Entwurfstext von selbst tut, solange niemand
den Geltungsbereich **hinschreibt**. Deshalb trägt jede Aussage im `README` und in [`SPRACHE.md`](SPRACHE.md) jetzt
einen — und wo keiner steht, ist das ein Befund.
