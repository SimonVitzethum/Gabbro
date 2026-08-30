# Gabbro — offene Punkte

> **Nach dem PLAN geschnitten, 2026-08-20.** Bis heute war diese Datei nach *Rolle* sortiert
> (Entscheidung · Messung · Bau · Buchhaltung) — ein Schnitt, den sie sich am 14. selbst
> vorgeschlagen und am 16. ausgeführt hat. **Er war die falsche Achse:** eine Rolle sagt, WAS
> ein Punkt ist, und nie, WANN er dran ist. *194 Punkte in vier Fächern sind keine Reihenfolge.*
>
> Jetzt tragen sie die **neun Stufen des Plans**, und die Reihenfolge IST die Aussage. Die
> Abschnittsüberschriften der alten Gliederung stehen darunter weiter — sie sagen, **woher** ein
> Punkt kommt, während die Stufe sagt, **wann** er dran ist. Kein Punkt ist verlorengegangen:
> **194 hinein, 195 heraus.** Der eine, der fehlt, ist *„braucht diese Datei einen Schnitt nach
> ROLLE?"* — durch diesen Schnitt beantwortet (`DONE.md`). Die zwei, die dazukommen, sind
> «B12» und «B10»: **Stufe 3 nannte drei Lesarten und die Liste führte nur eine**, weil die
> anderen zwei bisher nur als *Leserlücke* gebucht waren, nicht als *Entscheidung*. Was ausdrücklich
> zurückgestellt ist, steht unter **NICHT JETZT** —
> *mit Grund, denn eine stillschweigende Zurückstellung ist von einem Vergessen nicht zu
> unterscheiden.*

---

# Die vier Ziele, und ihre Spannung

| | |
|---|---|
| **1** | möglichst viele Programme in Gabbro schreibbar |
| **2** | Gabbro formal verifiziert |
| **3** | Gabbro möglichst gut nutzbar |
| **4** | keine Klempnerei beim Endnutzer — das ist K100 |

**Sie ziehen nicht in dieselbe Richtung.** Jedes Konstrukt, das eine Klempnereipflicht
schließt, ist eine **Schablone** — eine Beweispflicht des Erzeugers, die *einmal* fällt, aber
unbewiesen dasteht. **Ziel 1 und 4 kaufen sich auf Kosten von Ziel 2.** K100 hat das erkannt und
deshalb zwei Tore; ein Plan, der es nicht paart, erreicht `H = 0` und hat die Klempnerei nur vom
Menschen in eine unbewiesene Fläche verschoben.

Und **Ziel 3 hat als einziges keine Zahl.** Solange das so ist, ist „möglichst gut nutzbar" eine
Meinung. Das ist der Grund, warum Stufe 2 vor allem Bauen steht.

---

# Die Reihenfolge

| Stufe | | Block | warum hier |
|---|---|---|---|
| **0** | die Messschicht | **Q** | vier Instrumente wurden am 2026-08-20 dabei erwischt, dass sie nicht mehr messen. **Alle vier Ziele werden an Zahlen gesteuert** |
| **1** | der Maßstab | **C** | `H` misst zu sieben Zwölfteln die Vollständigkeit des Korpus, nicht die Deckung von Gabbro |
| **2** | Nutzbarkeit messen | **E** | das einzige Ziel ohne Instrument |
| **3** | die offenen Lesarten entscheiden | **A** | keine Grammatik, keine Schablone — **kostenlos für Ziel 2** |
| **4** | Programme schreiben, nicht Konstrukte | **A** | jedes echte Programm hat sofort Befunde geliefert; der Korpus ist von der Sprache nach außen geschrieben |
| **5** | die Beweise tragend machen | **D** | **läuft PARALLEL zu 4** — ein Beweis ohne Hersteller seiner Prämisse ist gefährlicher als eine ungeprüfte Zusage |
| **—** | die Kennzahl: eine W-Pflicht, die entsteht | **B** | **hatte bis zum 2026-08-23 keinen eigenen Posten** — die drei Punkte lagen am Ende von Stufe 4. *Der Block mit dem größten Gewicht und dem geringsten Stand; er entscheidet, ob die anderen sich gelohnt haben* |
| **6** | die fremden Rümpfe sprechen lassen | **C** | die eine Klasse, die sich auch unter „ganz Gabbro verifiziert" nicht auflöst |
| **7** | was Programme groß macht | **A** | `fnptr`-Erzeuger, dann sein Vertrag; ABI; Generizität |
| **8** | PL — die Logik des Prüfers | **D** | ohne die Sätze ist „formal verifiziert" nicht formulierbar |
| **9** | der Prüfer als Mathematik, in Lean 4 | **D** | **wartet auf einen gemessenen Auslöser, nicht auf einen Termin.** *Erst der Satz, dann der Beweis* — **seit PL.1 (2026-08-21) stehen ~~52~~ 71 Sätze über 12 von 12 Pässen, keiner bewiesen** *(nachgemessen 2026-08-30 mit `cargo run -q --bin gabbro -- paesse`: `SENTENCES: 71 over 12 passes -- 63 measured, 2 ARGUED, 6 CONJECTURED, 0 proved`; die Zahl steht seit heute im Register von `pruefe-zahlen.py`).* **Das ist die einzige LEBENDE Zahl, die der Reichweitendurchgang von heute falsch fand** — und der Reichweitenzähler sieht sie nicht, weil sie in einem Fließtext steht und nicht fettgedruckt in einer Tabellenzelle. Auslöser 1 ist damit erfüllt; es hält Auslöser 2 (Zahn 3 auf 8) |

**Der kritische Pfad ist diese Spalte.** Er ersetzt den alten *(B3 → K/A/W → `effects` →
closures → `table.induktion` → group `ops` → P5 → P6 → P7)* — der stand nach BAUSTEINEN, dieser
steht nach dem, was die Ziele einlöst. Der alte Pfad ist damit nicht widerlegt: seine offenen
Glieder stehen in Stufe 5 und 8 wieder da, nur nicht mehr an erster Stelle.

---

# DIE REGEL ÜBER ALLEM

> **Eine Buchung muss den Befehl nennen, der sie nachrechnet.**
>
> Eine Zelle, die auf eine *Regel* zeigt, prüft niemand nach — ein *Befehl*, der eine Zahl
> druckt, ist nachrechenbar.

**Fünf Fälle an einem einzigen Tag (2026-08-20):** die Registerklasse war *durch `R002`/`R003`*
gebucht und fand dort nicht statt · «B33» stand als Zusage und der Prüfer tat das Gegenteil ·
«B26» stand als „kein benannter Ausgang" und hat gar keinen Leser · der Netzwerkstack stand als
blockiert und war offen · `H = 2` war meine eigene Zahl und falsch.

**Vier zu optimistisch, einer zu pessimistisch — und die Richtungsmischung ist die eigentliche
Diagnose.** Eine Buchführung, die nur schönte, wäre Selbstbetrug und bräuchte ein Gegengewicht
aus Misstrauen. Eine, die in **beide** Richtungen abweicht, **veraltet** bloß — und dagegen hilft
kein Misstrauen, sondern ein Befehl, der die Zahl neu ableitet. *Der Unterschied bestimmt, wogegen
man sich schützt, und er ist der Grund, warum die Regel oben eine Regel ist und keine Mahnung.*

---

# STUFE 0 — DIE MESSSCHICHT  ⟨Q⟩

- [ ] **Der Prüfer hatte keinen Zweitlauf — und war nicht deterministisch** *(gefunden
      2026-08-24, [`messung/DETERMINISMUS.md`](messung/DETERMINISMUS.md))*. Derselbe
      Quelltext, zwanzigmal im selben Prozess: **mal `M104`, mal keine Absage.** Ursache
      gemessen: `HashMap::keys()` in der Typauflösung, Reihenfolge je Kartenexemplar zufällig.

      ```
      ZEHNMAL DASSELBE PROGRAMM:  leer=13  mit-Absage=7
      ```

      **Sortiert ist es deterministisch** (beide Auflösungsschleifen), und der bestehende
      Korpus war nicht betroffen — sechs Läufe auf `97b0574`, null Fehlschläge. *Der Defekt
      war latent: die auslösende Form (ein Verbund über einem benannten Bereichstyp, hinter
      einem Zeiger) stand in keiner Datei.*

      **Zwei Posten bleiben, und der zweite ist der wichtigere:**

      1. **WARUM die Reihenfolge durchschlägt.** `typ_aufloesen` steigt bei einem
         unaufgelösten Namen in `roh_typen` ab, *sollte* also reihenfolgeunabhängig sein.
         Die Sortierung beseitigt den Münzwurf; **ob sie die Ursache trifft oder nur
         verdeckt, ist offen.**
      2. **`pruefe-emission.sh` prüft die EMISSION im Zweitlauf auf Bitgleichheit
         (`1b. zweitlauf: ok`). Der PRÜFER hat diese Probe nicht** — sie ist billig, und sie
         hätte das hier am ersten Tag gefunden. *Ein Wächter, der einmal läuft, misst einen
         Münzwurf.*

      > **Und was das über die anderen Zahlen sagt:** „186 Tests bestehen" war eine Aussage
      > über den Zufallswert EINES Laufs. Sie war nicht falsch — der Korpus trifft die Form
      > nicht —, aber sie war schwächer, als sie klang, und niemand konnte das wissen.

**Warum zuerst:** am 2026-08-20 wurden vier Instrumente dabei erwischt, dass sie nicht mehr
messen — `pruefe-emission.sh` hing stundenlang (21 Läufe nebeneinander über einem Baum),
`zaehle-pflichten.py` verweigerte seit Wochen die Ableitung, `gift/214` prüfte etwas anderes als
behauptet, die B22-Sonde maß einen fremden Fehler. **Man kann nicht auf Zahlen steuern, die nicht
messen.**

**Das Tor:** jede Zahl im Ordner nennt den Befehl, der sie ableitet; ein Wächter leitet alle neu
ab und fällt bei Abweichung. Und jeder Wächter braucht dreierlei: eine **Frist**, eine
**Sprechprobe in beide Richtungen**, und einen Abbruch, der **rot** ist statt still.

## Stand 2026-08-20 — die zwei Instrumente stehen, und der zweite Durchgang hat sie gemessen

| | |
|---|---|
| **`./instrumente/pruefe-zahlen.py`** | das Register der Befehle. ~~64~~ ~~70~~ **76 Kennzahlen mit Befehl** *(Stand 2026-08-30; 64 am 2026-08-21, 12 am Vormittag des 2026-08-20)* — und es zählt daneben, was es *nicht* bewacht. Sprechprobe über alle, in beide Richtungen. **Seine EIGENE Reichweite kann es nicht bewachen** — der Fixpunktriegel verbietet es mechanisch (W18) —, also hält sie seit heute `pruefe-todo.py`: ein anderes Werkzeug, und das ist der ganze Ausweg |
| **`./instrumente/pruefe-waechter.py`** | der Wächter über den Wächtern. Vier Forderungen, **29 von 29 Instrumenten** tragen die drei statischen. `--lauf` führt **25 von 29** wirklich aus, mit Frist; vier stehen mit gemessenem Grund daneben (Speicher, Ort, Schreibwirkung), zwei mit fehlendem fremdem Korpus |
| **`./instrumente/zaehle-karten.py`** | neu — direkte Blicke auf die Karten der `Umgebung`, an `suche` vorbei |
| **`./instrumente/zaehle-theorien.py`** | neu — die Zeilenanteile der eigenen Theorien, und wer den Beweisschritt gesucht hat |
| **`./instrumente/zaehle-zeremonie.py`** | neu — das Nutzbarkeitsmaß von Stufe 2, mit seiner Kalibriertafel |

**Sechs Befunde beim ersten Lauf, keiner davon gesucht:** `pruefe-beweise.sh` kündigte eine
Zeitgrenze an und setzte sie nie durch (`ZEIT=600` stand in der Kopfzeile, der Wachhund sah nur
den Speicher) · `zaehle-b3.py` druckte `! ABBRUCH` und endete mit 0 · `pruefe-abstieg.py` war
nicht ausführbar · drei Wächter hatten keine Sprechprobe · fünf führten `cargo`/`cc` ohne Frist
aus. **Und einer an mir selbst:** ich formulierte die Wächterzahl im README aus ihrem Muster
heraus, und `pruefe-todo.py` meldete *„sauber"* über einer falschen Zahl. *Seit heute ist ein
Muster ohne Treffer selbst ein Befund — in beiden Werkzeugen.*

### Der zweite Durchgang, am Nachmittag — und er hat mehr gefunden als der erste

Das Register wuchs von 12 auf **39 Einträge**, gewählt nach `--reichweite` (Traglast zuerst).
**Sieben der neuen Einträge fielen sofort**, und die Richtungsmischung ist wieder die
Diagnose — keine Beschönigung, sondern **Fortschreibung**:

| Zahl | stand | ist | wo |
|---|---:|---:|---|
| `H` in der Postenliste | 15 | 12 | `PFLICHTEN.md` — *und die Spalte darunter summierte sich zu 17* |
| Prämissen ohne Pass | 7 | 9 | `PLAN.md`, «NL»-Tafel |
| Absagen mit tragendem Grund | 96 | 98 | `TODO.md` |
| gelesene Item-Arten | 21 von 23 | 23 von 23 | `TODO.md` |
| Schablonen im Register | 20, 15 unbewiesen | 21, 11 unbewiesen | `TODO.md` |
| Widerrufe | 7 | 11 | `TODO.md` |
| direkte Blicke auf die Karten | 13 | 35 | `TODO.md` |
| ZUSAGE ohne Leser | 13 | 0 | `PLAN.md`, «NL» — *das Tor von «NL» ist ERREICHT* |
| Fremdpflichten | 8 | 10 | `PLAN.md`, «NL» |
| emittierende Beispiele | 43 | 45 | `README.md` |
| Laufzeit von `pruefe-emission.sh` | ~25 min | **13,7 s** | `pruefe-waechter.py`, `SCHWER` |

> **Drei Register über einer Sache, und das mit dem Suchweg war das falsche.** In
> `PFLICHTEN.md` stand die Postenliste der hängenden Pflichten unter der Überschrift
> *„`H = 15`, abgelesen mit `./instrumente/zaehle-pflichten.py --haengend`"* — die Zahlenspalte darunter
> summierte sich zu **17**, und der genannte Befehl sagt **12**. *Genau die Form, gegen die
> die Regel über allem steht: eine Zahl, deren Suchweg ihr widerspricht, sieht belegt aus.*
> Die Spalte ist gestrichen; die zwölf stehen nur noch im Befehl.

**Und zwei Befunde am Messwerkzeug selbst — beide sind meine eigenen:**

| | |
|---|---|
| **Der Fixpunktriegel war einen Schritt tief** | W18 verbietet einen Registereintrag, dessen Befehl `pruefe-zahlen.py` **nennt**. Der Ring der Länge ZWEI lag offen daneben: `./instrumente/pruefe-waechter.py --lauf` führt jeden leichten Wächter aus, und das Register ist einer davon — **ein einziger Eintrag mit `--lauf` hätte den Ring geschlossen**, und der Namensriegel hätte ihn durchgelassen. Seit heute hängt der Riegel an einer Marke in der Prozessumgebung und greift in **jeder** Tiefe; gemessen an einem echten Kindprozess |
| **`pruefe-waechter.py --lauf` war hier grün und auf `ki-pc-fisch-101` rot** | bei identischen Quellen. Nicht der Code fehlte, sondern der **Gegenstand**: `zaehle-b3.py` und `zaehle-narrow.py` messen fremde Bäume (Caprock-Messbasis, SEL4Lake), und die liegen nur auf dem Arbeitsrechner. *Ein Wächter, dessen Urteil davon abhängt, auf welchem Rechner er läuft, ohne es zu sagen, misst den Rechner.* Beide stehen jetzt in `FREMDER_KORPUS`; ein fehlender Baum zählt als **nicht gemessen** und steht mit seiner Zahl in der Schlusszeile |

### Und der teuerste Befund ist die AUSNAHMELISTE, nicht eine Zahl

`pruefe-waechter.py` führte fünf Instrumente als *„zu schwer für einen Lauf hier"* — mit
geschätzten Kosten. **Vier von fünf Schätzungen waren falsch**, und die schlimmste hielt den
schwersten Wächter des Ordners aus jeder Messung heraus:

| | stand | gemessen auf `fisch` |
|---|---|---:|
| `pruefe-emission.sh` | *„46 Einheiten … ~25 min"* | **13,7 s** |
| `pruefe-luecken.py` | *„baut dreizehnmal neu"* | 10,7 s (27,8 s CPU) |
| `pruefe-beweise.sh` | *„zwölf Isabelle-Theorien"* | 8,1 s — es sind dreizehn |
| `pruefe-notation.py` | *„vierzehn `cargo run`"* | **0,56 s, und kein einziges `cargo run`** |

Die 25 Minuten stammen vom **Vormittag desselben Tages**, als der Wächter an `baum41` HING.
Die Frist hat den Hänger beseitigt — und die Zahl, die ihn beschrieb, blieb stehen, *als
Begründung dafür, ihn nicht zu messen.*

> **Eine Ausnahme, deren Grund niemand nachrechnet, ist dieselbe Klasse wie eine Zahl, die
> niemand nachrechnet — nur teurer.** Eine falsche Zahl verfälscht eine Messung; eine falsche
> Ausnahme **ordnet sie gar nicht erst an.** *Erfolg ohne Arbeit, eine Ebene über dem Urteil.*

Was blieb, steht mit dem richtigen Grund da, und der ist in keinem der vier die Zeit: es ist
der **Ort** (Speicherspitze, Rechenlast gehört auf den Server) oder die **Wirkung** (es
schreibt in Quellen). `pruefe-notation.py` ist ganz herausgefallen — *es stand auf einer
Liste, auf die es nie gehörte.* Der Lauf misst jetzt **19 von 25 in 4,4 s** und druckt die
Zeit je Wächter, damit die nächste Ausnahme nachrechenbar ist.

*Und dieselbe Falle noch einmal eine Ebene tiefer:* `../caprock-messbasis` ist ein **relativer**
Pfad. In einem `git worktree` zeigt er neben den Arbeitsbaum — und `zaehle-b3.py` lief darüber
bis in eine `ZeroDivisionError`, mit einer Ausgabe, die mit `Dateien 0` begann. **Null Dateien
ist eine Absage, kein Ergebnis;** das Werkzeug sagt es jetzt und endet mit 2.

### Und ein dritter Ortsbefund: `-rlpgoD` heilt `cargo` und bricht den Beweiswächter

`pruefe-beweise.sh` verlangt einen **Nachweis**, dass wirklich gebaut wurde — `isabelle build`
schweigt bei leerer Auswahl (W17). Der zweite Weg zu diesem Nachweis lautet *„kein Bauwerksbuch,
das jünger ist als jede Quelle"*, und das ist eine **Zeitstempelfrage**.

Wer den ganzen Baum mit `rsync -rlpgoD` überträgt — dem Schalter, den `cargo` braucht —, gibt
jeder `.thy` die aktuelle Zeit. **Isabelle rechnet nach Inhalt**, wählt korrekt nichts aus und
schweigt; der Wächter rechnet nach Zeit, findet keinen Nachweis und meldet `OHNE NACHWEIS` über
einer Sitzung, die vollständig aktuell ist.

> **Zwei Begriffe von „aktuell" in einer Kette, und keiner von beiden ist falsch.** Die
> bekannte Instanz (W16) log *grün*; diese lässt einen richtigen Lauf *durchfallen*. Die
> Richtung wechselt, die Frage bleibt: **misst dieser Lauf, was ich glaube, dass er misst?**

`CLAUDE.md` führt beide Übertragungen längst getrennt (`rsync -a beweise/` und
`rsync -rlpgoD ./`) — *das sieht nach zwei Gewohnheiten aus und ist eine Bedingung.* Die Absage
des Wächters nennt seit heute die wahrscheinlichere der zwei Ursachen und die Heilung; **eine
Absage, die ihren häufigsten Grund nicht nennt, kostet jedes Mal dieselbe halbe Stunde.**

**Was von den Punkten darunter erledigt ist:** die Spalte *„of which K"* (gestrichen, nicht
ausgerechnet) · *54 oder 102* (zwei Grundgesamtheiten, keine zwei Zahlen) · die
`narrow`-Klassen (`N_folgenlos` gebaut, `N_ritus` als Urteil benannt).

**Vier Klassen sind daraus in den Werkzeugkasten gegangen, weil sie über ihren Anlass hinausreichen:**

| | |
|---|---|
| **W17** | *Erfolg ohne Arbeit* — ein **positives Urteil über nichts**. Dreimal an einem Tag: `isabelle build` wählte nichts und endete grün, `zaehle-b3.py` druckte `! ABBRUCH` und endete mit 0, ein README-Muster traf nichts und meldete „sauber". **Die Vorkehrung ist die Arbeitsmenge neben dem Urteil** — seit heute die *vierte* Forderung in `pruefe-waechter.py` |
| **W18** | *Ein Register, das seine eigene Ausgabe enthält, hat einen **Fixpunkt statt einer Messung***. Nicht der Rücklauf ist das Schlimme — ein Fixpunkt, der **terminiert**, wäre gefährlicher: die Zahl stimmt dann immer, unabhängig davon, ob gemessen wurde. *R15 eine Ebene über dem Werkzeug.* **Als Code geriegelt**, nicht als Satz — und seit dem Nachmittag in **jeder Tiefe**, nicht nur in der ersten |
| **W19** | *Ein Urteil, das sich als Messung liest, bekommt die Autorität der Messung.* Die Auflösung hat zwei Teile, und der zweite wiegt schwerer: die urteilsfreie Hälfte bauen — **und sie anders benennen** |
| **W21** | *Ein Wächter, dessen Gegenstand woanders liegt, misst den Rechner.* Fehlt der fremde Baum, ist der Rücklaufwert ein **Fehlaufruf und kein Befund** — und beide Richtungen sind falsch: rot ohne Fehler, oder grün ohne Messung |

**Und die Reichweite ist nach Traglast sortiert, nicht nach Aufwand:** `--reichweite` listet
die unbewachten fettgedruckten Zahlen, tragende zuerst. *Wer die nächsten zwölf nach diesem
Kriterium wählt, senkt das Risiko schneller als die Zahl.* Die übrigen Punkte stehen einzeln
darunter.

### K100 — der Weg auf 100 % Klempnereiabdeckung ([`dokumente/PLAN.md`](dokumente/PLAN.md)) *(Teil)*

- [ ] **Die Zahlen der Kennzahlentafel, die kein Befehl ableitet** *(nachgezogen 2026-08-20,
      zweimal)*. ~~Die Spalte „of which K" summiert sich zu 33, die Summenzeile sagt 18~~
      *(2026-08-20)*. **Beide Spalten sind gestrichen** — sie waren ein drittes Register neben
      dem Handgang und dem Befehl. ~~Und die Postenliste darunter war das VIERTE~~ *(gestrichen
      2026-08-20 nachmittags: Überschrift 15, Spaltensumme 17, Befehl 12).*
      ~~**Was offen bleibt, ist der Rest der Tafel:** `total`, `K` und `L` (238 / 171 / 67)
      kommen aus dem Handgang, und der ist eine **Auszählung ohne Befehl**~~ — **GEBAUT am
      2026-08-30, und der Bau hat die drei Zahlen gleich WIDERLEGT.** Der Vorschlag dieses
      Punktes stand hier wörtlich: *„ein Befehl müsste die Klassenspalte `K`/`L` je Zeile
      auszählen — das ginge, und es ist die nächste Erweiterung von `zaehle-pflichten.py`"*.
      Er ist es geworden: **`./instrumente/zaehle-pflichten.py --spalten`** zählt sie, mit
      zwei Sprechproben (eine erfundene `L`-Zeile hebt `L`; eine Zelle mit maskierter Pipe
      zählt MIT — ohne diese zweite Probe misst der Zähler eine geschrumpfte Grundgesamtheit).
      **Das Ergebnis ist 239 / 173 / 66, und nicht eine der drei gebuchten Zahlen stimmte.**
      Die Spaltentafel summierte sich zu 173 / 65, die Zeile darunter las 171 / 67, und beide
      ergaben 238 — *eine Aufteilung, deren Summe stimmt, wird nicht nachgerechnet.* Eine
      Ebene tiefer lag die Ursache: **F4 hat 31 Zeilen, nicht 30.** Alle sechs Zellen der
      beiden Tafeln stehen jetzt im Register.
      **`pruefe-zahlen.py` führt heute 76 Kennzahlen mit Befehl** und zählt daneben
      **146 fettgedruckte Zahlen in Tabellenzellen ohne einen**. *Und diese beiden Zahlen hält seit dem
      2026-08-20 `pruefe-todo.py`: das Register kann seine eigene Reichweite nicht bewachen
      (W18), also tut es ein anderes Werkzeug.*

- [ ] **Zwei Blicke auf dieselbe Karte gingen auseinander, und nur einer hatte einen Test**
      *(gefunden 2026-08-17 beim Bauen von `const fn`, weil eine Giftprobe nicht fiel, die
      fallen musste -- R11)*. `typ_von_ort` schlug den globalen Traeger modulbewusst nach
      (`suche`), `index_pruefen` unqualifiziert (`get`). **`M103` schwieg damit in jedem
      `module`-Block fuer eine Tabelle, die ueber ihren globalen Namen adressiert wird.**
      Behoben und mit Gift 76 belegt.
      **Die allgemeine Frage hat seit dem 2026-08-20 einen Befehl** (`./instrumente/zaehle-karten.py`), und
      die alte Zahl war um den Faktor 2,7 zu klein: 16 Karten, 12 davon öffentlich,
      **38 direkte Blicke** auf die Karten aus 27 Passdateien, davon vier in einer
      Kandidatenschleife und **34 davon unqualifiziert**.
      *Die alte Zählung sagte 13 — sie kannte `.contains_key(` nicht, und das ist derselbe
      Blick.* **Ein Werkzeug, das eine der beiden Formen nicht liest, misst seine eigene
      Leseweite** (W16).
      **Was offen bleibt und woran es hängt:** wie viele der 32 in einem `module` danebengreifen,
      ist ungemessen. Es zu messen kostet **je Stelle eine Giftdatei mit `module`-Block** —
      zweiunddreißig Dateien, keine Passarbeit. *Bis dahin ist die Zahl eine Kandidatenliste und
      kein Fehlerbefund (W10).*

- [ ] **Zum ZWEITEN Mal in eine Beweissuche gelaufen -- und die Regel stand schon da**
      *(2026-08-17)*. Erst ein `metis` (9 Minuten, 6,3 GB), dann ein `blast` (12 Minuten,
      4,8 GB). **Eine Regel, die man kennt und trotzdem bricht, braucht keinen weiteren Satz
      -- sie braucht ein Werkzeug.** `./instrumente/pruefe-beweise.sh` haelt jetzt bei 3 GB an.
      **Die andere Hälfte ist seit dem 2026-08-20 gebaut, und sie ist eine Zählung, kein
      Wachhund:** `./instrumente/zaehle-theorien.py` zählt **31 eingefrorene Suchergebnisse**
      (`metis` 3, `blast` 28) gegen eine Ratsche und verbietet `sledgehammer`, `try0`,
      `nitpick` und `quickcheck` ganz — **heute null, über fünfzehn Theorien.**
      **Die Ratsche war GEBROCHEN, gemessen am 2026-08-28: 40 gegen 31.** Die neun
      dazugekommenen lagen vollständig in `beweise/Table_Ops_Erhaltung.thy` (6 → 15), also im
      `relabel`-Beweis desselben Tages; jede andere Theorie stand auf ihrer alten Zahl.
      **`MARKE_EINGEFROREN` blieb bei 31** — *eine Ratsche, deren Marke man hochzieht, wenn
      sie klemmt, ist keine.* Die Heilung waren neun ausgeschriebene Beweisschritte an Stelle
      von neun eingefrorenen Suchergebnissen: Isabelle-Arbeit am Beweis, keine Buchung.
      **BEZAHLT am 2026-08-30 abends** (`messung/NEUN-SUCHSCHRITTE.md`): alle neun ersetzt,
      **jede Stelle einzeln gebaut**, `zaehle-theorien.py` wieder grün bei genau 31.
      *Die Marke wurde nicht bewegt — sie wurde eingeholt.* Sieben der neun sind `OF`/`mp`
      mit benannter Instanz oder ein ausgeschriebener Widerspruch; **kein einziger `auto`-
      Rückfall war nötig**, auch nicht an der Stelle, die das Vorschlagsdokument selbst mit
      der niedrigsten Zuversicht geführt hat.
      *Ein Suchbefehl in einer eingecheckten Theorie ist keine Absicht, sondern ein
      vergessener Versuch; ein `metis` ist eine Suche, die einmal lief und deren Ergebnis
      jetzt dasteht.* **Was der Wachhund NICHT verhindert, bleibt: er greift erst, wenn die
      Suche schon läuft.** Die Ratsche greift davor — aber erst beim nächsten Lauf des Wächters,
      nicht beim Tippen.

### From the reassignment (2026-08-17) — three judgements the measurement forces

- [ ] **Frame and Publication are refuted as carried, each at ONE named site.** «B39» — die MMU
      schreibt `A`/`D` selbst, also ist *„nur was dasteht, ändert sich"* dort **falsch**, und die
      Grenze, die die Umbuchung vom 2026-08-16 aufschrieb (*„ein unbekannter Name fällt im
      Namenspass"*), deckt einen Schreiber nicht, der kein Programm ist. «B19» — siehe den Punkt
      unter BAUEN. **Die Kipp-Regel ist eindeutig** (*ein Konstrukt, das eine Klasse nur teilweise
      trägt, lässt sie hängen*); offen ist, ob der Ordner sie anwendet, was `N_neu` wieder auf
      **5** stellte.
      **Gemessen 2026-08-20: das ist KEINE Messschichtfrage, und der Beleg dafür ist, dass die
      Messschicht sie nicht berührt.** «B19»/«B38»/«B39» sind durch K100.2 in die Axiomschicht
      umgebucht und stehen in `gabbro annahmen` unter den 32; `zaehle-pflichten.py --haengend`
      zählt sie nicht mehr. *Es fehlt kein Befehl — es fehlt ein Urteil,* und zwar genau eins:
      **zählt eine Annahme mit Sonde als „getragen" oder als „woanders hingeschoben"?**
      Bleibt offen, und der Ort dafür ist Stufe 5, nicht Stufe 0.

- [ ] **Does a NAMED residue tip a class?** *Overflow* hat fünf hängende Pflichten, und drei davon
      sind `narrow … else` — eine **benannte, geprüfte, beschränkte** Erledigung mit eigener
      Schranke (≤ 24), keine unbenannte Lücke. **Kippt ein benannter Rest, steigt `N_neu` wieder;
      kippt er nicht, braucht die Regel das Wort „unbenannt" in sich.**
      **Und die Messschicht kann die Frage nicht entscheiden — sie kann nur sagen, warum:**
      `zaehle-bereichspflichten.py` misst seit dem 2026-08-20 `N_folgenlos` (ein `narrow`, dessen
      Entfernung nichts ändert — heute 0), und das ist die urteilsfreie Hälfte. Die andere hängt
      an der **Erreichbarkeit des `else`-Zweigs**, und die entscheidet kein Textzähler, sondern
      ein Pass. *Woran es hängt: an einem Erreichbarkeitsurteil über `else`-Zweige, also an
      M1-Arbeit.*

- [ ] **Dreizehn von 36 hängenden Klempnereipflichten gehören zu KEINER der elf Klassen** —
      Gerätenotation, `format`, das fehlende Verbundliteral, die fehlende Rückgabebindung.
      ~~Die Taxonomie ist für das gebaut, was ein Kernel falsch macht; ein Drittel der gemessenen
      Lücken handelt davon, was die Sprache nicht SAGEN kann.~~
      **Nachgemessen 2026-08-20, und die 36 ist eine Zahl vom 2026-08-17: heute sind es zwölf,
      davon fünf verankert — und alle fünf sind Notationslücken.** `./instrumente/zaehle-pflichten.py
      --haengend` nennt sie mit Zeile: `F2`:498 («B22-nah»), `F3`:613–624 («B9»), `F4`:764
      («B26»), `F4`:785–792 («B18»), `F5`:938–949 («B27»).
      **Damit hat die Frage sich umgedreht, und das ist der Befund:** die zweite Achse war nie
      eine Nebenklasse, sie ist heute *die ganze* verankerte Restmenge. Sieben von zwölf sind
      Absenkung, fünf von zwölf sind Notation, **null sind Klempnerei im Sinn der elf Klassen**.
      *Der Ordner zählt also auf einer zweiten Achse — er hat es nur nirgends hingeschrieben.*
      **Was offen bleibt:** die elf Klassen und die Notationsachse stehen unverbunden
      nebeneinander, und `pruefe-notation.py` (8 von 8 zu) misst die GRAMMATIK, nicht die
      Fragmente. Ein Fragment kann notationell versorgt sein und trotzdem hängen, weil
      `FRAGMENTE.md` eingefroren ist und nicht umgeschrieben wird.

- [ ] **`narrow`-Stellen sind nicht gleich, und K100.1 hat das nur im URTEIL getrennt**
      *(nachgemessen 2026-08-20)*. `FRAGMENTE.md`:1660 — der `else`-Zweig ist **erreichbar**
      (ein feindliches DTB nimmt ihn); `:1100` — er **kann nicht genommen werden** und muss
      dastehen. K100.1 buchte als Tor: *„`zaehle-bereichspflichten.py` unterscheidet die drei
      Fälle."* **Es tat es nicht** — die Trennung stand in `PFLICHTEN.md`, also im Urteil.
      *Sechster Fall an einem Tag, in dem eine Buchung auf etwas zeigte, das anderswo lag.*
      **Die eine messbare Hälfte ist gebaut:** `N_folgenlos` — ein `narrow`, dessen
      Entfernung nichts ändert, ist Zierde (Zwei-Ebenen-Sonde, W8). Heute **0**.
      **Und sie ist NICHT `N_ritus`:** `MESSUNGEN.md` definiert den über die *Erreichbarkeit*
      des `else`-Zweigs, und eine unerreichbare trägt sehr wohl eine Pflicht. *Zwei
      verschiedene Fragen, und bis heute hießen beide `N_ritus`.* **Was offen bleibt, ist die
      Erreichbarkeit** — und die ist ein Urteil, bis ein Pass sie entscheidet.

### From the escalation of 2026-08-14 — one number never reconciled

- [ ] **~~54 or 102 relational preconditions?~~ — aufgelöst 2026-08-20, und es war kein
      Streit, sondern eine falsche Beschriftung.** Die zwei Zahlen sind **zwei
      Grundgesamtheiten**: `MESSUNGEN.md`:370 zählt **102 flusssensitive** Subtraktionen und
      **davon 54 relationale** (`if a >= b { a - b }`). `SPRACHE.md` schrieb an zwei Stellen
      *„die 102 Stellen fallen alle unter diese Form"* und meinte V2 — also die 54.
      **Berichtigt.** *Was offen bleibt, ist die allgemeine Form dieses Falls:* zwei Zahlen aus
      derselben Messung, die eine als Teilmenge der anderen, und in einem zweiten Dokument
      ohne den Zusatz zitiert. **`pruefe-widerruf.py` kennt Widerrufe, keine Teilmengen** —
      heute **12 Widerrufe** über 122 Dateien, und keiner davon ist eine Teilmengenbeziehung.
      *~~103~~ … ~~121~~ — am 2026-08-30/31 **zehnmal** nachgezogen, aus sieben Ketten, und
      jedes Mal, weil ein Bericht geschrieben wurde. **Die Zahl misst den Ordner, nicht die
      Arbeit**, und sie ist an einem einzigen Tag von 103 auf 122 gestiegen, ohne dass ein
      einziger Widerruf dazukam: die Reichweite wächst mit jedem Dokument unter `messung/`,
      die Zahl der Widerrufe steht seit Wochen bei zwölf.*
      *~~109~~ am 2026-08-30 VIERMAL nachgezogen, und jedes Mal beim Zusammenführen: die
      Berichte kamen aus drei Ketten gleichzeitig, und keine Kette konnte die Summe kennen.
      **Nicht eine Seite genommen, sondern den Wächter gefragt** — das ist die einzige Zahl,
      die stimmt, wenn drei Bäume sich treffen.*
      *~~103~~ dreimal nachgezogen am 2026-08-28 — aus drei Bahnen kamen sechs Berichte dazu:
      `messung/ABSENKUNG.md`, `dokumente/PLAN-VERIFIKATION.md` und die vier des Rumpfkanals
      (`messung/RUF-TOR.md`, `messung/AUSSETZUNG.md`, `messung/VIER-LUECKEN.md`,
      `messung/SCHLEIFENZUSAGEN.md`). Die Reichweite steigt mit jedem Bericht unter
      `messung/`, und das ist die Richtung, in der eine Ratsche fallen darf — **und der
      Zusammenführung fiel genau diese Zeile dreimal als Konflikt auf.**
      *Die Reichweite sprang am 2026-08-25 von 64 auf 85, weil der Wächter seither die
      BERICHTE unter `messung/` liest* — und der Sprung fand sofort drei lebende Vorkommen,
      alle drei zu `fnptr` (`WB2`).
      *Woran es hängt: eine Teilmengenbuchung bräuchte je Zahlenpaar den Satz „A ist Teil von
      B", und den schreibt niemand hin, solange er nicht wehtut.*

### Design — open decisions

- [ ] **Roundtrip** `lesen(schreiben(x)) == x` gehört in den Differenztest.
      **Gemessen 2026-08-20: die Hälfte, die BEWEISBAR ist, steht schon** —
      `beweise/Format_Roundtrip.thy` (181 Zeilen, 3 Sätze) beweist genau diesen Satz über dem
      Modell. **Was fehlt, ist die andere Hälfte, und sie ist ausführbar, nicht beweisbar:**
      `pruefe-emission.sh` übersetzt und *läuft* je Einheit, prüft aber keinen Rundlauf über
      erzeugten `format`-Code. *Woran es hängt: an Werten.* Der Wächter fährt heute je Einheit
      **einen** Durchgang mit festen Eingaben; ein Rundlauf braucht eine Wertetafel je
      `format`-Deklaration — dieselbe Lücke, die die Mutationsprobe unter „Wertetafeln für die
      Bereichsarithmetik" nennt. **Bleibt offen, außerhalb der Messschicht.**

- [ ] **The line shares of the GABBRO side — that is what still closes the metric.** ⟨B⟩
      B3 has been run and did **not** supply them; it measures the code form, the formula
      weights proof obligations (`dokumente/MESSUNGEN.md`, *EINSETZUNG*). What is missing: what a
      proof **in Gabbro** costs for the same 73 obligations. **That is no longer a measurement on
      Caprock** — for it the obligations have to be written in Gabbro. Until then
      ~~the metric stands at `≥ 1,90`~~ **die Kennzahl lautet seit dem 2026-08-19 `unbekannt,
      > 0,5`**, und **jede kleinere Zahl im Umlauf verwechselt die zwei Seiten**. *Und der
      Posten hat seither einen genaueren Namen: nicht „ein Beweis in Gabbro", sondern **P6** --
      die ERZEUGTE Verfeinerungspflicht. Vorher gibt es nichts zu beweisen, das nicht erfunden
      waere.*
      **Und die Zählerseite hat seit dem 2026-08-20 einen Befehl** (`./instrumente/zaehle-theorien.py`) —
      siehe den Punkt *„Zeilenanteile"* weiter unten. Er schließt die Kennzahl nicht, aber er
      nimmt ihr die schlimmste Verwechslung: **eine Isar-Zeile dieses Ordners ist zu 45,8 %
      Prosa.**

### Die dritte Rezension *(2026-08-20)* — was von ihr NOCH offen ist

*Die fünf Punkte der offenen Hälfte sind geschlossen (M2 viermal, `decreases`, `U003`,
`V006`, `O006`, `N027`, die benannte Konstante). Was bleibt, ist eine Aussage über die
REICHWEITE, keine Lücke im Gebauten.*

*Der erste Punkt ist am **2026-08-20** erledigt und steht in [`DONE.md`](DONE.md): die
Emission trägt **38 von 38**, und alle 38 übersetzen unter `cc -Werror -O2`.*

### Vom ersten echten Treiber, 2026-08-20 *(siehe [`messung/BEFUNDE.md`](messung/BEFUNDE.md))*

- [ ] **Die Nummern der Korpusdateien fallen weg; die Reihenfolge kommt aus einer
      Indexdatei.** Am 2026-08-20 kollidierten zweimal zwei Dateien in derselben Nummer —
      beim Zusammenführen zweier Arbeitsbäume und wenige Stunden später zwischen einem Agenten
      und mir. **`git` meldet es nicht**, weil die Dateinamen sich unterscheiden.
      *Seit heute findet es ein Test* (`keine_zwei_korpusdateien_teilen_eine_nummer`) — beim
      Zusammenführen statt danach. **Die stabilere Fassung nimmt die Wahl ganz weg** (R19:
      *solange die Wahl besteht, bleibt es eine Aufmerksamkeitssache*).
      Nicht heute gebaut, und der Grund gehört zur Sache: die Umbenennung berührt jede
      Dateireferenz in zehn Dokumenten, **und sie mitten in einem Lauf zu machen, in dem
      gerade jemand numerierte Dateien schreibt, wäre die dritte Instanz derselben Kollision.**
      *Bestätigt am Nachmittag des 2026-08-20: derselbe Lauf schrieb weiter numerierte Dateien.*

- [ ] **`guarded` und `covered` sind VERSCHIEDENE Stärken, und die Trennung wird verlockend
      sein zu verwischen.** Eine bewachte Zelle sagt *„diese Kombination ist verboten, und die
      Absage fällt nachweislich"*; eine gedeckte sagt nur *„sie kommt vor, und irgendein Pass
      sieht sie"* — und Maß 2 hat gerade gezeigt, dass **Sehen keine Prüfung ist**.
      **Seit dem 2026-08-20 stehen beide Zahlen im Register und nicht mehr nur im Bericht:**
      **168 besetzte Zellen** stehen daneben, **25 nur im Gift** — und `gabbro blindstellen`
      druckt die vier Zahlen getrennt, *auf Ausdruck*, weil ein Einzelwert zwei Wochen später
      wie Fortschritt aussieht.
      *Die schärfere Frage bleibt dieselbe wie beim Schablonenregister: fällt an dieser Zelle je
      etwas?* — also **Mutation oder Giftprobe je KOMBINATION, nicht je Konstrukt.**
      **Woran es hängt, jetzt beziffert:** 164 Kombinationen brauchten je eine Probe; der
      Mutationskatalog trägt heute 240 Anker, also liegt die Größenordnung neben dem, was schon
      steht — *und das ist der Grund, warum es kein Nachmittag ist.*

- [ ] **85 Absagetexte sagen ihren Grund in KEINER der beiden Sprachen** (`./instrumente/pruefe-gruende.py`,
      2026-08-20). Die billige Näherung sortiert jede Regel danach, ob ihre Begründung eine
      Eigenschaft der **Absenkung** (*„hat keinen Speicher", „ist ein unbekannter Ruf", „die
      Breite läuft über"*) oder eine Eigenschaft der **Zusage** (*„genau einmal", „auf jedem
      Pfad"*) nennt. 104 sind tragend, 2 verdächtig — und **85 Absagetexte sagen ihren Grund in
      KEINER der beiden Sprachen**.
      **Die Zahl sprang am 2026-08-30 von 57 auf 85, und der Sprung ist kein Rückschritt am
      Prüfer — er ist eine Reparatur am WÄCHTER.** Sein Lesefenster war 4000 Zeichen lang
      und endete an keiner Regelgrenze; wo zwei Absagen näher beieinander standen, las die
      erste die Wörter der zweiten als ihre eigenen. *Aufgefallen an einer Änderung, die
      keine der beiden Regeln anfasste:* vierunddreißig eingefügte Kommentarzeilen zwischen
      `N029` und `N034` schoben `N029` von „tragend" nach „unklar" — es war nie durch seinen
      eigenen Text eingeordnet, sondern durch `promise` aus einer NOTIZ VON `N034`.
      **27 der 131 „tragenden" hingen so** (131 → 104). Die Fenstergrenze steht jetzt an der
      nächsten Kennung, und eine Sprechprobe hält sie. *Dieselbe Klasse wie W16: ein Wächter,
      der den Nachbarn misst, sieht genauso plausibel aus wie einer, der seinen Gegenstand
      misst.*
      *Wer eine Absage liest und daraus nicht erkennt, worauf sie ruht, kann auch nicht
      prüfen, ob sie weit genug reicht.* Das ist der größere Posten, nicht die zwei.
      **Berichtigt 2026-08-20: hier stand 96, der Befehl sagt 98** — die zwei kamen mit
      `N007`/`N008` dazu und niemand zog die Zahl nach. *Seit heute hält das Register alle drei
      Zahlen gegen den Befehl.* **Woran der Rest hängt:** die 44 sind kein Fehler, sondern ein
      **Schreibauftrag** — je Absage ein Satz, der ihren tragenden Grund nennt.
      Vierundvierzig Sätze, kein Pass, keine Grammatik.

- [ ] **Welche anderen Regeln stehen auf dem TECHNISCHEN statt auf dem tragenden Grund?**
      Am 2026-08-20 fiel dieselbe Klasse viermal: `diverges`, die Geistlöschung, der Geist im
      Speicher (der *lineare* Wert fiel durch, weil die Regel „hat keine Absenkung" sagte statt
      „hat keinen Pfad") und der Aufrufgraph (ein Konstruktor ist kein Ruf). **Eine Prüfung,
      die aus dem naheliegenden Grund gebaut wurde, deckt nicht, was der eigentliche Grund
      verlangt.** Alle vier kamen einzeln heraus, beim Schreiben von Programmen; eine
      systematische Antwort läse jeden erklärten Regelgrund gegen das, was die Regel wirklich
      halten muss.
      **Und die Messschicht sagt, warum sie das nicht kann:** `pruefe-gruende.py` liest den
      Regelgrund gegen eine **geschlossene Wortliste** und trennt damit *Absenkung* von
      *Zusage*. Was es nicht liest, ist der **Gegenstand** — ob der genannte Grund die Zusage
      wirklich trägt. Alle vier Fälle waren sprachlich tadellos und sachlich falsch.
      *Woran es hängt: an einer zweiten Quelle für das, was die Regel halten MUSS* — und die
      gibt es heute nur im Kopf. **Bleibt offen, außerhalb der Messschicht.**

### «OPT» — schnelles und sicheres C, geplant 2026-08-19 ([`dokumente/PLAN.md`](dokumente/PLAN.md)) *(Teil)*

- [ ] **~~OPT0 — der Wächter muss OPTIMIERT übersetzen~~ — WAR SCHON GEBAUT, seit dem
      2026-08-19.** Der Punkt sagte *„`pruefe-emission.sh` fährt `-Wall -Wextra -Werror` und
      **ohne `-O`** … gemessen habe ich das, nicht der Wächter."*
      **Der Wächter tut es.** Stufe 5 übersetzt jede Einheit ein zweites Mal unter
      `-O2 -Wall -Wextra -Werror`, führt sie aus und verlangt **dasselbe Ergebnis wie unter
      `-O0`**; Stufe 6 fährt sie unter `-fsanitize=undefined`. Beide tragen eine Sprechprobe,
      und die von Stufe 5 ist die schärfere: ein absichtlicher Typverstoß **muss** unter `-O0`
      und `-O2` verschieden rechnen, sonst hat die Stufe nichts gemessen. Der Lauf vom
      2026-08-20 druckt sie: *„Sprechprobe 5: ok (-O0 0 gegen -O2 1)"*.
      **Und dass ich ihn beim Durchgehen der Stufe 0 als offen wiederholt habe, gehört zum
      Befund**: der Punktetext war die einzige Quelle, die ich gelesen habe — *ein Punkt, der
      seinen eigenen Gegenstand nicht nennt, überlebt seine Erledigung.* Er nennt ihn jetzt.
      **Was WIRKLICH offen bleibt, ist eine Zeile davon:** `-fsanitize=address` läuft auf
      diesem Rechner nicht (gehärteter Kern, Schattenspeicher-Kollision). *Keine bestandene
      Probe, sondern eine nicht gefahrene* — und damit derselbe Fall wie der zweite Korpus
      zwei Punkte höher: **ortsgebunden, nicht schwer.**

- [ ] **Das GROBE Mass (greift ein Pass die Item-Art an?) findet die falsche Sache**
      *(2026-08-19, nachgemessen 2026-08-20)*. **23 von 23 Item-Arten** sind „gelesen" —
      **`ops` und `check` darunter**, obwohl keine ihrer Zusagen geprüft wird.
      `ItemArt::Check` wird nur angefasst, um in `can_fail` hineinzulaufen; `ops` steht als
      `!is_empty()` da. **Ein Konstrukt kann berührt werden, ohne dass eine einzige seiner
      Zusagen fällt.** *Ein Maß, das Zugriff mit Wirkung verwechselt, misst die Verdrahtung
      und nicht die Regel.*
      **Und die Zahl selbst ist der Beleg:** sie stand hier als *21 von 23* und ist inzwischen
      *23 von 23* — **das Maß ist gestiegen, ohne dass eine Zusage mehr geprüft würde.** Genau
      die Bewegung, vor der der Punkt warnt, und sie ist an ihm selbst passiert. Seit heute
      hält das Register die Zahl gegen `./instrumente/pruefe-konstrukte.py`.
      **Woran das schärfere Maß hängt:** es müsste je Item-Art fragen, ob eine ABSAGE an ihr
      fällt — das ist Maß 2 (Giftprobe je Konstrukt, heute 0 von 19 ohne) *je Zusage* statt
      *je Konstrukt*. **Dieselbe Größenordnung wie die Kombinationstafel oben. Bleibt offen.**

- [ ] **~~Die 161 zerbrochenen Meldungen hat kein Waechter gesehen~~ — GEBAUT 2026-08-20.**
      Beim Übersetzen ins Englische verloren die Zeilenfortsetzungen ihr Leerzeichen —
      *„that isa compile error"*. **Gefunden, weil ich eine Meldung gelesen habe.**
      `pruefe-englisch.py` prüfte die SPRACHE eines Textes, nicht seine Lesbarkeit.
      **Die Probe war billig und steht jetzt drin:** Rusts Zeilenfortsetzung frisst den Umbruch
      *und die Einrückung*, also hängt die Trennung an genau einem Zeichen — dem letzten davor.
      Heute **2093 Zeilenfortsetzungen** in den Quellen, **0 kleben**.
      *Die Zahl sprang am 2026-08-21 von 839, und der Grund ist eine einzige Datei:*
      `saetze.rs` trägt 46 Sätze als fortgesetzte Zeichenketten. **Die Fläche der Probe
      hat sich damit fast verdoppelt, ohne dass ein Programm dazukam** — wer die Quote
      liest, liest seit heute überwiegend ein Register und nicht mehr den Prüfer.
      **Und der Befund ist, dass es nicht null war:** der erste Lauf fand **16** Nahtstellen —
      ein Jahr nachdem die 161 von Hand geflickt worden waren. *Von Hand geflickt heißt: nicht
      bewacht.* Darunter `„…is verified--"`, `„…the rule therefore has**zero bite**"` und
      `„…reach the same stage.From strict one can loosen"`. Alle sechzehn sind repariert.
      *Was der Wächter NICHT sieht:* eine Meldung, die aus zwei Zeichenketten zusammengesetzt
      wird, geht nicht durch eine Fortsetzung — er verpflichtet, er spricht nicht frei (W10).

- [ ] **Ein WAECHTER, der die Ausgabe eines Werkzeugs liest, gehoert zu dessen Sprache**
      *(gefunden 2026-08-19 beim Uebersetzen der Berichte)*. Drei haetten es nicht ueberlebt
      und waeren STUMM gruen geblieben: `pruefe-emission.sh` (die Zeugniszeile per `sed`),
      `pruefe-todo.py` zweimal (`OFFEN`/`TEIL` aus `gabbro paesse`, und die Schablonenzahl).
      **Ein Muster, das nichts findet, meldet nichts.**
      **Die allgemeine Frage ist am 2026-08-20 zur Hälfte beantwortet, und die Antwort ist eine
      Bauform, keine Zahl:** `pruefe-zahlen.py` liest heute 39 Werkzeugausgaben mit einem
      Muster, und **jedes einzelne trägt eine Sprechprobe** — das Werkzeug verstellt die Zahl im
      Text und verlangt, dass der Eintrag fällt. *Ein Muster ohne Treffer ist dort selbst ein
      Befund, in beiden Richtungen.*
      **Was offen bleibt und woran es hängt:** die Muster außerhalb des Registers.
      `pruefe-emission.sh` und `pruefe-todo.py` lesen Werkzeugausgaben mit eigenen `sed`- und
      `grep`-Mustern, und für die gibt es keine mechanische Liste — *ein Muster ist dort nicht
      deklariert, es steht mitten im Code.* Eine vollständige Antwort verlangte, jedes
      Ausgabemuster als **Eintrag** zu führen statt als Zeile, also die beiden Wächter auf die
      Registerform umzubauen. **Bleibt offen.**

- [ ] **Der Waechter erkennt ETIKETTEN nicht** *(2026-08-19)*. `Art::Erhaltung => "Erhaltung"`
      blieb stehen -- ein Wort ohne Funktionswort faellt durch die geschlossene Liste. Von
      Hand uebersetzt. **Der Waechter sagt es ueber sich selbst** (86 Woerter, W10), *und die
      Stelle ist der Beleg, dass die Selbstauskunft keine Floskel ist.*
      **Gemessen 2026-08-20, und die Lücke ist genau beziffert:** von den 713 Meldungstexten der
      Sprachfläche bestehen die Etiketten aus **einem** Wort; die Liste kennt 86
      Funktionswörter, und ein Einwortetikett enthält per Konstruktion keins.
      *Woran es hängt:* die Gegenmaßnahme wäre eine **Wortliste in die andere Richtung** — ein
      Verzeichnis erlaubter englischer Etiketten — und damit ein zweites Register über
      derselben Sache (W7). **Bleibt bewusst offen:** der billigere Riegel ist, dass ein
      Etikett gar nicht erst durch die Sprachfläche läuft, und das ist Bauarbeit am Bericht,
      nicht am Wächter.

### «NL» — der Weg zu „nur noch eigene Logik" ([`dokumente/PLAN.md`](dokumente/PLAN.md)) — **PUNKT 1** *(Teil)*

- [ ] **Zweimal an einem Tag war die KLAUSELTABELLE keine Quelle** *(2026-08-19)*. Bei
      `leaves` sagte sie *„welche Wege die Schleife verlassen darf"* -- `SPRACHE.md`:730 sagt
      *lineare Werte*, und die danach gebaute Regel meldete zwei Befunde an einem RICHTIGEN
      Korpus. Bei `counterprobe` sagte sie *„kein Pass fuehrt sie aus"* -- der Grund ist, dass
      die Spezifikation den Namen nicht bindet. **Beide Saetze sind berichtigt.**
      **Die allgemeine Frage hat einen Befehl, aber er misst die andere Hälfte:**
      `./instrumente/pruefe-klauseln.py` liest 147 Feldnamen aus `ast.rs` gegen 29 Leserdateien und bucht
      22 Klauseln — *er sagt, WER eine Klausel liest, nicht ob die Tabelle sie richtig
      beschreibt.* **Und das ist die Trennung aus W19 an einer neuen Stelle:** die Stufe
      (gelesen / nur getragen / ungelesen) ist gemessen, die Klasse (ZUSAGE / FREMD /
      ABSENKUNG / TOT) ist ein Urteil, und das Werkzeug sagt es selbst.
      *Woran die vollständige Antwort hängt:* ein Vergleich Zeile-gegen-Pass verlangte eine
      **maschinenlesbare Fassung dessen, was die Klausel bedeutet** — und die gibt es nur in
      der Prosa der Tabelle. **Bleibt offen.**

### Aus «H2» *(ausgefuehrt 2026-08-19, `H = 17 → 15`)* — der Rest, den der Lauf hinterliess *(Teil)*

- [ ] **«P6» heisst ZWEIERLEI, und beide Register sind in Gebrauch** *(gefunden 2026-08-19
      beim Versuch, P6 fertigzubauen)*. `dokumente/SPRACHE.md` fuehrt eine Baureihenfolge
      P0–P7, `dokumente/PLAN.md` eine zweite P0–P8 — und **ab P1 bedeutet jedes Etikett etwas
      anderes**.
      **Und dieser Punkt war selbst abgeschnitten** *(gefunden 2026-08-20)*: er endete mit
      einem Doppelpunkt, und die angekündigte Tabelle stand nirgends. *Ein Punkt, der eine
      Liste ankündigt und keine führt, sieht vollständig aus* — dieselbe Klasse wie ein Muster
      ohne Treffer. **`pruefe-todo.py` bucht die Kollision seit dem 2026-08-19 als neun
      Abweichungen** (*„9 gebuchte Abweichungen, keine neue"*), und das ist die Liste, die hier
      fehlte: der Befehl führt sie, nicht der Absatz.
      **Was offen bleibt, ist die Entscheidung, nicht die Messung:** welche der zwei Reihen
      gilt. *Woran es hängt: an einem Wort des Ordners, und der Preis ist, dass die andere
      Reihe in jedem Dokument nachgezogen werden muss.*

- [ ] **~~Die Zeilenanteile der eigenen Theorien sind gezaehlt, aber nicht KLASSIFIZIERT~~ —
      GEBAUT 2026-08-20** (`./instrumente/zaehle-theorien.py`). Die alte Buchung sagte *„zehn Theorien,
      1 639 Zeilen, 48 Sätze, 86 Beweisschritte"* und ließ die Frage offen, was davon Prosa
      ist. Heute: **3512 Zeilen** in fünfzehn Theorien, **101 Sätze** darin — und klassifiziert:

      | | | |
      |---|---:|---|
      | Gerüst | 564 | 16,1 % — `theory`/`imports`/`begin`/`end` und Leerzeilen |
      | Prosa | 1 612 | **45,9 %** — Kommentare, `text`-Blöcke, Überschriften |
      | Modell | 226 | 6,5 % — Definitionen, Datentypen |
      | Beweis | 1 110 | 31,6 % — Sätze samt ihren Beweisen |

      **Und die fünfzehn sind ZUSAMMEN gebaut, nicht nur einzeln:** `isabelle build -D .`
      über den vereinigten Stand, 2026-08-30, **LOKAL** (`threads=4`, 12 s Wanduhr, 28 s CPU,
      Faktor 2,23, Rückgabewert 0). *Beide Bahnen hatten je vierzehn gebaut, und keine hatte
      die fünfzehn* — genau die Lücke, für die Schritt 6 im Plan steht. Lokal deshalb, weil
      `ki-pc-fisch-101` seit 19:42 nicht erreichbar ist und der Wachhund, vor dem `CLAUDE.md`
      warnt, auf diesem Rechner heute nicht greift (31 GB gesamt, 13 GB frei, 20 Kerne).
      *Die Regel bleibt trotzdem stehen: sie ist eine Aussage über den Speicher, nicht über
      die Gewohnheit — und der Speicher war heute ein anderer.*

      *~~2570 Zeilen, dreizehn Theorien, 76 Sätze, 956 Modell+Beweis~~ — nachgezogen
      2026-08-28 durch ZWEI Theorien aus zwei Bahnen: `beweise/Absenkung_Parametrisch.thy`
      (der Absenkungssatz, parametrisch über sechs Eigenschaften der Zielsemantik) und
      `beweise/Table_Zaehlung.thy` («B13»s Zählung, ihre Erhaltungsfrage und zwei Grenzen als
      Gegenbeispiel). **Die Anteile haben sich dabei um weniger als einen halben Punkt
      bewegt**, und das ist der eigentliche Befund: zwei weitere Theorien ändern die
      Verwechslung nicht.*

      **Fast die Hälfte ist Fließtext, und damit ist die Verwechslung beziffert:**
      **1336 Zeilen Modell und Beweis** sind das, was einer Verus-Zeilenzahl gegenübersteht —
      **38,0 % statt 100 %.** *Wer 3512 gegen eine Verus-Zahl hält, überschätzt die eigene
      Seite um den Faktor 2,6.*
      *Die sechzehn Zeilen vom 2026-08-30 abends sind die neun ausgeschriebenen
      Beweisschritte: **Suche durch Rechnung ersetzt kostet Zeilen**, und zwar genau im
      Anteil `Beweis`.* Dieselbe Verwechslung, an der `1,90` am 2026-08-19
      zurückgezogen wurde, eine Ebene tiefer.
      *Und was das NICHT heißt:* die Einteilung liest Zeilenanfänge; ein `text`-Block über ein
      Modell zählt als Prosa. **Eine Näherung mit benannter Kante, kein Parser** (W10).

- [ ] **`C001` sagt „keine Absenkung" und wird fuer FALSCHES mitbenutzt** *(gefunden
      2026-08-19 an «B24»)*. Eine Bitlage jenseits der Wortbreite ist kein *„das koennen wir
      noch nicht"*, sondern ein *„das ist falsch"* -- bis dahin trug beides dieselbe Kennung.
      Zwei der drei Faelle sind mit `N007`/`N008` in den Pruefer gezogen; **die Luecke im Wort
      bleibt bewusst `C001`**, weil erst die Absenkung eine bestimmte Wortgrenze braucht.
      **Nachgezählt 2026-08-20: `C001` steht an sechs Stellen im Prüfer und wird an fünfzehn
      Stellen im Korpus erwartet** — und `./instrumente/pruefe-gruende.py` führt `C001` als **verdächtig**
      (*„no lowering, byte, bytes"*), also als eine Regel, die sich über die Darstellung
      begründet. *Das ist derselbe Befund aus der anderen Richtung: die Kennung nennt die
      Absenkung, und gemeint ist teils die Wortbreite.*
      **Woran es hängt:** die sechs Stellen einzeln durchzusehen ist eine Stunde; was fehlt,
      ist das Urteil, ob eine zweite Kennung (*„jenseits der Wortbreite"*) den Wortschatz wert
      ist. **Bleibt offen — und der Verdacht steht jetzt in einem Befehl statt in einem Satz.**

- [ ] **`bool @N`: der ERZEUGER hat entschieden, `bitlage.rs` ist nicht mitgegangen**
      *(2026-08-19, geschärft 2026-08-20)*. Die Wortbreite einer Bitgruppe kommt seit dem
      2026-08-20 aus ihren **Ganzzahlfeldern** — *ein `bool` sagt, welches BIT, nie welches
      WORT* — und `format Pte` senkt damit ab. **`bitlage.rs` bucht `bool @N` weiterhin als
      `Unklar`.** Damit stehen zwei Register über derselben Sache und sind
      **auseinandergelaufen** (W7): der Erzeuger weiss die Breite, der Prüfer nicht. *Das ist
      keine untere Schranke mehr, sondern eine Divergenz — und die gehört aufgelöst, nicht
      verwaltet.*
      **Und die Messschicht kann sie nicht auflösen, sie kann sie nur zeigen:** eine Divergenz
      zwischen zwei Registern fällt erst auf, wenn beide dieselbe Zahl ableiten — und hier
      leitet keines eine ab. *Woran es hängt: `bitlage.rs` muss die Breitenregel des Erzeugers
      übernehmen — Passarbeit an einer Datei, kein Wächter.* **Bleibt offen, außerhalb der
      Messschicht.**

- [ ] **`pruefe-widerruf.py` ist ein GEDAECHTNIS und kein URTEIL** *(gebaut 2026-08-19)*.
      Heute zehn Widerrufe gebucht, elf Fundstellen geschlossen. **Er findet nur, was jemand
      als widerrufen aufgeschrieben hat** -- und dass zwei der acht in der SPEZIFIKATION
      standen (`SYNTAX.md`:165, `SPRACHE.md`:614) und von Hand nicht gefunden wurden, sagt,
      dass es weitere gibt.
      *Was fehlt, ist die andere Richtung: eine Liste dessen, was gebaut wurde, gegen die
      Dokumente gehalten -- statt eine Liste dessen, was widerrufen wurde.*
      **Woran es hängt, benannt 2026-08-20:** diese Richtung existiert in Stücken und ohne
      gemeinsamen Ort — `pruefe-notation.py` hält acht Grammatikentscheidungen gegen den
      Prüfer, `pruefe-konstrukte.py` 23 Item-Arten, `pruefe-klauseln.py` 147 Feldnamen,
      `pruefe-reichweite.py` die Tafel Pass mal Bauteil. **Vier Teilantworten, kein Register.**
      *Die vollständige Fassung wäre eine Liste „gebaut ⇒ steht in Dokument X" mit einer
      Sprechprobe je Zeile — und sie ist genau so groß wie das Gebaute.* Bleibt offen.

- [ ] **Die Zaehlerueberlaufklasse gehoert in die Messungen, nicht nur in ein Fragment**
      *(2026-08-18)*. `M101` fand in K2-F2 einen Ueberlauf, den das Original nicht prueft --
      `atomic_long_inc_not_zero` schuetzt gegen NULL, nicht gegen die obere Schranke. **Wie
      viele der 637 `atomic_*()`-Stellen des zweiten Korpus sind Zaehler ohne obere
      Schranke?** Das ist eine Zaehlung, und sie waere die erste Zahl dieses Ordners, die
      einen FREMDEN Fehler misst statt eine eigene Deckung.
      **Woran es hängt, gemessen 2026-08-20:** der zweite Korpus liegt **nicht** dort, wo
      gerechnet wird. `zaehle-narrow.py` nimmt ihn unter `~/Dokumente/SEL4Lake/SEL4Lake` an,
      und auf `ki-pc-fisch-101` — wohin die Rechenlast gehört — ist er nicht. *Das ist seit
      heute deklariert (`FREMDER_KORPUS` in `pruefe-waechter.py`) statt still.* **Die Zählung
      ist damit nicht schwer, sondern ortsgebunden**, und der erste Schritt ist eine
      Übertragung, kein Werkzeug.

### From the counter-check (2026-08-14) — what is still open

- [ ] **THE CHEAP CLOSURE, and it belongs BEFORE the big sentences about "nothing else":
      `effects` checks writes and `locks`, but not reads and not calls.**
      ~~Frame completeness holds today only for the **write half**~~ — **beide Hälften sind
      gebaut, nachgemessen 2026-08-20.** Die Leseseite steht seit dem 2026-08-16 als `E010`
      (Lesart A), die Rufwirkungen seit dem 2026-08-15 als `E008`; die Passleiste in `lib.rs`
      sagt es wörtlich: *„writes, `locks` and since 2026-08-16 reads (reading A, `E010`) are
      held against the list"*. **Der Punkt beschrieb einen Zustand von vor fünf Tagen** —
      *dieselbe Klasse wie die sieben veralteten Zahlen oben, nur in Prosa statt in einer
      Zelle, und deshalb von keinem Register erreichbar.*
      **Was WIRKLICH offen ist, und der Punkt sagt es selbst weiter unten:** die Abbildung der
      Rufwirkungen auf die **Argumente** — ein `writes p.slots` des Gerufenen wird mit SEINEM
      Parameternamen gesehen. Grob in die sichere Richtung (W9), *und die Abbildung braucht
      eine Aliasanalyse, die es nicht gibt.* **Das ist der ganze Rest dieses Punktes.**

- [ ] **`result` im Rumpf ist heute kein Fehler des Prüfers.**
      Gemessen 2026-08-30 (W24, unveränderter Prüfer): `gabbro pruefe` nimmt
      `{ let x = result; return k.eintritt; }` mit **0 Fehlern, 0 Hinweisen** an. Der
      Rumpfkanal sagt es ab (`result-in-body`, seit dem 30. unter eigenem Namen — siehe
      `messung/ERGEBNIS-ZWEI-NAMEN.md`), **aber eine Absage des Beweiskanals ist keine
      Zurückweisung des Programms**: wer nie `pflichten --lean` ruft, sieht nichts. `result`
      ist ein reserviertes Wort und benennt im Rumpf nichts — die Form ist unrettbar, nicht
      nur unübersetzbar. *Gemessener Bedarf im Korpus: null* — keine der 93 `.gab`-Dateien
      schreibt es, der Fall stammt aus einer erfundenen Probe. **Regel A: erst zählen, dann
      bauen** — die Frage ist, ob ein Pass eine Form zurückweisen soll, die niemand schreibt.

- [ ] **Zwei Wächter hängen am ÜBERTRAGUNGSWEG, und der erste `--voll`-Lauf hat beide gefunden.**
      Gemessen 2026-08-30 auf `ki-pc-fisch-101`, `abnahme.py --voll`:
      * **`pruefe-beweise.sh` ROT nach `rsync -rlpgoD`** — und der Wächter sagt die Ursache
        selbst: *„Häufigste Ursache ist NICHT eine Änderung an den Beweisen, sondern der Sync.
        `rsync -rlpgoD` gibt jeder übertragenen `.thy` die AKTUELLE Zeit. Isabelle rechnet nach
        INHALT und baut nichts; dieser Nachweis rechnet nach ZEIT und findet keinen."* Nach
        `rsync -a beweise/ …`: **`ALL PASS — 15 Theorien`**. `CLAUDE.md` sagt das, aber die
        **eine** `rsync`-Zeile, die ein Agent im Auftrag bekommt, ist die für `cargo`.
        *Zwei Werkzeuge im selben Baum verlangen entgegengesetzte Zeitstempel-Semantik, und
        wer nur eine Zeile kopiert, bekommt einen roten Wächter, der nichts über den
        Gegenstand sagt.* **Was fehlt, ist EIN Übertragungsbefehl**, der beides richtig macht
        (`--exclude beweise/` plus ein zweiter `-a`-Lauf) — ein Skript, nicht ein Merksatz.
      * **`pruefe-zahlen.py` bricht ohne `cargo` im `PATH` mit `FileNotFoundError` ab** —
        Rücklaufwert 1 und ein Fenster voll Rückverfolgung, das aussieht wie ein Befund. Für
        `ssh` ist `~/.cargo/bin` nicht im `PATH`, und das steht in keinem `FREMDER_KORPUS`.
        *Ein Wächter, dessen Urteil am `PATH` hängt, misst die Anmeldung.*

- [ ] **`pruefe-lean-beweis.sh` liegt zu dicht an seiner Frist.**
      Gemessen 2026-08-30: **194 s und 205 s** auf leerem `fisch`, **über 300 s** im
      `--voll`-Lauf direkt nach dem Mutationslauf — dort als `HAENGT` gemeldet, obwohl es nur
      langsam war. `abnahme.py` hat seine Frist deshalb auf `2 × FRIST` gesetzt (mit Grund im
      Quelltext), aber *das ist die Kompensation und nicht die Messung*: **niemand weiß, wie
      lange der Wächter unter Last wirklich braucht.** Eine Frist bei 1,5× der gemessenen
      Laufzeit macht LAST zu einem Befund — dieselbe Klasse wie ein falsches Grün, nur
      andersherum. *Was fehlt, ist eine Messung unter Last, keine größere Zahl.*

- [ ] **Die zwei Überlebenden von Fach 1 sind beide die echte Form — und eine ist die STILLE Richtung.**
      Sichtbar geworden, als `pruefe-aufloesung.py` am 2026-08-30 die 26 Stellen des
      Erzeugers nach Fach 0 sortierte (`messung/AUFLOESUNG-BEZUGSGROESSE.md`); vorher waren
      es zwei Nadeln in 28.
      * **`m1.rs:1401`, `endet_immer`** — `p.teile.last()` nimmt von `a::b::f` das `f` und
        fragt damit `u.funktionen`, das unter `a::b::f` geschlüsselt ist. **Im `module`
        liefert das immer `None`**: ein Aufruf einer `-> never`-Funktion wird dort nie als
        blockbeendend erkannt. Der Kommentar darüber nennt genau diese Antwort die sichere
        Richtung — aber für den INDIREKTEN Aufruf; für den qualifizierten steht es nicht da.
        *Konservativ, also nicht dringend — aber es ist die Form, die dreimal zuschlug.*
      * **`m1.rs:3552`, `name_aufloesen`** — zwei Zeilen untereinander, zwei qualifizierte
        Karten, **eine mit und eine ohne Entqualifizierung**: `funktionen.contains_key(n)`
        neben `tabellen.keys().any(|k| … k.rsplit("::") …)`. Richtung laut (ein falsches
        `M119` „is declared nowhere"), nicht still.
      **Nicht angefasst, Regel A: gemessener Bedarf null.** Kein Korpusprogramm ruft heute
      eine qualifizierte `-> never`-Funktion. Die Ratsche auf **2** hält beide fest — eine
      dritte Stelle fällt sofort auf. *Was hier fehlt, ist eine Giftprobe, die die stille
      Richtung sichtbar macht; ohne sie ist „konservativ" ein Argument und keine Messung.*

- [ ] **`pruefe-abstieg.py` endet seit mindestens dem 2026-08-28 mit 1**, und der Inhalt ist
      eine BENANNTE Weigerung (`emit::rumpf_als_wert`, 8 Arten) plus `m2::endet` ohne Abstieg
      in sieben Arten. *Ein Wächter, dessen roter Ausgang ein gebuchter Dauerzustand ist,
      unterscheidet einen neuen Befund nicht von dem alten* — er braucht entweder eine Marke
      wie die anderen Ratschen oder einen zweiten Ausgangswert.

- [ ] **The mutation probe covers the checker today, not the emission.**
      `./instrumente/mutiere-pruefer.py` beschädigt eine Regel des Prüfers und sieht nach, ob eine Probe
      fällt. Mutationskatalog: **346 von 346 Ankern** greifen (`--anker`, 2026-08-30).
      ~~345 von 345~~ nachgezogen am 2026-08-30: die 346. trennt die zwei Fälle von `result`
      (`messung/ERGEBNIS-ZWEI-NAMEN.md`). Die
      acht des Rumpfkanals kamen am 28. abends dazu, und am 30. fünf weitere aus drei Ketten:
      der **vierte Ort der Geistlöschung** (ein `let`-gebundener Geist, blank genannt), das
      `let … else` über einem `place` (`m1.rs`), und die drei Hälften von `return e;` am
      fehlbaren Register — Bindung (`M1`), Anerkennung (`N034`) und der Kanal, durch den der
      Grund hinausgeht (`emit.rs`).
      *Zwei Ketten haben den vierten Ort UNABHÄNGIG gefunden und beide repariert; behalten ist
      die gebaute und am `cc` in beide Richtungen nachgewiesene Fassung, die zweite samt ihrer
      Mutation entfernt.* **Zwei Register über derselben Sache sind W7, auch wenn beide
      stimmen.** Drei bewachen den
      Rufsammeltopf (`B1`, `messung/RUF-TOR.md`): der Optionswert, der wieder als Ruf gelesen
      wird, der Sammeltopf, der sich wieder schließt, und der Verbundkonstruktor, der wieder
      Ruf heißt. Zwei die Aussetzung (`B2`, `messung/AUSSETZUNG.md`): `breaking`, das wieder
      Ausgang heißt, und die ausgesetzte Invariante, die ihren Namen im Datum verliert.
      Zwei das Ergebnis (`B3`, `messung/VIER-LUECKEN.md`): das Glied, das einen ERZEUGTEN Wert
      verlangt, und `result`, das wieder im Rumpf übersetzt wird. Und eine die LOKALE
      (`B5`, `messung/SCHLEIFENZUSAGEN.md` §1): eine Zuweisung an ein `let mut`, die wieder
      als Weltspeicher übersetzt wird — **die einzige der acht, die kein Register verkleinert,
      sondern das Programm im Datum austauscht.**
      *Sieben der acht lassen die Bilanzzeile unberührt* — genau der Grund, warum die Proben
      den emittierten Text lesen und nicht die Zahl.

      **Der erste volle Lauf über die VEREINIGUNG, 2026-08-30** (lokal, 10 min 10 s Wanduhr,
      29 min CPU): **337 von 339 gültigen Mutationen gefangen (99 %)** — und die drei
      Auffälligkeiten stammen alle aus denselben acht.
      `messung/RUMPFKANAL-LUECKEN.md` misst sie einzeln:
      **zwei ÜBERLEBENDE** (eine Regel an zwei Armen mit einer Probe nur am zweiten; und eine
      Probe, die ihren Namen trug und nicht ihren Gegenstand — `W16`, zum zweiten Mal in drei
      Tagen) und **eine UNGÜLTIGE**, die nach der Reparatur ihres Escapes zu Recht überlebte,
      weil sie eine Tautologie einfügte. Alle drei geheilt, jede von Hand nachgemessen:
      vorher ÜBERLEBT, nachher GEFANGEN.
      **Der Lauf DANACH, derselbe Katalog: `340 von 340 gültigen Mutationen gefangen
      (100 %)`** (10 min 25 s Wanduhr, 29 min CPU) — keine Überlebende, keine ungültige.

      **Und dann noch zweimal, weil der Katalog weiterwuchs:** über 344 fiel eine als
      `ungueltig` heraus (`if false` an einem `match`-Arm, der dadurch unvollständig wurde —
      `E0004`), über **345 sind es 345 von 345 (100 %)**, keine ungültige, keine Überlebende
      (10 min 8 s). *Zum zweiten Mal an einem Tag hat eine ungültige Mutation den Nenner
      verkleinert*, und beide Male hat `--anker` sie durchgelassen:
      > **`--anker` sagt, dass der Ankertext sitzt. Ob der mutierte Baum ÜBERSETZT, sagt erst
      > der volle Lauf** — zehn Minuten später. Eine neu geschriebene Mutation ist erst fertig,
      > wenn sie einmal von Hand gesetzt, gebaut und als *genau eine fallende Probe*
      > nachgemessen wurde.
      *Die Quote ist zum ersten Mal voll, und sie misst weiterhin nur den Prüfer:*
      Prüfer 213 · Code 86 · Annotation 38 · Schablone 3. **Eine Fläche mit 0 Mutationen ist
      nicht gedeckt, sondern unbeschädigbar.**
      > **`--anker` fährt keine Mutation.** Bahn B meldete „335 von 335 Ankern" — das ist
      > wahr und es ist keine Quote. Ein Anker, der greift, sagt *diese Zeile gibt es noch*,
      > nicht *und eine Probe fällt, wenn sie sich ändert*. **Dazwischen liegen zehn Minuten,
      > und genau dafür steht der volle Lauf in Schritt 6.**
      Die
      Zahl stand hier als *24 von 24* und in `CLAUDE.md` als *159*, beide aus früheren Läufen.
      *Ein Katalog, der wächst, macht jede Zahl daneben zu einer Jahreszahl.*
      **Der erste volle Lauf seit mehreren Tagen, 2026-08-28** (`ki-pc-fisch-101`, 6 min 32 s):
      **325 von 326 gültigen Mutationen gefangen (99 %)** — Prüfer 209 · Code 84 · Annotation
      30 · Schablone 3, Nullmutation ÜBERLEBT, Giftmutation gefangen, `ungueltig: 0`.
      Die *eine* Überlebende war ein Wächterfehler und keiner des Erzeugers: die Zusicherung
      zum Schritt einer `bank` stand über der GANZEN Ausgabe, und seit dem 2026-08-26 trägt
      der emittierte Schreiber dieselbe Adressrechnung — er erfüllte sie allein. Geheilt an
      `rechenwerk.rs` (Zusicherung je BLOCK), danach die zweite Mutation für den Schritt des
      Schreibers, der bis dahin überhaupt keine Probe hatte. **Beide von Hand nachgemessen:
      vorher ÜBERLEBT, nachher GEFANGEN.** *Der volle Lauf über alle 327 steht noch aus und
      gehört in die Zusammenführung — zwei Handmessungen sind keine Quote.*
      Was weiterhin fehlt, ist dieselbe Probe auf der **Annotationsemission**: dort entsteht
      der Wunschform-Beweis, und dort ist bis heute nichts zu beschädigen, weil nichts
      emittiert wird.
      * **~~Die Mutationen sind von Hand geschrieben~~ — GEFAHREN 2026-08-15, Tor
        BESTANDEN.** `erzeuge-mutationen.py` verdreht systematisch: **7 von 39 gefangen
        (18 %)** gegen 38 von 38 der Handmutationen. Der Verdacht stimmte, und der eigentliche
        Befund ist **wo**: 6 der 15 echten Lücken in `typen.rs`, 5 in `umgebung.rs`. *Der
        Prüfer ist dicht, wo er ABSAGEN ERZEUGT, und dünn, wo er RECHNET.* Was davon offen
        bleibt: **Wertetafeln für die Bereichsarithmetik** — Beispieldateien treffen Klassen,
        keine Grenzen. *Woran es hängt: an Werten, nicht an Regeln — dieselbe Lücke wie beim
        Rundlauf oben.*

- [ ] **The parser is laxer than the EBNF at THREE places** *(was: six; corrected and
      checked 2026-08-16 — one `.gab` probe run per place)*:
      * Vocabulary words as names after `::`, in `reaches … via` and in `chain(a,b)` — three
        places that the file's own header does **not** exempt.
      **Closed are:** `pub` at 13 item kinds (`P041`, bis 2026-08-30 `P034`), `pub const` in the `table` body (was
      too strict), `type T = { };` as an empty sum type (`P035`, poison 61), and
      the comma rule — `entrydecl`, `slotdecl` and `reg … fields` carried **three different
      rules for the same thing**; now one: separating comma obligatory, trailing comma
      optional.
      **Und die Messschicht sagt, warum die drei stehenbleiben:** `./instrumente/pruefe-syntax.sh` hält
      154 EBNF-Regeln und 219 Terminale gegen die Wortschatztabelle — *er misst die Grammatik
      gegen sich selbst, nie den Parser gegen die Grammatik.* Ein Wächter für die Differenz
      bräuchte je Stelle eine Giftdatei, die der Parser **annehmen** und die EBNF **verbieten**
      muss — **drei Dateien, und der Prüfer müsste dafür rot werden, wo er heute grün ist.**
      *Das ist Bauarbeit am Parser, nicht am Wächter.* Bleibt offen.

### From P2 — what the parser found and what is now to be decided

- [ ] **THE DECISION that P2 forces: the closed vocabulary collides with
      ordinary naming** — nine words at eleven places, `slots` `ops` `next` `slot`
      `from` `boot` `stack` `check` `u64`. **The hardest case is `slots`, because the language
      generates the name itself** (`slots of c`, `c.slots[s]`) and at the same time forbids it as a place.
      Two ways out, both with a price: contextual words (then the table does not hold what it
      claims) or renaming (then every user carries the list in their head).
      **The compiler today admits words as names only after `.`/`->` and before `:`.**
      *Kein Messposten: die Zahlen (neun Wörter, elf Stellen) stehen, und `pruefe-wortschatz.py`
      hält 219 Terminale gegen die Tabelle. **Was fehlt, ist ein Urteil**, und der Preis steht
      in beiden Richtungen daneben.* Bleibt offen.

- [ ] **Per template at least one mutation that falls ONLY if the once-obligation is really
      checked.** Today: **0 of 21** — die meisten Schablonen sind entworfen, und was kein Code
      ist, fängt keine Mutation. **Die Kopplung der zwei Register ist die Bedingung dafür, dass
      das Schablonenregister mehr ist als eine Liste.**
      *Berichtigt 2026-08-20: hier stand „0 of 19", das Register führt 21.* **Woran es hängt:**
      eine solche Mutation muss die **erzeugte** Einmal-Pflicht beschädigen, und die entsteht
      erst in der Annotationsemission — derselbe fehlende Kanal wie zwei Punkte tiefer.

- [ ] **The annotation emission needs template entries of its own and mutations of its own.**
      Der Mutationskatalog misst heute den Prüfer (240 Anker); über den **Wunschform-Kanal**
      sagt er nichts — und genau dort wird ein kohärent geschwächter Erzeuger **von keinem
      Beweis** gefangen.
      *Berichtigt 2026-08-20: hier stand „65 von 65", und diese Zahl gibt es nicht mehr.*

- [ ] **Every new generated form needs its template entry BEFORE it becomes grammar.**
      Das Schablonenregister führt **21 Einträge**, **11 davon unbewiesen** (`gabbro
      schablonen`, 2026-08-20; die Ratsche erlaubt heute 28). Die Liste ist die Ratsche über
      der Fläche, in die der dritte Ausweg seine Beweislast verschiebt — **wächst sie, wächst
      die Vertrauensbasis, auch wenn die Kennzahl glänzt.**
      *Berichtigt 2026-08-20: hier stand „20, of which 15 unproved". Die Zahl steht seit heute
      im Register und wird bei jedem Lauf neu abgeleitet.*

### Checker and generator

- [ ] **Ein Ruf ins Leere in einem PRÄDIKAT ist still — gemessen 2026-08-28 bei «B13».**
      Dieselbe erfundene Funktion an drei Stellen, eine Probe durch den unveränderten Prüfer:
      | Stelle | gemessen |
      |---|---|
      | `table … invariant : forall o … : … == gibt_es_nicht(o)` | **0 Fehler, 0 Hinweise** |
      | `spec fn … = … == gibt_es_nicht(i);` | **0 Fehler, 0 Hinweise** |
      | `requires gibt_es_nicht(i) == 0` an einer `impl fn` | `E009` — und der kommt aus dem AUFRUFGRAPHEN, nicht aus einer Namensregel |
      **Nur wo die Wirkungshülle hinsieht, fällt etwas.** Ein Prädikat, das eine Funktion
      nennt, die es nicht gibt, behauptet nichts und sieht aus wie eine Behauptung — *dieselbe
      Klasse wie `M133`, `N033`, `S007`, `N020` und `D013` (2026-08-28), eine Fläche weiter.*
      Woran es hängt: die Namensauflösung über `pred` gibt es nicht; `maintains` hat sie seit
      `M131` für den KOPF, nicht für den Rumpf. *Probe und Zahlen:
      [`messung/AGGREGATION.md`](messung/AGGREGATION.md) §1.*

- [ ] **Mutation probe on the ANNOTATION EMISSION**, not only on the code emission. The coherently
      weakened case (code **and** contract) is caught by **no** proof — only by the
      differential test against the handwriting. That is its named task.
      *Derselbe Posten wie zwei Punkte höher, von der anderen Seite. **Woran es hängt: die
      Annotationsemission existiert nicht** — es gibt nichts zu beschädigen. Kein Messposten,
      und er bleibt so lange stehen, bis der Kanal steht.*

- [ ] **Emit the assumption set into the artefact** ("proved under A1…An"), as a **set of names**
      with a class, not as a number. A ratchet over a cardinal number does not bite against exchange.
      **Halb gebaut, gemessen 2026-08-20:** `gabbro annahmen` druckt 33 Annahmen als **Namen**
      mit Klasse (`assume`/`axiom`), Falsifizierbarkeit und Sonde — genau die verlangte Form.
      **Was fehlt, ist der zweite Halbsatz: „into the artefact".** Die Namen stehen im Bericht
      des Prüfers, nicht im erzeugten C. *Woran es hängt: an einer Zeile im Erzeuger* — der
      Kanal dorthin steht seit dem 2026-08-17, denn `pruefe-emission.sh` findet die Annahmen im
      erzeugten C wieder. **Der kleinste offene Posten dieses Abschnitts.**

- [ ] **~~Every falsifier needs its own speech test:~~ *can it fail at all?* — GEBAUT
      2026-08-20.** Das ist wörtlich die zweite Forderung von `./instrumente/pruefe-waechter.py`, und sie
      wird an **29 von 29** Instrumenten geprüft: eine saubere und eine kaputte Quelle, beide
      erfunden, und der Wächter muss die eine melden und die andere durchlassen.
      **Was der Punkt meinte und was gemessen wird, ist nicht dasselbe, und der Unterschied
      gehört hierher:** geprüft wird, ob der Wächter *überhaupt* rot werden kann — nicht, ob er
      an **seinem** Gegenstand rot wird. `pruefe-zahlen.py` schließt diese Lücke für seine 39
      Einträge (jede Zahl wird verstellt, jeder Eintrag muss fallen); für die übrigen Wächter
      ist die Sprechprobe eine **Selbstauskunft im Quelltext**, und dass sie dasteht, heißt
      nicht, dass sie an der richtigen Stelle steht. *Das Werkzeug sagt genau das über sich
      selbst.* **Der Rest ist damit benannt, nicht offen.**

- [ ] **The scope in [`dokumente/SPRACHE.md`](dokumente/SPRACHE.md) is new — run a counter-probe:** look for a construct
      whose line is too strong. The table has the same prehistory as the two
      overreaches in `dokumente/HISTORIE.md`.
      **Und die Gegenprobe hat seit dem 2026-08-20 zwei Werkzeuge, die sie zur Hälfte fahren:**
      `./instrumente/pruefe-reichweite.py` (0 ungelesen, zwei Bauteile von genau einem Pass gelesen) und
      `./instrumente/pruefe-klauseln.py` (22 Klauseln gebucht, sechs ungelesen). *Beide finden eine Zeile,
      die zu stark ist, nur dann, wenn niemand sie liest — nicht, wenn ein Pass sie liest und
      zu wenig tut.* **Woran der Rest hängt: an W13** (Berührung ist keine Prüfung), und die
      Antwort darauf ist dieselbe wie beim groben Maß oben — eine Probe je ZUSAGE.
      Bleibt offen.

---

# STUFE 1 — DER MASSSTAB  ⟨C⟩

**Der Befund:** `H = 12` wird gelesen als *„so viel Klempnerei ist in Gabbro noch übrig"*.
Sieben Zwölftel davon sind die **Vollständigkeit des Korpus**: 41 Stellen nennen 20 Namen, die
niemand deklariert, neun `let … else` rufen Rümpfe, die es nicht gibt, sechs Bitlagen sind
unbenannt. **Die Absenkungsspalte fällt um keinen Punkt**, ohne in eine eingefrorene Datei zu
schreiben.

**Die Entscheidung ist gefallen und AUSGEFÜHRT (2026-08-20):** Weg **(b)** —
[`messung/fragmente/`](messung/fragmente/), dieselben zehn um ihre fehlenden Zeilen ergänzt,
mit einer Kopfzeile je Datei, die sagt was ergänzt wurde. `FRAGMENTE.md` bleibt Bericht.

```
$ ./instrumente/zaehle-fragmente.py
7 von 10 prüfen sauber        (über den Ausschnitten: 5)
4 von 10 senken ab            (über den Ausschnitten: 3)
```

**Und der Ertrag sind drei Befunde, die der eingefrorene Korpus nicht zeigen konnte:**

| | |
|---|---|
| **`A::B` parst und wird nie aufgelöst** | der Namenspass liest die **erste Silbe** und schlägt sie als Wert nach. `module`, `reason`, Variantentyp — alle drei gemessen. **Null Korpusstellen benutzen einen qualifizierten Namen als Wert** |
| **Ein `reason`-Wert hat keinen Erzeuger** | `primary` kennt keine Produktion; **jede `or R`-Signatur im Korpus steht an einem `extern fn`**. *Dieselbe Gestalt wie «B9» bei `fnptr` — und damit gehört sie in Stufe 7* |
| **Ein `static` eines Verbunds senkt nicht ab** | die Zeile, die ich selbst ergänzt habe. *Steht im Kopf von F6, statt weggelassen zu werden* |

*Was bleibt: die vier Dateien, die noch nicht absenken, hängen jetzt an GABBRO-Absagen mit
Adresse — `dma`-Barriere, «B12» `elems of`, `walk … levels` als Konstantenname, `mappings of`.
Die stehen in Stufe 3 und 4.*

### K100 — der Weg auf 100 % Klempnereiabdeckung ([`dokumente/PLAN.md`](dokumente/PLAN.md)) *(Teil)*

- [ ] **K11.2.2 ist am Korpus nicht messbar, und das ist ein Befund** *(gemessen 2026-08-17)*.
      Vier Kontextwurzeln (3 × `entry`, 1 × `boot`), **null davon mit einem Rumpf, den Gabbro
      sieht** -- jedes `dispatch`-Ziel ist ein `extern fn`. Die Huelle ueber einer
      Kontextwurzel ist leer, also kann die Regel *„jeder Platz, den zwei Kontexte beruehren,
      ist gesperrt oder atomar"* nie feuern. **Dieselbe Lage wie `E010`.** Sie haengt damit am
      ZWEITEN Korpus, der ohnehin als Bedingung ueber K11 steht.

- [ ] **Der ZWEITE Korpus gehoert in denselben Plan wie das letzte Konstrukt.** Die zehn
      Fragmente sind nach ihrer SCHWIERIGKEIT gewaehlt; `H = 0` ueber ihnen ist keine Aussage
      ueber Gabbro. **Ohne einen Korpus, den beim Bauen niemand angesehen hat, ist K100 Falle 80
      in Reinform.**

### Aus «H2» *(ausgefuehrt 2026-08-19, `H = 17 → 15`)* — der Rest, den der Lauf hinterliess *(Teil)*

- [ ] **«K2» ist abgeschlossen -- und fuenf Fragmente sind keine Aussage ueber 64 000
      Dateien** *(2026-08-18)*. Vier von fuenf tragen ohne Rest; die Nachbildungen sind keine
      Uebersetzungen, denn die Strukturen sind erfunden, wo sie nicht mitgeschnitten waren.
      **Gemessen ist die FORM, nicht der Rumpf.** Wer die Zahl als Deckung liest, liest sie
      falsch -- *dieselbe Warnung, die schon bei den elf Uebersetzungseinheiten steht.*

### Die Fragmente: von sieben blockierenden Konstrukten sind fünf gebaut

**Gemessen 2026-08-17, neu gemessen 2026-08-20** über allen ```gabbro-Blöcken von
[`dokumente/FRAGMENTE.md`](dokumente/FRAGMENTE.md):

```
16 Blöcke · 8 prüfen sauber · 6 emittieren
```

*Die Tabelle, die hier stand, führte sieben Konstrukte als blockierend — `traverse`, `format`,
`device`, `retry`, `forever`, `walk`, `atomic`/`check`.* **Fünf davon senken seit dem
2026-08-19/20 ab**, `traverse` in drei seiner Domänen, `check` wird von M1 und der Paarung
gelesen. Was zwei saubere Fragmente noch aufhält, sind **zwei benannte Weigerungen**:

| Fragment | Weigerung | und warum sie richtig ist |
|---|---|---|
| F2 · F9 | die Bitlücke in einem `format` | *ein Format sagt, welche Bits EXISTIEREN* — sie heisst `reserved` oder gar nicht. **Der Erzeuger zählt nicht mit.** |
| F9 | `device … at dma` — welche Barriere | die **Axiomschicht**, seit jeher; M3 baut sie ausdrücklich nicht |



- [ ] **~~Ob ein Ausschnitt vom Kacheln ausgenommen gehört~~ — entschieden 2026-08-20, und
      zwar dagegen.** Ein ausgeschnittener `format`-Block nennt die Bits, um die es dem
      Ausschnitt geht; ein Programm muss auch die nennen, um die es NICHT geht. **Genau darin
      unterscheidet sich ein Bericht von einem Programm** — also wird nicht die Regel
      gelockert, sondern der Korpus vervollständigt: sieben `reserved`-Felder in
      [`messung/fragmente/`](messung/fragmente/), F2 und F9. *Eine Ausnahme für Ausschnitte
      hätte die Kachelregel für alle geschwächt, um zwei Dateien zu retten.*
      **Was offen bleibt, ist die andere Hälfte der Frage:** was ein Ausschnitt überhaupt
      ZUSAGT. Solange das nirgends steht, ist jede Messung über `FRAGMENTE.md` eine Messung
      über einen Text ohne erklärten Anspruch.

- [ ] **`cc -Wextra` finds a dead parameter and NO Gabbro pass does.** `FRAGMENTE.md` F8 takes
      `toeten(l, t, k)` and never reads `k` — the function resolves `t` instead. The C emitter
      silences it with `(void)k;` because *the user did not write the generated line*, and the
      finding belongs on the Gabbro level. **Today the checker has no diagnostic for an unread
      parameter**, and a C compiler found something ten passes did not. *That is a small pass
      and a real one.*

- [ ] **`publishes` at a DEVICE REGISTER — the one unbuilt item of the escalation of 2026-08-14.**
      Six of the seven are built, this one is not: `publishes` sits at `atomicdecl`, and the
      store the class *Publication* exists for is not an atomic at all — the virtio `avail`
      index is a **volatile store into a DMA region, to a device** («B19»,
      [`PFLICHTEN.md`](dokumente/PFLICHTEN.md) F4:796). **The class is carried for atomics and
      not for device registers**, and that is the second half of the same gap.

### The four items to the goal — plan with gates in [`dokumente/PLAN.md`](dokumente/PLAN.md) §A *(Teil)*

- [ ] **A5 — Abnahme: die Fragmente frisch durch den Übersetzer.** ~~Fehlt ganz.~~
      **Seit dem 2026-08-20 gibt es den Lauf**: `./instrumente/zaehle-fragmente.py` fährt alle zehn
      vervollständigten Dateien durch `pruefe` und `emit`, mit Frist und Sprechprobe, und die
      zwei Zahlen stehen im Zahlenregister. *Damit ist die Zählung zum ersten Mal über
      GABBRO-Quelltext statt über Rust.*
      **Was fehlt, ist die dritte Stufe: AUSFÜHREN.** `pruefe-emission.sh` misst 19 Einheiten
      durchgestochen — erzeugt, übersetzt, ausgeführt, gegen eine Handschrift verglichen. Die
      vier absenkenden Fragmente sind dort **nicht** eingetragen. *Ohne sie sagt „4 von 10
      senken ab" nichts darüber, ob das erzeugte C rechnet, was das Fragment sagt* — und genau
      das ist der Wortlaut der Pflicht.

---

# STUFE 2 — NUTZBARKEIT BEKOMMT IHR ERSTES INSTRUMENT  ⟨E⟩

**Ziel 3 hat als einziges keine Zahl gehabt.** Ohne sie ist „möglichst gut nutzbar" eine
Meinung — und „keine Klempnerei beim Endnutzer" ist eine Nutzbarkeitsaussage.

**AUSGEFÜHRT am 2026-08-20.** `gabbro zeremonie` zählt jede Klausel und jede Annotation, und
die Kalibrierung steht **im Werkzeug** (`--tafel`), nicht in einer Fußnote:

| | | |
|---|---|---|
| **Achse 1** | *gemessen* | steht diese Tatsache ein **zweites Mal** in dieser Einheit? — ableitbar / redundant / tragend |
| **Achse 2** | *erklärt* | darf die Zahl sinken? — je Regel ein Ja/Nein **mit Grund**, und ein Wächter verlangt den Grund |

```
$ ./instrumente/zaehle-zeremonie.py                    → messung/ZEREMONIE.md
Lehrkorpus     5.8 % dürfen sinken   (882 Stellen auf 5591 Zeilen, Dichte 15,8/100 Z.)
echter Code   12.8 % dürfen sinken   (109 Stellen auf  519 Zeilen, Dichte 21,0/100 Z.)
```

> **Der eigentliche Befund ist der Vergleich.** Im echten Code ist der ableitbare Anteil mehr
> als doppelt so hoch, und er besteht **ausschließlich aus `A4`** — der Wirkungszeile, die ein
> Gerufener ohnehin erklärt. *Ein Beispiel ruft wenig; ein Treiber ruft ständig.* Die Beispiele
> unterschätzen, was ein Nutzer schreibt.

**Erst die zwei Achsen erlauben den Fall, auf den es ankommt: `ableitbar` UND „darf nicht
sinken".** Mit einer Achse hätte man zwischen „nicht messen" und „zum Rückstand erklären"
wählen müssen, und beides wäre falsch gewesen (**W20**).

**Und die Sprechprobe wandert von den Mustern auf die Regeln.** Der Korpus meldete **null**
redundante Stellen — ein sauberer Korpus und ein blindes Werkzeug sehen von außen gleich aus
(W17). Also: *eine Regel der Tafel ohne Treffer ist selbst ein Befund*; 20 Regeln, 14 vom
Korpus, 6 von einer absichtlich schlecht geschriebenen Probe, **keine stumm**.

## Die vier Punkte dieser Stufe — zwei waren beim Nachsehen schon zu

| | |
|---|---|
| **Der Erzeuger liest den `let`-Typ ab** | war **gebaut**; `wert_ctyp` fragt die Signatur des Gerufenen seit dem 2026-08-20. *Und das Weglassen der Annotation in `beispiele/21` deckte auf, dass sie **zwei Leser** hatte und nur einer sie las: `verbundlokale` kannte `c` nicht als Verbund, das erzeugte C wurde `c->len`, `gabbro emit` gab 0 zurück und `cc` lehnte ab.* Geschlossen |
| **`S006` schweigt bei `on_exceeded <reason>`** | war **überholt**; `S007` — der dritte Zustand, gebaut am 2026-08-19 — meldet es. Nachgerechnet an einer Handprobe |
| **Fehlerweitergabe: `?` oder nicht** | **entschieden: kein `?`.** Gemessen statt argumentiert — 21 `let … else`-Stellen, **15 verschiedene** Rümpfe, 26 von 5569 Korpuszeilen (0,5 %). Die sechs, die wie Kopien aussehen, unterscheiden sich genau in der Fehlerkennung, *und die ist das Einzige, was `?` löschen würde* |
| **Folgefehler nach einer Leserabsage** | **entschieden: nicht anhalten, aber sagen.** `gabbro pruefe` druckt seit heute, wie viele spätere Meldungen Folgen sein können. *Anhalten hieße, ein `P001` im dritten Item verdeckt einen echten `M101` im ersten — Rauschen gegen Schweigen getauscht* |

*Und `on_exceeded` behält `-> never`:* der Wachhund ist die Stelle, an der die Schranke ihre
Wirklichkeit berührt; kehrte er zurück, wäre sie eine Zahl ohne Folge. Der Fehlerkanal
`-> T or R` ist eine **Rückgabe**konvention, eine überschrittene Schranke keine Rückgabe.
**Der Grund gehört an den Austritt** — und der ist der offene Punkt unten in Stufe 4.

### Was diese Stufe offen lässt

#### Der Ordner hat vierzig Instrumente, um SICH zu prüfen, und null, um jemandem beim Schreiben zu helfen *(gezählt 2026-08-25)*

*Jeder Posten hier ist ein Werkzeug, das aus einer Tabelle ERZEUGT wird, die es schon gibt —
keine zweite Quelle, kein Register, das auseinanderlaufen kann. Der erste ist gebaut, die drei
darunter sind gebucht, mit Abnahmebefehl.*

- [ ] ~~**`gabbro pruefe` erschlägt seinen eigenen Befund**~~ — **GEBAUT am 2026-08-25.**
      Gemessen an [`beispiele/16-by-ops-am-feld.gab`](beispiele/16-by-ops-am-feld.gab), einer
      **sauberen Datei von 39 Zeilen**: der Lauf gab **1 142 Wörter, davon 1 122 (98,2 %) das
      Register „Not checked in this run"** — und **zwanzig** das Ergebnis.
      **Und der Text kann sich zwischen zwei Läufen gar nicht unterscheiden:** `ungeprueft()`
      liest `passliste()`, eine statische Liste im Binärprogramm; er hängt weder an der
      geprüften Datei noch am Ergebnis. *Eine Offenlegung, die den Befund um den Faktor 56
      übertönt und beim zwanzigsten Mal denselben Wortlaut hat, ist garantiert ungelesen.*
      **Das Prinzip bleibt, die Vorgabe dreht sich um:** die Zahl steht weiter da, **jeder
      Pass wird beim NAMEN genannt**, jeder Zustand gezählt, und ein Fingerabdruck macht eine
      Änderung des Wortlauts sichtbar, ohne ihn abzudrucken. Der volle Text steht hinter
      `gabbro pruefe --paesse` und hinter `gabbro paesse`, wo er ohnehin schon stand.
      **1 142 → 91 Wörter.** Abnahme: `cargo test -p gabbro-cli` — vier Proben, und es sind
      **die ersten dieses Ordners, die die Kommandozeile laufen.**

- [ ] **Syntaxhervorhebung, ERZEUGT aus `crates/gabbro-syntax/src/kw.rs`.** Der Wortschatz ist
      **schon** eine maschinenlesbare geschlossene Tabelle — **220 Einträge**, jeder mit seiner
      Klasse (`ctx`/`res`), und `pruefe-wortschatz.py` hält sie gegen die EBNF. *Null Dateien
      im Ordner helfen beim Lesen einer `.gab`:* kein tree-sitter, kein TextMate, kein
      `.vim`. **Erzeugen, nicht pflegen** — eine gepflegte zweite Wortliste ist die Form, gegen
      die `pruefe-wortschatz.py` überhaupt gebaut wurde.
      Abnahme: `gabbro hervorhebung > x.tmLanguage.json && git diff --exit-code` — **neu
      erzeugen, null Diff erwarten**, als eigener Wächter in der Kette.

- [ ] **`gabbro neu --geraet` / `--tabelle` / `--modul` — Gerüst aus derselben Tabelle.** Eine
      neue `device`-Datei besteht heute daraus, dass jemand eine bestehende kopiert; welche
      Klauseln Pflicht sind, sagt der Prüfer erst hinterher und je Klausel einzeln.
      Abnahme: `gabbro neu --geraet D | gabbro pruefe /dev/stdin` gibt **0 Fehler** — *ein
      Gerüst, das nicht durchgeht, ist keins.*

- [ ] **Formatierer.** Der Korpus hat schon eine kanonische Ausrichtung (die `effects`/`costs`
      -Spalten stehen in allen 50 Dateien untereinander), und sie wird **von Hand** gehalten.
      Abnahme schreibt sich selbst: `gabbro formatiere beispiele/*.gab && git diff
      --exit-code` — **formatiere den Korpus, erwarte null Diff.** *Der Korpus ist damit die
      Probe des Formatierers und nicht umgekehrt.*

- [ ] **Das Zeremonieregister misst eine ABGEGRENZTE Grundgesamtheit, und die Grenze ist eine
      Entscheidung** *(2026-08-20)*. Draußen bleiben `module`/`use`/`pub`, `section`/`arch`/
      `when`, die Fälle eines `reason`, `entrust`/`boot`/`entry`, die `by`-Beweishinweise und
      die Typdeklarationen selbst — je mit Grund in `gabbro zeremonie --tafel`. **Was ein
      Werkzeug nicht misst, muss es sagen**, und gesagt ist es; ob die Grenze richtig liegt,
      entscheidet erst ein zweiter Korpus. *Die Zahl ist damit eine UNTERE Schranke der
      Zeremonie, nie eine obere* (W10).

- [ ] **`redundant = 0` über beiden Korpora ist gemessen und trotzdem dünn** *(2026-08-20)*.
      Die vier R-Regeln feuern **nur an der Probe**, an keiner einzigen echten Stelle. Das ist
      der ehrlichste Zustand, den ein Zähler haben kann — *und er heisst, dass die Spalte über
      diesen 55 Dateien nichts unterscheidet.* **Ihr Wert entscheidet sich am zweiten Korpus**,
      dort wo Code steht, den beim Bauen niemand angesehen hat.

### Syntax — open decisions (details in [`dokumente/SYNTAX.md`](dokumente/SYNTAX.md)) *(Teil)*

- [ ] **Die Zusage eines fremden Rumpfs ist eine TATSACHE im Prüfer — und sie entscheidet**
      *(gesehen 2026-08-20 beim Zeremoniemaß, nachgemessen 2026-08-21)*. Der Posten stand hier
      als Buchungsfrage (*„die Verengung ist Glaube"*). **Er ist keine.** Handprobe, in beide
      Richtungen:

      ```gabbro
      extern fn hole() -> u32 ensures result <= 100 …   -- ein Rumpf, den Gabbro NIE sieht
      impl fn nimm() -> Klein { return hole(); }        -- Klein = u32 in 0 .. 100
      ```
      ```
      mit `ensures`   ->  4 Items, 0 Fehler
      ohne `ensures`  ->  M101: die Rueckgabe requires `u32 in 0 .. 100`, the value has `u32`
      ```

      `m1.rs`:1222 ruft `aus_ensures(&roh, &sig.ensures)` — **ohne `sig.rumpf_da` zu fragen**,
      obwohl genau dieses Feld in seinem eigenen Kopfkommentar sagt: *„Ohne ihn ist jede
      Verengung aus `ensures` eine ANNAHME über fremden Code und gehört ins Zeugnis."*
      **Gemessen: 89 fremde Rümpfe im Korpus, 10 davon mit `ensures`, und aus jedem verengt M1.**

      > **Das ist «B33» ein zweites Mal:** ein Satz, der beschreibt, was gelten *sollte*, und
      > ein Pass, der das Gegenteil tut. *Eine Zusage, die kein Pass einlöst, ist die stille
      > Richtung* — hier löst ein Pass sie ein, den niemand dazu ermächtigt hat.

      **Die Entscheidung ist zweiteilig, und die zweite Hälfte ist die dringende:**
      (a) die Fläche als Annahme buchen — `gabbro zeugnis` führt sie schon;
      (b) **prüfen, wo die Fakten in Verengungen einfließen, und diese Stellen als EIGENEN
      Posten ins Zeugnis nehmen**, nicht in die allgemeine Annahmenfläche. *Eine Verengung mit
      Wirkung im Erzeugnis ist etwas anderes als eine Zeile, die niemanden bindet.*

      **AUSGEFÜHRT am 2026-08-21.** (a) war keine Lücke — die Fläche steht längst in
      `zeugnis` E und in `pflichten` als Klasse `F`, an einer Handprobe nachgeprüft.
      (b) steht: **Abschnitt `F` im Zeugnis**, eine eigene Zahl in der Befundzeile, und
      [`./instrumente/zaehle-fremdverengung.py`](instrumente/zaehle-fremdverengung.py) über
      den ganzen Korpus. Bericht: [`messung/FREMDVERENGUNG.md`](messung/FREMDVERENGUNG.md).

      **Und die Verengung ist NICHT abgeschaltet worden** — sie ist sichtbar. Ein Vertrag an
      einem fremden Rumpf soll wirken; das ist sein Zweck. Was fehlte, war die Buchung.

      ```
      F  FOREIGN CONTRACTS THAT NARROWED -- a foreign `ensures` became a FACT here
           127:   abarbeiten -> naechste_menge     range     result >= 1
                  u32 in 0 .. 4096  ->  u32 in 1 .. 4096
      ```

      > **Der Satz „aus jedem verengt M1" war falsch, und der Irrtum ist der Ertrag: 1 von
      > 10.** Sechs Klauseln nennen `result` gar nicht (Weltzustand), zwei nennen es und
      > bewegen nichts (`result >= 1` auf `u32 in 1 .. 4096`), eine hängt an einer Funktion,
      > die niemand ruft. *Drei wortgleiche Zeilen an derselben Bauform, und nur eine bindet
      > jemanden.* Genau diese Unterscheidung — **wirksam** gegen **vorhanden** — trägt eine
      > einzige Zeile im neuen Modul, und ohne sie hätte der Posten neun Zeilen als
      > Vertrauensfläche gebucht, die keine sind.

      **Ein Leser, nicht zwei:** `crates/gabbro-check/src/fremdverengung.rs` beantwortet die
      Frage *„verengt diese Klausel, und wie?"* einmal; `m1` und das Zeugnis rufen dieselbe
      Funktion. *Das ist die Lehre vom 2026-08-20, an der `verbundwert` zu `c->len` wurde.*

      **Was der Posten NICHT geschlossen hat:** die relationale Hälfte
      (`ensures result <= s.len` an einem fremden Rumpf) hat im Korpus **null** Fundstellen
      und ist nur durch Test und Mutation bewacht — **Regel A ist an dieser Hälfte offen.**
      Und `M115` ist mit Begründung *nicht* als eigener Posten gebucht: eine falsche
      Vorbedingung kann ein richtiges Programm abweisen, nie ein falsches durchlassen. *Die
      Begründung steht im Zeugnis und im Bericht — wer sie umstoßen will, findet sie, statt
      sie zu suchen.*

### Aus «H2» *(ausgefuehrt 2026-08-19, `H = 17 → 15`)* — der Rest, den der Lauf hinterliess *(Teil)*

- [ ] **Gabbro unterdrueckt Folgefehler nicht -- und seit dem 2026-08-20 SAGT es das**
      *(gefunden 2026-08-19 an `M112`)*. Die Entscheidung ist gefallen (nicht anhalten,
      sondern die Zahl nennen). **Was offen bleibt, ist die Genauigkeit der Zahl:** gezaehlt
      wird ueber die QUELLPOSITION -- jede Meldung hinter der ersten Leserabsage gilt als
      moegliche Folge. *Das sieht mehr Folgen als da sind, nie weniger* (W10), und eine
      schaerfere Zaehlung braeuchte den Bezug von Meldung auf das Item, das nicht las.

---

# STUFE 3 — DIE OFFENEN LESARTEN ENTSCHEIDEN  ⟨A⟩

**Der billigste Posten des Plans — und er hat trotzdem etwas gekostet.** Drei Konstrukte
standen in der Grammatik und wurden in **zwei Lesarten** benutzt. **AUSGEFÜHRT am 2026-08-20**,
ohne ein neues Terminal und ohne eine neue Schablone:

| | entschieden | und die Begründung, die allein trägt |
|---|---|---|
| **«B12» `elems of`** | bindet einen **INDEX** | *Aus dem Index bekommt man das Element, aus dem Element den Index nicht.* `forall i in elems of dst.msg : dst.msg[i] == old(src.msg[i])` — die tragende Zusage des IPC-Fastpath — ist unter der Elementlesart **nicht schreibbar** |
| **«B10» `by consuming`** | leert die **ganze** Schlange, *und das ist die Bedeutung* | Der Fastpath will den ersten lebenden Empfänger und hört dann auf. **Das ist eine andere Schleifenform, keine andere Lesart dieser.** `traverse` liefert keinen Wert und trägt keine Marke, kann also nicht verlassen werden |
| **`mappings of`** | die **Blattmenge** | Die Domäne wurde gebaut, damit **W^X über die ganze Tabelle** formulierbar wird. *W^X ist eine Aussage über die Menge; über einen Pfad ist sie sinnlos* |

**Und eine Regel statt acht Einzelfälle:** *eine Domäne bindet die **Adresse** eines Eintrags
und heißt nach dem, **worüber** sie läuft — nicht nach dem, was die Variable hält.* `slots of`
bindet ebenfalls einen Index; das ist seit heute eine Regel und kein Zufall. Die eine Ausnahme
ist `mappings of`, dessen Einträge keine einzelne Adresse haben — und dessen Deklaration das
sagt.

## Ein vierter Fall fiel beim Entscheiden mit ab

`by decreasing` wurde zusammen mit `by consuming` abgelehnt, mit *„was es für den Lauf heißt,
ist nicht entschieden"*. **Für `by decreasing` war das eine offene Frage über etwas, das gar
keine Laufwirkung hat:** das Maß ist ein Terminierungszeuge. Die drei stehen jetzt getrennt —
`by unvisited` und `by decreasing` **laufen gleich**, und nur `by consuming` trägt die Entnahme,
die erzeugter Code ist.

## Was die Entscheidungen gekostet haben, und warum das der Ertrag ist

```
messung/fragmente/  7 von 10 prüfen sauber  →  6 von 10
```

**F9 sagt `costs <= 4096 ops` zu und der Rumpf kostet 137 438 953 472.** Die Zeile begründet
sich im Ausschnitt mit *„`levels` mal `node`-Länge"* — also mit genau der kleineren Lesart, die
auch der Kostenpass trug.

> **Der Fehler stand seit dem Schnitt in der Datei und war unsichtbar, solange der Pass
> dieselbe falsche Lesart trug wie der Mensch, der die Zeile schrieb.** Zwei Register über
> derselben Sache, und beide falsch (W7). *Eine entschiedene Lesart macht aus einer
> unsichtbaren Zusage eine gemessene Absage.*

Und dieselbe Klasse ein zweites Mal, eine Ebene höher: der Mutationskatalog meldete danach
**zwei Mutationen, die nichts mehr messen** — ein Anker war verschwunden, einer doppelt. *Ein
Katalog, dessen Anker unter ihm wegwandern, misst über einer schrumpfenden Bezugsgröße und
liest sich wie Deckung.* Beide sind umgezogen, 236 von 236 greifen.

### Was diese Stufe offen lässt

- [ ] **Eine Laufzeit-Traversierung über `mappings of` trägt keine Kostenzusage — das ist die
      FOLGE der Entscheidung und wird ausgehalten** *(2026-08-20)*. Die Form, die eine tragen
      kann, ist ein Abstieg entlang **eines** Pfades — genau die Zahl, die der Kostenpass bis
      heute geführt hat (`levels × Knotenlänge`). **Sie hat keinen Namen.** *Ihn zu vergeben
      kostet ein Terminal und gehört damit nicht in diese Stufe*; was er beschreibt, steht
      dagegen fest, und der Bedarf ist an F9 gemessen statt entworfen.

- [ ] **Die Absenkung von `mappings of` fehlt, und sie ist jetzt ein BAUPOSTEN statt einer
      Frage** *(2026-08-20)*. Eine Traversierung über die Blattmenge braucht einen **erzeugten
      rekursiven Abstieg** entlang `down` und `leaf`. Der Erzeuger sagt es beim Namen ab
      (`C001`), und die Absage nennt seit heute den Bauposten statt der offenen Lesart.

- [ ] **`by consuming` senkt nicht ab, weil die ENTNAHME erzeugter Code ist** *(2026-08-20)*.
      Die Bedeutung steht fest; was fehlt, ist die `ops`-Operation, die den Eintrag entfernt.
      *Zusammen mit dem Leser-Befund in Stufe 5 (`by consuming` liest kein Pass) ist das
      dieselbe Sache von zwei Seiten* — und die Hälfte, die in der **Bedeutung** fehlte, ist
      jetzt gefüllt.

- [ ] **Drei Domänen binden weiter eine Variable ohne TYP** *(gesehen 2026-08-20 beim
      Entscheiden von «B12»)*. M1 setzt die Laufvariable einer `traverse` auf `Unbekannt` —
      für `slots of`, `descendants of` und `ancestors of` genauso wie für `elems of`. **Die
      Schranke steht in der Deklaration und wird für die Kosten gelesen, für den Wert nicht:**
      `p[i]` innerhalb der Schleife ist damit nicht nachweislich im Bereich. *Das ist kein
      Loch der Entscheidung, sondern eines, das sie sichtbar gemacht hat* — und es ist an
      allen vier Domänen dasselbe, also eine Änderung und nicht vier.

---

# STUFE 4 — PROGRAMME SCHREIBEN, NICHT KONSTRUKTE  ⟨A⟩

**Das Herz des Plans.** Der Korpus ist von der Sprache nach außen geschrieben — eine Datei je
Konstrukt — und **die Fehler sitzen an den Kombinationen**: 79 blinde Zellen von 285. Jedes echte
Programm hat sofort geliefert: der virtio-net-Treiber fünf Befunde, «K2» drei, die ein eigener
Korpus nicht gegeben hätte, das Registerbeispiel vom 2026-08-20 vier.

**Das nächste Programm ist der Netzwerkstack.** Der IP-Kopf senkt ab, Verbindungstabelle,
Paketpool, Prüfsumme, Neuübertragung, Zeitgeber — alles vorhanden. Was fehlt, ist das Programm.

> **Regel A: kein neues Konstrukt ohne ein Programm, das es gebraucht hat.** Das ist Zahn 1 der
> Ratsche, auf die Sprache angewandt.
>
> **Regel B, und ohne sie hält Regel A nicht: die VORLAGE kommt von außen.** Ein Stack, den
> derselbe Autor in derselben Sprache schreibt, hat dieselbe Passungsschwäche wie ein
> selbstgeschriebener Korpus — er misst wieder, wie gut Gabbro zu Gabbro passt. Der Schutz ist
> billig und zweimal angewandt (Caprock, «K2»): **RFC-Verhalten als Vorlage, ein bestehender
> Stack als Referenz, echte Pakete gegen die Prüfsumme.** *Ein Stack, der gegen einen echten
> Gegenüber spricht, ist ein zweiter Korpus im Kleinen; einer, der nur die eigenen Testpakete
> versteht, misst Passung.*

**AUSGEFÜHRT am 2026-08-20** — [`messung/netz/`](messung/netz/), Ethernet → ARP → IPv4 → UDP,
238 Zeilen, gegen RFC 791/826/768/1071 und gegen **veröffentlichte Testvektoren**:

```
$ ./instrumente/zaehle-netz.py
ok   ohne   Gabbro b861  Gegenrechnung b861   IPv4-Kopf, Feld genullt (RFC 791)
ok   mit    Gabbro 0000  Gegenrechnung 0000   derselbe Kopf MIT der Summe — muss 0 sein
ok   summe  Gabbro ddf2  Gegenrechnung ddf2   RFC 1071, Abschnitt 3
```

*Die Gegenrechnung kommt aus einer **zweiten Implementierung**, absichtlich anders geschrieben
— ein Vergleich gegen die eigene Zahl ist kein Vergleich (W7).*

**Und der Ertrag ist genau das, was Regel A verspricht: vier Löcher, die 45 Beispiele nicht
zeigen konnten** — sie stehen unten als eigene Punkte. Zwei davon sind sofort geschlossen
worden, weil ein Programm sie gebraucht hat; eines ausdrücklich **nicht**, weil keines es
gebraucht hat.

Darunter steht die **Ernte** der bisherigen Programme und Werkzeugläufe: jeder Posten hier ist ein
Loch, das ein Programm oder ein Messwerkzeug gefunden hat, nicht ein Entwurf.

### Vom Netzwerkstack, 2026-08-20 *(siehe [`messung/netz/`](messung/netz/))*

- [ ] **„Lies dieselben Bytes als big-endian 16-Bit-Worte" ist nicht schreibbar**
      *(gemessen 2026-08-20)*. Ein `format` erklärt die Byteordnung **für seine Felder**; ein
      Feldtyp `[u16; 10]` darin wird **zweimal** abgesagt — der Feldtyp selbst, und der
      Zugriff darauf (*„ein Leser liefert einen WERT, und ein Wert hat keine Stelle in den
      Bytes"* — und das ist richtig). **Die Folge steht im Prüfstand: das Zusammensetzen der
      Worte aus den Bytes passiert in C, nicht in Gabbro.** *Die Prüfsumme rechnet Gabbro; die
      zweite Sicht auf dieselben Bytes kommt von außen* — und damit liegt genau der Schritt
      außerhalb der Sprache, den eine Sprache für Netzcode können müsste. Ohne ihn ist auch
      eine variable Kopflänge (`ihl > 5`) nicht behandelbar.
      **Und die Kante steht fest, BEVOR gebaut wird** *(2026-08-21)*: **die Bytesicht darf
      keine Aliasfrage öffnen.** Dieselben Bytes unter zwei Sichten sind genau das, was M3
      sonst ausschließt — und sind beide Sichten gleichzeitig *schreibbar*, ist die Ordnung
      der Schreibvorgänge eine Aussage, die kein Pass trägt (M3s offener Rest IST die
      Aliasanalyse). **Die tragfähige Form: eine Sicht schreibend, alle anderen lesend, und
      der Wechsel ist ein EREIGNIS** — das ist die Gestalt von `state`/`transition`, auf
      Sichten statt auf Zustände angewandt. *Sonst kauft der Posten seine Vollständigkeit mit
      einer stillen Alias-Ausnahme.*
      **Ausgeschrieben am 2026-08-21** als Vorbedingung eines künftigen Baus, dort wo ein
      Bauer sie finden muss: [`dokumente/SYNTAX.md`](dokumente/SYNTAX.md) §3 und
      [`messung/netz/README.md`](messung/netz/README.md). **Gegen einen gemessenen Zustand,
      nicht gegen eine Vermutung:** `m3.rs` sagt im eigenen Modulkopf, dass er kein
      Alias-Analysator ist; `R004` beißt nur am syntaktisch gleichen Ort an zwei
      `own`-Parametern; `zwei(r, r)` an zwei `ptr<normal, rw>` gibt **0 Fehler**.

- [ ] **Der Aliasfall ist keine Vorhersage — er steht SCHON im Korpus, und er ist still**
      *(gemessen 2026-08-21)*. `messung/netz/udp-echo.gab:207` (`echo_beantworten`) liest die
      IPv4-Prüfsumme über `w : ptr<normal, r> Kopfworte` und schreibt danach `k.ttl = 64`
      über `k : ptr<normal, rw> IpKopf` — **dieselben zwanzig Bytes**, denn `w` ist
      `kopfworte_von(k)` (`udp-echo.gab:146`). Ab dieser Zeile ist die über `w` gelesene
      Prüfsumme veraltet, und **RFC 791 verlangt sie neu gerechnet**. `gabbro pruefe`:
      **0 Fehler, 0 Hinweise** — *nicht weil es das duldet, sondern weil es nicht weiß, dass
      die zwei eins sind.*

      > **Die Rechtehälfte stimmt dort schon** — eine Sicht schreibend, die andere lesend.
      > **Es fehlt die EREIGNISHÄLFTE:** nichts entwertet `w` an der Schreibstelle. *Eine
      > Bytesicht, die nur die Rechtehälfte übernimmt, erbt dieses Loch und gibt ihm ein
      > Konstrukt, hinter dem es sich verstecken kann.*

      Das ist die Aliasfrage nicht als Entwurfsfrage, sondern als Loch im **einzigen Programm
      des Ordners, das gegen eine fremde Vorlage geschrieben ist** — und damit Regel B.

- [ ] **`old(place)` in einem RUMPF: die Regel steht nur auf der Erzeugerfläche**
      *(2026-08-20, [`gift/220`](beispiele/gift/220-old-in-einem-rumpf.gab))*.
      [`dokumente/SPRACHE.md`](dokumente/SPRACHE.md) §6 sagt *„`old(place)` only in
      `ensures`"*; ein Rumpf darf es trotzdem schreiben, `gabbro pruefe` meldet **0 Fehler und
      0 Hinweise**, und erst `C001` fällt. **Dieselbe Klasse wie das `!` davor — nur
      andersherum:** dort hatte die Sprache recht und der Erzeuger fehlte, hier hat der
      Erzeuger recht und der Prüfer fehlt.

- [ ] ~~**Der Fehlerkanal ist gebaut, der Erzeuger eines Grundes nicht — und jetzt steht es im
      erzeugten C**~~ *(2026-08-20)* — **ÜBERHOLT am 2026-08-21, nachgezogen am 2026-08-25.**
      Der Satz lautete: *„`*_grund` bleibt ungeschrieben, weil `primary` keine Produktion für
      einen `reason`-Wert kennt."* **Gemessen heute schreibt der Erzeuger sie:**

      ```c
      static bool hol(uint32_t x, uint32_t *_wert, HolFehler *_grund) {
              *_grund = HolFehler_Leer;
              return false;
      ```

      *Die `(void)`-Absicherung ist damit kein Ersatz mehr, sondern nur noch der Fall, in dem
      ein Rumpf den Kanal wirklich nicht benutzt.* **Der Posten in Stufe 7, auf den diese
      Zeile verwies, ist derselbe und ebenfalls zu.**

### Vom vervollständigten Fragmentkorpus, 2026-08-20 *(siehe [`messung/fragmente/`](messung/fragmente/))*

- [ ] **`A::B` parst und wird NIE aufgelöst** *(gemessen 2026-08-20)* — **von den DREI
      Lesarten ist eine zu, zwei sind offen** *(nachgemessen 2026-08-25)*.
      `path = ident { "::" ident }` steht in der Grammatik; der Namenspass liest die **erste
      Silbe** und schlägt sie als Wert nach. Der Eintrag sagte *„gleichgültig ob `IpcResult`
      ein `module`, ein `reason` oder ein Variantentyp ist"* — **das gilt so nicht mehr:**

      | Lesart | heute | Absage |
      |---|---|---|
      | `reason` | **aufgelöst** seit 2026-08-21 | `M126`, wenn `R` kein erklärter `reason` ist |
      | `module`-qualifizierter Wert | offen | `M119` *„`probe` is declared nowhere"* |
      | Variantenkonstruktor eines `tagged` | offen | `E009` + `K003` *„`Kurz` is not declared here"* |

      **Und der Rest ist nicht „kein Leser", sondern ein FALSCHER GRUND.** Beide offenen
      Lesarten melden über eine **Silbe** eines Pfades, den der Schreiber ganz hingeschrieben
      hat: `probe::qual::inner::MM` fällt als *„`probe` is declared nowhere"*, und
      `Nachricht::Kurz(7)` als *„`Kurz` is not declared here"*. Wer das liest, sucht einen
      Tippfehler in einem Namen, der stimmt — **die Sprache kennt die FORM nicht, und keine
      Absage sagt es.** *Dieselbe Klasse wie „die Absage nennt das Konstrukt nicht" bei
      `breaking` und wie der falsche Grund bei `leave` auf eine `retry`-Marke.*

      *Null Korpusstellen benutzen einen qualifizierten Namen als Wert;* die `::`-Treffer im
      Korpus sind samt und sonders `module a::b`-Köpfe und seit 2026-08-21 die Grundwerte in
      [`beispiele/48-grund-mit-erzeuger.gab`](beispiele/48-grund-mit-erzeuger.gab).
      **Auflösen ist deshalb ohne gemessenen Bedarf; den Grund richtigstellen ist es nicht.**
      Abnahme: eine Absage, die den PFAD zitiert und die Form benennt, nicht seine erste
      oder letzte Silbe.
- [ ] **«B11» schrumpft: `forever` HAT einen Ausgang, aber der Ausgang trägt keinen GRUND**
      *(nachgerechnet 2026-08-20)*. `leave <marke>` steht in der Grammatik
      ([`dokumente/SYNTAX.md`](dokumente/SYNTAX.md):658), prüft mit **0 Fehlern** und senkt zu
      `goto marke_ende;` mit gesetzter Marke ab. **Was fehlt, ist ein Austritt mit Namen:** die
      Vorlage schreibt `leaves ServiceExit` / `leave EndpointGone`, und `leaves` heißt in
      Gabbro etwas anderes — die **linearen Werte**, die den Bereich verlassen
      ([`dokumente/SPRACHE.md`](dokumente/SPRACHE.md):730). *D0 war genau das: dass der
      Austritt der Dienstschleife keinen Namen trug, hat zehn Tage gekostet* — und die halbe
      Antwort steht seit heute fest, die andere Hälfte nicht.
      **Und der zweite Befund ist, wie der veraltete Satz nach `messung/fragmente/F05.gab`
      kam:** dieser TODO wusste es längst; die Datei entstand am selben Tag und trug den
      Wortlaut des *eingefrorenen* Berichts vom 2026-08-14 mit. *Ein Korpus, der einen Bericht
      nachbildet, vervielfältigt sein Alter, wenn niemand auf den Gegenstand sieht.* Die
      Korrektur steht mit Datum daneben, der Wortlaut des Ausschnitts unangetastet.

- [ ] **Ein `static` eines Verbunds mit gewöhnlichem Anfangswert senkt nicht ab**
      *(2026-08-20)*. `static irq : IrqMarke = IrqMarke(tiefe_max: 0, n: 1);` — der Erzeuger
      sagt `static` of a `tagged` type or a record initialised with a plain … ab. *Die Zeile
      ist die, die ich selbst in `messung/fragmente/F06.gab` ergänzt habe, und sie steht dort
      mit ihrem Befund im Kopf, statt weggelassen zu werden.*

### K100 — der Weg auf 100 % Klempnereiabdeckung ([`dokumente/PLAN.md`](dokumente/PLAN.md))




- [ ] **«B26»: `RegDecl::requires` hat KEINEN LESER** *(gemessen 2026-08-20, `PFLICHTEN.md`:764)*.
      Die Klausel steht seit jeher in der Grammatik, wird geparst und dann fallengelassen --
      `grep -rn "r.requires" crates/` findet nichts. **Der Ordner fuehrte sie als „traegt eine
      `requires`, aber keinen benannten Ausgang"; der Befund ist eine Stufe darunter.**
      *Dieselbe Gestalt wie `ensures` an einem `extern fn`: grammatisch moeglich, und kein Pass
      liest es.* **Der Ausweg ist keine groessere Bedingung, sondern eine Form, die ABSENKT:**
      `requires … else <reason>` macht die Lesung fehlbar, und `let q = d.REG else (e) { … }`
      traegt der Erzeuger schon («B14b»). **Was NICHT geht, ist ein Fakt daraus** -- das waere
      «B33» ein zweites Mal: das Register ist fluechtig, und ein feindliches Geraet meldet, was
      es will.

- [ ] **Ein Traversierungszaehler erbt die Schranke seiner Domaene** — die letzte
      `narrow`-Klempnereipflicht des Korpus (`FRAGMENTE.md`:1100). Die Traversierung laeuft
      ueber `s.worte`, also kann `i` die Laenge nicht ueberschreiten; **M1 sieht es nicht**,
      weil der Zaehler eine gewoehnliche lokale Variable ist. *Eine V-Regel, keine neue
      Grammatik.* Tor danach: **`N_ritus = 0`**.

- [ ] **`opaque` beisst -- aber es gibt keine UMWANDLUNG** *(gebaut 2026-08-18, `D003`)*.
      Ein undurchsichtiger Typ hat die Rechnung seines Traegers nicht; Vergleiche bleiben
      erlaubt. **Null Korpusstellen fielen** -- der Beleg kommt aus Gift 211 (drei Operatoren; am 2026-08-20 von `79`
      umbenannt, weil zwei Dateien die Nummer trugen)
      und vier Sprechproben, nicht vom Korpus. *Was jetzt fehlt, ist der Ausweg:* heute gibt
      es keine Form, einen undurchsichtigen Typ ABSICHTLICH zu oeffnen, also ist die Regel ein
      Verbot ohne Tuer. **Solange kein Korpusstueck sie braucht, ist das richtig** -- aber es
      gehoert benannt, bevor jemand `opaque` deshalb weglaesst.

- [ ] **Der Netzwerkstack: die Entscheidung ist gefallen, der STACK ist es nicht**
      *(nachgemessen 2026-08-20)*. ~~«B24» blockiert den IP-Kopf.~~ **Der Eintrag war seit
      dem 2026-08-18 falsch, am Tag seiner eigenen Bewertung**: «B24» wurde noch am selben Tag
      entschieden, und [`beispiele/24-ip-kopf.gab`](beispiele/24-ip-kopf.gab) prueft mit null
      Fehlern und senkt ab -- `version:4 IHL:4 DSCP:6 ECN:2` stehen da, jede Lage im EIGENEN
      Wort. *Der Ordner sagte „blockiert", der Gegenstand sagte „offen", und dazwischen lagen
      zwei Tage.* **Was jetzt fehlt, ist kein Konstrukt, sondern ein PROGRAMM:** niemand hat
      den Stack geschrieben, und die Befunde kommen erst dabei -- so wie beim ersten echten
      Treiber und bei «K2». *Ein Posten, der eine Entscheidung verlangt, hat einen Adressaten;
      dieser hier verlangt Schreibarbeit.*

- [ ] **`const fn` -- comptime, das WERTE rechnet und keine Schablone kostet**
      *(bewertet 2026-08-17, `PLAN.md`: „Wozu Gabbro taugen wird")*. Heute rechnet
      `konst_wert` nur Literale und `const`-Ketten; `count NSLOTS * 2` oder
      `costs <= laenge(T) + 4` sind nicht schreibbar, und der Zusammenhang dreier Konstanten
      steht in einem Kommentar. **Ein `const fn` erzeugt keinen Code, also keinen
      Schabloneneintrag** -- seine Beweispflicht ist Totalitaet, und die traegt die Sprache
      schon (drei beschraenkte Schleifenformen, `effects { pure }` erzwungen).
      *Die Linie: comptime, das Werte rechnet, ist frei; comptime, das CODE erzeugt, kostet
      eine Schablone -- und ein nutzergeschriebener Erzeuger ist einer, dessen Beweispflicht
      niemand aufgeschrieben hat.*

### «B41» — three domains are demanded as measured. Build them or not?


      **The three are NOT of equal rank, and the ordering is half the decision:**
      * ~~**`ancestors of`**~~ — **built 2026-08-17** (`beispiele/18`, poison 69). And the
        build uncovered a gap that `descendants of` already had: over an
        `index into T` the cost pass did not find the bound, because the table name came
        unqualified out of the index type. **No example had ever triggered the
        site** — the corpus carries `descendants of` only in predicates, where no
        cost pass runs.
      * **Edge function — the line question has had its CRITERION since 2026-08-16.** It is the
        general case of `chain(a,b)`, and the precedent already stands in the language:
        **the `update` body of `exchange` — pure, M1-typed, over a value, without a
        quantifier.** An edge function of the same class (*one value in, one `option` value
        out, no world*) is **not a quantifier stock but a declared step.**
        > **The cut:** quantifier stock begins where the function appears in **statements**
        > instead of in **domain generation**. As long as it only supplies witnesses and stands in
        > no `requires`/`invariant`, the line does not move.
        **With this cut the chain swallows `ancestors of`**, and «B41» goes from three
        gaps back to **one design line**. *And the measurement from the same day shows that
        it is the same subject as the closure item:* `impl Fn(u16) -> Option<u16>`
        stands three times in `sched/redirect.rs` and is both at once.
      * **Union-find — will probably get NO traversal form at all.** `find` with
        path compression mutates the structure it runs over: **the interlocking from
        P0.1 attempt 1, disguised as a read operation.** Prediction in the folder: it stays a
        5 : 1 item or becomes **group-`ops` material** (compression as a generated operation
        with preservation of the representative invariant). *The prediction stands there so that a
        proposal for a `union_find` domain has to beat it first.*

      **W3 is satisfied (measured need), and W3 does not demand that one follow it.** The price
      stands in column 2 of the convergence metric: **every further domain is one more domain that
      every reader has to believe.**

- [ ] **The need is on the table, with `file:line` — the decision is not.** B3 found
      **584 non-traversable lines**, and **226 of them (38,7 %) stand in DMAR/PCIe**,
      that is, in none of the three suspected areas. Three named gaps:
      * **`ancestors of`** — the device topology is walked **upwards** (`cur =
        topo[cur].parent`, four bodies). Downwards it is a domain, upwards it is not.
      * **Union-find** — `dmar.rs:519` `find` **writes the chain it is walking**
        (`parent[x] = parent[parent[x]]`). Traversal and surgery in one statement;
        none of the eight domains covers that.
      * **Chain over an edge function** — `redirect.rs:577`/`625` walk the handler edge
        over a parameter `kante: impl Fn(u16) -> Option<u16>`; the chain arises only
        through the call and is not declarable.

### Syntax — open decisions (details in [`dokumente/SYNTAX.md`](dokumente/SYNTAX.md)) *(Teil)*

- [ ] **Variable lengths in `format`** — the hard 20 % of every parser generator, no
      notation available.

### From the inversion of the question ([`dokumente/SPRACHE.md`](dokumente/SPRACHE.md))

- [ ] **The eighteen conversions are claims about lowerability, not evidence.** Each needs
      its C lowering written down — before the canonisation in [`dokumente/SYNTAX.md`](dokumente/SYNTAX.md).

- [ ] **`retry` with `bounded`/`progress`/`on_exceeded` is the replacement for "unbounded waiting".**
      Open: is one number enough, or does it need two bounds (attempts **and** ticks)?

- [ ] **No. 14 demands a `publishes` clause at 2 231 sites.** Whether that carries is decided by no
      paper exercise — that is the largest single item of the whole conversion.

- [ ] **`breaking I { … }` legalises an invariant violation.** The price is visibility
      instead of hiding; whether that is enough is undecided.
      **Gewogen am 2026-08-28 gegen die andere Form** («B17», `messung/ZWEI-ORTE.md`): an der
      Stelle, an der zwei Orte EINEN Zustand bilden, ist `breaking` die haltbare der beiden
      Zusagen. Ein atomarer `transition` verspricht, dass es keinen Zwischenzustand GIBT, und
      braucht dafür einen benannten Beobachter, den er auf einem Mehrkerner nicht hat
      (`schablonen.rs::transition.transset`, `Stand::Entworfen`). `breaking` verspricht das
      Gegenteil und kann es halten. **Die Grundsatzfrage bleibt trotzdem offen** — dies ist
      eine Entscheidung über EINE Stelle, keine über das Konstrukt.
      *Was daran gebaut wurde:* `D013` — `I` muss etwas nennen; und `D009` schreibt den Bruch
      seither dem Träger zu, dessen Invariante er nennt, statt jedem mit `ops`. Erste saubere
      Korpusstelle überhaupt: `beispiele/53-zwei-orte.gab`.

### Vom ersten echten Treiber, 2026-08-20 *(siehe [`messung/BEFUNDE.md`](messung/BEFUNDE.md))* *(Teil)*

- [ ] **Die nominale Gleichheit steht NEBEN dem Typmodell, nicht darin.** `N030` hält
      `opaque`/`linear`/`ghost`/`tagged` an vier Stellen auseinander (Ruf, Bindung, Rückgabe,
      Vergleich) — und tut es in `namen.rs`, weil M1s `Typ` ein **Bereichsmodell** ist: es
      beantwortet *welche Werte passen hier hinein*, nie *was ist das*. **Damit gibt es zwei
      Typbegriffe in zwei Pässen, und das ist W7.** *Der Fix ist richtig und die Buchung
      lautet: die nominale Hälfte gehört auf Dauer INS Typmodell, nicht daneben.*

- [ ] **Der Korpus wächst per Konstrukt, die Fehler sitzen an den KOMBINATIONEN.**
      `gabbro blindstellen` zählt Form mal Stellung und nennt **130 blinde und 22 bewachte**
      Felder über den 38 Beispielen (2026-08-20). *Bewacht heißt: eine Regel verbietet es, und
      der Giftkorpus beweist, dass die Regel fällt* — das ist keine Arbeit, sondern die
      stärkste Zusage, die eine Zelle tragen kann.
      **Und die Zahl darf kein Ziel werden:** sie durch 130 kleine Dateien auf null zu
      bringen hiesse, den Korpus VOM INSTRUMENT nach außen wachsen zu lassen — derselbe
      Fehler eine Ebene höher. Auf dem Korpus von einen Tag vorher nennt es genau die
      beiden Befunde, für die ein echter Treiber nötig war: `ghost` in Rückgabestellung einer
      Funktion **mit Rumpf**, und ein Formatfeld in **Schreibstellung**.
      *Die Konsequenz ist keine Passarbeit: mehr Programme schreiben, nicht mehr Konstrukte.*

- [ ] **Ein Variantenkonstruktor als Anfangswert eines `static`.** Seit 2026-08-20 weigert sich
      der Erzeuger benannt: `static mut x : <tagged> = 0;` erzeugte ungültiges C bei 0
      Prüferfehlern, und *welche Variante die Null ist, sagt die Deklaration nicht*. Die
      Alternative — ein Konstruktor in der Anfangswertstellung — ist eine Sprachfrage.

### Vom zweiten Arbeitslauf über Tafel C, 2026-08-20 — elf Befunde, keiner still

*Jeder gegen HEAD nachgemessen, jeder mit Kleinstfall. Drei weitere aus demselben Lauf sind
sofort geschlossen worden («V9» in beide Richtungen, der Pfeil im `traverse`, zwei tote
Mutationsanker) und stehen deshalb nicht hier.*




- [ ] **`breaking` hat überhaupt keine Absenkung — und die Absage nennt das Konstrukt nicht.**
      `emit.rs::anweisung` hat keinen `StmtArt::Bricht`-Zweig; es fällt in den Sammelzweig
      `_ => weigere(…, "statement kind")`. **`SPRACHE.md` §8.3 spezifiziert es samt
      Buchungsregel, und `kbedingung.rs` sammelt seine Stellen für die K-Bedingung — die Liste
      ist immer leer.** Null Fundstellen im ganzen Ordner; was daran fällt, ist eine einzige
      Zeichenkette in `tests/beispiele.rs`. *Kein Nullbefund: eine Spezifikation ohne
      Implementierung.* **Und die Absage widerspricht der eigenen Doktrin des Moduls**
      (*„refuses by name"*), weil sie das Konstrukt nicht benennt.

- [ ] **`!x` hat keine Absenkung.** `ausdruck()` kennt `ExprArt::Unaer` nicht — nur
      `ausdruck_eintrag` im `walk`-Zweig kennt es. `if !b { … }` → `C001 "expression form"`.
      Im ganzen Korpus steht `!` nur in `ensures`-Prädikaten und `when`-Klauseln, **nie in
      einer Anweisung**. Betrifft auch das unäre Minus.

- [ ] **`leave`/`next` auf eine `retry`-Marke: Prüfer ja, Erzeuger nein — mit falschem Grund.**
      Die Grammatik gibt `retry` eine optionale Marke und `S001` nimmt sie als Sprungziel an;
      nur `forever` trägt sich in `Austritt::schleifen` ein. Der Erzeuger sagt
      `"leave/next naming no enclosing loop"` — **die Schleife ist da.** *Eine Regel, die zwei
      Stellen verschieden beantworten.*

- [ ] **`retry` ist nur in vier Umgebungen absenkbar.** `sammle_retry` steigt in `Retry`,
      `Sperrt`, `Match` und `Narrow` ab — **nicht** in `Wenn`, `Traverse`, `Forever`,
      `Observiert`, `LetSonst`, `Exchange`; und `retry_schranken` läuft nur über
      `ItemArt::Funktion`, also nie in einen `can_fail`-Rumpf. Die Absage lautet *„the per-pass
      cost is not fixed"* — **auch das ist der falsche Grund: es hat niemand hingesehen.**
      *Dieselbe Signatur wie W16: ein Werkzeug ohne Abstiegsschritt.*

- [ ] **`match` über einem Rufergebnis hat keine Absenkung.** `marken_quelle` kennt nur
      Parameter, Slot-/Verbundfelder und `let` **mit Typklausel auf oberster Rumpfebene**.
      `match lage() { … }` → `C001`.

- [ ] **`option index into T` als lokales `let` gibt es nicht.** Der `Let`-Zweig ruft
      `ausdruck()` ohne den `option_wert`-Pfad, den die Zuweisung hat. `let mut w : option
      index into T = None;` → `C001`. **Damit ist eine lokale Suchvariable über einer Tabelle
      unschreibbar.**

- [ ] **`let m = <geraet>.<reg>;` hat keinen ablesbaren Typ.** `wert_ctyp` kennt
      Geräteregister nicht. Mit Typklausel geht es. *Kein Korpusrumpf hat je ein Register
      gebunden.*

- [ ] **Ein unbenutzter `Some(j)`-Binder bricht den Bau.** `match_option` schreibt
      `uint32_t j = _o1;` ohne `(void)`-Absicherung; unter `-Werror=unused-variable` ist das
      ein Fehler. **Der `tagged`-Zweig macht es richtig** — zwei Fassungen derselben Sache.

- [ ] **Eine unbegrenzte Schleife in einem begrenzten Durchgang geht mit 0 Fehlern durch.**
      `forever` in `forever`, in `locks` und in `traverse`: Prüfer 0, `emit` OK, `cc` OK.
      `SYNTAX.md` §8 nennt ausdrücklich *„a pass that is itself unbounded"* als nicht erlaubt,
      §9.3 Punkt 1 *„a `locks` block whose body costs exceed K is a compile error"*.
      **`per_pass bounded 8 ops` über einer endlosen inneren Schleife ist heute eine
      widerspruchsfreie Zusage.**

- [ ] **M1 wirft Bereichstatsachen über `static`-Orten an JEDEM Ruf weg — auch an einem
      `pure`.** Nach `narrow g to 0 ..< 8` und einem `let v = q()` mit `effects { pure }` gibt
      `g += 1` ein `M101`. Über einem **Parameter** überlebt die Tatsache. *Die Wirkungsliste
      des Gerufenen wird nicht konsultiert, obwohl `pure` geprüft ist.*

- [ ] **`N027` deckt seinen eigenen Beispielfall nicht.** Der Regelkommentar zeigt
      `can_fail { a = 1; schreibt(); }` — die Regel prüft `Zuweisung`, `Sperrt`, `Publish`,
      `Exchange`, **nicht `StmtArt::Ruf`**. Ein Ruf mit Schreibwirkung in einer Probe geht mit
      0 Fehlern durch, und weil ein `check` keine Wirkungsliste trägt, sieht ihn sonst kein
      Pass. *(Nebenbei: `H008` sieht `can_fail`-Rümpfe ebenfalls nicht.)*

- [ ] **`narrow <lokaler let-Name> to 0 .. X` ist unter `-Werror` nicht baubar.** Der Erzeuger
      kennt den Vorzeichenstand eines `let`-gebundenen Namens nicht und gibt `alt >= 0 && …`
      aus — `-Werror=type-limits`. **Die Richtung ist bewusst** (*Unwissen fällt nach
      lautstark*), macht die Kombination aber unschreibbar.

- [ ] **`K009` prüft eine SYNTAKTISCHE hinreichende Form** — `n - k` und `n / k` mit der
      Massgrösse links. Ein Mass, das über einen `const fn` oder eine gerechnete Grösse
      fällt, wird abgewiesen, obwohl es fällt. *Aus der strengen Lesart kann man lockern,
      und das ist der Weg — aber die Lockerung braucht eine Rechnung, keine Vermutung.*

- [ ] **`N027` verbietet dem `can_fail`-Block jedes Schreiben.** Die Alternative wäre, dem
      `check` eine `effects`-Liste zu geben und ihn wie eine Funktion zu prüfen — *eine
      Sprachänderung*, und damit die teurere und vielleicht richtigere Antwort.

### «C» — vollständige Absenkung nach C, geplant 2026-08-19 ([`dokumente/PLAN.md`](dokumente/PLAN.md))

*Stand 2026-08-19, nach C1/C2/C3a/C3b/C3c/C4/C5: **23 von 35 Beispielen senken ab, 17
Einheiten stechen bis zum ausgeführten Ergebnis durch, 21 Weigerungen** — alle `C001`, keine
stille. (Ausgang: 17 von 33, 12 Einheiten, 46 Weigerungen.) **Sechzehn der 21 sind benannt**
— Axiomschicht (5), Entscheidung (8), gezogene Linie (3); **fünf sind Bauarbeit**, und jede
hat eine Adresse. Die Zielaussage ist nicht „0 Weigerungen", sondern **„3 Weigerungen, und
jede ist eine Linie mit einem Satz Begründung".***



- [ ] **Die ENTSCHEIDUNG, die C3a erzwang und die NICHT getroffen wurde: die
      Fehlerrückgabe-Konvention.** `let x = f() else (e) { … }` steht in der Grammatik
      (`SYNTAX.md`:644), und **keine Zeile sagt, wie ein Ruf scheitert.** `extern fn hol()
      -> u32` hat keinen Fehlerkanal, und nichts bindet eine Funktion an ein `reason`. Der
      Erzeuger müsste beides erfinden: *wie* der Fehler zurückkommt (Ausgabeparameter?
      Sonderwert? globale Zelle?) und *was* `e` trägt. **Eine Sprachentscheidung, die nur
      der Absenkung dient, wird nicht getroffen** — die Absage nennt seit dem 2026-08-19
      genau diesen Grund. *Dieselbe offene Stelle steht seit jeher am `on_exceeded` eines
      `retry`, das auf einen `reason`-Wert zeigt: zwei Fundstellen, eine Entscheidung.*

- [ ] **Die Sprechprobe muss MITWACHSEN: je Stufe eine weitere durchgestochene Einheit.**
      Heute siebzehn (war zwölf). Erzeugen → `cc -Werror` → **ausführen** → vergleichen → verfälschtes C
      muss fallen. Dazu je Stufe eine Mutation: die Emissionsfläche stand am 2026-08-17 bei
      **0** Mutationen, *und was 0 Mutationen hat, ist nicht gedeckt, sondern
      unbeschädigbar.*

- [ ] **Zwei Weigerungen bleiben, und sie zählen NICHT gegen die Abdeckung:** eine Bitlücke
      in einem `format` (*ein Format sagt, welche Bits EXISTIEREN* — sie heisst `reserved`
      oder gar nicht) und `table` ohne `count` (eine Zahl, die niemand nennt, wird nicht
      geraten).
      *Die dritte ist am 2026-08-20 gefallen:* `forever` senkt ab, und `on_exceeded` bekommt
      **keinen Zweig, sondern eine geprüfte Bezugnahme** — der C-Übersetzer liest die Klausel
      ein zweites Mal. Der zweite Grund der alten Weigerung («B11»: kein Ausgang) **war zu dem
      Zeitpunkt längst nicht mehr wahr**, und die Absage zitierte ihn weiter.

- [ ] **Wo endet die Forderung `Has(X)`?** *(2026-08-19, offen gelassen bei `N016`)*. Heute
      muss der Rufer sie DEKLARIEREN, und die Kette endet an der aeussersten Funktion. **Dass
      ein `check` oder eine `assume` sie HERSTELLT, ist eine Form, die es nicht gibt** -- und
      ohne sie steht am Rand jeder Kette ein `requires Has(X)`, das niemand einloest.
      *Dieselbe Frage wie bei `Held(…)`, nur ohne die Sperre, die man nehmen kann.*

- [ ] **`masks` traegt die UNTERBRECHBARKEIT, und die ist keine der elf Klassen**
      *(2026-08-19)*. `SPRACHE.md`:275: *„ein Effekt: `masks irqs` bzw. seine Abwesenheit. Ein
      Handler ist kein Aufruf -- er kann zwischen zwei beliebigen Anweisungen laufen."* Die
      Zeile stand als TOT mit *„ungelesen"*. **Eine zwoelfte Sorge in einer TOT-Zeile.**
      *Entweder sie wird eine Klasse, oder es steht dabei, warum nicht.*

- [ ] **Die drei `ops`-Ruempfe sind gebaut, und der Beweis DARUEBER fehlt**
      *(2026-08-28)*. `insert`/`remove`/`relabel` erzeugen C, `D012` haelt die
      Umhaenge-Bedingung an der Aufrufstelle, und `Table_Ops_Erhaltung.thy` traegt
      `umhaengen_erhaelt` (U-3). **Was fehlt, ist die Bruecke:** dass die emittierten
      C-Ruempfe die drei MODELLFUNKTIONEN *sind* -- dieselbe Luecke, die
      `Table_Absenkung.thy` mit eigenen Worten nennt.
      *Der Bau selbst steht seit dem 2026-08-28 in [`DONE.md`](DONE.md); er stand bis dahin
      als `- [x]` hier, in einer Datei, die ausschliesslich Offenes fuehrt.*

### «NL» — der Weg zu „nur noch eigene Logik" ([`dokumente/PLAN.md`](dokumente/PLAN.md)) — **PUNKT 1**


- [ ] **NL.1 -- `ops` braucht eine WORTMENGE, und das ist der groesste Posten** *(2026-08-19)*.
      `table.ops.erhaltung` traegt die K-Spalte -- **28 von 73 Pflichten** -- und ist
      `entworfen`, weil `opdecl` beliebige Bezeichner nimmt. **Der zweite Ausweg (der Nutzer
      schreibt die Wirkung) ist keiner: dann faellt Schnitt (c).** *Welche Operationen die
      Menge fuehrt, ist eine Messung am ZWEITEN Korpus -- der erste hat null `ops`-Stellen.*
      **Gemessen 2026-08-19** (`kernel/` + `mm/`, 659 Dateien): entfernen 479 · einfuegen 448
      · anlegen 408 · umhaengen 127 · ersetzen 11. **Einfuegen und Entfernen tragen 63 % --
      und `umhaengen` steht an 127 Stellen, also genau die Operation, fuer die
      `Table_Ops_Erhaltung.thy` das GEGENBEISPIEL fuehrt.** *Der Korpus braucht die Operation,
      von der der Beweis sagt, dass sie bricht.* Die Entscheidung steht damit mit Zahlen da.

### Aus «H2» *(ausgefuehrt 2026-08-19, `H = 17 → 15`)* — der Rest, den der Lauf hinterliess

**H2.1** (Zaehlerregel, `domaene.rs`, `elems of <Feld>`, Gift 114/115) und **H2.2** (die alte
Begruendung beschrieb den falschen Zweig) sind gebaut; beide `narrow` sind fort, beide
`PFLICHTEN.md`-Zeilen zu. **Alle acht verbleibenden verankerten Pflichten sind
NOTATIONSLUECKEN -- nicht eine ist ein Handbeweis.** Was daraus offen bleibt:







      | | SPRACHE.md | PLAN.md |
      |---|---|---|
      | P5 | C emission | axiom layer and entry |
      | **P6** | **pairing pass + `entry` emission** | **the generated refinement obligation** |
      | P7 | one Caprock module end to end | race freedom |

      Es sind nicht zwei Namen, sondern **zwei Fassungen EINES Plans**: beide fangen mit
      Papier an und enden beim Strangler-Muster, PLAN.md hat eine Stufe mehr, und ab P1
      verschiebt sich alles. `pflichten.rs`, `TODO.md` und PLAN.md folgen der einen,
      `SPRACHE.md` und `pruefe-todo.py` der anderen. *Der Waechter gegen Etiketten-
      Zweitvergabe sah nur TODO.md-Ueberschriften und deshalb die groesste Zweitvergabe des
      Ordners nicht* — er sieht seit heute PLAN.md mit, und die neun Abweichungen sind
      gebucht. **Welche Reihe gilt, ist ein URTEIL und keine Aufraeumarbeit**: 177 Verweise
      haengen daran.








- [ ] **Der zweite Korpus hat keine `H`-Messung, und ohne sie ist `H = 15` Falle 80**
      *(2026-08-19)*. Ueber den zehn Fragmenten beweist kein Mensch mehr Klempnerei von Hand
      -- **aber die zehn sind selbst gewaehlt.** Fuenf Linux-Fragmente stehen daneben, und
      ueber ihnen ist nichts gezaehlt. *Das ist der eine Posten, der zwischen „Boden der
      Messung" und „Boden der Sprache" steht.*

- [ ] **`FRAGMENTE.md` benutzte `Stack`, ohne ihn je zu deklarieren** *(gefunden 2026-08-19)*.
      Nachgetragen wie `STACK_MAX` am 2026-08-15, mit abgeleiteter Wortzahl. **Wie viele
      weitere Traeger benutzt der Ausschnitt, ohne sie zu nennen?** Jeder davon macht eine
      Pflicht unsichtbar -- die zweite fiel hier sofort auf (`s.len - frei`, geschlossen mit
      der relationalen Nachbedingung). *Eine Zaehlung, und sie ist klein.*

- [ ] **`group` steht an EINER Korpusstelle** *(2026-08-19)*. ~~`beispiele/17` ist die
      einzige;~~ **`beispiele/17` ist die einzige, SOWEIT GESUCHT** *(abgeschwächt
      2026-08-30)*;
      die vier Verbindungsinvarianten des Sweeps vom 2026-08-16 (V1-V4) sind gemessen, aber
      nicht geschrieben. **Zwei bewiesene Schablonen ueber einem Konstrukt mit einer
      Fundstelle** -- das ist der Grund, warum die Amortisationszahl heute zweimal gestiegen
      ist. *Solange V1-V4 nicht als `group` dastehen, misst die Zahl den Beweisvorlauf und
      nicht die Amortisation.*

      > **„Ist die einzige" war ein Allquantor über einen Korpus, den niemand abgeschritten
      > hatte.** Er ist zu „soweit gesucht" abgeschwächt — und *das ist nur dann kein
      > Nullbefund, wenn der Suchweg danebensteht.* Also steht er hier.

      **Der Suchweg, 2026-08-30.** Durchsucht wurden **alle 408 `.gab`-Dateien** des Baums
      (`find . -name '*.gab'`, ohne `target/` und `.git/`), Muster `^\s*group\b` — `group`
      am Zeilenanfang, also das Konstrukt und nicht das Wort. Gegenprobe mit dem freien
      Muster `group` über dieselbe Menge: 12 Dateien, dieselben 12. **Keine Fundstelle
      steht nur in einem Kommentar.**

      | wo | Dateien mit `group` | zählt als Korpus? |
      |---|---:|---|
      | `beispiele/*.gab` | 1 — `beispiele/17-gruppe-ueber-zwei-sperren.gab` | **ja** |
      | `beispiele/gift/*.gab` | 9 — `63`, `64`, `65`, `66`, `185`, `262`, `280`, `281`, `282` | nein (W23: eigene Giftproben) |
      | `messung/race-proben/*.gab` | 2 — `gruppe-unbekannter-traeger`, `gruppe-unbekannte-sperre` | nein (Messproben) |
      | alles übrige (`messung/fragmente`, `fnptr-proben`, `abi-proben`, `caprock`, `netz`, `treiber`, `grenze`, `messungen`, `programmlogik/beispiel`) | 0 | — |

      **Damit ist die Aussage schärfer als vorher, nicht schwächer:** es ist nicht nur
      *behauptet*, dass `beispiele/17` allein steht — es ist über 408 Dateien nachgesehen,
      und die elf anderen Fundstellen sind benannt statt verschwiegen. *Der zweite Korpus
      (`messung/fragmente`) hat keine einzige.*

      **Was ausdrücklich NICHT gebaut wurde: ein mechanisches Maß über
      „Verbindungsinvariante".** Ein Werkzeug, das zählt, an wie vielen Stellen eine
      Verbindungsinvariante *hingehörte*, müsste entscheiden, wann zwei Träger
      zusammenhängen — und genau das ist das Urteil, um das es hier geht. **Ein Urteil in
      Werkzeugform ist kein Maß, es ist dasselbe Urteil mit einer Zahl davor**, und die
      Frage stünde unverändert eine Ebene tiefer. *Die vier V1-V4 sind von Hand gefunden;
      dass es genau vier sind, ist eine Lesung und wird hier nicht als Zählung ausgegeben.*

- [ ] **`N009` sieht nur ZAHLLITERALE** *(2026-08-19)*. Ein berechneter Registerversatz
      (`CAP.FRO * 16`) bleibt stumm, und `bank`-Register werden nicht gegen die Hauptebene
      gehalten -- die Basis waere zu raten. **W10: der Bericht verpflichtet, er spricht
      nicht frei.** *Was fehlt, ist die Zaehlung, an wie vielen Korpusstellen ein Versatz
      NICHT literal ist.*

- [ ] **`ops` hat keine WORTMENGE, und das ist der Rest von Punkt 2** *(gemessen 2026-08-19)*.
      `opdecl = "ops" identlist ";"` nimmt beliebige Bezeichner; `insert, remove, relabel,
      delete_leaf` sind in `SPRACHE.md` 10.2 ein BEISPIEL, keine Menge. **Ein Erzeuger kann
      aus einem Namen keine Wirkung ableiten.** Zwei Auswege: eine geschlossene Wortmenge mit
      je definierter Wirkung (wie `merge add|max|min`), oder der Nutzer schreibt die Wirkung
      und der Erzeuger prueft sie -- *dann ist es aber keine ERZEUGTE Mutation mehr, und
      Zuschnitt (c) faellt.* **Vorher zaehlen, welche Operationen der zweite Korpus
      braucht** -- der erste hat null.

- [ ] ~~**P6 ist EROEFFNET, nicht erledigt**~~ — **ERLEDIGT am 2026-08-21, und er hat einen
      ANDEREN Posten freigelegt** ([`messung/P6.md`](messung/P6.md)).
      `gabbro pflichten --isabelle` schreibt denselben Bestand, den `gabbro pflichten` zählt,
      als Isabelle-Theorie — **je Pflicht entweder ein geschlossenes Ziel oder eine BENANNTE
      Absage**, und jede Kopfzeile trägt `goals + refused = total`.

      ```
      47 Pflichten · 1 Ziel · 46 benannte Absagen        ./instrumente/zaehle-p6.py
      == P6-BEWEIS: 1 erzeugte Pflicht in 63 Theorien, ISABELLE GRUEN ==
      ```

      **Und die 46 sind keine Lücke von 46:** 12 tragen schon die Sperrdisziplin
      (`Held(…)` → `H005`/`H006`/`H012`/`H016`), 11 sind **Annahmen und keine Pflichten**
      (fremdes `ensures`), **23 bleiben wirklich offen.** *Aus einer schlechten Zahl wird eine
      informative, weil jede Absage ihren Grund trägt.*

      > **Die eine durchgehende Pflicht ist eine `K`-Pflicht, keine `W`** — über die Kennzahl
      > sagt sie nichts, und sie wird ausdrücklich zurückgehalten. **Was sie belegt, ist die
      > KETTE:** von der Zählung über die Erzeugung bis `isabelle build` grün, mit einem
      > Wächter, der beim Mutieren fällt. *Eine Eins mit funktionierender Kette ist mehr wert
      > als zehn ohne.*

      **Nebenbei geschlossen: die Fläche `annotation` stand seit Wochen bei 0 Mutationen** und
      steht bei 7. *Der Wunschform-Kanal war der Posten, der als „unbeschädigbar" dastand — er
      hat jetzt Zähne.*

      Ein eigener Fehler ist gemessen und dokumentiert: der erste Bau löste die Argumente auf,
      **bevor** er das Prädikat las, und meldete zwölf getragene Pflichten als ungebaut.
      *Dieselbe Klasse wie ein Werkzeug, das zu wenig liest — nur in der REIHENFOLGE statt in
      der Tiefe, und in die pessimistische Richtung.*

- [ ] **Die Kachelungsluecke (`N009`) ist NICHT gebaut, und der Grund ist der Korpus**
      *(gemessen 2026-08-19)*. `format Elf64Ph` laesst mit `p_flags : u32 @[2:0]`
      neunundzwanzig Bits unbenannt; die Regel im Pruefer haette den eigenen Korpus zerlegt.
      **Der Erzeuger sagt sie ab, und dort ist sie richtig** -- eine Luecke macht das Wort
      unentscheidbar, sobald jemand Bytes anfassen will. *Offen ist, ob `Elf64Ph` seine
      uebrigen 29 Bits `reserved` nennen sollte -- dann faellt die Ausnahme mit.*

- [ ] **Ein Waechter, der jeden Pass-Walker gegen die blockfuehrenden Anweisungsarten haelt**
      *(fuenfte Instanz am 2026-08-19)*. Vier blinde Walker an einem Tag (`H007` in
      `observes`, der RCU-Walker in Schleifen, `typ_von_ort` gegen `index_pruefen`, und der
      `retry`-Rumpf), und jetzt die fuenfte: **`sammle_namen_pred` betrat den `Ort`, aber
      nicht seinen Index** -- `ensures … W.slots[tippfehler]` ging mit 0 Fehlern durch.
      *Jedes Mal wurde der Rumpf betreten und ein Zweig davon nicht.* **Fuenf Funde derselben
      Bauart sind kein Zufall, sondern ein fehlendes Werkzeug** -- dasselbe Argument wie bei
      `pruefe-klauseln.py` und `pruefe-widerruf.py`, und beide haben beim ersten Lauf
      geliefert.

- [ ] **`atomic` ist ein ITEM, kein Slotfeld** *(gemessen 2026-08-18 an K2-F2)*. Das Original
      benutzt `atomic_long_inc_not_zero` -- **ein atomares RMW ist seine eigene
      Wechselseitigkeit**, und ein RCU-Leser darf damit einen Zaehler erhoehen, ohne die
      Schreibersperre zu nehmen. In Gabbro ist ein Zaehler IM Objekt nicht atomar
      deklarierbar, also verlangt `H010` dort eine Sperre, die das Original nicht braucht.
      *Die Nachbildung ist damit strenger als das Vorbild -- und das ist ein Befund ueber die
      Sprache, nicht ueber den Prueferlauf.*

- [ ] **`observes` senkt nicht ab** *(2026-08-18)*. Der Erzeuger weigert sich benannt. Die
      Absenkung waere zwei fremde Ruempfe wie bei `lock` (`_beobachten`/`_freigeben`), und die
      Zeugniszeile muesste sagen, dass diese Einheit eine RCU-Domaene liest -- **eine Aussage
      ueber die Rueckgewinnung, nicht ueber Zahlen.**

- [ ] **`D004` hat auf diesem Korpus NULL Biss** *(gemessen 2026-08-18)*. Alle zwoelf
      `opaque`-Deklarationen der Beispiele erklaeren und benutzen im **selben Modul**, also
      greift die Modulgrenze zu Recht nicht. **Dieselbe Lage wie `E010`**, und derselbe
      Beleg: die Regel ist an Giftproben gemessen, nicht am Korpus. *Eine Eigenschaft des
      Korpus, nicht der Regel -- und ein weiteres Argument fuer den zweiten.*

---

# STUFE 5 — DIE BEWEISE TRAGEND MACHEN *(parallel zu Stufe 4)*  ⟨D⟩

**`L = 1` sieht gut aus und heißt wenig.** Daneben stehen **8 Prämissen ohne Pass** — ein Beweis,
den nichts einlöst.

> **Das ist nicht Buchhaltung, das ist die schärfste Form der Klasse, die in einer Woche fünfmal
> zugeschlagen hat.** Ein Beweis, dessen Voraussetzung niemand herstellt, ist **gefährlicher als
> eine ungeprüfte Zusage — weil ein Isabelle-Häkchen darüber steht.** Der Registerversatz war
> genau das: bewiesener Satz, keine Prüferzeile.

**Darum parallel und nicht danach.** Die Stufe kostet keine Programmierarbeit im Prüfer, nur den
Abgleich *Prämisse → Pass*. Und jeder Tag, an dem sie offen ist, ist ein Tag, an dem
`gabbro zeugnis` zehn Beweise ausweist, von denen ein Teil in der Luft hängt — **und das Zeugnis
ist das Artefakt, mit dem Gabbro nach außen tritt.**

**Das Tor:** Zahn 3 — jede bewiesene Schablone bindet ihre Prämissen an einen Pass, und
`gabbro schablonen` fällt, wenn eine keinen Leser hat. *Verwandelt zehn dekorative Beweise in zehn
tragende, ohne eine Zeile Isabelle.*

## Das Tor steht seit dem 2026-08-20 — und die Kostenschätzung des Plans war falsch

```
$ gabbro schablonen --tor
9 premises of PROVED templates have no pass -- a proof nothing establishes    → 1
$ ./instrumente/pruefe-schablonen.py
Marke 6 — eine Ratsche, keine Zielzahl · 0 ohne Adresse
```

**Zwei verschiedene Dinge, und sie bleiben getrennt:** `--tor` trägt das *Ziel* und fällt,
solange eine Prämisse hängt; der Wächter trägt die *Bewegung* und fällt, wenn die Zahl steigt.
*Ein Werkzeug, das jeden Tag rot ist, wird nicht gelesen.*

**Der Plan sagte „kostet keine Programmierarbeit im Prüfer, nur den Abgleich Prämisse → Pass".
Das Register selbst widerlegt es:** von den neun brauchen zwei eine **ganze Schicht** (die
Ausführungskontexte K11.2.2, die Axiomschicht), zwei einen **Erzeuger**, zwei eine
**Sprachform** — und nur der Rest ist Prüferarbeit. *Die neun sind mehrheitlich keine
vergessene Prüfarbeit, sondern nicht getroffene Entscheidungen.*

### Und zwei der neun Adressen waren VERALTET

**Das ist der eigentliche Ertrag dieser Stufe.** Der Wächter zählt Adressen, er prüft sie
nicht — also von Hand am Gegenstand nachgerechnet:

| | stand da | ist heute |
|---|---|---|
| `consuming.ordnung` | *„`abstieg` ist heute eine **ZUSAGE ohne Leser**"* | **falsch seit dem 2026-08-19** — `S005` liest ihn. S005 prüft aber, dass das *Maß* sich bewegen kann, nicht dass die *Auswahl* minimal ist: zwei verschiedene Aussagen |
| `table.ops.erhaltung` | *„eine **WORTMENGE** für `ops` — heute nimmt `opdecl` beliebige Bezeichner"* | die Wortmenge war am 2026-08-19 **entschieden** und stand nur in der EBNF |

**Und die zweite Zeile war in BEIDE Richtungen falsch:**

```
ops erfundenes_wort;   →  0 Fehler   -- jedes Wort ging durch
ops insert;            →  P002       -- die drei GÜLTIGEN gingen NICHT
```

Die drei stehen im Lexer als reservierte Wörter, also konnte die `identlist` des Parsers sie
gar nicht lesen. *Die Grammatik sagte das eine, der Lexer das zweite, der Parser das dritte* —
und `opdecl` hatte **null Korpusstellen**, also hat es niemand bemerkt. **Gebaut** (`P039`),
mit Gegenprobe in [`beispiele/47`](beispiele/47-ops-wortmenge.gab) und
[`gift/221`](beispiele/gift/221-ops-erfundenes-wort.gab).

> **Dass ausgerechnet die Giftproben erfundene Wörter trugen, ist der Grund, aus dem die Lücke
> nicht auffiel.** Drei Dateien mussten nachgezogen werden.

### Die `own`-Entscheidung ist gefallen

**`own` ist die FREIGABEOPERATION, kein Signaturvermerk** ([`dokumente/SPRACHE.md`](dokumente/SPRACHE.md) §5.1).
Die andere Lesart war nie tragfähig: ein Signaturvermerk ist eine Klausel ohne Leser, und
`own` war bis zum 2026-08-19 ein Synonym für `rw`.

*Und sie wird trotzdem nicht gebaut, aus einem gemessenen Grund:* der ganze Korpus hat **eine**
Funktion mit zwei Zeigern desselben Trägers (`beispiele/07::wechseln`), und die trägt kein
`own`. **Regel A** — kein Konstrukt ohne ein Programm, das es gebraucht hat. Die Prämisse
trägt jetzt diese Adresse statt einer fehlenden Entscheidung.

### K100 — der Weg auf 100 % Klempnereiabdeckung ([`dokumente/PLAN.md`](dokumente/PLAN.md)) *(Teil)*

- [ ] **K100.4 — die STARKE Fassung von (b) fehlt noch.** `gabbro zeugnis` zaehlt auf, worauf
      eine Uebersetzung ruht (gebaut 2026-08-17, acht Einheiten, je Befund gebucht). *Es sagt
      nicht, dass sie haelt.* Die starke Fassung waere ein maschinell geprueftes Zeugnis je
      Uebersetzung -- **und die Vorstufe ist als Vorstufe benannt**, damit die Zahl nicht mehr
      verspricht, als sie misst.
      **Geschaerft 2026-08-20 — der Posten sagte nicht, was noch DAZWISCHEN steht, und es ist
      mehr, als „fehlt noch" nahelegt.** Was schon mechanisch ist: die **Kreuzprobe** zwischen
      Erzeuger und Zeugnis (`beispiele.rs`, „das Zeugnis muss alles verbuchen, was der
      Erzeuger absenkt" — senkt `emit.rs` etwas ab, das `zeugnis.rs` nicht einordnet, faellt
      `UNZUGEORDNET`). *Das ist die Zusicherung, dass die Liste VOLLSTAENDIG ist, nicht dass
      sie stimmt.* Und die vier bewiesenen Absenkungsschablonen (`table.absenkung`,
      `table.indexschranke`, `option.sonderwert`, `verbund.konstruktor`) sind je EIN Satz
      ueber die erzeugte Form, nicht ueber den erzeugten Lauf.
      **Der Preis der starken Fassung, mit Adresse:** ein Zeugnis je Uebersetzung muss ueber
      dem ERZEUGNIS reden, und in `beweise/` gibt es keine C-Semantik — `Table_Absenkung.thy`
      kommt genau bis dahin und beruft sich fuer den Rest auf *„die Sprachdefinition von C
      und keine Annahme dieses Beweises"*. **Damit ist K100.4 dieselbe Baustelle wie P6 im
      README** (*„was fehlt, ist die ERZEUGTE Verfeinerungspflicht"*), und nicht ein
      Ausbaustueck des Zeugnisses. *Ein Posten, der nach Werkzeugarbeit klingt und eine
      Semantik kostet, wird in der falschen Reihenfolge geplant.*

- [ ] **Ein Rumpf, dessen Kosten SELBST symbolisch sind, rechnet `Unbekannt` statt `40 * n`**
      *(Rest des Postens „parametrische `costs`-Zusage", der am 2026-08-20 beim Nachsehen
      schon zu war)*. `kosten.rs` liest eine Zusage als Summe aus einer Konstanten und
      Vielfachen nichtnegativer Größen und vergleicht gegen die **kleinste** Belegung — das
      trägt, solange der Rumpf eine Zahl ergibt. *Ergibt er selbst einen Term, fällt die
      Rechnung auf `Unbekannt` zurück, und die Zusage wird nicht geprüft, sondern
      übersprungen.* Der Grund steht im Kopf von `kosten.rs`.
- [ ] **All three S17 obligations stand as FORM. What is missing is the preservation.**
      Built: (a) locks in rank order (`U003`/`U005`), (c) no intermediate exit (`U006`),
      (b) the statement connects (`U007`).
      **Pulled up 2026-08-16:** the clause stands, and with it `U007` — a
      group invariant must name **at least two** carriers, otherwise it belongs at the
      table. With that (b) is built as a **form**. **What stays open is (b) as PRESERVATION:** that the
      statement holds under an operation is the prover's business and falls to S16/S17 — the checker
      establishes the three conditions under which the question can be put at all.
      **The next step is therefore the group operation** (`ops` over the group), and it
      is no longer a preliminary but the recipient of the proof obligation.
      **Geschaerft 2026-08-20 — die Etiketten sind gewandert, und der Posten haengt an EINER
      Sache.** „S17" heisst im Register heute `ops.suche`; die Gruppe fuehrt `S20 gruppe.ops`
      und `S21 gruppe.sperrabdruck`, beide **entworfen**. `U001`–`U007` stehen und sind der
      Formteil. **Woran die Erhaltung haengt, sagt `gabbro schablonen` in einem Wort:**
      das `braeuchte` von `gruppe.ops` lautet *„die AXIOMSCHICHT — eine Aussage ueber das
      Speichermodell, nicht ueber Zustaende"*. *Das ist keine Pruefarbeit und keine
      Grammatikzeile; es ist dieselbe Schicht, an der `race` und die Paarung (A10) haengen —
      also EIN Preis fuer drei Posten und nicht drei.*

### Design — open decisions *(Teil)*

- [ ] **Cost figure per invariant** ~~and at `by unbesucht`~~: which structure, who resets it,
      what the reset costs, whether it may live under the lock.
      **Die zweite Haelfte ist entschieden, und die Antwort ist: gar keine Struktur**
      *(Stufe 3, 2026-08-20, nachgesehen im Erzeuger)*. `emit.rs:4586` und `:4693` sagen es
      ausdruecklich: `by unvisited` heisst *jeder Knoten einmal* und ueber die Reihenfolge
      nichts — **das ist die Laufform selbst**, und die Nachordnung, die `by consuming`
      ohnehin erzeugt, haelt die staerkere Zusage. *Damit gibt es keine Besuchtmenge, niemanden,
      der sie zuruecksetzt, und keine Frage, ob sie unter der Sperre leben darf.* Die
      Zeugenordnung ist ein Beweismittel, kein Laufzeitding.
      **Was offen bleibt, ist die Kostenzahl je Invariante — und sie haengt an einem Leser:**
      `./instrumente/pruefe-klauseln.py` fuehrt das `cost`-Feld der Invariante bis heute unter UNGELESEN,
      das `runs`-Feld unter NUR GETRAGEN. *Solange `cost O(n)` niemand liest, ist die
      Frage „passt die Invariante in die `costs` der erzeugten Mutation" nicht einmal
      stellbar* — derselbe Faden wie der Kleinkram-Posten weiter unten.

### Induction — entered, and the one number is missing


- [ ] **~~The generated scheme has to go into Isabelle once~~** — **beim Nachsehen schon zu,
      seit dem 2026-08-16.** `beweise/Table_Induktion.thy` fuehrt es als `lemma
      table_induktion` (`assumes wf`, `assumes schritt`, `shows "P s"`, `by
      (rule wf_induct_rule)`), und `gabbro schablonen` fuehrt `S7 table.induktion` als
      **bewiesen**. Nachgerechnet 2026-08-20 mit `./instrumente/zaehle-theorien.py`: 13 Theorien,
      2 329 Zeilen. *Die Theorie ist ausserdem schaerfer als der Posten: sie zerlegt „wohl-
      fundiert und vollstaendig" in die vier einzeln dastehenden Nebenbedingungen N-1 bis
      N-4.*

- [ ] **Well-foundedness hangs on an invariant one wants to prove.** The declaration has to
      name which — and the measure (number of descendants) is a premise, not a result.
      **Geschaerft 2026-08-20, und der Preis ist EINE Klausel:** `Table_Induktion.thy` sagt
      es selbst (*„Wohlfundiertheit ist HYPOTHESE, nicht Ergebnis … die Deklaration muss die
      tragende Invariante nennen"*), und die Grammatik hat den Platz dafuer schon — `by
      induction over <domain>` an der `invariant`. **Nur nennt sie eine DOMAENE und keine
      Invariante, und gelesen wird sie von niemandem:** `./instrumente/pruefe-klauseln.py` fuehrt `by`
      (FnDecl/Invariante) bis heute unter UNGELESEN. *Damit haengt dieser Posten an demselben
      Faden wie der `by`-Eintrag im Kleinkram unten — ein Leser fuer `by`, und beide fallen
      zusammen.*

### «NL» — der Weg zu „nur noch eigene Logik" ([`dokumente/PLAN.md`](dokumente/PLAN.md)) — **PUNKT 1** *(Teil)*

- [ ] **`bedingung` hat die Klasse verlassen, ohne dass ihre Zusage gehalten wuerde**
      *(2026-08-19, und es ist ein Befund ueber den WAECHTER)*. `N012` liest die
      `where`-Klausel, um die Schranke eines `offset_into` zu finden -- damit gilt sie
      mechanisch als gelesen. ~~**Ob die Bedingung HAELT, prueft weiterhin niemand.** (2026-08-20)~~ *Das
      Mass des Waechters ist „ein Pass greift zu", nicht „ein Pass haelt es nach"; die
      Vergroeberung stand in seinem Kopf und zahlt hier zum ersten Mal.* Der Posten steht
      jetzt hier, wo ihn keine Ratsche traegt -- **ein Waechter, der eine Zeile aus seiner
      eigenen Liste verliert, muss sagen, wohin sie geht.**
      **Nachgesehen 2026-08-20, und die Antwort ist: ein Pass haelt sie nach, nur ein
      anderer.** `emit.rs:2243` legt jede `where`-Klausel eines `format`-Feldes in
      `<Format>_gueltig()`, neben die Laengenpruefung (`:2449`) — **eine Funktion, die der
      Rufer EINMAL stellt, und danach braucht kein Zugriff mehr eine Pruefung.** *Und das ist
      auch der einzig moegliche Ort:* der Wert kommt vom Draht, ein feindlicher Kopf setzt
      ihn, wohin er will — statisch ist da nichts zu beweisen.
      **Was als Befund BLEIBT, ist der ueber den Waechter, und er wird dadurch schaerfer:**
      die Klausel verliess die Liste wegen `N012`, und `N012` liest sie, um eine **Schranke
      zu finden** — nicht, um sie einzuloesen. *Der Waechter hat also das Richtige gemeldet
      und aus dem falschen Grund; haette `emit.rs` die Zeile nicht getragen, waere die
      Meldung dieselbe gewesen.* **Das Mass „ein Pass greift zu" trennt nicht zwischen
      lesen und einloesen** — und solange es das nicht tut, ist jeder Abgang aus der Liste
      von Hand nachzusehen.

### Aus «H2» *(ausgefuehrt 2026-08-19, `H = 17 → 15`)* — der Rest, den der Lauf hinterliess *(Teil)*

- [ ] **Die STARKE Fassung von `M115` braucht eine Entscheidungsprozedur** *(2026-08-19)*.
      Heute faellt nur, was der Bereich des Arguments AUSSCHLIESST; dass der Rufer die
      Vorbedingung HERSTELLT, prueft niemand. **M1 stellt Fakten her und entscheidet keine
      Praedikate** -- die starke Fassung ist ein eigenes Stueck Maschinerie und zerlegte
      ausserdem den Korpus. ~~*Vorher zaehlen, an wie vielen Rufstellen eine Vorbedingung
      heute unbewiesen bleibt.*~~ **Gezaehlt am 2026-08-20: es sind 12** (`gabbro pflichten
      beispiele/*.gab`, neue Spalte `V`; die Summe steht in `dokumente/PLAN.md` und wird von
      `./instrumente/pruefe-zahlen.py` neu abgeleitet). *Der Preis der schwachen Fassung stand bis heute
      NIRGENDS* — `gabbro pflichten` zaehlte Pflichten, die eine DEKLARATION erzeugt, und
      keine, die ein RUF erbt. **Ein Preis, den kein Werkzeug nennt, sieht aus wie null.**
      Die Zahl ist nach oben eine Schranke (eine am Rufort trivial geltende Bedingung zaehlt
      mit, weil heute nichts sie entscheidet) und nach unten eine (ein Ruf, dessen Pfad sich
      nicht aufloest, wird nicht gefunden). **Was offen bleibt, ist die Entscheidungsprozedur
      selbst — jetzt mit ihrem Gegenwert daneben.**

- [ ] **Zwei der NEUN haengenden Praemissen brauchen keine Pruefarbeit, sondern eine
      SPRACHFORM** *(gemessen 2026-08-19, nachgerechnet 2026-08-20)*. `by consuming` braucht
      einen genannten Zeitpunkt fuer die Leerheit, `accumulates.monoid` die
      Ausfuehrungskontexte. **Die haengenden Praemissen sind mehrheitlich keine vergessene
      Pruefarbeit, sondern nicht getroffene Entscheidungen** -- und das aendert, wer sie
      schliessen kann.
      *Berichtigt 2026-08-20 (Stufe 5): hier stand „drei der sieben", und beide Zahlen waren
      falsch.* Die Wortmenge fuer `ops` war der dritte Posten -- **sie war seit dem 2026-08-19
      entschieden und stand nur in der EBNF**; `P039` haelt sie seit dem 2026-08-20. Und
      `gabbro schablonen` zaehlt neun, nicht sieben.

- [ ] **Der Beweis, dass `bitlage::lies` die Lagen trennt, hat kein Register**
      *(2026-08-19)*. Die Praemisse `trennt f g` von `format.roundtrip` ist durch die
      KONSTRUKTION erfuellt -- sequentielle Byte-Lagen, monoton wachsender Versatz. **Das ist
      eine Aussage ueber den PRUEFER, und fuer die gibt es kein Register**; dieselbe Lage wie
      `Intervall_Aussen.thy`. *Heute steht der Grund in `durch:` als Prosa.*
      **Haengt am selben Faden wie „Der PRUEFER hat kein Register" weiter unten** — seit dem
      2026-08-20 traegt der Faden eine Zahl (`./instrumente/zaehle-theorien.py`: 2 von 13 Theorien ohne
      Register). *Dieser Posten faellt mit jener Entscheidung, nicht vor ihr.*

- [ ] **`einfuegen` braucht ZWEI Bedingungen, und keine hat einen Pass** *(2026-08-19,
      `Table_Ops_Erhaltung.thy`)*. Der Platz ist FRISCH, der Elter ERREICHBAR. Beim Loeschen
      traegt das `requires ist_blatt(c, s)` des Rufers die Bedingung -- beim Einfuegen gibt
      es keine solche Zeile. *Ein Erzeuger, der `einfuegen` ausliefert, muesste sie
      herstellen oder verlangen.*

- [ ] **`maintains` nennt UNQUALIFIZIERT** *(2026-08-19)*. `M112` sammelt `spec fn` und
      Invarianten ueber alle Module flach ein, weil der Korpus unqualifiziert schreibt.
      **Zwei gleichnamige Invarianten in zwei Modulen sind damit ununterscheidbar** --
      dieselbe Bauart wie `typ_von_ort` vor dem 2026-08-17, nur noch nicht ausgeloest.
      ~~*Eine Regel, die mehr verlangt als der Korpus schreibt, zerlegt ihn; die
      Verschaerfung braucht also zuerst eine Messung, wie viele Stellen qualifizieren
      muessten.*~~ **Gemessen 2026-08-20: es sind NULL.** Ueber 277 Einheiten stehen
      **11 `maintains`-Stellen**, und keine einzige muesste qualifizieren — die Mehrdeutigkeit
      braucht zwei gleichnamige Invarianten in zwei Modulen **derselben Uebersetzungseinheit**,
      und nur **6 von 277 Einheiten tragen ueberhaupt mehr als ein `module`**. *Die
      Verschaerfung zerlegt den Korpus also nicht — sie hat heute auch keinen einzigen
      Biss, und das ist der andere Befund.* **Ausgeloest wird die Klasse erst von «ABI»:**
      ein `.gabi` ist gueltiger Gabbro-Quelltext mit eigenem `module`, und der Importeur
      bekommt damit ein zweites Modul in seine Einheit. *Dort, nicht hier, wird aus der
      Bauart ein Fall.* (Nachrechnen: `grep -c "^[ \t]*maintains" beispiele/*.gab
      messung/**/*.gab` und `grep -lc "^module" …` — die Zahlen stammen aus einem
      Handgang ueber genau diese zwei Muster.)

- [ ] **Der PRUEFER hat kein Register** *(2026-08-18)*. `Intervall_Aussen.thy` ist die erste
      Theorie dieses Ordners, die von M1 handelt statt vom Erzeuger -- und sie steht in
      **keinem** Schablonenregister, weil das Register Erzeugerpflichten fuehrt
      (*„eine Beweispflicht, die der Erzeuger schuldet"*). **Damit gibt es jetzt zwei
      Vertrauensflaechen und nur eine Buchung.** Die zweite wird bisher nur von
      `mutiere-pruefer.py` gemessen -- Mutationen, nicht Saetze. *Ein zweites Register waere
      die naheliegende Antwort; ob es eines sein soll, ist eine Entscheidung.*
      **Geschaerft 2026-08-20: die Luecke ist jetzt GEZAEHLT statt beschrieben.**
      `./instrumente/zaehle-theorien.py` haelt seit heute jede `.thy` gegen `schablonen.rs` und meldet
      **2 von 13 ohne Register**, mit einer Ratsche darauf. *Und die zweite ist ein eigener
      Befund:* `Table_Induktion.thy` IST eine Schablone (`S7`, bewiesen) — nur nennt der
      Registereintrag seine Datei nicht. **Die andere Richtung derselben Luecke: nicht die
      Flaeche fehlt, sondern die Zeile, die sie verknuepft.** Die Entscheidung bleibt offen;
      was sie jetzt hat, ist eine Zahl, die nicht mehr still wachsen kann.

### Deklariert, exportiert, nie gelesen — die Klasse hat einen Namen und einen Waechter

**Neu gemessen 2026-08-20** mit `./instrumente/pruefe-klauseln.py`: **147 Feldnamen** aus `ast.rs` gegen
**30 Leserdateien**, davon 5 tragend. **22 Felder gebucht** -- 16 nur getragen (nur
`emit.rs`/`zeugnis.rs`/`cli`), 6 ungelesen. Nach Urteil: **0 ZUSAGE**, 2 FREMD,
5 ABSENKUNG, 15 TOT. *Die Stufe ist gemessen, die Klasse ist ein Urteil, und das Werkzeug
sagt beides getrennt an.*

> ~~*Gemessen 2026-08-18: 131 Feldnamen gegen 23 Leserdateien, 48 Felder gebucht --
> 21 nur getragen, 27 ungelesen; 17 ZUSAGE, 6 ABSENKUNG, 25 TOT.*~~ **Acht Zahlen, und
> jede stand am 2026-08-20 falsch da.** Die teuerste ist die erste: **ZUSAGE steht auf
> null** — *das ist das Tor von «NL» selbst, und es ist erreicht.* `dokumente/PLAN.md`
> fuehrt die Null seit dem 2026-08-20 und wird von `./instrumente/pruefe-zahlen.py` nachgerechnet;
> **dieser Abschnitt fuehrte daneben die 17 weiter.** *Zwei Buchungen ueber derselben
> Messung, und nur eine hatte einen Leser* — genau die Klasse, gegen die W7 steht.

Der Waechter klemmt in beide Richtungen und weist seine Messfaehigkeit nach (R14: `span` muss
als gelesen herauskommen, `section` nicht). **Die Liste unten ist eine UNTERE Schranke** --
gemessen wird je Name, nicht je Struktur (W10).



- [ ] **~~`leaves` und der Abstieg des `traverse` haben weiter keinen Leser~~**
      *(gebucht 2026-08-18)* — **beim Nachsehen schon zu, und zwar BEIDE.**
      **`L106`** liest `leaves` (`m2.rs:565`, seit «NL.2.6», 2026-08-19) und **`S005`** den
      Abstieg (`schleifen.rs:250`, «NL.2.3», gleicher Tag). *Und der Posten hatte selbst den
      falschen Satz darin:* `leaves` nennt nicht, „was den Ausgang verlaesst", sondern die
      **linearen Werte**, die den Geltungsbereich verlassen — die Ausgaenge nennt
      `leave <marke>`. Der erste Anlauf baute die Regel nach der Waechterbeschreibung und
      meldete zwei falsche Befunde an `beispiele/04`. **Eine Klauselbeschreibung, die seit
      Wochen in der Waechtertabelle steht, ist keine Quelle — die Spezifikation ist eine.**
      Beides ist die **notwendige** Bedingung: dass das Mass FAELLT, bleibt bei
      `consuming.ordnung`. **Beleg ohne Bau:** `./instrumente/pruefe-klauseln.py` bucht
      am 2026-08-20 weder `verlaesst` noch `abstieg` — die 22 gebuchten Felder sind eine
      andere Liste. *Was daneben stehenbleibt und in `schablonen.rs` steht: das `braeuchte`
      von `consuming.ordnung` sagt weiter „`abstieg` ist heute eine ZUSAGE ohne Leser". Die
      Zeile ist ueberholt, und sie gehoert dem Zahn-3-Posten.*

- [ ] **Zahn 3: NEUN Praemissen ohne Hersteller, und das Tor faellt seit dem 2026-08-20
      mechanisch** *(gemessen 2026-08-18, nachgerechnet 2026-08-20)*. **Das ist die Umkehrung
      der Klausel-Klasse und teurer als sie:** bei einer ungelesenen Klausel weiss niemand
      etwas, hier weiss man etwas Falsches.
      `gabbro schablonen --tor` gibt **1** zurueck, solange eine haengt; `./instrumente/pruefe-schablonen.py`
      traegt die Ratsche (Marke 8, sie geht nach unten) und verlangt je Praemisse eine
      Adresse. **Was die beiden NICHT koennen: die Adressen nachpruefen** -- zwei von neun
      waren am 2026-08-20 veraltet, und das fiel nur von Hand am Gegenstand auf (W10).
      *Berichtigt: hier stand „acht", und die schaerfste war `device.konstruktor` -- die
      steht nicht mehr darunter.* Was offen bleibt, ist die Zahl selbst: **zwei der neun
      brauchen eine ganze Schicht** (Ausfuehrungskontexte, Axiomschicht), zwei einen Erzeuger,
      zwei eine Sprachform -- nur der Rest ist Pruefarbeit.

- [ ] **`by consuming` liest kein Pass** *(gemessen 2026-08-18)*. Beide Praemissen von
      `consuming.ordnung` -- *die Mutation ist ein ENTFERNEN* und *die Auswahl ist MINIMAL* --
      sind damit nicht bloss unhergestellt, sondern unherstellbar, solange niemand das
      Konstrukt ansieht. **`Consuming.thy` K-2 fuehrt fuer die erste ein Gegenbeispiel**: EIN
      Umhaengen macht aus einem wohlfundierten Zustand eine Schlinge.

- [ ] **`versatz`: der bewiesene Satz hat keine Prueferzeile** *(gemessen 2026-08-18)*. Dass
      zwei `reg` einander nicht ueberlappen, ist der HAUPTSATZ von `Device_Konstruktor.thy`;
      gelesen wird das Feld nur von `emit.rs`. Gleich daneben: `schritt` -- **`stride 0` macht
      die Bank leer**, und die Theorie nennt das selbst eine Fundstelle. *Ein bewiesener Satz
      ohne Pass ist eine Zusage ueber ein Programm, das so nicht geprueft wird.*

- [ ] **~~`pub` ist wirkungslos~~** *(gebucht 2026-08-18)* — **beim Nachsehen schon zu.**
      Der Satz endete auf *„eine Bibliotheks-ABI beginnt bei genau diesem Wort"*, und genau
      dort ist er eingeloest worden: `abi.rs:95,99-103` liest `oeffentlich` und entscheidet
      daran, was in ein `.gabi` geht. Die Sichtbarkeit selbst prueft `N025` an der
      Bezugsstelle (`umgebung.rs:215` sagt es im Doktext, samt der Umbenennung von
      `kandidaten_oeffentlich`, die sie versprach und nicht tat). **Beleg ohne Bau:**
      `./instrumente/pruefe-klauseln.py` bucht `oeffentlich` nicht mehr.

- [ ] **`ensures`/`maintains` werden GEZAEHLT, nicht gelesen** *(gebucht 2026-08-18)*.
      ~~`zeugnis.rs:370,391` ruft `.len()` und `.is_empty()`; kein Pass haelt sie gegen den
      Rumpf oder auch nur gegen die Wohlgeformtheit.~~ **Die zweite Haelfte ist gefallen, die
      erste steht** *(nachgesehen 2026-08-20)*. Die Wohlgeformtheit prueft M1: `M111` an
      `ensures`, `M112`/`M113`/`M114` an `maintains` (der Name loest auf · eine `spec fn`
      erhaelt nichts · die Invariante muss ueber etwas sprechen, das die Funktion anfasst).
      Die Zeilennummern im Posten sind ausserdem gewandert — es ist `zeugnis.rs:632,653`.
      **Was offen bleibt, ist die Haelfte, die keine Wohlgeformtheit ist: dass der RUMPF sie
      einloest.** Das ist P6, und `gabbro pflichten` zaehlt es statt es einzuloesen —
      3 Erhaltungspflichten und 7 Nachbedingungen ueber `beispiele/*.gab`. *Ein Posten, der
      zwei Fragen in einem Satz fuehrte, war nur zur Haelfte zu.*

- [ ] **`invariant` und der Kleinkram: gelesen und sonst nirgends** *(gemessen 2026-08-18,
      gekürzt 2026-08-20)*. `cost`/`runs` an der `invariant`, `by` (der Induktionshinweis
      verfällt), `masked` an einer Sperre, `exhaustive`, der Ergebnistyp eines `axiom` und die
      Formatversion. *Kein Fehler, aber auch keine Sprache.*
      **Vier sind am 2026-08-20 gefallen:** der Abstieg eines `walk` (`levels`/`node`/`down`/
      `leaf` senken ab), `scale` (im `format`-Leser, und ein Setzer wird dafür benannt
      verweigert), der `can_fail`-Rumpf eines `check` (M1 **und** der Paarungspass lesen ihn)
      und der Fehlername im `let … else` (er trägt den `reason` aus `-> T or R`).
      **Nachgezählt 2026-08-20 mit `./instrumente/pruefe-klauseln.py`: es sind genau diese sechs, und
      die Liste stimmt** — die Spalte UNGELESEN hat heute sechs Einträge und keinen siebten.
      *Eine Korrektur an der Aufzählung selbst:* `cost` und `runs` stehen NICHT im selben
      Zustand. Das `cost`-Feld der Invariante ist ungelesen; das `runs`-Feld wird von
      `emit.rs:5794` getragen — **der Erzeuger sieht es an, kein Pass hält es nach.** Der
      Unterschied ist der zwischen *„niemand weiss davon"* und *„einer benutzt es und keiner
      prüft es"*, und der zweite ist der teurere. **Und `by` trägt zwei Posten**: hier den
      Kleinkram und oben die Wohlfundiertheit der Induktion — ein Leser, und beide fallen.

### The write-right line `by ops` — and the group proof sentence that precedes it



      *And a side finding of the sweep changes the expectation: **there is in the existing code NO
      double acquisition of the same lock class** (`system.rs`:15). The expected first test case for
      `locks ordered` thereby drops out; the one that was found is a different one — two classes with
      an ordering over two crates (V4).*

- [ ] **~~`by ops` is built — what stays open is ONE breakthrough: `breaking` on a
      `by ops` field.~~** — **geschlossen 2026-08-20, und die Buchung sagte das Gegenteil der
      Messung.** Sie las: *„`ist_geschlossen` verlangt, dass es keine `breaking`-Stellen gibt
      — ein `breaking` oeffnet den Traeger damit wieder, statt ein Uebersetzungsfehler zu
      sein."* **Zwei Dinge daran waren falsch, und beide sind messbar:**
      * `ist_geschlossen` gibt es nicht. Die Funktion heisst `Traeger::k_haelt`.
      * Ein `breaking` oeffnet nichts. `kbedingung.rs::sammle` steigt ueber
        `crate::unterbloecke` in den Rumpf ab wie in jeden anderen Unterblock: **die
        Handmutation faellt an `D001`, am `by ops`-Feld zusaetzlich an `D002`.**

      **Was `breaking` wirklich bewegt, ist die MESSUNG** — der Traeger faellt aus der
      Zaehlung *„K haelt"*, weil das Messprotokoll verlangt, dass ALLE Mutationen erzeugt
      sind, und ein Bereich, in dem ein Satz ruht, ist genau der, den *„der Erzeuger zeigt es
      einmal"* nicht deckt. *Zwei Fragen, die der Ordner zusammengezogen hatte.* Gesagt steht
      es jetzt in `SPRACHE.md` §10.2.1, gefallen ist es in
      `beispiele/gift/226-breaking-oeffnet-den-traeger-nicht.gab`, und die Gegenrichtung
      (ohne `ops` geht dieselbe Handmutation durch) steht in `rechenwerk.rs`.
      **Und die dritte Bewegung:** `breaking` hatte bis zu diesem Gift **null Korpusstellen**
      — *ein Satz ueber ein Konstrukt, an dem nie etwas gefallen ist, ist eine Vermutung*
      (W11). Nebenbefund: `pruefe-konstrukte.py` misst 23 ITEM-Arten und keine
      Anweisungsarten; `breaking` ist eine, und darum konnte die Luecke dort nicht auffallen.
      (Breakthrough 2 — the `dma` edge — is closed: `R001`, placement rule.)

- [ ] **The group proof sentence: the quantifier is open, the walkthrough is no longer.**
      *"B13 falls exactly when **every** connection invariant occurring in the tree has a
      group whose `ops` close it."* **What fell on 2026-08-16:** the
      paper walkthrough at the CapSpace/CDT pair (three answers), the sweep for the *other*
      invariants (**four found: V1–V4**), the grammar line (`group … over { … }`) and
      three of the four form obligations (`U003`/`U005`/`U006`/`U007`).
      **What is open is exactly two things:**
      * **The quantifier itself.** Four found means four found — W12. The sweep was a
        candidate list with search paths, not a mechanical walkthrough. What it systematically
        misses stands beside it: invariants without a common index field, say a
        sum condition over two tables.
      * **The `ops` over the group** — the recipient of the proof obligation from S16/S17.
        The checker today establishes the three conditions under which the question *"does the
        invariant hold?"* can be put at all; **it does not answer it.**

      **Geschaerft 2026-08-20 — die zwei Haelften haben verschiedene Preise, und nur eine ist
      Arbeit.** Die zweite (`ops` ueber der Gruppe) ist heute `S20 gruppe.ops`, *entworfen*,
      und haengt an der **AXIOMSCHICHT** — derselbe Preis wie beim Posten „three forms stand"
      oben. **Die erste — der Quantor — haengt an gar nichts ausser einer Entscheidung:**
      „vier gefunden heisst vier gefunden" (W12) wird nie zu „alle", solange die Suche ein
      Kandidatengang ist. *Entweder es gibt ein mechanisches Mass ueber „Verbindungs-
      invariante" — dann ist es ein Werkzeug und keine Suche —, oder der Satz bekommt sein
      „soweit gesucht" dazugeschrieben.* **Was er heute NICHT darf, ist als Allaussage
      dastehen**, und das ist die billigere der beiden Antworten.

### Group `ops` + `by ops` — the design, BEFORE the first grammar line

Three commitments from the paper test, each re-checked. **They stand here because they change the
design, not because they decorate it.**

### E1 — The group's lock imprint is TWO-LEVEL, and that decides the grammar

Mutations take exclusive, the generated read operation (`lookup` class) takes **shared** —
that is measured in the tree: `33 CAPS.read()` against `44 CAPS.write()`. **The
construct therefore declares both modes PER `op`, not one per group.**

```
group Kappen over { Slots, Objekte } locks KAPPEN {
    op einfuegen  exclusive;
    op entfernen  exclusive;
    op nachschlagen shared;      -- der heisse Pfad
}
```

**Without this line `locks shared` would be built and the group could not use it** —
every generated operation would take exclusive, and the most-travelled path of the kernel would be
the slowest again. *A construct that makes another one unusable is a
design error, not a feature backlog.*

**Nachgesehen 2026-08-20: nichts davon steht in der Grammatik, und der Platz dafuer ist
BESETZT.** `gruppedecl` (`SYNTAX.md`) lautet heute `"group" ident "over" "{" identlist "}"
( "{" { invariant } "}" | ";" )` — **kein `locks`, kein `op`.** Und eine Zeile darunter steht
eine Entscheidung, die zu E1 hingehalten werden muss: *„The lock order does NOT stand at the
group — every carrier lies under a `lock … rank N`, and the ranks give the order; a second
declaration would be a second truth about the same thing."*
> **Die zwei widersprechen einander nicht, und genau deshalb ist die Verwechslung billig:**
> E1 will den **Modus je `op`** (exklusiv/geteilt), die getroffene Entscheidung verbietet den
> **Rang an der Gruppe**. *Wer E1 baut, muss den Satz daneben stehenlassen und im selben
> Atemzug sagen, warum er ihn nicht bricht* — sonst liest der naechste den Widerspruch und
> nicht die Unterscheidung.

### E2 — The speech test has an obligatory direction, and it is a FILE

`refcount -= 1` with the null check **afterwards** must be unwritable under `by ops`. That
belongs as a **poison fragment in the test, not as a sentence in the text** — the folder's
rule that a promise needs a place at which it falls.

**CORRECTED.** I had written that the cut stands in two **independently
written** cores. That is wrong, and it is mechanically refuted:

```
$ git log --follow --name-status -- crates/caprock-cap/src/space.rs
R099   crates/sel4lake-cap/src/space.rs -> crates/caprock-cap/src/space.rs
```

**`R099` — a rename with 99 % similarity.** The same authorship line, the same file;
the copy under `ARMTest/` is an older snapshot of the same lineage, not a second
core. *Two sites from one inheritance are one site.*

The load-bearing justification is a different one — and it is measured, not inferred:

```
$ git log -L 1060,1075:crates/caprock-cap/src/space.rs --oneline
b026c83  A-3.3: Finalized leiht seinen Speicher …          2026-07-29
083a698  DMA: Teardown-Token (ext-37) -- Freigabe nur gegen Nachweis
0f246f9  ext-23 D0: DmaCap + DmaEnforcer …
9085cc0  ext-22 P4: generische Device-MMIO-Infrastruktur …
2d50d42  feat(cap/ipc): first-class Reply-Cap mit Revocation
2111f30  initial                                            2026-06-23
```

The line sequence has stood **since the original commit** (`2111f30`, there at line 341/342, literally
the same order) and has survived **five rebuilds of exactly this region** — among them
two that rewrote the release semantics themselves (`Reply-Cap mit Revocation`,
`DMA-Teardown-Token`). Over five weeks, over a package rename, over the
duplication of the file.

> **B29 is not a slip but an attractor.** Whoever writes the delete path writes
> it that way — even at the fifth rebuild, even after the trap had been paid for once. **That carries
> the speech-test obligation just as well as the refuted independence claim, and it
> is the true justification.**

The existing probe `beispiele/gift/37-b29-unter-ops.gab` covers `ops` on the **table**
(`D001`). The new one covers `by ops` on the **field** — `field : u16 by ops` — and must hit exactly
this line sequence.

**Eingeloest — beim Nachsehen am 2026-08-20 lag die Datei schon da:**
`beispiele/gift/60-b29-unter-by-ops.gab` (`-- erwartet: D002`), mit genau der Zeilenfolge
`zaehler -= 1;` gefolgt von der Null-Pruefung, und mit dem Unterschied zu Gift 37 im Kopf
notiert: *„dort nennt die TABELLE `ops`, hier nur das FELD."* **Die Pflicht, die E2 als
FORDERUNG fuehrte, ist damit ein Ort im Korpus** — und seit dem 2026-08-20 steht daneben die
dritte Frage derselben Ecke beantwortet (`breaking` oeffnet den Traeger nicht, Gift 226).

### E3 — The Verus template: take over the clause structure, NOT the types

**Re-checked, and the mechanism is a different one than assumed — the warning becomes
stronger thereby, not weaker.**

`cap_space.rs:17` carries `pub refcount: nat`. At the delete path stands:

```
:791   let oldrc = cs.objects[o as int].refcount;
:792   assert(oldrc >= 1);                        // <- WIRD BEWIESEN, aus der Invariante
:793   let newrc: nat = (oldrc - 1) as nat;
```

**The model proves the precondition.** So it is not that the template answers the question
wrongly — it answers it rightly, **from the invariant**. What `nat`
takes away is something else: the type carries **no width**, so over the
*representation* no obligation ever arises. There is exactly **one** net, and it hangs on the invariant.

In Gabbro the same field carries `u32 in 0 ..= NSLOTS`. With that `-= 1` at 0 is an
**M1 error out of the TYPE** — without any reference to the invariant. **Two independent nets
instead of one**, and the second is exactly what fell in the speech test as `M104` next to `D001`.

> **The template takes over the CLAUSE STRUCTURE of the model (one `spec fn` over all
> clauses, preservation per operation), not its TYPES.**
>
> If it inherits `nat` along with it, the generated obligation list looks complete while the second
> net is missing — and worse: a generated C emission could
> omit the range check, *because the proof says it cannot go negative*. That is literally the
> booked error class: **releasing a claim about the model into the machine**
> (`dokumente/HISTORIE.md`, commit `5904cae`). Then the model would be a trojan gift.

**The checking line against it, mechanically:** no field generated by a template may carry a
type without a width. That is checkable at the template itself, not only at the artefact.

**Nachgesehen 2026-08-20 — die Pruefzeile braucht es nicht, und der Grund ist besser als
sie.** `SYNTAX.md` §`intty` laesst genau `u8|u16|u32|u64|i8|i16|i32|i64 [ "in" range ]` zu:
**es gibt in Gabbro keinen Ganzzahltyp ohne Breite.** Ein Uebertragen von `nat` ist nicht
schwer zu entdecken, sondern nicht schreibbar. *Eine Eigenschaft, die die Grammatik traegt,
braucht keinen Pass — und ein Pass, der sie trotzdem prueft, sieht wie eine Absicherung aus
und ist eine Doppelung.*
> **Was von E3 UEBRIG bleibt, ist damit keine Pruefarbeit, sondern eine Sperre gegen eine
> kuenftige Grammatikzeile:** wer je einen unbeschraenkten Ganzzahltyp einfuehrt, nimmt das
> zweite Netz weg, und der Verlust faellt nirgends auf — *das erzeugte C liesse die
> Bereichspruefung weg, weil der Beweis sagt, es koenne nicht negativ werden.*
### The four items to the goal — plan with gates in [`dokumente/PLAN.md`](dokumente/PLAN.md) §A *(Teil)*

- [ ] **A4 — `costs` at a RECURSIVE function stays an assumption.** A call counts
      the *declared* costs of the callee; at a cycle nobody recomputes. That is
      the intention of §7. ~~— but it means that the termination hangs there on a promise.~~
      **Der zweite Halbsatz ist ueberholt** *(nachgemessen 2026-08-20)*: seit «K5.4» traegt
      die Rekursion ein Mass. `K008` verlangt an einer Funktion, die sich selbst erreicht,
      ein `decreases`; `K009` verlangt, dass an jeder rekursiven Rufstelle mindestens eine
      der genannten Groessen sich aendert. Probe: `impl fn f(n : u32 in 0 .. 1000) … { …
      return f(n - 1); }` ohne `decreases` gibt **`K008`** (und `E009` als dritten Zustand
      fuer die Wirkungen). **Die TERMINIERUNG haengt damit an einer geprueften notwendigen
      Bedingung, nicht mehr an einer Zusage** — *dass das Mass faellt, bleibt Beweisersache,
      und genau diese Trennung ist die Zielform.* **Was als Posten stehenbleibt, ist die
      ZAHL:** `costs` an einer rekursiven Funktion ist weiter eine Annahme, weil jede Kante
      des Zyklus einmal zaehlt. *Ein Posten, der Terminierung und Kostenzahl in einem Satz
      fuehrte, war nur zur Haelfte offen.*

---

# DIE KENNZAHL — EINE W-PFLICHT, DIE ENTSTEHT  ⟨B⟩

**Dieser Abschnitt ist am 2026-08-23 entstanden, und zwar durch eine ZUORDNUNG, nicht durch
einen Fund.** Die drei Punkte darunter standen am Ende von Stufe 4 („Programme schreiben") —
zwischen 56 Punkten über die Sprache. *Dort gehören sie nicht hin.* Stufe 4 arbeitet an dem
Block, der am weitesten ist; diese drei tragen die **einzige Zahl, an der das Vorhaben
scheitern kann**.

> **Ein Block ohne Überschrift wird nicht abgearbeitet, er wird gestreift.**

**Was hier steht und sonst nirgends:** `0,5 : 1` ist zurückgezogen (`unbekannt, > 0,5`), und
zurückgeholt wird sie nur über eine **W**-Pflicht, die in Isabelle durchgeht. P6 hat den Kanal
gebaut; die eine Pflicht, die hindurchgeht, ist eine `K`
([`messung/P6.md`](messung/P6.md) §7). *Solange das so bleibt, misst dieser Ordner seine
Infrastruktur und nicht seine These.*


- [ ] **Was fehlt, heißt seit dem 2026-08-21 genauer: nicht „P6", sondern DIE
      ISABELLE-SEMANTIK EINES GABBRO-RUMPFS** *(freigelegt beim Bau von P6)*.
      **16 der 23 wirklich offenen Pflichten sitzen an genau dieser einen fehlenden Sache**
      (Rumpfwirkung), 7 am Weltmodell.

      > **Die Brücke ist nicht das Teure, das MODELL ist es.** Das war beim Lean-Plan
      > (Stufe 9) eine Vermutung; seit heute ist es gemessen. *Ein Beweiser kann eine Pflicht
      > nur angehen, wenn er weiß, was ein Rumpf BEDEUTET* — und das steht nirgends.

      **Damit ist die Kennzahl `w` nicht durch P6 blockiert, sondern hierdurch.** Solange
      dieser Posten steht, erzeugt P6 `K`-Pflichten und keine `W`-Pflichten, und die Zahl
      bleibt zurückgezogen (`unbekannt, > 0,5`).
      *Er gehört als Fund gebucht und nicht als Rückstand* — sonst liest er sich in zwei
      Wochen als ein Posten, der liegen blieb, statt als der, den ein fertiger Bau sichtbar
      gemacht hat.

- [ ] **Die Kopfform von P6 hat NULL Fundstellen** *(gemessen 2026-08-21)*: **kein einziges
      `spec fn`/`impl fn`-Paar im Korpus** (8 gegen 168). Die Verfeinerungspflicht aus einem
      solchen Paar ist deshalb **nicht gebaut** — Regel A, gemessen statt vermutet.
- [ ] **P6 ist die Grundlage der Kennzahl, nicht ihr Zubehoer** *(geschaerft 2026-08-19)*.
      Die Zahl ist zurueckgezogen (`unbekannt, > 0,5`), weil `w` an VERUS-Zeilen gemessen war.
      Ein Isabelle-verankertes `w` braucht **eine W-Pflicht, die ENTSTANDEN ist** -- und
      erzeugt wird sie von P6, der Verfeinerungspflicht aus `spec fn`/`impl fn`. ~~**Keine
      Sprachsemantik noetig:** die Absenkung nach C ist die Bedeutung, und beide Seiten stehen
      in einer Sprache.~~ **— widerrufen am 2026-08-21 (`WK1`), durch den Bau von P6 selbst:**
      16 der 23 offenen Pflichten sitzen an der Rumpfwirkung. *Die Absenkung nach C ist eine
      Bedeutung fuer den UEBERSETZER, keine fuer den BEWEISER.* *Solange P6 fehlt, muesste man die Pflicht erfinden, die man dann
      misst -- genau die Bewegung, gegen die R7 und W3 stehen.*

# STUFE 6 — DIE FREMDEN RÜMPFE SPRECHEN LASSEN  ⟨C⟩

**89 fremde Rümpfe im Korpus, 11 sprechen ihre Pflicht aus — und genau EINE verengt wirklich
etwas.** `ensures` an einer rumpflosen Deklaration ist grammatisch seit jeher möglich.

> **Berichtigt am 2026-08-21, und die Überschrift war in BEIDE Richtungen falsch.** Hier stand
> *„0 sprechen ihre Pflicht aus — und kein Pass liest es"*. Es sind **10**, und ein Pass liest
> es sehr wohl: `M1` verengt daraus (Entscheidung 14, Stufe 2). *Zu pessimistisch in der
> Zahl, zu optimistisch im Schluss.* **Die 0 stand als Literal im Suchmuster ihres eigenen
> Wächters** — eine Zahl, die im Muster ihres Wächters als Konstante steht, ist unbewacht und
> sieht bewacht aus (W16). Seit heute kommen beide Zahlen aus dem Lauf.
> ```
> $ ./instrumente/zaehle-fremdverengung.py
>   1 wirksame Fremdverengungen aus 10 ausgesprochenen Vertraegen
>   109 fremde Ruempfe insgesamt (beispiele/ + messung/)
> ```
> **Und die schärfere Zahl ist die 1 von 10.** Sechs der zehn Klauseln nennen `result` gar
> nicht (Weltzustand), zwei nennen es und bewegen nichts, eine hängt an einer Funktion, die
> niemand ruft. *Neun Verträge, die aussehen wie Pflichten und niemanden binden* — das ist
> die Lücke dieser Stufe, schärfer gefasst als vorher.

Das ist die eine Klasse, die sich auch unter *„ganz Gabbro verifiziert"* nicht auflöst, und damit
**genau die Klempnerei, die beim Endnutzer übrig bleibt: Ziel 4 hängt hier stärker als an `H`.**
Eine Sperre schuldet gegenseitigen Ausschluss, Fortschritt und die Rangordnung, und keine Zeile
sagt das heute.

> **Berichtigt am 2026-08-21 — und diesmal war es kein Zahlenfehler, sondern ein SATZ.**
> Hier steht *„die Zeilen hinschreiben (kostet nichts)"*. Für **31 der 109** fremden Rümpfe
> kostet es nicht nichts — **es geht nicht:** `lock`, `rcu`, `guest`, `entry`, `boot` und
> `gabbro_kern` haben **kein `ensures`-Feld in der Grammatik**, und `zeugnis.rs` schiebt ihren
> Vertrag als deutschen Fließtext von Hand in die Liste.
> ```
> $ ./instrumente/zaehle-fremdpflichten.py
>   STUMM 31 | SCHWEIGT 67 | UNGELESEN 10 | WIRKT 1     (109 fremde Ruempfe)
> ```
> **Die Sperre — das Beispiel, das dieser Posten selbst nennt — ist genau der Fall, der nicht
> geht.** *Die ehrliche Bezugsgröße ist 78, nicht 109.* Wer diese Zeilen will, ändert die
> GRAMMATIK, nicht seine Sorgfalt — und das ist ein anderer Posten als der gebuchte.

Zwei Hälften: die Zeilen hinschreiben (kostet nichts) und den Prüfer sie in die Beweispflicht des
Rufers tragen lassen (Passarbeit). Dazu die Axiomschicht — 33 Annahmen, jede mit Sonde oder Grund,
und die Sätze, die ihr noch fehlen.

### K100 — der Weg auf 100 % Klempnereiabdeckung ([`dokumente/PLAN.md`](dokumente/PLAN.md)) *(Teil)*

- [ ] **Die FREMDEN RUEMPFE sind die eine Klasse, die sich auch unter „ganz Gabbro
      verifiziert" nicht aufloest** *(gemessen 2026-08-17)*. F7 -- das Fragment, das
      vollstaendig abgesenkt und an der Ausfuehrung gemessen ist -- besteht aus **sieben**
      Rufen an Ruempfe, die Gabbro nie sieht; jede Sperre bringt vier Prototypen mit.
      **`gabbro zeugnis` zaehlt sie je Datei.** *Was fehlt, ist die andere Haelfte: eine Form,
      in der der Rufer die Pflicht des fremden Rumpfes AUSSPRICHT statt sie nur zu unterstellen
      -- die Sperre etwa schuldet gegenseitigen Ausschluss, Fortschritt und die Rangordnung,
      und keine Zeile sagt das heute.*
      **Gemessen 2026-08-17: 48 fremde Ruempfe im Korpus, NULL sprechen ihre Pflicht aus.**
      `ensures` an einer Deklaration ohne Rumpf ist grammatisch seit jeher moeglich (geprueft,
      0 Fehler) -- *und kein Pass liest es.* Die Schicht hat damit zwei Haelften: die sieben
      Zeilen hinschreiben (kostet nichts) und den Pruefer sie in die Beweispflicht des Rufers
      tragen lassen (PL-Arbeit).

- [ ] **`ensures` ist wohlgeformt geprueft -- die EINLOESUNG fehlt** ⟨B⟩ *(nachgemessen
      2026-08-19)*. ~~Ein Tippfehler in einem `ensures` faellt nicht.~~ Er faellt seit dem
      2026-08-18 an `M109` und `M111`, an einem `impl fn` wie an einem rumpflosen
      `extern fn`; die Grundnamen loesen auf (Parameter, Globale, Konstanten, `result`).
      **Was offen bleibt, ist die andere Haelfte und sie ist die groessere:** dass der Rumpf
      die Zusage HERSTELLT, prueft niemand, und das ist Beweisersache. *Der kleinste naechste
      Schritt ist nicht der Beweis, sondern die Quantorbinder und `Self` -- die zwei
      Namensarten, die `sammle_namen_pred` heute nicht kennt.*

### Design — open decisions *(Teil)*

- [ ] **Quantify the axiom layer — the x86 half is runnable, the aarch64 half is NOT.**
      **As long as the number is missing, "memory-safe under A1…An" is a form without content.**
      * **x86: GEMESSEN am 2026-08-21** ([`messung/AXIOMSCHICHT.md`](messung/AXIOMSCHICHT.md)).
        **33 Annahmen, 6 nicht falsifizierbar** — und deren Gründe sind *nicht eine Währung,
        sondern vier*: zwei prinzipiell unwiderlegbar (Speichermodell), zwei am Messapparat
        hängend, eine gilt **nur auf der Testmaschine** (`x2apic_zweischritt`: *„qemu64 hat
        kein x2APIC"* — auf echter Hardware wäre sie falsifizierbar, und das ist die
        schwächste der sechs), eine über die Sprache.

        > **Und der Befund, der den Posten trägt: von den 27 benannten Sonden existiert
        > KEINE als Programm.** Der Ordner buchte das bisher für **zwei**. *Ein `falsifier`,
        > dessen Sonde nirgends ist, ist eine Zusicherung über das Ausbleiben einer
        > Widerlegung — R15 an der Axiomschicht.* Die Buchung war nicht falsch, sie war zu
        > klein, **und in der schmeichelhaften Richtung.**

        **Was bleibt, ist nicht die Zahl, sondern ein ORT FÜR SONDEN.** Solange es ihn nicht
        gibt, ist „falsifizierbar" eine Eigenschaft des Satzes, nicht des Ordners.
      * **~~aarch64~~ — BLOCKED, and not for reasons of time (2026-08-15).** The
        only aarch64 tree in the folder (`SEL4Lake/ARMTest/stm32mp25-kernel`) is **not a
        second kernel but an older snapshot of THE SAME lineage** — evidenced
        with `git log --follow`: `R099`, a rename with 99 % similarity from
        `sel4lake-cap` to `caprock-cap` (see [`dokumente/HISTORIE.md`](dokumente/HISTORIE.md), *Zwei Fundstellen
        aus einer Vererbung*). It lies outside git.
        **A counter-table from it would not be a second architecture but the same line
        counted twice** — exactly the error class this folder booked on 2026-08-15.
        *The number would not be imprecise but wrong, and in the flattering
        direction: it would evidence transferability where only a copy stands.*
      * **What it would take:** an aarch64 kernel with a lineage **of its own**, or the
        honest version of the sentence — *"measured for x86; for aarch64 no number stands,
        and the available tree cannot supply one."*

### Vom zweiten Arbeitslauf über Tafel C, 2026-08-20 — elf Befunde, keiner still *(Teil)*

### From the criterion ([`dokumente/BEWEIS.md`](dokumente/BEWEIS.md))



### «NL» — der Weg zu „nur noch eigene Logik" ([`dokumente/PLAN.md`](dokumente/PLAN.md)) — **PUNKT 1** *(Teil)*

- [ ] **NL.3 — `ensures` über WELTZUSTAND: AUFGESCHRIEBEN, nicht gebaut**
      *(gemessen 2026-08-21, [`messung/FREMDPFLICHTEN.md`](messung/FREMDPFLICHTEN.md))*.
      Sechs der zehn ausgesprochenen Fremdpflichten reden über Plätze
      (`ensures mmu_an_zahl == 1`, **sechsmal** in `beispiele/22` — nicht siebenmal, die
      siebte Klausel nennt `result`). **Sie kollidiert mit U4/U5 und wäre die erste Ausnahme
      davon.** *Gemessen, bevor gebaut wird:*
      * **15** nichtlokale Fakten sterben im ganzen Korpus, an **13** von **153** Rufstellen
        — das ist die **Obergrenze jeder denkbaren Ausnahme.**
      * **0** davon gäbe die gemeinte Ausnahme zurück: die sechs Klauseln hängen alle an
        `hochlauf`, und dort sterben an zwölf Rufstellen **null** Fakten. *Die fünf
        Weltzustandsnamen werden nirgends GELESEN.*

      **Regel A ist nicht erfüllt** — und der Auslöser für den Bau ist benannt und messbar:
      ein Programm, das einen Weltzustandsnamen nach dem Ruf liest. *Erst dann die Frage nach
      der FORM* — ein `ensures` über einen globalen Platz gilt nur, solange kein anderer ihn
      schreibt, und genau diese Rahmenbedingung hat U4/U5 heute nicht, weil es pauschal tötet.

      > **Dieser Posten stand bis zum 2026-08-21 ZWEIMAL da** (hier und unter «H2» als *„Die
      > häufigere Hälfte von Punkt 4"*) — W7, und der zweite trug als einzigen eigenen Inhalt
      > eine Zahl, die veraltet war (*„28 fremde Deklarationen"*; es sind 109). Er ist
      > gelöscht, dieser bleibt.

### Aus «H2» *(ausgefuehrt 2026-08-19, `H = 17 → 15`)* — der Rest, den der Lauf hinterliess *(Teil)*

- [ ] **Die Axiomschicht schuldet einen Satz ueber den SPERRABDRUCK** *(benannt 2026-08-19
      von `Gruppe_Erhaltung.thy`)*. Das Locale `zug` nimmt `voll i` als *„der Abdruck ist
      gehalten"* und schliesst daraus, dass niemand hinsieht. **Dass ein gehaltener Abdruck
      einen fremden Kern wirklich fernhaelt, ist eine Aussage ueber das SPEICHERMODELL** und
      faellt nicht in diesen Satz -- dieselbe Stelle, an der `paarung` ihre
      `release`/`acquire`-Sichtbarkeit schuldet.
      **ERLEDIGT 2026-08-21:** die benannte Annahme `sperrabdruck_haelt_fremde_kerne_fern`
      steht in der Axiomschicht und ist mit dem Locale `zug` verbunden — **Zahn 3 von 9 auf
      8.** *Der Satz selbst ist unveraendert; was sich geaendert hat, ist, dass ein Leser die
      Praemisse SIEHT, statt sie zu unterstellen.*

- [ ] **Die `until`-Bedingung eines `retry` wird NICHT begangen** *(gemessen 2026-08-21,
      beim Zählen der Fremdpflichten)*. Ein Ruf dort bekommt keine Fremdverengung — und,
      schärfer: **ein Ruf an eine Funktion, die es gar nicht gibt, fällt dort nicht.**

      ```
      if gibtsnicht() == 9 { … }              ->  Fehler: [K003] … is not declared here
      retry lesen until gibtsnicht() == 9 …   ->  0 Fehler (nur Hinweis E009)
      ```

      *Dieselbe Bauart wie die fünf blinden `PredArt`-Zweige, ein Konstrukt weiter:* ein
      Ausdrucksbaum, den kein Pass begeht, sieht von außen aus wie einer ohne Befund.
      Betrifft `m1.rs` (Verengung) und `kosten.rs` (`K003`). **Eine Giftprobe fehlt noch** —
      und sie ist die Bedingung dafür, dass der Posten überhaupt gebaut werden darf.

- [ ] **Die GNADENFRIST ist eine ANNAHME, keine Pruefung -- und hat noch keinen Ort**
      *(2026-08-18)*. `H011`/`H012` halten die zwei pruefbaren Haelften (nicht im eigenen
      Lesebereich, nicht ohne Schreibersperre). Dass kein Leser das alte Objekt mehr sieht,
      stellt kein statischer Pass her. **Sie gehoert dorthin, wo `progress` steht** -- und der
      Pruefer verlangt sie noch nicht: ein `rcu … reclaims` ohne eine benannte
      Gnadenfristannahme geht heute durch. *Dieselbe Regel wie `S003`, an einem anderen
      Konstrukt.*

      **GEBAUT am 2026-08-21 als `H015`** — und die Handprobe VOR dem Bau bestaetigte den
      Posten: `beispiele/43-gegenprobe.gab` traegt `rcu … reclaims` ohne Gnadenfrist und ging
      mit **0 Fehlern** durch. Gift 230, zwei Mutationen, beide gefangen.

      **Was offen bleibt, und es ist die schwaechere Stelle:** `H015` haengt am **Namen im
      Satz** statt an einem Grammatikplatz. Der saubere Weg braucht **null neue Woerter** --
      `rcu … reclaims P progress G;` -- kostet aber `ast.rs`, `parse.rs`, `SYNTAX.md` und drei
      `.gab`-Dateien. *Dann pruefte `H015` wie `S003` gegen die Annahmenliste statt gegen
      einen Satztext.* Dazu die S004-Haelfte: eine unfalsifizierbare Gnadenfrist.

- [ ] **`N024` endet an der DATEIGRENZE** *(gemessen 2026-08-21, Nebenbefund der
      Axiomschicht)*. `geraet_quittiert` (`beispiele/02`) und `vtd_srtp_quittiert`
      (`beispiele/09`) sind zwei Annahmen mit **verschiedenen Namen, identischem Satz und
      DERSELBEN Sonde** (`sonde_vtd_srtp`) — in einem Lauf über beide Dateien: **0 Fehler.**
      `N024` läuft je Übersetzungseinheit, und `manifest::vereinige` prüft nur die andere
      Richtung (gleicher Name → gleicher Inhalt).
      *Ein grüner Lauf entlastet dann beide, und eine davon hat nie jemand geprüft* — genau
      der Satz, mit dem `N024` selbst begründet ist. **Der Ort ist da, wo `vereinige` schon
      steht.**

### From wave 4 (2026-08-16) — two conditions and one candidate

- [ ] **«B39» — GEMESSEN am 2026-08-21, und die Antwort war „nicht bauen"**
      ([`messung/TRAEGER-UND-HARDWARE.md`](messung/TRAEGER-UND-HARDWARE.md)). Die Kollision
      zwischen Hardwareaxiom und K-Bedingung **tritt nicht ein und kann es nicht:** `group`
      hat keine `ops`-Klausel und `walk` kein `by ops`. **`R001` sieht einen `walk` in KEINEM
      Raum** — nicht bloß im `normal`-Raum, wie [`dokumente/FRAGMENTE.md`](dokumente/FRAGMENTE.md)
      schreibt; *der Satz dort ist zu freundlich* (Gegenprobe: `gift/58` fällt sehr wohl).

      **Was offen BLEIBT, ist kleiner und hat eine Adresse:** `mmu_schreibt_nur_a_und_d` (A7)
      ist mit nichts verknüpft — **`ein_kern` ist der einzige Annahmenname, den überhaupt ein
      Pass liest.** *Ein Axiom, das eine Schreibstelle erlaubt, die keine Regel kennt, ist
      eine stille Ausnahme mit einem Namen darauf.*
      **Fällig wird der Bau, wenn die Seitenmaschinerie einen erzeugten Träger bekommt** —
      vorher wäre `hardware A, D;` Spalte 1 der Konvergenzwette ohne gemessenen Bedarf.

- [ ] **`reserved` hat KEINE Prüferregel — es beißt im C-Übersetzer** *(gemessen 2026-08-21,
      beim Nachrechnen der Begründungsanalogie von «B39»)*. `./instrumente/pruefe-klauseln.py`
      führt `reserviert / FeldDecl` unter **NUR GETRAGEN**; ein `p.reserviertes_feld = 1;`
      gibt **0 Fehler**, und `gabbro emit` ruft danach einen Setzer, den `emit.rs`:2228 nie
      definiert — `cc -Werror` meldet eine implizite Deklaration. **Die falsche Meldung, im
      falschen Werkzeug, hinter dem Rücken der elf geprüften Klassen.**
      *Und die Messung kann nicht trennen, ob `reserved` nicht beißt oder ob ein Feldschreiben
      über einen Zeiger gar nicht aufgelöst wird* — die Kontrollprobe auf ein nicht
      existierendes Feld fällt genauso wenig. **Dieselbe Klasse wie „ein unbekannter TYPNAME
      fällt nirgends".**

- [ ] **`lock … masks irqs` liest niemand** *(gemessen 2026-08-21)*.
      `./instrumente/pruefe-klauseln.py`: `maskiert / LockDecl` steht unter **UNGELESEN** —
      *„der Leser füllt sie, niemand sieht hin"*. `H101` deckt seit heute den Träger in der
      **Wirkungsliste**, nicht das Sperrattribut. *Zwei Schreibweisen für dieselbe Sache, und
      nur eine hat einen Leser.*

---

# STUFE 7 — WAS PROGRAMME GROSS MACHT  ⟨A⟩

**`fnptr` — erst der Erzeuger, dann der Vertrag: GEBAUT am 2026-08-21**
([`messung/FNPTR.md`](messung/FNPTR.md)). Ein Funktionszeiger entsperrt jede
Dispatch-Tabelle, jede Treiber-ops-Struktur, jede Scheduler-Politik — Caprocks
`&mut dyn SchedOps` ist genau das. ~~Heute hat `fnptr` null Korpusstellen und keinen
Erzeuger: die Sprache kennt kein `&f`.~~ *(überholt am 2026-08-21, nachgezogen am
2026-08-25)* **Alle vier Hälften stehen:** der Erzeuger
`&f` (`ExprArt::FnWert`, `M127`/`M128`), der Ruf über einen ORT (`CallTarget::Place`,
`M129`), die Absenkung (`bool (*bereit)(void);` und `t->senden(b)`) und der Vertrag am
Zeigertyp (`N035`–`N037`). [`beispiele/49-dispatch-tabelle.gab`](beispiele/49-dispatch-tabelle.gab)
prüft mit **0 Fehlern** und senkt ab.

> **Und der Satz stand vier Tage länger, als er wahr war** *(nachgezogen 2026-08-25)*.
> Er sagte nicht *„hier ist noch etwas offen"*, sondern *„die Sprache kennt es nicht"* —
> **er verhindert Arbeit, statt sie zu verzögern**, und das ist genau die Klasse von
> [`instrumente/pruefe-widerruf.py`](instrumente/pruefe-widerruf.py). *Der Wächter konnte
> ihn nicht fangen, und das ist kein Mangel des Wächters:* sein eigener Kopf sagt
> *„er ist ein Gedächtnis, kein Urteil"* — er findet, was jemand als widerrufen
> aufgeschrieben hat, und niemand hatte. **Seit heute steht er als `WB2` drin.**

*In der anderen Reihenfolge wäre der Vertrag eine Zusage ohne Einlöser gewesen — die
Bewegung, gegen die K100s zweites Tor steht.*

- [ ] ~~**Ein unbenannter Parameter im Zeigertyp ist nicht schreibbar**~~ — **GESCHLOSSEN
      am 2026-08-25**, und der Befund geht über die Reparatur hinaus. `fn(u8)` fiel an `P002` (*„`u8` is a word of the vocabulary, not an
      identifier"*), `fn(b : u8)` parste. **Alle 11 Zeigertypstellen in
      `../caprock-messbasis` schreiben ohne Namen, null von elf mit** — die Vorlage nach
      Regel B kannte nur die Form, die die Grammatik nicht hatte. *Am 2026-08-21 trat
      `params` an die Stelle von `typelist`, damit eine Wirkungszeile am Zeigertyp einen ORT
      nennen kann; das war richtig und hat nebenbei die vorige Form weggenommen.*
      **Der teure Teil ist der zweite:** `N035` (*„kein Vertrag am Zeigertyp"*, gebaut
      2026-08-21) hatte in den Fragmentkorpus **null Reichweite**, weil der Leser die Form
      vorher abwies. `messung/fragmente/F03.gab`, dieselben fünf Zeilen:
      **23 Items / 5 Leserabsagen** vorher, **24 Items / 5 `N035`** nachher — und die
      Fehlerzahl blieb bei 11, in beiden Läufen. *Eine Regel kann durch eine Form, die der
      Leser ablehnt, nicht beissen, und von aussen sieht der Lauf gleich aus.*
      Abnahme: `cargo run --bin gabbro -- pruefe messung/fragmente/F03.gab` nennt fünf
      `N035` und keine `P002`/`P003`.

Dazu die **ABI** (Bibliotheken, die sich mischen lassen) und die **Generizität** — ohne sie
braucht jede Tabelle ihr eigenes `traverse`.

- [ ] **Die Wirkungsliste des Rufers RECHNEN statt verlangen — der größte Einzelposten des
      Nutzbarkeitsmaßes** *(gemessen 2026-08-20, `A4`)*. **Im echten Code sind 14 von 14
      ableitbaren Stellen Wirkungszeilen, die ein Gerufener ohnehin erklärt**; im Lehrkorpus
      47 von 51. `aufrufgraph::huelle_der_gerufenen` trägt sie schon über den Aufrufrand,
      samt Abbildung auf die Argumente — *die Rechnung existiert, nur verlangt der Prüfer die
      Zeile trotzdem.*
      **Und sie darf nur auf EINE Weise fallen:** die Liste wird gerechnet und **gedruckt**
      (`gabbro abi`), nicht weggelassen. Sie ersatzlos zu streichen machte `E008` rückgängig —
      den Posten, der `effects` am 2026-08-15 erst kompositional gemacht hat, *als eine
      `pure`-Zusage noch an der ersten Aufrufgrenze endete.* **Ohne den Druck wandert eine
      neue Wirkung stillschweigend nach oben durch, und das ist die verbotene Richtung.**

- [ ] **Ein `reason`-Wert hat KEINEN ERZEUGER — und das ist «B9» ein zweites Mal**
      *(gemessen 2026-08-20 am vervollständigten Fragmentkorpus)* — ~~offen~~ **GEBAUT am
      2026-08-21** ([`messung/ERZEUGER.md`](messung/ERZEUGER.md) Posten 1: sieben Absagen,
      acht eigene Giftproben, zehn Mutationen, ein Beispiel), **nachgezogen am 2026-08-25**.
      `R::F` ist seither die Schreibform (`reasonval`,
      [`dokumente/SYNTAX.md`](dokumente/SYNTAX.md):517), `Typ::Grund` trägt sie im Typmodell,
      `M126` sagt ab, wenn `R` kein erklärter `reason` ist, und `M124` hält die drei
      Stellungen auseinander, durch die ein Grund gehen darf.
      [`beispiele/48-grund-mit-erzeuger.gab`](beispiele/48-grund-mit-erzeuger.gab) ist das
      Beispiel dazu, und der Erzeuger schreibt `*_grund = HolFehler_Leer;` ins C.

      > **Und dieser Posten ist der ZWEITE stehengebliebene Satz derselben Klasse an einem
      > Tag** — der erste ist der Kopf dieser Stufe, `WB2`. *Beide sagten nicht „offen",
      > sondern „die Sprache hat es nicht", beide waren am 2026-08-21 gebaut, und beide
      > standen vier Tage.* Der Widerrufswächter kannte keinen von beiden und las die
      > Berichtsdatei nicht, in der die Wahrheit stand; **seit heute liest er `messung/`.**

      *Gefunden an F1, F3 und F5, sobald die fehlenden Deklarationen dastanden — der
      eingefrorene Korpus konnte es nicht zeigen.*

### K100 — der Weg auf 100 % Klempnereiabdeckung ([`dokumente/PLAN.md`](dokumente/PLAN.md)) *(Teil)*

- [ ] **Nachgemessen 2026-08-20: die Schnittstelle faellt LAUT, nicht lautlos.** Zwei
      Dateien in EINEM Lauf werden weiter getrennt geprueft — jede ist ihre eigene
      Uebersetzungseinheit. Ein `use bib::tu;` ueber die Dateigrenze ergibt **`E009`**
      (*„`tu` is unknown to the graph"*) und **`K003`** (*„promises costs, but `tu` is not
      declared here"*), also einen FEHLER. *Der Eintrag oben sagt „faellt lautlos auf untere
      Schranke zurueck" — gemessen faellt sie nicht durch, sie faellt.* **Was fehlt, ist
      nicht der Riegel, sondern die Bruecke.** Und `pub` hat seit dem 2026-08-19 einen Leser
      (`N025`) — die Sichtbarkeitshaelfte einer API steht damit. Der Erzeuger schreibt
      weiterhin **keinen Kopf**: eine `.c` je Einheit, Prototypen inline.

- [ ] ~~**Eine Bibliotheks-ABI, und das Format steht schon**~~ — **GEBAUT am 2026-08-21,
      und der Befund lag NICHT dort, wo dieser Posten ihn vermutete**
      ([`messung/ABI.md`](messung/ABI.md)).

      **`ABI0`/`ABI1` waren schon gebaut:** `gabbro abi` schrieb ein `.gabi`, `pruefe --mit`
      las es. **Was fehlte, war die MAUT.** `abi.rs` trug `ItemArt::Lock` nie — die
      Schnittstelle exportierte `effects { locks SPEICHER }` und **nicht** `lock SPEICHER …
      rank 0`. `H012` schlug den Rang nach, fand nichts und **`continue`te im Schweigen.**

      > **Ein Programm aus zwei Bibliotheken, das beide Sperren in beiden Richtungen
      > schachtelt — ein Deadlock — ging mit `0 Fehler, 0 Hinweise` durch.** Genau der
      > Ausgang, den der Auftrag schlimmer nennt als gar nicht zu bauen, und er war der
      > Zustand *vor* dem Bau.

      **Die Wurzel lag eine Ebene tiefer, INNERHALB einer Einheit:** ein undeklarierter
      Sperrname war für die ganze Sperrdisziplin unsichtbar — eine Datei, die `NIEDA` zweimal
      nennt, gab **4 Items, 0 Fehler, 0 Hinweise.** Geschlossen als **`H016`**, dem Spiegel
      von `H008`: *genommen, aber nie erklärt.*
      Dazu trägt `abi.rs` jetzt die `lock`-Zeile, und `emit --mit` kam dazu — *ohne ihn war
      die ABI halb: prüfbar, nicht übersetzbar.*

- [ ] **Die schärfste Behauptung dieses Ordners über die ABI war FALSCH** *(nachgerechnet
      2026-08-21)*. Hier stand: *„zwei Bibliotheken mit unabhängig vergebenen Rängen ergeben
      einen ZYKLUS, den keine von beiden allein sehen kann."*

      **Unabhängig vergebene ABSOLUTE Ränge können keinen Zyklus erzeugen** — eine
      Rangfunktion in die ganzen Zahlen ist eine Totalordnung, und eine Totalordnung hat
      keine Zyklen. Was sie erzeugen, ist eine **willkürliche** Ordnung: falsche Absagen,
      nicht falsche Freisprüche. *«ABI2» ist damit eine Frage der Ausdruckskraft, nicht der
      Verklemmungsfreiheit.*

      > **Das eigentliche Loch war schlimmer und von anderer Art:** es überquerten
      > **gar keine Ränge** die Grenze. *Ein Satz, der die Gefahr an der falschen Stelle
      > vermutet, ist teurer als keiner — er lenkt die Suche weg.*

      Offen bleibt daraus die echte «ABI2»-Frage: wie zwei unabhängig vergebene Rangskalen
      zueinander gestellt werden, ohne dass eine Bibliothek die andere umnummeriert.

- [ ] **Der Korpus hat keine ABI, und die beruhigende Zahl misst nichts** *(gemessen
      2026-08-21)*. Jedes erzeugte `.gabi` durch den Prüfer zurückgefahren gibt *„49 sauber,
      0 Fehler"* — **48 davon sind LEER**, und keines trägt eine Sperre.
      *Eine Deckungszahl über einer leeren Menge ist die Form, gegen die W17 steht.* **Der
      ganze Beleg der ABI ruht auf sechs handgeschriebenen Dateien**, und das steht so im
      Bericht.

- [ ] **`observes NIEDADOM` ohne `rcu`-Deklaration gibt 0 Fehler** *(gemessen 2026-08-21)*.
      `H016` hat die Sperr-Instanz eines allgemeineren Lochs geschlossen: **ein genommener
      Name, den niemand erklärt hat, ist für den zugehörigen Pass unsichtbar.** Dieselbe
      Gestalt, ein Konstrukt weiter — und dort steht sie noch offen.
- [ ] **Genericity** — without it every table needs its own `traverse`; with it the question
      of how contracts are parameterised.
      **Und vor dem Bau steht eine ZÄHLUNG, nicht eine Reihenfolge** *(2026-08-21)*. *„Sonst
      braucht jede Tabelle ihr eigenes `traverse`"* ist eine **Vorhersage**, und die Zahl dazu
      ist erhebbar: **wie viele duplizierte Traversierungsrümpfe stehen heute im Korpus, und
      wie viele blieben nach Monomorphisierung?**
      Generizität ist der größte Einzeleingriff der offenen Liste — Grammatik,
      Vertragsparametrisierung, Monomorphisierung, mindestens zwei Schablonen — und der
      einzige Posten, bei dem [`dokumente/PLAN.md`](dokumente/PLAN.md) selbst vermutet, dass
      **zwei geforderte Eigenschaften einander widersprechen.**
      > **Ein Bau ohne Zählung wäre der erste dieser Liste, der ohne gemessenen Bedarf
      > beginnt** — und damit dieselbe Bewegung, die `locks ordered` getötet hat.

      **GEZÄHLT am 2026-08-21, und die Zahl ist NULL**
      ([`./instrumente/zaehle-traversierungen.py`](instrumente/zaehle-traversierungen.py)):

      ```
      22 Traversierungsruempfe stehen heute im Korpus
      22 blieben nach Monomorphisierung
       0 duplizierte Ruempfe  — streng UND unter der weitesten Lesart, die zu verteidigen ist
      ```

      Nicht klein, sondern null, und unter **beiden** Normalisierungen. Belegt statt
      behauptet: 12 Paare liegen über 85 % Ähnlichkeit, jedes einzeln nachgesehen. Das
      nächste (98,9 %) unterscheidet sich **in einem `!`** — *kein Typparameter der Welt
      entfernt eine Verneinung*; die vier Widerrufsschleifen unterscheiden sich in der
      **Argumentliste**, also in einem **Wert**parameter, und was sie zusammenzöge, wäre eine
      höherstufige Traversierung — ein anderes Konstrukt.

      > **Die Vorhersage trifft auf diesen Korpus nicht zu.** Die 22 Rümpfe sind nicht
      > verschieden, weil die Tabelle verschieden ist, sondern **weil die Aufgabe verschieden
      > ist.** *Die Null widerlegt die Begründung, nicht die Entscheidung* — wer Generizität
      > weiter will, braucht ein anderes Argument als dieses.

      **Und die Gegenrichtung steht im Werkzeug, nicht in einer Fußnote:** ein Rumpf, den
      jemand *nicht geschrieben hat*, weil ihm Generizität fehlte, hinterlässt im Text keine
      Spur. Diese Zählung findet ihn nie (W10).

### «ABI» — Bibliotheken, die sich mischen lassen, entworfen 2026-08-20 ([`dokumente/PLAN.md`](dokumente/PLAN.md))

*Eine Bibliotheksgrenze ist kein Riegel, sondern eine **Brücke mit Maut**. Eine ABI, die
Zusagen ungeprüft weiterreicht, macht aus elf geprüften Klassen elf behauptete.*

- [ ] **ABI0/ABI1 — `.gabi`: das Zeugnis, maschinenlesbar, und `gabbro pruefe --mit`.**
      `gabbro zeugnis` schreibt heute für Menschen, was die Übersetzung trägt; die ABI ist
      dieselbe Aussage in einer Form, die der Prüfer liest. Danach verschwinden `E009` und
      `K003` an der Dateigrenze — **weil geprüft wird, nicht weil geschwiegen wird.**

- [ ] **Ein unbekannter TYPNAME fällt nirgends** *(gemessen 2026-08-20, beim Merge)*.
      `pub extern fn f(x : GibtsNicht)` gibt **null Fehler**; `table T count FEHLT { slot { a :
      AuchNicht, } }` ebenso — weder der Typ noch die `count`-Konstante wird aufgelöst.
      **Gefunden nicht durch Nachdenken, sondern weil `gabbro abi` eine Schnittstelle schrieb,
      die zwei Namen nannte und keinen erklärte** — und die Selbstprobe schwieg dazu.
      *Ein Namenspass, der unbekannte Namen durchlässt, ist an einer Bibliotheksgrenze mehr
      als eine Lücke: dort kommt JEDER Name von woanders.* Die mechanische Hälfte ist zu
      (die Schnittstelle sammelt bis zum Fixpunkt), die Regel fehlt. **Vor ABI3**, denn die
      Vereinigung zweier Zeugnisse ruht darauf, dass beide Seiten dieselben Namen meinen.

- [ ] ~~**Darf eine `pub`-Signatur einen privaten Namen nennen?**~~ — **ENTSCHIEDEN und
      gebaut am 2026-08-25: NEIN, und sie fällt an `N038`** (`crates/gabbro-check/src/bindung.rs`).
      Der Eintrag stand hier als *„eine Sprachentscheidung, keine Bauarbeit"*, und das war
      richtig; die Entscheidung ist die zweite Lesart geworden. **Möglich wurde sie erst,
      als `table`, `device`, `format` und `lock` ihr `pub` bekamen** — vorher KONNTE ein
      Träger gar nicht privat sein, und die Nachziehschleife war nicht Bequemlichkeit,
      sondern die einzige Form, in der eine Schnittstelle überhaupt geschlossen sein konnte.
      *Der Fixpunkt in `abi.rs` ist damit ersatzlos weg: die Ausfuhrmenge steht geschrieben.*

- [ ] **Ein `pub static` überlebt die Bibliotheksgrenze NICHT — und nichts sagt es**
      *(gemessen 2026-08-25, beim Bau von `N038`)*. Der Erzeuger senkt **jeden** Weltzustand
      zu einem C-`static` ab, also zu INTERNER Bindung. Eine `.gabi` trägt ein
      `pub static mut zaehler` mitsamt Anfangswert hinaus — und die Einheit des Importeurs
      erzeugt daraus **ihre eigene zweite Kopie**:

      ```
      w1.o: 0000000000000000 b zaehler      -- die Bibliothek
      w3.o: 0000000000000000 b zaehler      -- der Nutzer, ein ANDERES Objekt
      Nutzer sieht 0, die Bibliothek sieht 2
      ```

      Der Prüfer sagt **0 Fehler, 0 Hinweise**, `cc -Werror` übersetzt, der Binder bindet,
      und die beiden Seiten schreiben in verschiedene Variablen. *Das ist genau die Klasse,
      die `abi.rs` in seinem eigenen Kopf ausschliesst* — **„was eine ABI ausdrücklich nicht
      darf: eine Klasse von geprüft auf behauptet absenken"** —, nur eine Stufe tiefer: hier
      wird nicht abgesenkt, sondern **verdoppelt**.

      **Dieselbe Klasse, zweite Instanz: eine `pub table`, die der IMPORTEUR bei ihrem Namen
      anspricht.** `Kaesten.slots[i].wert` beim Nutzer ergibt ein zweites
      `static Kaesten Kaesten_speicher;` in seiner Einheit — er liest seine eigene leere
      Tabelle. Die durchgestochene Probe (`pruefe-emission.sh`, Stufe 10) geht nur deshalb
      durch, weil ihr Nutzer den Träger **ausschliesslich über Funktionen** anfasst.

      > **Und `N038` treibt in genau diese Ecke.** Wer `effects { writes z }` exportiert,
      > MUSS `z` seit heute `pub` schreiben — die Regel ist richtig und macht diesen Weg
      > zum normalen.

      Der Grund, warum es hier steht und nicht gebaut ist: **der Erzeuger kann nicht
      unterscheiden, welche Items aus dem `--with`-Vorspann kommen.** Der Vorspann wird
      textlich vorangestellt, und `emittiere` sieht einen Baum. Zwei Formen sind denkbar,
      und beide sind eine Entscheidung und keine Reparatur:
      *(a)* die `.gabi` schreibt Weltzustand **ohne Anfangswert** in einer eigenen Form, und
      der Erzeuger macht daraus ein C-`extern`;
      *(b)* `emittiere` bekommt die Vorspanngrenze und senkt Importiertes als `extern` ab.
      *Bis dahin ist die Zahl der betroffenen Stellen im Korpus **null** — `pub static` und
      `pub atomic` kommen in keiner einzigen Datei vor.*

- [ ] **Ein `static`, den niemand nennt, fällt nirgends auf** *(2026-08-20)*. Der Erzeuger
      setzt seit heute `__attribute__((unused))` an jeden — richtig, weil `36-asm.gab` sein
      `GERAET` **im `asm`-Block** schreibt und der C-Übersetzer das nicht sehen kann.
      **Damit ist aber auch der echte Fall stillgelegt:** ein Weltzustand, den kein
      `effects` und kein Rumpf nennt. *Die Warnung gehört auf die Gabbro-Ebene* — dieselbe
      Klasse wie das `(void)k;` beim ungelesenen Parameter, und derselbe fehlende Pass.

- [ ] **`M117` liest nur die ÄUSSERE Typform eines Items.** Typ, Parameter, Rückgabe,
      `const`, `static` — ein leerer Bereich tief in einem Verbundfeld oder einem
      Array-Element fällt nicht auf. Dahinter steht `IntBereich::ist_leer()` als Riegel, der
      aus dem Leeren `None` macht statt zu rechnen; *ein Riegel ist aber keine Absage*, und
      der Anwender erfährt nichts.

### Vom zweiten Arbeitslauf über Tafel C, 2026-08-20 — elf Befunde, keiner still *(Teil)*

- [ ] **ABI2 — ORDNUNG statt RANG, und das ist eine SPRACHÄNDERUNG.** `lock … rank 0` ist
      eine absolute Zahl; zwei unabhängig geschriebene Bibliotheken vergeben beide `rank 0`.
      **Absolute Zahlen komponieren nicht.** Die ABI trägt `KAPPEN vor OBJEKTE`, und beim
      Vereinigen rechnen `H006`/`H012` auf dem Graphen weiter — *ein Zyklus ist die Absage,
      die keine der beiden Bibliotheken allein sehen kann.* **Steht vor ABI3**, weil eine
      Sprachänderung nach dem Bau der Vereinigung jede geschriebene ABI-Datei bricht.

- [ ] **ABI3 — die Vereinigung ist die VEREINIGUNG.** Ein `UNPROVED` in irgendeiner
      Bibliothek färbt das ganze Erzeugnis; verschiedene Darstellungen desselben Typs
      (`option`-Sonderwert, `count`) sind eine Absage und keine Umrechnung; verschiedenes
      `arch` mischt nicht. *Die Vertrauensfläche einer Mischung ist die Vereinigung, nie der
      Durchschnitt.*

- [ ] **ABI4 — `annimmt { … }`: ein `override` ist eine BEWEISPFLICHT, keine Ersetzung.**
      Eine Bibliothek wurde **unter** ihrer Annahme geprüft; wer die Annahme austauscht,
      tauscht die Voraussetzung ihrer Beweise aus — **die Beweise wandern nicht mit.** Drei
      Fälle, getrennt: *wortgleich* → nichts; *stärker* → `A_neu ⟹ A_alt` wird eine gezählte
      Pflicht (die Implikation ist nicht mechanisch entscheidbar, also wird sie gezählt und
      nicht geraten); *`entfaellt`* → dieselbe Pflicht ohne Ersatz. **Schwächer oder
      unvergleichbar ist eine Absage**, es sei denn, der Importeur schreibt `reopens { … }`
      und nennt einzeln, welche Zusagen damit auf unbewiesen zurückfallen. *Ohne diesen
      Riegel wäre ein `override` das perfekte Werkzeug, eine unbequeme Annahme
      wegzudefinieren — und das Erzeugnis sähe danach besser aus als vorher.*

### The four items to the goal — plan with gates in [`dokumente/PLAN.md`](dokumente/PLAN.md) §A

**The goal is: Gabbro proves everything except functional correctness.** Read against this goal
the greater part of the 31 fragment findings falls away (`dokumente/PLAN.md` §A, resorting) —
what remains is four, and **one of them is not solved but grazed**.







- [ ] **A2 — RUN: dynamic calls are forbidden, `fnptr` needs no contract.**
      The two dynamically used traits have ONE implementation each. **New and
      undecided: 64 closures** (`dyn FnMut`/`Fn`) — Gabbro has none, and what becomes of them
      (embedding, pointer plus context, prohibition) stands nowhere.

- [ ] **Ein Gabbro-Programm ist heute GENAU EINE Übersetzungseinheit — und vor der Wahl eines
      Bausystems stehen drei Sprachfragen** *(gemessen 2026-08-24, aufgeworfen durch den
      Vorschlag „Meson")*.

      ```
      moduledecl = [ "pub" ] "module" path "{" { item } "}" ;   # SYNTAX.md:258 -- ein BLOCK
      usedecl    = [ "pub" ] "use" path ";" ;                   # ein Pfad, KEINE Datei
      ```

      **Es gibt keinen dateiübergreifenden Import**, `gabbro` hat kein Bau-Verb (15 Befehle,
      keiner davon baut), und `emit` arbeitet je Datei. *Damit gibt es nichts zu bauen*: 49
      Beispiele, 10 Fragmente, drei echte Stücke — jedes eine Datei, ein `cc`, ein
      Binärprogramm.

      **Die drei Fragen, alle sprachlich, keine davon Werkzeugwahl:**

      | | |
      |---|---|
      | **(a)** | sieht eine `.gab` die Deklarationen einer anderen — und mit welcher Regel über `pub`? |
      | **(b)** | **komponiert das Zeugnis?** A nimmt an, B verengt — was nimmt das PROGRAMM an? *Davon hängt ab, ob „speichersicher unter A1…An" für ein mehrteiliges Programm überhaupt formulierbar ist* |
      | **(c)** | wer besitzt den `#include`-Graphen des erzeugten C? |

      **(b) ist die teure.** Die anderen zwei sind Konvention; diese entscheidet, ob die
      Annahmemenge eine Eigenschaft der Datei oder des Programms ist.

      > **Der Auslöser, gemessen statt terminiert:** das erste Gabbro-Programm, das über mehr
      > als eine Übersetzungseinheit geht und einen Linkschritt braucht. **Bis dahin IST
      > `pruefe-emission.sh` das Bausystem** — und es prüft mehr, als ein voreingestelltes
      > prüfen würde: zweimal emittieren und bitgleich, Lizenzhinweis, `cc -Werror` bei `-O0`
      > und `-O2`, UBSan, das `zeugnis`, seit P6 die erzeugten Theorien.

      **Und was die Werkzeugwahl dann NICHT ist: frei.** Im Strangler (P8) liegt genau eine
      Linkerzeile, und `cargo` besitzt sie: Caprock baut mit `Cargo.toml` + `kernel/build.rs`
      + `rustup nightly` (`-Z build-std`), das Linkerskript über `cargo:rustc-link-arg`.
      *`kernel/build.rs` beginnt mit vierzig Zeilen über eine BEZAHLTE Falle* — Cargo mischt
      `.cargo/config.toml` aus jedem Vorfahrenverzeichnis, `-T` stand zweimal auf der
      Linkerzeile, `lld` wertete `SECTIONS` zweimal aus, **der Bau lief durch und das Abbild
      bootete nie.** Wer diesen Treiber ersetzt, trägt die Falle an einen Ort, an dem noch
      niemand für sie bezahlt hat.

      | Ziel | Treiber |
      |---|---|
      | **Caprock, im Strangler** | `cargo` bleibt, `build.rs` ruft `gabbro emit` |
      | **eigenständige Programme** (Treiber, Userspace) | **Meson** — `custom_target` und Cross-Dateien passen genau |

      > **Ein `custom_target`, das `gabbro emit` ruft und das `.c` an `cc` weiterreicht, ist
      > gegenüber heute ein RÜCKSCHRITT im Prüfen — und er sieht grün aus.** Das ist die
      > Klasse, gegen die dieser Ordner steht, und sie gilt für jedes Bausystem gleich.

---

# D2 AUF DEN PRÜFER ANGEWANDT — was der `CallTarget`-Griff verallgemeinert  ⟨A⟩

**Beim Bau von `fnptr` wurde `Ruf.pfad: Pfad` zu `Ruf.ziel: CallTarget` — ein Summentyp ohne
Auffangzweig.** Der Übersetzer zählte daraufhin **72 Passstellen in 14 Dateien** auf, an denen
der Gerufene aufgelöst wird. *Schweigen war kein Vorgabezweig, sondern ein Übersetzungsfehler,
und jede Stelle bekam ihre Antwort mit ihrem Grund im Quelltext.*

> **Das ist D2, auf den Prüfer selbst angewandt** — dieselbe Medizin, die die Sprache ihren
> Nutzern verschreibt: *undurchsichtige Typen ohne stille Umwandlung.* Und es ist die dritte
> oder vierte Instanz desselben Musters (der Registerabdruck in `entry`, das erschöpfende
> `match` mit `-Wswitch` als zweitem Leser).

**Und es steht in scharfem Kontrast zu dem, was der Grunderzeuger fand:** 53 `match`es über
`ExprArt` mit `_`-Zweig, während der Übersetzer nur fünf erzwang. *Ein Grundwert rutschte
durch sieben Positionen still.*

- [ ] **Ein Durchgang: wo steht sonst `Option` oder `_`, wo ein Summentyp die
      VOLLSTÄNDIGKEIT erzwingen würde?** *(gestellt 2026-08-21, nachdem ein einziger
      `Option → enum`-Wechsel 72 begründete Antworten erzwang)*. Die Fläche, gemessen:

      ```
      138 `Option<`-Stellen im Prüfer
      155 Auffangzweige über einem AST-Summentyp
          parse.rs 32 · emit.rs 28 · namen.rs 17 · m1.rs 15 · wirkungen.rs 9
      ```

      **Nicht jeder davon ist ein Fund** — ein `_`-Zweig über `Kw` ist richtig, ein `Option`
      für *„nicht angegeben"* auch. *Die Zahl ist eine obere Schranke und eine Arbeitsliste,
      kein Urteil.* **Erwartet wird eine Trefferquote wie bei den letzten drei Wächtern**, und
      die war jedes Mal höher, als vorher jemand geschätzt hätte.
      **Die Reihenfolge nach Gewicht:** `parse.rs` und `emit.rs` tragen zusammen 60 der 155,
      und `emit.rs` ist die Fläche, über die `244 von 244` ausdrücklich nichts sagt.

- [ ] **Ein Deckungssprung gegen den Vorlauf ist selbst ein Prüffall** *(2026-08-21)*. Beim
      `fnptr`-Bau fiel die Deckung einer Handprobe auf **25 %** — und wurde **gedruckt**, statt
      die Datei abzulehnen. *So ist es richtig gebaut: eine Ablehnung wäre ein Urteil, ein
      Druck ist eine Messung.* **Aber eine gedruckte 25-%-Deckung, die niemand ansieht, ist
      ein stiller Ausfall MIT Beleg** — und das ist die schlechteste Sorte, weil sie sich
      hinterher als „stand doch da" verteidigen lässt.
      **Gehört zur Arbeitsmengen-Regel (W17):** nicht die Deckung selbst wird bewacht, sondern
      ihr SPRUNG gegen den vorigen Lauf. *Wer eine Zahl druckt, die niemand vergleicht, hat
      sie nicht gemessen, sondern nur ausgegeben.*

---

# DIE KLASSE «RENNEN», JE RENNFORM AUFGESCHLÜSSELT — und die Grenze läuft anders als gebucht  ⟨C⟩

- [ ] **`A4` ist gemessen und wird NICHT gebaut — der Auslöser steht** *(2026-08-24,
      [`messung/RACE.md`](messung/RACE.md) §1.2)*. Ein atomares RMW je Objekt braucht ein
      atomares SLOTFELD; `atomic` ist heute ein Item. Gemessen am Ziel:

      ```
      575  globale `static … : Atomic…`   -- Gabbro traegt das heute
       20  atomare Felder JE OBJEKT       -- die Form, um die es geht
      ```

      **Und die zwanzig sind es nicht:** 4 sind eine Ticket- und eine Leser-Schreiber-Sperre
      (**Code, den Gabbro ersetzt**), 10 sind Statistikzähler einer *einen* Konsole, 6 der
      Hochlaufzustand *einer* SMMU. *Kein einziger ist ein Refcount je Objekt.*

      > **Der Fall, der `A4` aufgeworfen hat, stammt aus dem ZWEITEN Korpus** — und der liegt
      > bis heute nicht dort, wo gerechnet wird. **Ein Konstrukt für einen Fall aus einem
      > Korpus, den niemand messen kann, ist die Bewegung, gegen die R7 steht.**

      **Auslöser:** eine Stelle im Ziel, die es braucht — oder eine Zählung über dem zweiten
      Korpus, die eine KLASSE zeigt statt eines Falls.

**`README.md` sagt seit Wochen: *„race hängt an der Axiomschicht"*. Gemessen am 2026-08-21
stimmt das nicht** ([`messung/RACE.md`](messung/RACE.md)):

```
Von 28 unterschiedenen Rennformen tragen
  21  auf einer REGEL
   2  auf der AXIOMSCHICHT
   1  auf beidem
   4  auf NICHTS
```

> **Die Klasse hängt nicht an der Axiomschicht — sie hängt an ihr an genau DREI Stellen**,
> und an drei weiteren an etwas anderem: **dem Alias**, der im Ordner bis heute keine Zahl
> hatte. *Ein Satz, der die Last an der falschen Stelle vermutet, lenkt die Suche weg* —
> dieselbe Klasse wie die falsche Zyklusbehauptung bei der ABI, am selben Tag.

- [ ] **Vier Rennformen tragen auf NICHTS** *(gemessen 2026-08-21)*. Sie stehen einzeln in
      [`messung/RACE.md`](messung/RACE.md). *Das ist die eigentliche Lücke der Klasse, und sie
      war bisher hinter dem Satz „hängt an der Axiomschicht" unsichtbar.*

- [ ] **`H011` und `H012` tragen je ZWEI verschiedene Regeln — und vier Zeilen der
      Renntafel stehen auf ihnen** *(2026-08-21)*. **Eine ausfallende Regel bleibt grün, weil
      die andere denselben Code schreibt.** Dieselbe Klasse wie die fünf Parserkennungen, nur
      an der Stelle, an der die Rennabdeckung ihre Belege holt.
      *Erst auflösen, dann darf die Renntafel sich auf diese vier Zeilen berufen.*

- [ ] **Die Aliasfläche hat seit dem 2026-08-21 eine Zahl, und die Analyse ist NICHT gebaut**
      (`gabbro alias`, fünf Schichten über 53 Einheiten):

      ```
      S1 = 10   Signaturen mit >= 2 Zeigerparametern
      S2 =  3   Rufstellen, die >= 2 Zeiger übergeben
      S3 =  0   davon zwei Argumente EINER Wurzel
      S4 =  2   Umsichten `fn(ptr A) -> ptr B`
      S5 =  5   Rümpfe, die durch einen schreiben und aus einem anderen lesen
      ```

      **Und der ungeplante Fund ist der wertvollere:** was `R004` an zwei `own`-Parametern
      erkennt, **IST S3** — der Unterschied ist eine Rechtebedingung, keine Aliasanalyse.
      *Nicht gebaut, weil `S3 = 0` auf dem sauberen Korpus.* **Eine gemessene Null ist ein
      Ergebnis.**

- [ ] **`sonden/` gibt es, und darin läuft GENAU EINE Sonde** *(2026-08-21)*.
      `sonde_release_sichtbarkeit.c` trägt einen **positiven Kontrollarm, der fallen MUSS**
      (gemessen: 3 322 Verletzungen gegen 0 im ersten Arm). *Eine Sonde ohne Kontrollarm
      misst ihre eigene Nachsicht.*

      > ~~**Der Zähler bleibt bei `0 von 27`:** die eine gebaute Sonde gehört zu **keiner**
      > der 26 benannten.~~ *(überholt 2026-08-30)* — **er steht auf `1 von 30`:**
      > `sonde_boot_unerreichbar.c` ist dazugekommen und gehört zu einer benannten. Und von
      > den drei Annahmen, die die Rennklasse wirklich tragen, kann **keine** heute eine
      > laufende Sonde bekommen.

      **Und die 29 übrigen Namen sind am 2026-08-30 GESTRICHEN.**
      *Wer einen Namen behalten will, schreibt die Sonde; der Rest fällt, und mit ihm die
      Zusicherung.* Manifest und Zeugnis tragen einen Sondennamen nur noch, wenn die Sonde
      als **Programm** steht (`manifest::SONDEN_MIT_PROGRAMM`, gepflegt gegen
      `sonden/sonde_*.c`); sonst heißt die Klasse **`ungedeckt`** und die Sondenspalte
      trägt `--`.

      ```
      A2  write_cr0    ungedeckt   --
      -- 36 Annahmen
      -- 29 Sondenname(n) GESTRICHEN: die Sonde steht nicht als Programm.
      ```

      **„Nicht gefahren" war ein Übersetzungsfehler, kein Zwischenzustand** — ein Name ohne
      Programm las sich im Manifest wie eine Deckung und war eine Zusicherung über das
      Ausbleiben einer Widerlegung. *Das Manifest ist das Artefakt, mit dem Gabbro seine
      Zusage nach AUSSEN trägt; dort wog der Name am schwersten.*

      **Die Zahl bleibt stehen** — die Schlusszeile sagt, wie viele gestrichen wurden, *sonst
      wäre eine Liste, die schrumpft, von einer, die nie größer war, nicht zu unterscheiden.*
      Das Zeugnis führt sie als **dritte Währung** neben `NOT FALSIFIABLE`, und
      `pruefe-sonden.sh` liest jetzt diese Zeile statt die Namensspalte — *sonst hätte der
      Läufer ab sofort `1 benannt` gemeldet und ausgesehen, als sei die Anklage erledigt.*
      Alles gebaut und getestet: `cargo test` grün.

- [ ] **`release_stellt_sichtbarkeit_her` ist als „nicht falsifizierbar" gebucht — mit einer
      Begründung, die die GRÜNE Richtung argumentiert** *(gefunden 2026-08-21 beim Bau der
      Sonde)*. Der Grund sagt, eine erfolgreiche Probe zeige nichts; **Falsifizierbarkeit ist
      aber die ROTE Richtung** — es geht darum, ob eine Probe die Annahme *widerlegen* könnte.
      *Die Buchung beantwortet die falsche Frage, und niemand hat es bemerkt, weil die Antwort
      für sich genommen richtig ist.*

---

# DIE SPRACHLINIE, NEU GEZOGEN AM 2026-08-21  ⟨A⟩

**Bis heute lief die Linie zwischen dem, was Gabbro SAGT, und dem, was der Ordner ÜBER Gabbro
sagt** — Absagetexte englisch, Quellkommentare deutsch. *Sie läuft jetzt zwischen QUELLE und
DOKUMENT:* **Bezeichner und Kommentare der Quellen sind englisch**, die Arbeitsdokumente
(`TODO.md`, `dokumente/`) bleiben deutsch, und ein Bezeichner in einem `.gab`-Programm bleibt
das Wort des Nutzers.

**Der Rest, gemessen statt geschätzt** (`./instrumente/pruefe-englisch.py`):

```
**7910 von 12954 Kommentarzeilen** im Pruefer sind deutsch
 1072 von  1515 in den Instrumenten
  286 von   914 Bezeichnern tragen einen deutschen Stamm   (OBERE Schranke)
```

*Der Block stand am 2026-08-25 auf `7904 / 12359 / 1043 / 1280 / 273 / 845` und ist gegen den
Lauf nachgezogen — **die Abweichung war nicht die deutsche Hälfte, sondern die
Grundgesamtheit**: der Prüfer ist seither um 595 Kommentarzeilen gewachsen, die Instrumente um
235. `pruefe-zahlen.py` sah nur die erste Zahl und hat sie gemeldet; die fünf daneben standen
im selben Block und in keinem Register.*

Die schwersten: `emit.rs` 1489, `rechenwerk.rs` 802, `m1.rs` 771, `namen.rs` 387.

> **Eine halb übersetzte Quelle ist schlechter als jede der beiden reinen Formen** — das ist
> wörtlich der Befund, mit dem dieser Wächter gebaut wurde: *41 von 100 Absagetexten waren
> deutsch, und die Mischung lief durch einzelne Sätze.* Deshalb ist die Zahl eine **Ratsche**
> und keine Absichtserklärung.

**Und die Entscheidung dazu ist gefallen, am selben Tag: NUR NEUER CODE.** Der Bestand wird
**nicht** übersetzt, jetzt nicht und nicht nebenbei. *Ein Umbau, der 7731 Zeilen anfasst,
während vier Stufen offen sind, tauscht Arbeit gegen Gleichmäßigkeit* — und die Ratsche macht
genau das unnötig: sie hält den Stand fest, ohne dass jemand ihn heute senken muss.

- [ ] **Die Ratsche wurde am 2026-08-21 ERHÖHT, und das ist eine Schuld, keine Messung**
      *(180 Zeilen im Prüfer, 21 in den Instrumenten)*. Der `emit.rs`-Lauf schrieb deutsche
      Kommentare, obwohl sein Auftrag Englisch verlangte. **Die ehrliche Reparatur wäre das
      Übersetzen gewesen** — genau das ist am selben Tag zweimal geschehen, einmal für acht
      Zeilen, die der Verfasser des Wächters selbst geschrieben hatte.
      **Hier ist es NICHT geschehen**, weil die Übersetzung gegen Stufe 7 und K100
      zurückgestellt wurde. *Eine Ratsche, die man beim ersten Verstoß hebt, ist keine* —
      deshalb steht die Erhöhung mit Zahl, Datum und Grund im Wächter selbst, statt still
      aufgesogen zu werden. **Die Marke darf fallen, sobald jemand die 201 Zeilen übersetzt.**

- [ ] **Der Bestand wird später übersetzt, Datei für Datei, mit der Ratsche als Beleg.**
      Reihenfolge nach Gewicht, nicht nach Bequemlichkeit. **Ausdrücklich zurückgestellt am
      2026-08-21** — *eine stillschweigende Zurückstellung ist von einem Vergessen nicht zu
      unterscheiden.*
      Der Auslöser ist kein Termin: **wer eine dieser Dateien ohnehin für eine Stufe
      aufmacht, übersetzt sie dabei mit.** So fällt der Bestand mit der Arbeit statt neben
      ihr, und die Ratsche zeigt es.

- [ ] **Die Bezeichner sind die teurere Hälfte, und der Grund steht nicht im Compiler**
      *(2026-08-21)*. Eine Umbenennung ist mechanisch — aber
      [`./instrumente/mutiere-pruefer.py`](instrumente/mutiere-pruefer.py) trägt **264 Anker,
      die WÖRTLICHE Quellzeilen sind.** Wer umbenennt, ohne sie mitzuziehen, macht aus 264
      Ankern 264 tote. *Der Wächter fängt es — `--anker` fällt sofort —, und darum steht die
      Warnung in seiner Ausgabe und nicht in einer Fußnote.*
      Dasselbe gilt für die Dateinamen der Instrumente: sie stehen in ~165 Befehlsverweisen,
      in `pruefe-zahlen.py` und in zwei Globs. **Ein zweiter Umbau derselben Bauart wie der
      Ordnerwechsel** — und der hat gezeigt, dass das Verschieben der harmlose Teil ist.

---

# ZWISCHEN 7 UND 8 — was der `M120`-Fund aufgedeckt hat  ⟨A⟩

- [ ] **Der Kennungswächter löst auf DATEIEBENE auf, und das ist eine Näherung**
      *(gefunden 2026-08-21 an `M120`)*. Seine Regel lautet *„eine Kennung darf in beliebig
      vielen Zeilen stehen, aber nur in EINER Datei"* — eine Näherung an **„eine Kennung, eine
      REGEL"**, und sie war richtig, solange Dateien und Regeln eins zu eins standen.
      `M120` stand zweimal in `m1.rs`: `Self` im `ensures` und der Grundwert.

      > **Das ist dieselbe Vergröberung wie bei W16 — nur nicht in der TIEFE, sondern in der
      > AUFLÖSUNG.** Ein Werkzeug, das grob genug auflöst, meldet nichts und sieht aus, als
      > hätte es nachgesehen.

      **Die naheliegende Verschärfung geht nicht, und das ist gemessen:** *„zähle die
      Vergabestellen, alles über eins ist ein Befund"* ergäbe **32 Befunde**, von denen
      **18 dieselbe Regel aus mehreren Zweigen** ausgeben (`erwarte_z`/`erwarte_kw` melden
      beide `P001`). *In die andere Richtung zu grob.* Was auflöst, ist der **Meldungstext**:
      eine Regel ist, was sie sagt.
      **Gebaut als [`./instrumente/pruefe-vergabe.py`](instrumente/pruefe-vergabe.py)** —
      Kandidatenliste, kein Urteil, mit allen drei Fehlerrichtungen benannt.

- [ ] **67 Kommentare im Prüfer nennen eine fremde Kennung, ohne zu sagen wo sie lebt**
      *(gemessen 2026-08-28, `./instrumente/pruefe-zitate.py`)*. **Die Marke steht seit heute
      auf 274 und ist damit eine SCHULD, keine Buchung** — das Ziel ist **207**, der Stand,
      den derselbe Wächter am 2026-08-21 hatte, als seine Marke gesetzt wurde.

      | Stand | zeilenweise | absatzweise |
      |---|---:|---:|
      | `62b997b` — hier wurde 226 gesetzt | 226 | **207** |
      | `927c1a5` — vor den Zusammenführungen des 2026-08-28 | 256 | 233 |
      | heute | 309 | **274** |

      **Zwei getrennte Befunde, und nur einer ist bezahlt.** Der erste: der Wächter las
      *zeilenweise*, seine eigene Regel sagt aber „the comment" — ein Satz über zwei Zeilen
      verlor damit seinen Ortshinweis. Das ist geheilt (Absatz statt Zeile, getrennt an
      leeren Kommentarzeilen, damit ein Modulkopf nicht durch ein einziges `siehe`
      freigesprochen wird), und es nimmt 35 der 309 heraus.
      **Der zweite ist nicht bezahlt:** 207 → 274 sind echte Kommentare, und der Nenner
      erklärt davon nichts — von den 233 des Standes `927c1a5` ist **keiner** weggefallen und
      **keiner** entstand dadurch, dass eine Kennung die Datei wechselte. *Der Gegenstand
      wächst, nicht die Leseweite.*
      Warum hier nicht bezahlt: es sind 67 Kommentare in zwanzig Prüfer-Dateien, `emit.rs`
      mit 40 voran — ~~und **`emit.rs` ist die Datei, deren wörtliche Zeilen der
      Mutationskatalog als Anker führt.** Wer dort schreibt, während die Anker umgezeigt
      werden, misst eine Mischung.~~

      **Der Ankerhaken ist am 2026-08-30 nachgemessen worden, und er hält nicht**
      ([`messung/ANKERHAKEN.md`](messung/ANKERHAKEN.md)). Angeordnet war, hier nicht das Ziel
      zu erreichen, sondern die **Grundgesamtheit zu berichtigen** — ein Anker-Kommentar
      zählt nicht als Kandidat. Gemessen:

      | | Zahl |
      |---|---:|
      | Ankerzeilen im Katalog, verschieden | 499 |
      | davon **Kommentarzeilen** | **4** |
      | Anker mit einer Kennung in Rückstrichen | **0** |
      | Kandidaten, die die Regel herausnimmt | **0** (274 → 274) |

      **Die beiden Grundgesamtheiten sind bauartbedingt disjunkt:** ein Anker ist ein Lauf
      wörtlichen Quelltextes, ein Kandidat braucht eine Kennung in Rückstrichen, und **kein
      Anker trägt eine.** `emit.rs` führt 135 Ankerzeilen, davon ist genau **eine** ein
      Kommentar, und sie zitiert nichts — **keiner der 40 genannten `emit.rs`-Kommentare ist
      ein Anker.** Es gibt also nichts zu berichtigen; die Korrektur ist nicht strittig,
      sie ist **leer**.

      **Zähler und Nenner bleiben damit stehen: 274 gegen 207, die Schuld unvermindert.**
      Eingebaut ist die Regel trotzdem — nicht um etwas herauszunehmen, sondern um die
      Disjunktheit zu **prüfen statt sie anzunehmen**: `ankerprobe` rechnet beidseitig und
      druckt die Differenz bei jedem Lauf, und ein unlesbarer Katalog ist `ABORT`, keine
      stille Null. *Schreibt jemand eine Kennung in einen Anker, hört die Zahl auf, null zu
      sein.*

- [ ] **`M120` war NICHT der einzige Fall — im Parser stehen vier weitere** *(gemessen
      2026-08-21)*. Je zwei unverwandte Regeln unter einer Kennung:

      | | die eine Regel | die andere |
      |---|---|---|
      | `P022` | „`table` kennt genau ein `tree`-Wort" | „Kostenangabe fängt mit `O` an" |
      | `P023` | „im `tree`-Rumpf erwartet: parent, child, sibling" | „the `node` of a `walk` declaration is an array" |
      | `P024` | „diese Kante steht in `tree` zweimal" | „`@version` erwartet" |
      | ~~`P034`~~ **GETRENNT** | „`_` on its own is not an identifier" — bleibt `P034` | „`pub` is not in the grammar here" — jetzt **`P041`** |
      | `P035` | „is neither a record nor a sum type" | „gibt es in Gabbro nicht" |

      *Alle fünf im Parser, alle in einer Datei* — genau dort, wo der alte Wächter
      bauartbedingt blind war. **`P034` ist am 2026-08-30 getrennt** (`P041` für das
      verirrte `pub`), weil bei ihm zwei Giftproben einander deckten; die vier übrigen
      stehen weiter — siehe den Posten darunter.

- [ ] **Was eine Doppelvergabe RÜCKWIRKEND kostet, und das ist teurer als der Fund**
      *(gemessen 2026-08-21)*. Die Giftproben prüfen auf **Kennungen**. Eine doppelt
      vergebene Kennung macht jede Probe darauf **mehrdeutig: sie fällt grün, während die
      GEMEINTE Regel ausgefallen sein kann.** Damit entwertet ein Duplikat rückwirkend die
      Deckungsaussage aller Proben, die darauf zeigen.

      ```
      59 Proben zeigen auf eine Kennung mit unaehnlichen Vergabestellen (von 302, die
      ueberhaupt eine Kennung erwarten)
      ```

      **Bei `P034` steht der Fall konkret:** `gift/05-auffangzweig` prüft die eine Regel,
      `gift/45-pub-wo-es-nicht-steht` die andere — *jede der beiden bliebe grün, wenn die
      Regel der anderen ausfiele.* Was fehlt, ist je Fall die Entscheidung: **zweite Kennung
      vergeben, oder begründen, dass es eine Regel ist.** Die 58 sind eine Ratsche.
      **Nachgerechnet 2026-08-28: 18 Kandidaten, 58 Proben** — und die Erhöhung kam zu zwei
      Dritteln aus dem Werkzeug, nicht aus dem Prüfer. `botschaft()` konnte eine mit `\`
      umgebrochene Rust-Meldung nicht lesen und verglich statt ihrer Klammern; zwei so
      verstümmelte Stellen sahen einander ähnlich und fielen aus der Liste. *`F002` und
      `K009` waren dadurch verdeckt, und verdeckt ist hier die gefährliche Richtung.*

      **Nachgemessen 2026-08-30** ([`messung/DECKUNGSLUECKE.md`](messung/DECKUNGSLUECKE.md)).
      ~~18 Kandidaten, 58 Proben~~ *(überholt 2026-08-30)* — der heutige Stand vor dem
      Eingriff war **20 und 61**;
      die Auftragszahl war überholt, und das ist mitgebucht.

      **Die entscheidende Frage ist nicht „sind das zwei Regeln?", sondern: decken zwei
      Giftproben unter dieser Kennung EINANDER?** Das ist keine Urteilsfrage, sondern eine
      nachprüfbare Eigenschaft der Probenmenge. Je Kennung wurde bestimmt, welche
      Vergabestelle jede ihrer Proben auslöst:

      | Gruppe | Kennungen | Befund |
      |---|---:|---|
      | **A — zwei Proben decken einander** | 9 | `E008` `M104` `P034` `F002` `H011` `M124` `N030` `O011` `R009` |
      | B — alle Proben auf EINER Stelle | 3 | `D012` `H012` `K009` — die andere Stelle ist unbeprobt |
      | C — weniger als zwei Proben | 8 | `P022` `P023` (null) · `O001` `O006` `N023` `P035` `R010` `F005` (eine) |

      **Geheilt ist genau einer: `P034`** — das verirrte `pub` heißt jetzt `P041`. Beide
      Ratschen sind daraufhin **gefallen: 20 → 19 Kandidaten, 61 → 59 Proben.**

      **Warum die acht übrigen aus Gruppe A hier NICHT geheilt sind, und es ist keine
      Aufwandsfrage:** `E008` hat vier Vergabestellen, `R009` fünf — sie zu trennen hieße zu
      *entscheiden*, was hier eine Regel ist, und `messung/PHASENKLASSE.md` hat für `R009`
      ausdrücklich die Gegenrichtung entschieden. **Das zu überschreiben wäre kein Heilen,
      sondern ein zweites Urteil ohne neue Messung.** Dazu: es gab keinen Übersetzer
      (`ki-pc-fisch-101` nicht erreichbar), und eine Trennung ist nur so lange durch Lesen
      prüfbar, wie sie eine Quellzeile, eine Probenzeile und eine Testliste umfasst.
      *Gruppe B und C gehören ausdrücklich nicht in diesen Posten — dort deckt keine Probe
      eine andere; ihr Befund ist eine FEHLENDE Probe, nicht eine falsche Deckungsaussage.*

---

# STUFE 8 — PL: DIE LOGIK DES PRÜFERS  ⟨D⟩

~~**Zwölf Pässe entscheiden über jedes Programm, und keiner schuldet einen Satz** (`struct Pass`
hat kein Feld dafür).~~ — **eingelöst am 2026-08-21 (PL.1).** **Ohne die Sätze ist „Gabbro
formal verifiziert" nicht einmal formulierbar** — man wüsste nicht, was zu beweisen wäre; seit
PL.1 wüsste man es. *Was daraus folgt, steht im nächsten Punkt und es ist nicht PL.2.*

Dieselbe Bauart wie `schablonen.rs`, mit denselben zwei Zähnen; ~22 Sätze geschätzt. Zweiter Zahn
sofort: *kein neuer Absagecode ohne seinen Satz* (2026-08-21 gebaut; heute 71 Sätze über 239 Codes, 45 Codes noch ohne).

### K100 — der Weg auf 100 % Klempnereiabdeckung ([`dokumente/PLAN.md`](dokumente/PLAN.md)) *(Teil)*

- [ ] **PL.1b — die Spalte `ARGUED`, und sie steht VOR PL.2** *(entschieden 2026-08-24)*.
      Zwischen `measured` und `PROVED` fehlt der Zustand, der am meisten kauft und am
      wenigsten kostet: **ein Satz, für den ein Korrektheitsargument aufgeschrieben ist** —
      mathematisch, von Menschen geprüft, nicht maschinell.

      | | was es heißt |
      |---|---|
      | `measured` | eine Giftprobe fällt, eine Mutation wird gefangen. **Misst die UMSETZUNG an geprüften Fällen** |
      | **`ARGUED`** | *wenn dieser Pass annimmt, dann gilt P* — hingeschrieben, mit dem Modellstück, das es braucht. **Kann falsch sein; ist durch die Bewegung des Prüfens gegangen** |
      | `PROVED` | maschinengeprüft. Heute **0 von 52** |

      **Der Beleg, dass es trägt, steht im eigenen Register.** `kosten.domaenenschranke` las
      für `mappings of` **2 048**, wo die Domäne **512⁴ = 68 719 476 736** ist — *sieben
      Größenordnungen, drei Tage getragen*, und gefunden, weil der ERZEUGER hineinlief.
      **Wer den Satz „die gelesene Zahl IST die Mächtigkeit der Domäne" hinschreiben muss,
      sieht in einer Stunde nach, ob das stimmt.** *Das ist der ganze Ertrag: nicht Gewissheit,
      sondern der Zwang hinzusehen.*

      **Aufwand, geschätzt (Eingangszahlen gemessen, Gewichte geschätzt):** je Satz 1–3 Tage
      samt dem Modellstück, das er braucht → **3–6 Personenmonate für alle 52.** Die
      maschinelle Fassung derselben Sache: **2–5 Personenjahre** (Aufschlüsselung siehe den
      Kettenabschnitt unter NICHT JETZT). *Faktor fünf bis zehn, und die Antwort auf „ist die
      Idee richtig" liegt fast ganz im billigen Teil.*

      **Reihenfolge: `K001` zuerst** — der mit dem gemessenen Fehler, also der, bei dem sich
      sofort zeigt, ob die Übung trägt. Dann `H006`, dann `V2`.

      > **Und was `ARGUED` NICHT ist: ein Beweis.** Ein Papierargument ist nicht
      > maschinengeprüft. *Es steht in dieser Spalte, damit niemand es für den anderen Zustand
      > hält* — dieselbe Trennung, die `measured` von `PROVED` trennt, eine Stufe tiefer.
      > **Ein `ARGUED`, das als `PROVED` gelesen wird, ist teurer als ein leeres Feld.**

- [ ] **PL.2 — die drei Sätze BEWEISEN.** Aufgeschrieben sind sie seit dem 2026-08-21, **keine
      Zeile Isabelle.** `K001` ist dabei **geteilt** in `kosten.summation` (*gemessen*) und
      `kosten.domaenenschranke` (**VERMUTET**) — damit der gemessene Fehler (2 048 gegen
      512⁴, **sieben Größenordnungen, drei Tage getragen**) im Satz *sichtbar* bleibt, statt
      von einer glatten Formulierung überschrieben zu werden.
      **V2 ist der teuerste, und der Grund ist ein Befund über das Geschirr:** die Regel hat
      **keine eigene Kennung** — sie erweitert, was durchgeht. Eine Giftprobe müsste ein
      **PAAR** zeigen (ohne Fakt fällt, mit Fakt geht durch), und dafür hat `beispiele/gift`
      keine Form. *Dasselbe gilt für V3 und `m2.geisterloeschung`.*

- [ ] **Die 268 Mutationen sagen an VIERZIG Stellen weniger, als sie drucken**
      *(2026-08-21)*. 40 Proben zeigen auf eine Kennung mit unähnlichen Vergabestellen;
      **bis die fünf Kennungen aufgelöst sind, ist eine solche Probe kein Beleg** — sie fällt
      grün, ohne zu zeigen, welche der Regeln gefallen ist.
      **Die Reihenfolge ist deshalb festgelegt: erst die Kennungen auflösen, dann die Proben
      nachziehen.** Nach der eigenen Regel — *Belege statt Versuche* — ist die ehrliche
      Zwischenmeldung nicht „268 von 268", sondern:

      ```
      227 belegt · 41 in Klärung
      ```

      *Die Deckungszahl ist nicht falsch; sie ist an vierzig Stellen unbelegt, und das ist ein
      Unterschied, den nur die Buchung sichtbar hält.*

- [ ] **NEUN Befunde sind beim AUFSCHREIBEN abgefallen — der erste ist BEHOBEN, acht stehen**
      *(2026-08-21, Liste in [`messung/PASSREGISTER.md`](messung/PASSREGISTER.md))*.

      ~~**Der schwerste: `kbedingung.rs` setzt die K-Bedingung nicht durch.**~~
      **GESCHLOSSEN am 2026-08-21 als `D009`.** `k_haelt()` verlangte `breaking.is_empty()`
      seit dem ersten Tag; der Pass meldete nur Handschrift, und `breaking` wurde gesammelt,
      gezählt, **gedruckt und nie abgesagt.** *Ein Programm konnte Pass 2 passieren, ohne die
      K-Bedingung zu erfüllen.*

      > **Und das ist nicht nur ein falsch rechnender Pass, sondern eine Zusage, auf der eine
      > MESSUNG ruht:** die K-Spalte der K/A/W-Zählung hat **28 von 73** Pflichten als „durch
      > Konstruktion" gebucht, und die K-Bedingung war das mechanische Kriterium dafür.

      **Die Nachfrage danach ist die wichtigere, und sie ist gemessen statt geschätzt:**

      ```
      0 `breaking`-Stellen im sauberen Korpus (beispiele/ + messung/)
      0 Dateien, an denen `D009` heute fällt
      ```

      **An der Zählung ändert sich nichts** — nicht *„wahrscheinlich nicht", sondern null,
      mit dem Befehl daneben.* Der ganze Beleg der neuen Regel ist damit Gift
      (`gift/249`), und das steht in ihrem Satz (W10).
      *„Wahrscheinlich nicht" ist genau die Formulierung, die dieser Ordner sonst nicht
      durchgehen lässt.*
      Dazu: `N028`/`N029` schlüsseln verschieden (Kurzname gegen vollen Pfad, `m::f()` trifft
      nie), die Paarung ist global statt transitiv, der Adressraum wird außer bei `R001`
      nirgends geprüft, `melden` in `phasen.rs` ist toter Code, rekursive Funktionen bekommen
      gar keine Rahmenprüfung.

      > **Keinen davon hat ein Werkzeug gemeldet.** Sie fielen auf, weil jemand den Satz
      > aufschreiben musste, den der Pass schuldet — *und das ist genau die Wirkung, für die
      > das Register gebaut wurde, gemessen am ersten Tag.*

- [ ] **PL.3 — die Bruecke: (c) je Satz eine Sprechprobe, die den Rust gegen das Modell faehrt.**
      Das Geschirr steht (`mutiere-pruefer.py`, 148 von 148) -- was fehlt, ist der Satz, der
      sagt, WELCHE Beschaedigung fallen muss. *Aus 132 Mutationen ohne Satz werden 132 mit
      einem.*

### The nine partial passes — **3 built, 9 CARRIED, 0 partial** (2026-08-19)

*Asked to finish all nine, the answer turned out not to be building work for six of them. What
was building work is done; what is not has an ADDRESS.*

| built | | |
|---|---|---|
| D1/D2 | exhaustive `match` over `tagged` | **`D005`** |
| M2 | the ghost erasure | **was already built** — in the EMITTER; `f(m : Marke, v : u32)` lowers to `uint32_t f(uint32_t v)` |
| costs | `per_pass` with an input-dependent bound | **read symbolically**, decided against the smallest assignment |

| carried, with an address | |
|---|---|
| M3 — the barrier from the space | axiom layer, beside A10 |
| M3 — the alias question | a LANGUAGE decision (`own`) |
| Paarung — the memory model | A10, already booked |
| Gruppe — the preservation | templates S16/S17 |
| costs — THAT the measure falls | `consuming.ordnung` |
| Phasen — the softer reading | a DECISION: from the strict one can loosen, never the other way |
| effects — the reach of `E010` | a drawn LINE: only known world state |




- [ ] **`CARRY` is an address, not a promotion.** A residue without an address belongs back in
      `PART`. *The guardian `pruefe-todo.py` had to grow with it — it counted `OPEN` and
      `PART`, reported three passes instead of twelve, and was right in the arithmetic and
      wrong in the question.*

- [ ] **`H013` still has zero bite on the corpus.** `gabbro kontexte beispiele/07` prints it:
      4 context roots, 2 with a visible body, 1 place touched, **0 of them declared in this
      unit.** The rule's whole evidence is poison 146/152. *Falle 80 until the second corpus.*

- [ ] **A disequality at the range boundary does not narrow.** Found while writing
      `beispiele/33`: `if n == 0 { return 0; }` followed by `n - 1` still reports `M104`,
      because `n != 0` is not turned into `n >= 1` although `0` is the lower bound of the
      declared range. *Small, and it costs a `narrow` line at every recursion.*

- [ ] **The full argument mapping is only one level deep.** `writes p.slots` becomes
      `writes q.slots` through the base name; an argument that is itself an expression
      (`f(g(x))`) keeps the callee's name. *Coarse in the safe direction, and named here so
      the next reader does not read it as complete.*

- [ ] **`own` still buys no exclusivity, and cannot without alias analysis.** What is open is
      not a pass but a decision: does Gabbro get a release operation (then `own` carries it),
      or does the right stay a signature annotation? `own @ident` has no reader either way.

- [ ] **Acceptance of the third addition** (§6): catalogue against count — **every counted instruction
      has an axiom or a construct, every line an instruction**; the mode ladder as a speech test
      (a swapped `write_cr0(PG)` **must** break); the precomputed boot tables byte-identical
      against what today's trampoline builds at run time.

- [ ] **P5–P7** from [`dokumente/SPRACHE.md`](dokumente/SPRACHE.md) §6 — **the form table with
      witness pairs, the C emission, one Caprock module end-to-end.**
      **Every stage consumes the result of the previous one, like a `Duty`.**
      *(P4 has fallen: M2 stands as `L101`–`L105`, the pairing pass as `V001`–`V004`.
      What stays open at P4 is the **template** for M2 — it stands in the template list,
      not here.)*

---

# STUFE 9 — DER PRÜFER ALS MATHEMATIK, in Lean 4 und unabhängig vom Code  ⟨D⟩

**Die Frage, gestellt am 2026-08-21: früher oder später soll die Mathematik des Prüfers und
des Erzeugers vollständig bewiesen werden, unabhängig vom Code — und wäre das JETZT
sinnvoll?**

**Die Antwort ist: ja früher oder später, nein jetzt — und der Grund ist gemessen, nicht
Geschmack.** Er steht in einer Zeile:

```
$ grep -n -A6 "^pub struct Pass" crates/gabbro-check/src/lib.rs
    pub nummer: u32,  pub name: …,  pub quelle: …,  pub zustand: Zustand,
```

~~**`struct Pass` hat kein Feld für einen Satz. 194 Absagekennungen, null Sätze.**~~ — **überholt am 2026-08-21 durch PL.1:** das Feld steht, 52 Sätze über 12 von 12 Pässen, 210 Kennungen, davon 45 ohne Satz. *Der Satz bleibt stehen, weil er die Begründung dieses Abschnitts TRUG; was ihn ersetzt, steht darunter.* Einen
Algorithmus zu beweisen setzt voraus, dass aufgeschrieben ist, *was er entscheiden soll* —
und genau das ist Stufe 8 (PL.1), die noch nicht angefangen hat.

> **Es ist wörtlich dieselbe Regel, die über Stufe 7 steht: *erst der Erzeuger, dann der
> Vertrag.*** Hier heißt sie: **erst der Satz, dann der Beweis.** Ein Beweisprojekt vor dem
> Passregister müsste sich seinen Beweisgegenstand ausdenken — und was man erfindet, bevor man
> es misst, ist die Bewegung, gegen die R7 und W3 stehen.

## Die drei Zahlen, die heute gegen einen Start sprechen

| | |
|---|---|
| ~~**`struct Pass` schuldet keinen Satz**~~ **— eingelöst 2026-08-21** | 216 Kennungen, **54 Sätze**, 0 `PROVED` — *aufgeschrieben ist es; **dieser** Auslöser hält nicht mehr* |
| **Zahn 3 steht auf 8** | acht Prämissen **bewiesener** Schablonen hängen an keinem Pass. *Die vorhandene Beweisschicht ist nicht zu Ende gebunden;* eine zweite danebenzustellen vervielfacht die ungebundene Fläche, statt sie zu schließen |
| **27 Sonden, keine existiert** | jeder Beweis „unabhängig vom Code" ruht auf der Annahmenmenge (33, davon 6 nicht falsifizierbar). *Solange keine der 27 benannten Sonden ein Programm ist, kauft die Unabhängigkeit weniger, als sie aussieht* |

**Und die vierte, die kein Argument gegen Lean ist, sondern eine Auflage:** eine zweite
Beweisschicht neben Isabelle ist **W7** — zwei Register über derselben Sache. Heute stehen
15 Theorien, 3 496 Zeilen, 101 Sätze, 10 von 21 Schablonen maschinell geprüft. *Wer Lean
danebenstellt, muss sagen, welche Aussage wo lebt, sonst wandert dieselbe Aussage in beide und
niemand weiß, welche gilt.*

## Warum trotzdem LEAN 4 und nicht mehr Isabelle — der Punkt, an dem es kippt

**PL.3 verlangt schon heute genau das, was Lean 4 kann und dieser Isabelle-Aufbau nicht:**

> *„je Satz eine Sprechprobe, die den Rust gegen das MODELL fährt."*

Ein Lean-4-Modell ist **ausführbar**. Der Prüferalgorithmus — Bereichsverbände, Wirkungshüllen
über dem Aufrufgraphen, Rangordnung, Linearität — ist endliche Mathematik ohne `mathlib`-Tiefe,
und ein bewiesenes Lean-Modell kann **neben** dem Rust auf demselben Korpus laufen. *Dann ist
die Bindung zwischen Modell und Code keine Behauptung, sondern ein Differenztest* — dieselbe
Bauart wie `pruefe-emission.sh`, nur eine Ebene höher.

Isabelle hier kann das nicht ohne Codeerzeugung, und dieser Ordner hat **kein AFP** und keinen
eingerichteten Export. *Das ist eine Aussage über diesen Aufbau, nicht über Isabelle.*

**Die Arbeitsteilung, die daraus folgt** — und sie ist die Antwort auf W7:

| | wo | was |
|---|---|---|
| **Schablonen** | Isabelle, bleibt | Aussagen über EINE Absenkung: `deckt fs zs ⟷ map fst zs = fs`. Kleine, abgeschlossene Sätze am Erzeugnis |
| **Passlogik** | Lean 4, neu | die ENTSCHEIDUNGSPROZEDUR: terminiert sie, ist sie monoton, ist sie korrekt gegen die Semantik. Ausführbar, also differenztestbar |

## Der AUSLÖSER, gemessen statt terminiert

*Ein Vorhaben ohne Auslöser ist ein Vorsatz.* Stufe 9 beginnt, wenn **alle drei** gelten:

1. **PL.1 steht** — `struct Pass` trägt ein Satzfeld, und jeder der zwölf Pässe hat einen
   aufgeschriebenen Satz (~22 geschätzt). *Das ist der Beweisgegenstand; ohne ihn gibt es
   keinen.*
2. **Zahn 3 steht auf 0** — oder jede verbliebene Prämisse hat einen benannten Grund, warum
   sie an keinem Pass hängt. *Sonst erbt Lean eine ungebundene Schicht.*
3. **Die drei Sätze mit der größten Traglast sind gewählt und formuliert** (PL.2: `K001`
   Summation — *hat heute schon einen gemessenen Fehler* —, `H006` Rangordnung, V2
   relationale Verengung mit 102 Stellen). *Ein Beweisprojekt, das mit dem leichtesten Satz
   anfängt, misst seine eigene Nachsicht.*

## Was JETZT sinnvoll ist, und es ist genau eine Sache

- [ ] **`struct Pass` bekommt sein Satzfeld, bevor die nächste Absagekennung vergeben wird**
      *(entschieden 2026-08-21)*. Das ist **der zweite Zahn von PL.1**, und er ist das einzige
      Stück, das teuer wird, wenn man es aufschiebt: *jede Kennung, die zwischen heute und
      Stufe 8 dazukommt, ist ein Satz mehr, den später jemand rückwärts rekonstruieren muss.*
      Am 2026-08-21 gebaut: 51 Sätze über 210 Kennungen, 45 davon noch ohne — die Ratsche steht.
      **Eine Ratsche kostet nichts, solange sie früh steht** — genau wie Zahn 2 der
      Schablonenliste. *Der Rest von Stufe 9 wartet auf seinen Auslöser; dieser eine Posten
      wartet auf nichts.*

## Und was Stufe 9 ausdrücklich NICHT kauft

**Ein Beweis des Algorithmus ist kein Beweis des Codes.** Er sagt: *die Entscheidungsprozedur
ist richtig* — nicht: *dieses Rust tut sie.* Die Lücke dazwischen ist genau das, was heute
`mutiere-pruefer.py` mit 254 von 254 misst, und sie bleibt bestehen.

> **Deshalb gehört zu Stufe 9 vom ersten Tag an ein ZAHN 3 für Pässe:** jeder bewiesene Satz
> bindet sich an einen Pass und an eine Sprechprobe, die den Rust gegen das Modell fährt.
> *Ohne ihn entsteht eine zweite Beweisschicht, die niemanden bindet — und diese Form hat
> dieser Ordner schon einmal gebucht* («B33»: ein Satz, der beschreibt, was gelten sollte, und
> ein Pass, der das Gegenteil tut).

---

# DIE BOOTSTRAP-KETTE — ausgeplant und ZURÜCKGESTELLT, mit gemessenem Grund  ⟨Z⟩

*Aufgeworfen und ausgeplant am 2026-08-24. Der Plan steht hier ganz, damit die
Zurückstellung eine Entscheidung ist und kein Vergessen.*

**Die Idee:** eine winzige Stufe 0, klein genug, dass ein Mensch sie liest; darauf eine Stufe 1,
die deutlich mehr kann und formal verifiziert wird; darauf der volle Gabbro-Übersetzer.
**Vertrauensbasis: ein bis drei Kilozeilen statt einer Werkzeugkette.**

**Die Form ist richtig und erprobt** — sie ist nicht exotisch:

| Vorbild | was es zeigt |
|---|---|
| **CakeML** | ein verifizierter ML-Übersetzer mit **verifiziertem Bootstrap**, in HOL4 |
| **stage0 / live-bootstrap** | eine Kette von einem wenige hundert Byte großen Hex-Monitor bis zur vollen Werkzeugkette |
| **CompCert** | der verifizierte C-Übersetzer, in Coq — **ohne** Bootstrap |

## Zwei Prämissen der ursprünglichen Fassung, beide korrigiert

**(1) „Stufe 0 übersetzt Lean 4 in Binärprogramme, unter 1k Zeilen C."** Das liegt um drei bis
vier Größenordnungen daneben. Lean 4 ist abhängig getypt: Elaboration mit Unifikation,
implizite Argumente, Typklassenauflösung, Metavariablen, Kernprüfer, Makro- und Taktiksystem,
Codeerzeuger — dazu eine Laufzeit mit Referenzzählung, geboxten Werten, Closures und
GMP-gestütztem `Nat`. Leans eigener Bootstrap liefert vorerzeugtes C in der Größenordnung von
Hunderttausenden bis Millionen Zeilen. *Aus dem Gedächtnis, und es gehört nachgerechnet — aber
nicht um Faktor 3, sondern um Faktor 1000.*

> **Der Umbau, der die Idee rettet: Stufe 0 muss Lean gar nicht übersetzen.** **Lean ist der
> BEWEISER, nicht die Implementierungssprache.** Stufe 0 muss die Sprache übersetzen, in der
> Stufe 1 geschrieben ist — und die wählt man klein.

**(2) „Es gibt keinen formal verifizierten C-Übersetzer."** Doch: **CompCert**, in Coq bewiesen,
Semantikerhaltung maschinengeprüft. *Mit drei Einschränkungen, die zur Sache gehören:*
Präprozessor, Assemblierer und Binder liegen **außerhalb** des Beweises; die freie Lizenz ist
**nicht-kommerziell**, was zu einem AGPL-Ordner mit eigenem Lizenzzusatz nicht spannungsfrei
passt; und der Beweis gilt für **CompCert C**, eine große Teilmenge, nicht für jedes C.

**Damit ändert sich die Begründung für Assembler, aber nicht unbedingt die Wahl:**

| Stufe 0 in | dafür | dagegen |
|---|---|---|
| **Assembler** | **gar kein Übersetzer in der Vertrauensbasis** — nur ein Assemblierer, und der kann selbst winzig oder handassembliert sein (stage0: 357-Byte-Hex-Monitor) | je Architektur einmal; schwerer zu LESEN, und Lesbarkeit ist der ganze Zweck |
| **C + CompCert** | 1–3k Zeilen C sind für einen Menschen ungleich besser prüfbar | die Vertrauensbasis wird CompCert samt Coq-Kern **plus** unverifiziertem Assemblierer/Binder — *groß, aber maschinengeprüft* statt *klein, aber gelesen* |
| **C, mit ZWEI Übersetzern gebaut** | **Diverse Double-Compiling** (Wheeler): denselben Quelltext durch CompCert *und* gcc/clang, Erzeugnisse vergleichen. Man muss dann keinem der beiden allein trauen | zwei Werkzeugketten, und der Vergleich ist Arbeit |

**Die dritte Zeile ist die stärkste**, und sie ist dieselbe Bauart wie `pruefe-emission.sh`
(zweimal erzeugen, bitgleich) — nur über dem Übersetzer statt über der Emission.

## Die Kette, ausgeplant

| Stufe | was | geschrieben in | Größe | Prüfform |
|---|---|---|---|---|
| **0** | nicht-optimierender Übersetzer einer Minimalsprache `L0` → Maschinencode, **eine** Architektur (x86_64; `aarch64` bleibt versiegelt) | C-Teilmenge oder Assembler | **1–3k Zeilen** | **gelesen**, plus DDC gegen zwei Übersetzer |
| **1** | Übersetzer einer Gabbro-Teilmenge | in `L0` | größer | **formal** — und der Beweis ist genau PL.1b/PL.2, über dem ALGORITHMUS |
| **2** | der volle Gabbro-Übersetzer | in der Gabbro-Teilmenge | wie heute | übersetzt von Stufe 1 |

## Der Einwand, der aus diesem Ordner selbst kommt — und er ist der schwerste

```
dokumente/SYNTAX.md:1381   "What deliberately does not exist: … self-hosting …"
crates/gabbro-syntax/tests/verfassung.rs::kein_selbst_hosting
   "Ein Erzeuger, der sich selbst uebersetzt, verliert seinen unabhaengigen
    Pruefer -- die Kisten bleiben Rust."
```

**Stufe 2 IST Selbst-Hosting**, und das Verbot ist kein Formfehler. Es ist der Grund, aus dem
heute **zwei unabhängige Instanzen** über jeder Emission stehen: der Rust-Prüfer und
`cc -Werror` bei `-O0` *und* `-O2`, dazu UBSan. Ein selbstgehosteter Übersetzer verliert die
Unabhängigkeit — ein Fehler kann sich in seinem eigenen Erzeugnis verstecken (Thompsons
*Trusting Trust*).

> **Der Ausweg ist bekannt und er ist derselbe wie in Zeile drei der Tabelle oben: DDC.**
> Aber er *kostet* den zweiten Übersetzer — und **den hat dieser Ordner heute geschenkt,
> solange die Kisten Rust bleiben.** Wer Stufe 2 baut, kauft eine Eigenschaft, die er heute
> umsonst hat, und muss sie danach bezahlen.

## Warum NICHT jetzt, und der Grund ist eine Zahl, keine Neigung

**Die Kette schrumpft die Vertrauensbasis der WERKZEUGKETTE. Gabbros Vertrauensbasis wird heute
nicht von der Werkzeugkette dominiert:**

```
52 Sätze über zwölf Pässe          0 bewiesen          45 Kennungen ohne Satz
33 Annahmen                        26 Sondennamen OHNE PROGRAMM
emit.rs 6 976 Zeilen               1 Kennung           0 Sätze
die Aliasfläche                    der ganze Rest der Klasse RENNEN
```

**Eine perfekt gebootstrappte Kette über einem falschen Algorithmus erzeugt zuverlässig
falschen Code** — und `kosten.domaenenschranke` zeigt, dass das kein hypothetischer Fall ist:
sieben Größenordnungen, drei Tage getragen.

> *Die Kette härtet eine Sache, die noch nicht als richtig erwiesen ist.* **Erst wissen, ob die
> Idee stimmt (PL.1b, 3–6 Personenmonate) — dann die Kette bauen, die sie unfälschbar macht.**

## Der AUSLÖSER, gemessen statt terminiert

Die Kette beginnt, wenn **beide** gelten:

1. **`ARGUED` steht bei allen 52** — oder jeder Rest hat einen benannten Grund. *Vorher gibt es
   keine Aussage, deren Unfälschbarkeit sich zu kaufen lohnt.*
2. **Die Selbst-Hosting-Entscheidung ist umgekehrt, mit Datum** — oder Stufe 2 entfällt und die
   Kette endet bei Stufe 1. **Beides ist zulässig; stillschweigend gegen die eigene Verfassung
   zu bauen ist es nicht.**

- [ ] **Die Zahlen dieses Abschnitts sind SCHÄTZUNGEN und tragen keinen Befehl** *(gebucht
      2026-08-24)*. „1–3k Zeilen", „Faktor 1000 bei Lean", die CompCert- und CakeML-Anker:
      alle aus dem Gedächtnis, keiner nachgerechnet. **Wer die Kette beginnt, rechnet sie
      zuerst nach** — dieselbe Auflage, die `PLAN.md` über der seL4-Aufschlüsselung trägt.

---

# NICHT JETZT — ausdrücklich zurückgestellt, mit Grund  ⟨Z⟩

> *Eine stillschweigende Zurückstellung ist von einem Vergessen nicht zu unterscheiden.*

| | Grund |
|---|---|
| **`H` auf 0 jagen** | sieben Zwölftel messen die Vollständigkeit des Korpus. Stufe 1 entscheidet den Maßstab, danach ist die Zahl wieder brauchbar |
| **«B18» (`device`-Phasen), «B27» (Registerzuordnung)** | groß, und sie entsperren **keine Programmklasse** — je ein Fragment |
| **Weg (a), der verifizierte Erzeuger** | CompCert-Größenordnung. Und solange neun Prämissen keinen Leser haben, wäre er ein Beweis über einer Fläche, deren Voraussetzungen niemand herstellt |
| **Konstrukte aus dem Entwurf** | jedes ist eine Schablone, also Vertrauensfläche — die Ratsche verlangt vorher einen **gemessenen** Bedarf (Stufe 4, Regel A) |
| **Gleitkomma «F»** | die Kosten sind eine **zweite Faktenlogik**, kein zweiter Zahlentyp: ist ein Operand NaN, folgt aus `!(x < y)` nicht `x >= y`. Bedarf zählen, bevor gebaut wird |
| **«OPT», «Z»** | Geschwindigkeit und Zwischenspeicher vor der ersten Vergleichsmessung. *Die Messung selbst steht in Stufe 0* |
| **Papierschritte, Kernfrage** | sie können die These kippen, aber keines der vier Ziele weiterbringen, solange die Messschicht nicht steht |

- [ ] **Gehoert der Rundungsmodus in den TYP?** *(offen seit 2026-08-18)*. Ein `f64<RNE>`, das
      sich mit `f64<RTZ>` nicht mischen laesst, beseitigt eine ganze Fehlerklasse
      STRUKTURELL -- ohne einen einzigen Beweis ueber Zahlenwerte. **Es waere die vierte
      Instanz eines vorhandenen Musters**: `ptr<normal, rw>`, `atomic … seq`, `format … endian
      big` stellen ihren Modus schon an den Typ statt in Umgebungszustand. Gemessen: `ptr<…>`
      ist kein allgemeiner Typparameter, sondern ein eigener Typkonstruktor mit zwei
      geschlossenen Wortmengen -- **genau diese Form haette `f64<RNE>`.** *Und die Frage haengt
      nicht daran, ob Gabbro je rechnet: auch der Gast hinter `entrust` hat einen
      Rundungsmodus, und heute sagt darueber niemand etwas.* Nicht zu verwechseln mit
      Fehlerschranken im Typ (Rosa/Daisy) -- die brauchen Refinement-Types und sind die
      wertgetragene Schranke eine Stufe schaerfer.

### K100 — der Weg auf 100 % Klempnereiabdeckung ([`dokumente/PLAN.md`](dokumente/PLAN.md)) *(Teil)*

- [ ] **Gleitkomma-Memo: die Kosten sind eine ZWEITE FAKTENLOGIK, nicht ein zweiter
      Zahlentyp** *(2026-08-18)*. Intervallarithmetik ueber IEEE-754 ist gebaut und bekannt.
      **Was bricht, ist die NEGATION einer Vergleichsbedingung:** ist ein Operand NaN, sind
      alle Vergleiche falsch, und `!(x < y)` folgt `x >= y` nicht. `m1::fakten_aus(…,
      negiert = true)` waere unsicher -- *das ist die Maschinerie, mit der jede Verengung in
      dieser Sprache arbeitet.* Zwei Auswege, beide teuer: NaN durch Konstruktion ausschliessen
      (Laufzeitpruefung, W6) oder die Negation kein Faktum liefern lassen (sicher, und dann
      ungeprueft genau dort, wo man pruefen wollte). **Bedarf zaehlen, bevor gebaut wird.**

### The question that decides the core


---
- [ ] **Real linearity is the only mechanism no existing tool supplies** —
      measured: Verus' `tracked` is **affine**, Rust is affine, SPARK's leak check hangs on an
      **allocation**. The boot phase, `Parked` and the linear checking obligation hang on it.
      **Open: is one mechanism enough to justify a language?** The cheaper answer
      would be a contribution to Verus (linear instead of affine). That is the most expensive open question in the folder.

- [ ] **ATS is the nearest relative for the core and is unexamined** — linear types plus proofs,
      compiled to C. The same logic as the Verus gate: *the nearest relative is built, the
      folder is not.* **Should have been run before P2; P2 ran first.** That does not make the comparison
      void, only more expensive: it now measures against something built instead of against
      a design.

- [ ] **For every further mechanism, run the counter-calculation.** M2 at the lock evidence and M1 came out
      against the folder on 2026-08-13. **M3 is to be measured against the right baseline:
      not Verus, but `tock-registers`/`svd2rust`** — typed register accesses are a
      Rust library. The question is what it lacks: transitions over bits, conditions over
      register boundaries, barrier domain in the type.

### Syntax — open decisions (details in [`dokumente/SYNTAX.md`](dokumente/SYNTAX.md))

- [ ] **Version evolution:** ~~does an `@version 3` reader also read v2 — refusal or
      migration? Both defensible, neither decided.~~ **ENTSCHIEDEN am 2026-08-21: die
      ABSAGE**, und sie ist gemessen statt abgewogen.

      ```
      16 `@version`-Textstellen in Korpus + FRAGMENTE:  12 × „1", 2 × „17"
       8 VERSCHIEDENE Deklarationen — `messung/fragmente/` ist byteidentisch mit FRAGMENTE.md
       1 weitere in `dokumente/SPRACHE.md`: die einzige `@version 3` des Ordners
       0 Formate mit einer zweiten Fassung        — `./instrumente/zaehle-formate.py`
      ```

      **Null gemessene Formatentwicklungen.** Deklarierte Migration hieße: eine
      Abbildungsvorschrift je Feldpaar, ein Erzeuger dafür, und damit eine neue Schablone —
      **Vertrauensfläche für einen Bedarf mit null Fundstellen.**
      Der Einwand *„ein Kernel, der ein v2-Gerät findet, muss etwas tun können"* stimmt und
      trifft nicht: **„etwas tun" ist nicht „migrieren".** Eine benannte Absage *ist* eine
      Handlungsmöglichkeit, und der Rufer entscheidet, ob er einen v2-Leser hat.

      > **Das ist wörtlich die Regel, die `locks ordered` getötet hat** — *kein Konstrukt ohne
      > gemessenen Bedarf* ([`dokumente/HISTORIE.md`](dokumente/HISTORIE.md)). Und der Satz,
      > der die Empfehlung erledigt hat, gehört daneben: **„Vollständigkeit vor Einfachheit"
      > darf nicht zu „Vollständigkeit vor gemessenem Bedarf" werden.**

      ~~*Was offen bleibt, ist die Zählung selbst als Befehl:* die 14 Angaben sind von Hand
      genommen, also eine Zahl ohne Werkzeug.~~ **Geschlossen am 2026-08-21:
      [`./instrumente/zaehle-formate.py`](instrumente/zaehle-formate.py) rechnet sie nach, und
      der Wächter hält sie.** *Die Handzählung stimmte — und sah zwei Dinge nicht:* dass die
      Korpushälfte dieselben sieben Zeilen ein zweites Mal zählt, und dass die einzige
      `@version 3` des Ordners **außerhalb der Menge lag, auf die sich die Entscheidung
      berief**. Beides ändert den Schluss nicht und wäre ohne Werkzeug nie aufgefallen.

      > **Und was beim Messen aufflog, ist mehr wert als die Zahl: `@version` hat KEINEN
      > LESER.** `grep -rn "\.version" --include=*.rs crates/` findet null Stellen — geparst
      > (`parse.rs:3225`), gespeichert (`ast.rs:1223`), von keinem Pass, keinem Erzeuger und
      > keinem Zeugnis gelesen. *Dieselbe Klasse wie `obermenge`/`gates`/`mirrors` vor «K5».*
      > **Nur ist die Antwort hier nicht „einen Leser bauen":** ein Leser machte `@version` zur
      > Formatidentität, und das IST die Migration, die diese Entscheidung ablehnt. Der eigene
      > Posten dafür steht unten.

- [ ] **`@version` wird geparst und von NIEMANDEM gelesen** *(gemessen 2026-08-21, beim
      Nachrechnen der Entscheidung darüber)*. `pub version: Option<u128>` steht in
      `ast.rs:1223`, gefüllt von `parse.rs:3225` —
      `grep -rn "\.version" --include=*.rs crates/` findet **null Lesestellen**. Die Zahl
      nimmt an keiner Identität, keinem Layout und keinem erzeugten C teil.
      **Dieselbe Klasse wie `obermenge`/`gates`/`mirrors`/`counterprobe` vor «K5» — eine
      Klausel ohne Leser.** *Nur ist die übliche Antwort hier die falsche:* einen Leser zu
      bauen hieße, `@version` zur Formatidentität zu machen, und das **ist** die Migration,
      die am selben Tag abgesagt wurde. **Was fehlt, ist kein Pass, sondern ein Satz an der
      Grammatikstelle** — der steht seit dem 2026-08-21 in `SYNTAX.md` §9; offen bleibt, ob
      ein Wächter ihn hält.

- [ ] **The stock of quantifiers in `spec fn` is undecided — and that is exactly where the line moves**,
      if nobody watches.

- [ ] **The keyword language** is in English, because that is what the existing code is. Price: a break with the
      German running text. Reversible (one table in the lexer).

### Paper steps — not a line of code. Every item can kill the thesis

> **Renamed 2026-08-14.** This heading was called "P0", the next one "P1" — and
> [`dokumente/SPRACHE.md`](dokumente/SPRACHE.md) §6 assigns P0…P7 to the **checker plan**, where P1 is the
> grammar unification and not `check`. **Two label systems with the same names
> in the same file**; the same error class as the G collision further up.

- [ ] **`touches` is too coarse** — it needs a form for "changes the set only through
      consumption". Without it the ordering hangs on a promise instead of on a condition.

### Performance — two items, both before the first benchmark


---

- [ ] **Amortise the bound check:** `bounded N ops` does not have to be checked per
      iteration. `progress` carries the termination, the bound is a **watchdog** — a check
      **every 2^k iterations** lowers the cost to ~1/2^k, the promise becomes "breaks after at most
      N + 2^k". **Decide before the first benchmark**, otherwise it measures a construct nobody
      would build that way.

- [ ] **The tension lowering-flat against fast is unpriced.** The folder has paid it only on the
      correctness side; on the performance side the lowering is a **bet on the
      C compiler**, and it hangs on the unwritten form table.

### «OPT» — schnelles und sicheres C, geplant 2026-08-19 ([`dokumente/PLAN.md`](dokumente/PLAN.md))

*Gemessen, `cc -O2`: die Schrankenprüfung ist **nie da** — `M103` beweist sie zur
Übersetzungszeit, und `effects { reads o }` ist schon heute `const Objekte *o`.*


- [ ] **OPT1 — `restrict` ist der grösste Hebel, und er ist gesperrt.** Gemessen: **2,85**
      wo `cc` die Herkunft nicht sieht, **1,00** wo doch. Zum Vergleich kostet die
      Schrankenprüfung **1,34** bzw. **1,00**. *Die Aliasfrage ist über dreimal so viel wert
      wie die Schranken.* Gabbro darf `restrict` heute **nicht** setzen: `own` kauft keine
      Exklusivität (`R004` deckt nur die syntaktische Hälfte). **M3s offener Rest hat damit
      einen Preis**, und die Sprachentscheidung lautet: `own` als Freigabeoperation trägt
      `restrict`, `own` als Signaturvermerk nicht.

- [ ] **OPT2 — fünf Angaben, die ein Pass schon hält und der Erzeuger verschenkt.**
      `pure` → `__attribute__((pure))`, `-> never` → `_Noreturn`, `tagged` → `switch` **ohne
      `default`**, `u32 in 0 .. 63` → der kleinste C-Typ. **`costs` gehört NICHT dazu** — eine
      Iterationszahl ist eine Eigenschaft des Programms, eine Zeitmessung nicht («B24»). Und
      die Falle: GCCs `const` verbietet **jedes** Lesen von Speicher, Gabbros `pure` erlaubt
      Parameterlesen — *zwei Wörter, die dasselbe heissen und Verschiedenes bedeuten.*

- [ ] **OPT3 — `asm` als VERSIEGELTES Loch, mit pflichtigem `arch`, `effects`, `costs`,
      `clobbers`.** Ein `asm`-Block ist ein Loch in jedem der zwölf Pässe; ohne Versiegelung
      wird jede Zusage zu einer Aussage über das, was *vor* dem Block stand. Alles daran ist
      **Annahme**, nicht Prüfung — Gabbro liest den Befehlstext nicht —, also gehört jeder
      Block **ins Zeugnis**, neben `extern fn` und `entrust`. **Und die entstehende Zahl ist
      die eigentliche Aussage: wie viele Zeilen Assembler trägt ein Gabbro-Kern?**

- [ ] **Die Vergleichsmessung aus P5s Tor („erzeugt ≤ Handschrift + Rauschen") EXISTIERT
      NICHT.** Solange sie fehlt, wird über die Geschwindigkeit des erzeugten C **nichts**
      behauptet. *Ein Erzeuger, der schnelles C liefert, das manchmal etwas anderes rechnet,
      ist schlimmer als einer, der langsames liefert — er sieht aus wie ein Ergebnis.*

### «Z» — Zwischenspeicher, geplant 2026-08-19 ([`dokumente/PLAN.md`](dokumente/PLAN.md))


- [ ] **Z0 — Umgebung und Aufrufgraph EINMAL bauen.** Gemessen: 14 Module rufen
      `Umgebung::sammle` (18 Aufrufe je Lauf, 358 ms auf 120 k Zeilen), sechs bauen den
      Aufrufgraphen (6 Aufrufe, 252 ms). **610 der 672 ms Passzeit sind der Neubau
      derselben zwei Strukturen**; die eigentliche Passlogik kostet ~60 ms. Erwartet:
      899 → ~290 ms. *Der Preis ist echt:* die Pässe hören auf, einzeln fahrbar zu sein,
      und die Mutationsproben nutzen das heute.

- [ ] **Z1 ist ein `cargo`-MERKMAL, standardmässig AUS** *(entschieden 2026-08-19)*. Nicht
      weil er schwer wäre, sondern weil er eine Klasse stiller Fehlurteile eröffnet und die
      Zahl ihn heute nicht verlangt (~190 ms für ganz Caprock nach Z0). **Ein Merkmal, das
      aus ist, ist keine Vorstufe, sondern eine Wahl mit Adresse.** Drei Auslöser, jeder
      einzeln genügend, stehen im Plan, *damit sie nicht im Moment des Wunsches erfunden
      werden*: ein Lauf > 3 s, dateiübergreifende Einheiten, oder ein Wächter bei jedem
      Commit. **Und ein Wächterlauf `--features speicher` gehört in denselben Commit** —
      sonst ist das ausgeschaltete Merkmal genau der tote Anker, den dieser Ordner am
      2026-08-19 fünfundzwanzigmal aus dem Mutationskatalog gezogen hat.

- [ ] **Z1 — der Speicher je Übersetzungseinheit, und sein Schlüssel.** Heute ist eine
      Datei eine ganze Einheit (gemessen: die CLI schleift über Dateien, kein Binden über
      Dateigrenzen), also ist der Schlüssel trivial vollständig. **Der Satz wird als
      erster falsch**, sobald `use` über Dateigrenzen greift — und dann liefert ein
      Schlüssel, der nur die eine Datei hasht, veraltete Urteile. Ins Bauzeichen gehört
      ein Hash über die Prüferquellen, sonst antwortet ein NEUER Prüfer mit ALTEN Absagen.

- [ ] **Z2 — die Emission muss REPRODUZIERBAR ZUGESAGT sein, nicht beobachtet.** Gemessen
      ist sie es (25 Läufe, ein SHA-256, kein Zeitstempel im Kopf), aber `pruefe-emission.sh`
      hält es nicht: ihm fehlt die Zeile *zweimal erzeugen, Hashes vergleichen*. Ohne sie
      ruht jeder `ccache`-Treffer auf meinem Gedächtnis.

- [ ] **Die Abbruchbedingung ist ernst gemeint: prüft Caprock nach Z0 unter einer Sekunde,
      wird Z1 NICHT gebaut.** Der Durchsatz ist linear (~7,5 µs je Zeile), Caprock hat
      75 294 Zeilen, das sind ~570 ms heute und ~190 ms nach Z0. *Ein Speicher, der eine
      Sekunde spart und eine Klasse stiller Fehlurteile eröffnet, ist ein schlechtes
      Geschäft.*

### `check` without a language


---

---

- [ ] **`check` as a Rust macro library**, retroactively against the 33 measurement-discipline traps, each with a
      mutation. Gate: **≥ 5 caught**. Useful even if Gabbro never comes into being.

### Aus «H2» *(ausgefuehrt 2026-08-19, `H = 17 → 15`)* — der Rest, den der Lauf hinterliess *(Teil)*

- [ ] **Die zwei Gleitkommasonden gibt es als NAMEN, nicht als Programm**
      *(2026-08-18)*. `sonde_mxcsr_rne` und `sonde_keine_ueberbreite` stehen im Manifest, und
      damit ist die Annahme falsifizierbar ERKLAERT. **Geschrieben ist keine von beiden.**
      *Das Manifest sagt selbst, dass es nur die Sonde nennt und nicht ihren Lauf* -- aber ein
      Name ohne Programm ist die schwaechste Form von falsifizierbar, die es gibt.

- [ ] **`F003` (Rundungsmodus im Typ) ist heute UNERREICHBAR, und das ist die Antwort**
      *(2026-08-18)*. Die Absage soll einen anderen Modus als RNE treffen -- **es gibt keine
      Form, einen zu schreiben.** Sie jetzt zu bauen hiesse, drei oder vier Woerter in den
      Wortschatz zu nehmen, deren einziger Zweck es waere, abgelehnt zu werden: eine
      Spracherweiterung ohne gemessenen Bedarf (W3). *Die Entscheidung `f64<RNE>` bleibt
      gebucht; die Absage entsteht mit ihr, nicht davor.*

- [ ] **`F003` (Rundungsmodus im Typ) und `F006` (`long double`/`f16`)** *(2026-08-18)*. Die
      beiden letzten Absagen der Familie. `f64<RNE>` waere die vierte Instanz eines
      vorhandenen Musters (`ptr<…>`, `atomic … seq`, `format … endian`); `long double` wird
      benannt abgelehnt, und der Korpus begruendet es (FF2: eine Sprosse von sieben).

- [ ] **Produkt, Quotient und die Null haben ihren Satz noch nicht**
      *(2026-08-18)*. `Intervall_Aussen.thy` deckt die SUMME. Fuer Produkt und Quotient
      rechnet der Pruefer ueber die vier Ecken; dass das Minimum der vier die untere Schranke
      ist, braucht Monotonie in beiden Argumenten und eine Fallunterscheidung nach Vorzeichen.
      Die Null ist ein eigener Satz: `-0.0` liegt in `0.0 .. 1.0`, und `1.0 / x` gibt `-inf`.

### «F» — f32 und f64, geplant 2026-08-18 (`PLAN.md`, „«F» — f32 und f64, vollstaendig")

**Der Beschluss weicht von W3 ab und sagt es:** der Bedarf ist gemessen null, die Entscheidung
zu bauen ist die des Ordners. **Ersatz fuer die Bedarfszaehlung ist der Korpus, und er kommt
zuerst** -- sonst entwirft man fuer eine vorgestellte Verwendung.




- [ ] **F0: drei bis fuenf echte Gleitkommafragmente**, jedes mit seinem Befund. *Der Bedarf
      darf entschieden werden; er darf nicht erfunden werden.*

- [ ] **F1: sieben Entscheidungen vor der Grammatik.** Die tragende ist die dritte: **die
      Negation liefert ihre Tatsache GENAU DANN, wenn beide Operanden als Nicht-NaN bekannt
      sind.** Damit ist die Verengungsmaschinerie bedingt statt abgeschaltet -- *ohne diese
      Entscheidung ist Gleitkomma in Gabbro unbrauchbar, mit ihr gewoehnlich.*

- [ ] **F3: die sechzehn gemessenen Stellen** (`umgebung` 6, `m1` 6, `typen` 4) entscheiden je,
      was sie mit `Typ::Gleitkomma` tun. **Keine darf stillschweigend durchfallen.**

- [ ] **F5/F6: die Einheit rechnet mit Gleitkomma -- das gehoert ins ZEUGNIS.** Es aendert
      Aufrufkonvention und Kontextwechsel; fuer einen Kernel ist es eine Aussage ueber
      Preemption, nicht ueber Zahlen. Dazu SSE2 als Annahme mit Falsifikator.

- [ ] **P-F1 ist das wichtigste Tor: der GANZZAHLPFAD bleibt bitgleich**, nachgewiesen von
      einer Differenzeinheit statt von einem Eindruck. *Wer dort etwas verschiebt, beschaedigt
      eine Sprache mit gemessenem Bedarf zugunsten einer mit entschiedenem.*

- [ ] **`backed` steht im Pruefer und noch nicht im ZEUGNIS** *(2026-08-18)*. Eine Einheit,
      die Adressraum von Speicher trennt, sagt damit etwas ueber ihren Speicherbedarf --
      **und das Zeugnis nennt es nicht.** Dieselbe Klasse wie die Gleitkommazeile: der Leser
      muss es sehen, ohne den Quelltext zu lesen. *Dazu die Frage, ob der Erzeuger die
      Reserve als Feld anlegen soll oder ob sie eine Aussage an den Binder ist.*

- [ ] **Wer die Hinterlegung ERHOEHT, verspricht die Seiten** *(2026-08-18)*. `M108` haelt
      jeden Zugriff unter `backed`; dass die Seiten dahinter wirklich eingehaengt sind, ist
      eine Aussage ueber den Verwalter und steht in keiner Annahme. **Der Kernel ist selbst
      die Instanz, die sie einhaengt** -- die Zusage gehoert damit in die Axiomschicht, mit
      Sonde, oder an eine `ensures`-Klausel der einhaengenden Funktion.

- [ ] **`i < N` ist nicht `i ist hinterlegt`** *(2026-08-18)*. Eine `table count 1000000000`
      geht sauber durch und senkt zu einem Feld von knapp 30 GiB ab. Was Gabbro NICHT sagen
      kann: dass nur die ersten `k` Plaetze hinterlegt sind. Ein Zugriff auf einen nicht
      hinterlegten Platz ist typkorrekt und trotzdem ein Fehlzugriff -- **und in einem Kernel
      ist das besonders scharf, weil er selbst die Instanz ist, die Seiten hinterlegt.** Das
      ist der Bedarfsbeleg fuer die wertgetragene Schranke.

- [ ] **Bindet `stack` an eine Deklaration?** *(offen seit 2026-08-18)*. `entrust … at NAME`
      wird gehalten (`N006`), der Stapel nicht. Ein Gaststapel ist womoeglich ein
      Bindersymbol und keine Gabbro-Deklaration -- **die Frage ist eine Entscheidung, keine
      Bauarbeit**, und bis sie faellt, steht `stapel` als FREMD gebucht.

### From the paper test of 2026-08-14 — one dead and two live candidates

> **One candidate died on 2026-08-14 and therefore stands here NO LONGER:**
> `locks ordered` — zero test cases in the tree. The obituary stands in
> [HISTORIE.md](dokumente/HISTORIE.md), the measurement in [MESSUNGEN.md](dokumente/MESSUNGEN.md).
> *This file carries exclusively what is open; a construct that has died is not a done
> item but a break with our own intention — and that belongs in the history.*



### Later



---

---

- [ ] **Binary verification** — the only route that takes the lowering out of the trust base.
      A project of its own.

- [ ] **Reusable specification theories** — they help the **second** project. May be counted in
      no cost calculation as long as there is one kernel.

---

# Historie dieser Datei  ⟨Z⟩

*Was hier stand, bevor der Schnitt nach dem Plan kam — die Datei hat sich dreimal über sich
selbst geirrt, und jedes Mal hat die Korrektur mehr gebracht als die Zahl, die sie ersetzte.*

> **Cut by ROLE 2026-08-16.** The file had put this question to itself in the reconciliation of
> the 14th and left it unanswered — *"a list in which half a day of paper stands next to a
> subproject no longer sorts, and a list that does not sort does not get read."* Four roles:
> **decisions · measurements · building · bookkeeping.**
> On top of that **six outdated places** have been pulled up (the five scratchpad classes, the
> 17-way split, the four domain fragments, "compiler up to P3", the call effects,
> "P2 at 1 of 6") — *exactly the class the reconciliation of the 14th has already paid for once.*
>
> **Tidied up 2026-08-16.** The eight design and measurement documents now lie in
> [`dokumente/`](dokumente/); in the root directory there stand only **README, TODO and DONE**.
> **Twenty items have been checked against the CODE and moved to [`DONE.md`](DONE.md)** —
> not against memory: per item a refusal code, a file or a command line.
>
> **Caprock items taken out 2026-08-16.** This list carries **Gabbro**. Whatever has its subject
> in Caprock's code or bookkeeping belongs there — even if it arose here. *A task list that
> carries two projects sorts for neither.*
> Taken out: eager FP, K1–K3, N2, the two open plumbing obligations,
> progress/starvation (D8). **Not deleted, but moved to
> [`dokumente/AN-CAPROCK.md`](dokumente/AN-CAPROCK.md)** — they are findings, only
> not ours.
>
> **Reconciled 2026-08-14.** This file carries **exclusively what is open**; what is done stands
> in the design files, what is refuted in [`dokumente/HISTORIE.md`](dokumente/HISTORIE.md), what is measured in
> [`dokumente/MESSUNGEN.md`](dokumente/MESSUNGEN.md). The reconciliation on 2026-08-14 found the file **untrue
> about itself in eight points** — eight done entries, six statements the folder had
> overtaken, three topics carried twice, two colliding label systems and
> stale numbers from P1. **A list that is not right costs more than none:**
> it says at every point "this is still open", and the reader believes it.
> What the reconciliation found item by item stands at the end under *Reconciliation*.

---


> ~~**B3**~~ → ~~**K/A/W substitution**~~ → ~~**`effects` reading**~~ → ~~**closures**~~ →
> ~~**`table.induktion` into Isabelle**~~ → **group `ops` → P5 → P6 → P7**

> **The path changed its head on 2026-08-16, and against its own earlier
> statement.** Not group `ops`, but **the first proved template**. The reason is
> not effort but a curve: *the amortisation argument — a template falls
> ONCE, not per program — **holds only from the first proved template onwards.*** Until then
> the template list is structurally the same mountain as seL4's proof mountain, only unclimbed.
> **One proved out of eighteen is qualitatively something other than zero out of seventeen:** the
> register changes from *"list with a length"* to *"list with a fall direction"*.
>
> `table.induktion` is the smallest, it has been marked as an L3 item since the INDUCTION entry,
> and **it has not got its turn for days, because it competes with nothing except
> everything.**

**The first two fell on 2026-08-16** (`DONE.md`), and the substitution has **shortened** the path
rather than lengthened it: `p_B3 = 0,0096`, surcharge `≥ +0,05` — *below the resolution of the
metric.* **B3 is done as a cost item; ~~the metric stays open at `≥ 1,90`~~ — die Zahl ist am
2026-08-19 ZURUECKGEZOGEN und lautet `unbekannt, > 0,5`**, weil `w` an VERUS-Zeilen gemessen
war und Gabbro in Isabelle/HOL beweist. *Die Pflichtseite bleibt der Ort, an dem sie haengt;
nur steht dort jetzt keine Zahl.* The head position now belongs to the
decision, not to the measurement.

> **And the sentence the measurement chain produced belongs at its head:** *the expensive
> obligations are **many, but small*** — W = 38 of 73 by head count, but only 34 % of the lines; a
> W obligation is on average **half the size** of a K or A obligation (`dokumente/BEWEIS.md`).
> **The distance to the floor therefore hangs almost entirely on the W column itself**, not on
> loop forms. Whoever wants to attack the design attacks there.

**Everything else is parallelisable or a memo.** And the only item on this path that is
neither code nor a run but **a word of the folder** is the slot:

| | |
|---|---|
| **`M-effects-lesen` — direction** | **A** — redeclare the ten fragment functions (2026-08-16) |

**Justification, and it has two parts, both of them checkable:**

1. **E3 consistency.** The folder says at every other point *"nothing is implicit"*. A
   coarser frame promise (C) would be exactly the silent exception — a read that names no line
   because the line would get too long.
2. **A is the reading whose violation the pass can report PRECISELY.** C reports
   *"read somewhere outside `mmio`/`dma`/`atomic`"*; A reports **which function
   reads which place without naming it**. *What cannot be reported exactly, no
   pass enforces — the same justification reading B died on.*

**The pre-registered price was a factor of three — and it did NOT occur.** The memo
said *"A drops 10 of 32 functions, C drops three"*. Measured after the pass was built
(`dokumente/MESSUNGEN.md`, *Lesart A gebaut*): **0 of 32.** `FRAGMENTE.md` already declares its
reads; what fell were **two of my own examples**, and that is not a property of the
reading but of my care in writing.

**Reading B had already been eliminated before that** — by its own finding: it is not
mechanically separable, and *what cannot be counted, no pass can enforce.*

**The unbuild route (R12) still stands:** the read half is an addition in `wirkungen.rs` against
the same list the write side runs against. If it falls, one refusal class falls —
*no grammar change, no data type, no example has to go back.*

*The direction stands and is built (`E010`). With that the critical path is for the first time free
of items that are neither code nor a run — what remains is building and measuring.*

---

---

# BOOKKEEPING  ⟨Z⟩
### The order, cheapest first — three documents converge on ONE missing number

1. ~~**The five scratchpad classes into the repo.**~~ **RUN 2026-08-15** as
   *a fresh collection of all eleven* — `N_neu = 5`, today 4. The 19 are **replaced, not
   continued**; their subject was no longer nameable (W7).
2. ~~**Split the 17 measured logic obligations**~~ **RUN 2026-08-16** over
   `N_L = 81`: K = 28, A = 13, W = 40 — and **booked as MISSED** over the
   corrected population (`N_L = 73`, W = 38), because eight seq lemmas
   are tool artefacts. **What is missing is B3** — without line shares no
   substitution into the weighting formula. *(originally:)* split into *by construction · descent statement
   (generated scheme bites) · value statement (does not bite)*. **Half a day of paper, and the
   greatest leverage in the folder:** the gap calculation ends at "k unknown", the hard
   promises end at the same split, and the ceiling of the step promises hangs on it.
   **Three documents, one number.**
3. ~~**The four missing domain fragments**~~ **WRITTEN 2026-08-16** (F7–F10). The
   convergence bet has its data points: **four fragments, zero new constructs** — and in
   the second column **three changed meanings** («B37», «B38», «B39»).

> **~~No checker line before the result of 2.~~ — VIOLATED on 2026-08-14, on announcement.**
> The compiler was begun before the result of 2. The rule stays standing here,
> struck through instead of deleted: what it was meant to prevent has happened — P2 and P3
> can no longer kill the thesis *before* the compiler is built. What the build brought in
> stands in [`dokumente/MESSUNGEN.md`](dokumente/MESSUNGEN.md); what it cost stands here.
### Reconciliation — what 2026-08-14 found in this file

**The question was whether this list is still sensible at all.** Answer: the **content** yes,
the **bookkeeping** no. Eight classes of finding, all mechanically demonstrable:

| | Finding | done |
|---|---|---|
| **1** | **Eight `[x]` entries** in a file whose closing sentence reads "exclusively what is open" | taken out; each is recorded elsewhere (see below) |
| **2** | **"there is no compiler (P2–P7)"** — there is one up to P3 | corrected |
| **3** | **Two ordering rules stood there as being in force although they are violated** ("no checker line before 2", "not a line of Rust") | struck through with a date, not deleted |
| **4** | **"Six of the nine passes are missing"** — it is five whole and two half | corrected |
| **5** | **Stale numbers from P1**: 117 rules, 187 terminals (today 154 / 219) | taken out along with the entry |
| **6** | **Three topics twice** — `narrow` three times, *variable lengths* and *version evolution* twice each | drawn together |
| **7** | **Two label systems with the same names**: the headings "P0"/"P1" against the checker plan P0…P7, where P1 is the grammar unification | renamed |
| **8** | **Four done items carried as open**: `by consuming` (has stood in the grammar since `dokumente/SYNTAX.md`:416), `vtd.rs` and `space.rs` (both run, see `dokumente/MESSUNGEN.md` P0.2/P0.3), P0.4 (run, `dokumente/MESSUNGEN.md`) | taken out |

**And one that is mine:** the correction *"the mark ≤ 24 is missed, not open"*
I reported as done on the same day — in `dokumente/MESSUNGEN.md` it was, **here it was not**.
The replacement missed the quotation mark and ran silently into nothing. *A correction
one reports without looking it up is the same movement as a number one claims
without measuring it.*

### What that says about the form of this file

It has **grown chronologically** — every day appended at the bottom, and nobody went back.
Exactly the prehistory out of which the folder drew its 24 files together to 9 on 2026-08-14.
**The next question is therefore not a tidying question but a question of role:**


### Where the removed items are recorded

| Item | Source |
|---|---|
| P1 — grammar unification | [`dokumente/SPRACHE.md`](dokumente/SPRACHE.md) §6 (checker plan), guardian `pruefe-syntax.sh` |
| P2 — lexer and parser | [`dokumente/MESSUNGEN.md`](dokumente/MESSUNGEN.md), section *P2* |
| P3 — M1 + V1–V3 | [`dokumente/MESSUNGEN.md`](dokumente/MESSUNGEN.md), section *P3* |
| `revoke` on paper | [`dokumente/MESSUNGEN.md`](dokumente/MESSUNGEN.md), *P0.1* |
| P0.1b — witness ordering | [`dokumente/SPRACHE.md`](dokumente/SPRACHE.md) §9.2 |
| `by induction over` | [`dokumente/SYNTAX.md`](dokumente/SYNTAX.md) §5, [`dokumente/SPRACHE.md`](dokumente/SPRACHE.md) part V |
| seL4 split, SPARK ladder | [`dokumente/PLAN.md`](dokumente/PLAN.md) |
| `vtd.rs`, `space.rs`, P0.4 | [`dokumente/MESSUNGEN.md`](dokumente/MESSUNGEN.md), *P0.2/P0.3* and *P0.4* |
| **G1–G11** (2026-08-15) | [`dokumente/SYNTAX.md`](dokumente/SYNTAX.md) (EBNF pulled up), `beispiele/11-grammatikbefunde.gab`, poison `43`–`45` |
| **Counter rule** (2026-08-15) | [`dokumente/SPRACHE.md`](dokumente/SPRACHE.md) §1, *„Die Zaehlerregel"* |
| **F4/F6 outdated** (2026-08-15) | [`dokumente/FRAGMENTE.md`](dokumente/FRAGMENTE.md); **gate P2 stands at 10 of 10** (2026-08-16) |
| **Mutation generator** (2026-08-15) | `erzeuge-mutationen.py`, advance protocol + result in [`dokumente/MESSUNGEN.md`](dokumente/MESSUNGEN.md) |
| **TODO guardian** (2026-08-15) | `pruefe-todo.py`, seven classes with a speech test |

### To be re-checked, because quoted from memory


---
- [ ] **The freedom of the name "Gabbro"** across package registries, GitHub and language lists — together with what
      was found. "I found nothing" is a null finding without a size.

### What that says about the form of this file

It has **grown chronologically** — every day appended at the bottom, and nobody went back.
Exactly the prehistory out of which the folder drew its 24 files together to 9 on 2026-08-14.
**The next question is therefore not a tidying question but a question of role:**

---

## Aus der Absenkungsmessung (2026-08-28) — [`messung/ABSENKUNG.md`](messung/ABSENKUNG.md)

*Angefügt am Ende, additiv. Alle fünf sind gemessen, keiner ist geschätzt.*

- [ ] **`gabbro zeugnis` ist blind für `ops`** — und das ist genau der Fall, gegen den `K100.4`s
      Kreuzprobe gebaut wurde. Zwei Dateien mit einem Zeilenunterschied (`ops insert, remove,
      relabel;`): das erzeugte C wächst von 26 auf 73 Zeilen und bekommt drei Funktionen,
      **das Zeugnis ist byteidentisch** und meldet weiter `1 templates (0 of them UNPROVED)`.
      `grep -c 'table.ops.erhaltung' crates/gabbro-check/src/zeugnis.rs` → `0`.
      **`UNZUGEORDNET` fällt nicht**, weil `ops` eine Klausel INNERHALB eines schon
      eingeordneten `table`-Items ist und der Auffangzweig auf Item-Ebene sitzt.
      *Der Erzeuger ist innerhalb eines eingeordneten Items gewachsen, und der Wächter, der
      genau diesen Fall fangen sollte, sieht ihn nicht.* Dieselbe Klasse wie `W16`.

- [ ] **`ops` ist an NULL Stellen durchgestochen.** `grep -c relabel instrumente/pruefe-emission.sh`
      → `0`; `ops` steht an genau einer Korpusstelle (`beispiele/47-ops-wortmenge.gab`), und die
      ist unter den 24 Durchstichen nicht dabei. Die drei jüngsten erzeugten Formen werden
      erzeugt und übersetzt, aber **nie ausgeführt und nie mit einer Handschrift verglichen**.
      *Der billigste offene Posten der ganzen Absenkungsmessung.* Und er beantwortet nebenbei
      `K4` aus `messung/ABSENKUNG.md`: findet ein Durchstich die Abweichung am freien Platz von
      selbst, oder nur, weil ein Satz sagt, wo man hinsehen muss?

- [ ] **`A8` („18 claims open") ist nachgerechnet: 12 eingelöst, 2 offen, 4 WIDERLEGT** —
      und die vier Widerlegungen brauchen eine Heilung in `dokumente/SPRACHE.md`:2621–2638.
      **Nr. 5** behauptet für `linear Uninstalled(Object)` „disappears"; `emit.rs`:1355–1366
      erzeugt für `linear type T;` **ein Byte**, und `SPRACHE.md`:750 sagt vier Seiten früher
      selbst *„echte Ressource: Bytes im Erzeugnis"* — **der Tabellenzeile fehlt das Wort
      `ghost`.** **Nr. 8** behauptet „generated `printf`"; `grep -c printf
      crates/gabbro-check/src/emit.rs` → **0**, und `measures` erreicht keine erzeugte Zeile.
      **Nr. 12** behauptet „none" für `breaking`; `emit.rs`:5614 **weigert sich** — 53 Dateien
      in `beispiele/` gegen `MARKE_EMIT=52`, und die eine ist `beispiele/53-zwei-orte.gab`.
      **Nr. 18** behauptet `#if`; gebaut ist ein Filter vor dem Erzeuger (`gatter.rs`:111).
      Offen bleiben **Nr. 3** (`chain` + Generationsstempel — null Zeilen Code im ganzen Baum)
      und **Nr. 6** (`Duty` wird nirgends erzeugt, `namen.rs`:1445 sagt es selbst).
      *Eine widerlegte Behauptung ist teurer als eine offene, und `A8` zählte zwölf Erledigte,
      zwei Offene und vier Irrtümer als achtzehn gleiche Einheiten.*
      **Und drei der vier Widerlegungen sind Widerlegungen durch den ERZEUGER, nicht durch C.**

- [ ] **Die achtzehn brauchen einen Wächter, und heute kann keiner sie sehen.**
      `pruefe-zahlen.py`s Reichweitenzähler verlangt eine **fett** gesetzte Zahl in einer
      Tabellenzelle; `A8` schreibt `18 claims open` ohne Fettung, also meldet er sie nicht
      einmal als unbewacht (`sed -n '859p' dokumente/PLAN.md | grep -c '|\s*\*\*[0-9]'` → 0).
      *Vier Widerlegungen in einer einzigen Auszählung sind der Beleg dafür, dass eine Tabelle
      ohne Wächter kein Register ist.*

- [ ] **Der parametrische Absenkungssatz für `insert` und `remove`.**
      `beweise/Absenkung_Parametrisch.thy` hat ihn für `relabel` — sechs benannte Eigenschaften
      der Zielsemantik, keine davon nennt C oder eine Maschine. `insert` schreibt **zwei**
      Anweisungen und verlangt damit eine **siebte**: die Hintereinanderausführung. *Ob die sich
      parametrisch hinschreiben lässt, ohne eine Auswertungsreihenfolge festzulegen, ist die
      Frage, an der die zweite Naht ein zweites Mal zieht* (`messung/ABSENKUNG.md` §2.3, `K2`).

- [ ] **Die S-Nummern in den Theorieköpfen sind sämtlich veraltet.** `gabbro schablonen` vergibt
      `S{n+1}` **positionsabhängig** über `SCHABLONEN.iter().enumerate()`; die Kopfkommentare der
      Theorien zitieren Stände von vor mehreren Umsortierungen — `table.ops.erhaltung` steht als
      `S5` und ist `S6`, `table.absenkung` als `S15` und ist `S16`, `consuming.ordnung` als `S1`
      und ist `S3`. **Kein einziger Kopf trifft die heutige Position, und kein Wächter prüft es.**
      Der Name ist stabil, die Nummer ist es nicht — *wer nach S-Nummern quer liest, liest falsch.*
