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

| Stufe | | warum hier |
|---|---|---|
| **0** | die Messschicht | vier Instrumente wurden am 2026-08-20 dabei erwischt, dass sie nicht mehr messen. **Alle vier Ziele werden an Zahlen gesteuert** |
| **1** | der Maßstab | `H` misst zu sieben Zwölfteln die Vollständigkeit des Korpus, nicht die Deckung von Gabbro |
| **2** | Nutzbarkeit messen | das einzige Ziel ohne Instrument |
| **3** | die offenen Lesarten entscheiden | keine Grammatik, keine Schablone — **kostenlos für Ziel 2** |
| **4** | Programme schreiben, nicht Konstrukte | jedes echte Programm hat sofort Befunde geliefert; der Korpus ist von der Sprache nach außen geschrieben |
| **5** | die Beweise tragend machen | **läuft PARALLEL zu 4** — ein Beweis ohne Hersteller seiner Prämisse ist gefährlicher als eine ungeprüfte Zusage |
| **6** | die fremden Rümpfe sprechen lassen | die eine Klasse, die sich auch unter „ganz Gabbro verifiziert" nicht auflöst |
| **7** | was Programme groß macht | `fnptr`-Erzeuger, dann sein Vertrag; ABI; Generizität |
| **8** | PL — die Logik des Prüfers | ohne die Sätze ist „formal verifiziert" nicht formulierbar |

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

# STUFE 0 — DIE MESSSCHICHT

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
| **`./pruefe-zahlen.py`** | das Register der Befehle. **34 Kennzahlen mit Befehl** *(Stand 2026-08-20; 12 am Vormittag)* — und die Zahl steht hier OHNE Befehl daneben, mit Bedacht: ein Register, das sich selbst zaehlt, hat einen Fixpunkt (W18). Es zählt daneben, was es *nicht* bewacht. Sprechprobe über alle, in beide Richtungen |
| **`./pruefe-waechter.py`** | der Wächter über den Wächtern. Vier Forderungen, **25 von 25 Instrumenten** tragen die drei statischen. `--lauf` führt die leichten wirklich aus, mit Frist; die fünf schweren stehen mit Grund daneben, die zwei mit fremdem Korpus ebenso |
| **`./zaehle-karten.py`** | neu — direkte Blicke auf die Karten der `Umgebung`, an `suche` vorbei |
| **`./zaehle-theorien.py`** | neu — die Zeilenanteile der eigenen Theorien, und wer den Beweisschritt gesucht hat |

**Sechs Befunde beim ersten Lauf, keiner davon gesucht:** `pruefe-beweise.sh` kündigte eine
Zeitgrenze an und setzte sie nie durch (`ZEIT=600` stand in der Kopfzeile, der Wachhund sah nur
den Speicher) · `zaehle-b3.py` druckte `! ABBRUCH` und endete mit 0 · `pruefe-abstieg.py` war
nicht ausführbar · drei Wächter hatten keine Sprechprobe · fünf führten `cargo`/`cc` ohne Frist
aus. **Und einer an mir selbst:** ich formulierte die Wächterzahl im README aus ihrem Muster
heraus, und `pruefe-todo.py` meldete *„sauber"* über einer falschen Zahl. *Seit heute ist ein
Muster ohne Treffer selbst ein Befund — in beiden Werkzeugen.*

### Der zweite Durchgang, am Nachmittag — und er hat mehr gefunden als der erste

Das Register wuchs von 12 auf **34 Einträge**, gewählt nach `--reichweite` (Traglast zuerst).
**Sieben der neuen Einträge fielen sofort**, und die Richtungsmischung ist wieder die
Diagnose — keine Beschönigung, sondern **Fortschreibung**:

| Zahl | stand | ist | wo |
|---|---:|---:|---|
| `H` in der Postenliste | 15 | 12 | `PFLICHTEN.md` — *und die Spalte darunter summierte sich zu 17* |
| Prämissen ohne Pass | 7 | 9 | `PLAN.md`, «NL»-Tafel |
| Absagen mit tragendem Grund | 96 | 98 | `TODO.md` |
| gelesene Item-Arten | 21 von 23 | 23 von 23 | `TODO.md` |
| Schablonen im Register | 20, 15 unbewiesen | 21, 11 unbewiesen | `TODO.md` |
| Widerrufe | 7 | 9 | `TODO.md` |
| direkte Blicke auf die Karten | 13 | 35 | `TODO.md` |

> **Drei Register über einer Sache, und das mit dem Suchweg war das falsche.** In
> `PFLICHTEN.md` stand die Postenliste der hängenden Pflichten unter der Überschrift
> *„`H = 15`, abgelesen mit `./zaehle-pflichten.py --haengend`"* — die Zahlenspalte darunter
> summierte sich zu **17**, und der genannte Befehl sagt **12**. *Genau die Form, gegen die
> die Regel über allem steht: eine Zahl, deren Suchweg ihr widerspricht, sieht belegt aus.*
> Die Spalte ist gestrichen; die zwölf stehen nur noch im Befehl.

**Und zwei Befunde am Messwerkzeug selbst — beide sind meine eigenen:**

| | |
|---|---|
| **Der Fixpunktriegel war einen Schritt tief** | W18 verbietet einen Registereintrag, dessen Befehl `pruefe-zahlen.py` **nennt**. Der Ring der Länge ZWEI lag offen daneben: `./pruefe-waechter.py --lauf` führt jeden leichten Wächter aus, und das Register ist einer davon — **ein einziger Eintrag mit `--lauf` hätte den Ring geschlossen**, und der Namensriegel hätte ihn durchgelassen. Seit heute hängt der Riegel an einer Marke in der Prozessumgebung und greift in **jeder** Tiefe; gemessen an einem echten Kindprozess |
| **`pruefe-waechter.py --lauf` war hier grün und auf `ki-pc-fisch-101` rot** | bei identischen Quellen. Nicht der Code fehlte, sondern der **Gegenstand**: `zaehle-b3.py` und `zaehle-narrow.py` messen fremde Bäume (Caprock-Messbasis, SEL4Lake), und die liegen nur auf dem Arbeitsrechner. *Ein Wächter, dessen Urteil davon abhängt, auf welchem Rechner er läuft, ohne es zu sagen, misst den Rechner.* Beide stehen jetzt in `FREMDER_KORPUS`; ein fehlender Baum zählt als **nicht gemessen** und steht mit seiner Zahl in der Schlusszeile |

*Und dieselbe Falle noch einmal eine Ebene tiefer:* `../caprock-messbasis` ist ein **relativer**
Pfad. In einem `git worktree` zeigt er neben den Arbeitsbaum — und `zaehle-b3.py` lief darüber
bis in eine `ZeroDivisionError`, mit einer Ausgabe, die mit `Dateien 0` begann. **Null Dateien
ist eine Absage, kein Ergebnis;** das Werkzeug sagt es jetzt und endet mit 2.

**Was von den Punkten darunter erledigt ist:** die Spalte *„of which K"* (gestrichen, nicht
ausgerechnet) · *54 oder 102* (zwei Grundgesamtheiten, keine zwei Zahlen) · die
`narrow`-Klassen (`N_folgenlos` gebaut, `N_ritus` als Urteil benannt).

**Vier Klassen sind daraus in den Werkzeugkasten gegangen, weil sie über ihren Anlass hinausreichen:**

| | |
|---|---|
| **W17** | *Erfolg ohne Arbeit* — ein **positives Urteil über nichts**. Dreimal an einem Tag: `isabelle build` wählte nichts und endete grün, `zaehle-b3.py` druckte `! ABBRUCH` und endete mit 0, ein README-Muster traf nichts und meldete „sauber". **Die Vorkehrung ist die Arbeitsmenge neben dem Urteil** — seit heute die *vierte* Forderung in `pruefe-waechter.py` |
| **W18** | *Ein Register, das seine eigene Ausgabe enthält, hat einen **Fixpunkt statt einer Messung***. Nicht der Rücklauf ist das Schlimme — ein Fixpunkt, der **terminiert**, wäre gefährlicher: die Zahl stimmt dann immer, unabhängig davon, ob gemessen wurde. *R15 eine Ebene über dem Werkzeug.* **Als Code geriegelt**, nicht als Satz — und seit dem Nachmittag in **jeder Tiefe**, nicht nur in der ersten |
| **W19** | *Ein Urteil, das sich als Messung liest, bekommt die Autorität der Messung.* Die Auflösung hat zwei Teile, und der zweite wiegt schwerer: die urteilsfreie Hälfte bauen — **und sie anders benennen** |
| **W20** | *Ein Wächter, dessen Gegenstand woanders liegt, misst den Rechner.* Fehlt der fremde Baum, ist der Rücklaufwert ein **Fehlaufruf und kein Befund** — und beide Richtungen sind falsch: rot ohne Fehler, oder grün ohne Messung |

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
      **Was offen bleibt, ist der Rest der Tafel:** `total`, `K` und `L` (238 / 171 / 67)
      kommen aus dem Handgang, und der ist eine **Auszählung ohne Befehl** — `zaehle-pflichten.py`
      leitet heute nur die *hängenden* ab, nicht die Grundgesamtheit.
      **Woran es hängt, in einem Satz:** die drei Zahlen entstehen beim LESEN der Fragmente,
      und ihre Quelle ist eine Tabelle in `PFLICHTEN.md`, deren Zeilen ein Mensch geschrieben
      hat. Ein Befehl dafür müsste die Klassenspalte `K`/`L` je Zeile auszählen — *das ginge*,
      und es ist die nächste Erweiterung von `zaehle-pflichten.py`, nicht dieses Registers.

- [ ] **Zwei Blicke auf dieselbe Karte gingen auseinander, und nur einer hatte einen Test**
      *(gefunden 2026-08-17 beim Bauen von `const fn`, weil eine Giftprobe nicht fiel, die
      fallen musste -- R11)*. `typ_von_ort` schlug den globalen Traeger modulbewusst nach
      (`suche`), `index_pruefen` unqualifiziert (`get`). **`M103` schwieg damit in jedem
      `module`-Block fuer eine Tabelle, die ueber ihren globalen Namen adressiert wird.**
      Behoben und mit Gift 76 belegt.
      **Die allgemeine Frage hat seit dem 2026-08-20 einen Befehl** (`./zaehle-karten.py`), und
      die alte Zahl war um den Faktor 2,7 zu klein: 16 Karten, 12 davon öffentlich,
      **35 direkte Blicke** auf die Karten aus 26 Passdateien, davon vier in einer
      Kandidatenschleife und **31 davon unqualifiziert**.
      *Die alte Zählung sagte 13 — sie kannte `.contains_key(` nicht, und das ist derselbe
      Blick.* **Ein Werkzeug, das eine der beiden Formen nicht liest, misst seine eigene
      Leseweite** (W16).
      **Was offen bleibt und woran es hängt:** wie viele der 31 in einem `module` danebengreifen,
      ist ungemessen. Es zu messen kostet **je Stelle eine Giftdatei mit `module`-Block** —
      einunddreißig Dateien, keine Passarbeit. *Bis dahin ist die Zahl eine Kandidatenliste und
      kein Fehlerbefund (W10).*

- [ ] **Zum ZWEITEN Mal in eine Beweissuche gelaufen -- und die Regel stand schon da**
      *(2026-08-17)*. Erst ein `metis` (9 Minuten, 6,3 GB), dann ein `blast` (12 Minuten,
      4,8 GB). **Eine Regel, die man kennt und trotzdem bricht, braucht keinen weiteren Satz
      -- sie braucht ein Werkzeug.** `./pruefe-beweise.sh` haelt jetzt bei 3 GB an.
      **Die andere Hälfte ist seit dem 2026-08-20 gebaut, und sie ist eine Zählung, kein
      Wachhund:** `./zaehle-theorien.py` zählt **31 eingefrorene Suchergebnisse**
      (`metis` 3, `blast` 28) gegen eine Ratsche und verbietet `sledgehammer`, `try0`,
      `nitpick` und `quickcheck` ganz — **heute null, über dreizehn Theorien.**
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
      davon fünf verankert — und alle fünf sind Notationslücken.** `./zaehle-pflichten.py
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
      heute **9 Widerrufe** über 59 Dateien, und keiner davon ist eine Teilmengenbeziehung.
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

- [ ] **The line shares of the GABBRO side — that is what still closes the metric.**
      B3 has been run and did **not** supply them; it measures the code form, the formula
      weights proof obligations (`dokumente/MESSUNGEN.md`, *EINSETZUNG*). What is missing: what a
      proof **in Gabbro** costs for the same 73 obligations. **That is no longer a measurement on
      Caprock** — for it the obligations have to be written in Gabbro. Until then
      ~~the metric stands at `≥ 1,90`~~ **die Kennzahl lautet seit dem 2026-08-19 `unbekannt,
      > 0,5`**, und **jede kleinere Zahl im Umlauf verwechselt die zwei Seiten**. *Und der
      Posten hat seither einen genaueren Namen: nicht „ein Beweis in Gabbro", sondern **P6** --
      die ERZEUGTE Verfeinerungspflicht. Vorher gibt es nichts zu beweisen, das nicht erfunden
      waere.*
      **Und die Zählerseite hat seit dem 2026-08-20 einen Befehl** (`./zaehle-theorien.py`) —
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
      **164 besetzte Zellen** stehen daneben, **26 nur im Gift** — und `gabbro blindstellen`
      druckt die vier Zahlen getrennt, *auf Ausdruck*, weil ein Einzelwert zwei Wochen später
      wie Fortschritt aussieht.
      *Die schärfere Frage bleibt dieselbe wie beim Schablonenregister: fällt an dieser Zelle je
      etwas?* — also **Mutation oder Giftprobe je KOMBINATION, nicht je Konstrukt.**
      **Woran es hängt, jetzt beziffert:** 164 Kombinationen brauchten je eine Probe; der
      Mutationskatalog trägt heute 234 Anker, also liegt die Größenordnung neben dem, was schon
      steht — *und das ist der Grund, warum es kein Nachmittag ist.*

- [ ] **44 Absagetexte sagen ihren Grund in KEINER der beiden Sprachen** (`./pruefe-gruende.py`,
      2026-08-20). Die billige Näherung sortiert jede Regel danach, ob ihre Begründung eine
      Eigenschaft der **Absenkung** (*„hat keinen Speicher", „ist ein unbekannter Ruf", „die
      Breite läuft über"*) oder eine Eigenschaft der **Zusage** (*„genau einmal", „auf jedem
      Pfad"*) nennt. 98 sind tragend, 2 verdächtig — und **44 Absagetexte sagen ihren Grund in
      KEINER der beiden Sprachen**.
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

- [ ] **OPT0 — der Wächter muss OPTIMIERT übersetzen.** `pruefe-emission.sh` fährt
      `-Wall -Wextra -Werror` und **ohne `-O`**. Nachgemessen liefert die Einheit bei
      `-O0`/`-O2`/`-O3` dasselbe und läuft sauber unter `-fsanitize=undefined` — **aber
      gemessen habe ich das, nicht der Wächter.** Eine Abweichung zwischen `-O0` und `-O2`
      ist der Fingerabdruck von undefiniertem Verhalten und **die einzige Probe, die ein
      falsches `restrict` findet**. *`address` läuft auf diesem Rechner nicht (gehärteter
      Kern, Schattenspeicher-Kollision): keine bestandene Probe, sondern eine nicht
      gefahrene.*
      **Woran es hängt, beziffert 2026-08-20:** der Wächter fährt 46 Einheiten mit je
      erzeugen/übersetzen/ausführen/UBSan und braucht dafür rund 25 Minuten. Ein zweiter
      Übersetzungs- und Laufdurchgang unter `-O2` **verdoppelt das**, und damit fällt er
      endgültig aus jedem `--lauf` heraus — er steht schon heute unter den fünf schweren.
      *Die Entscheidung ist deshalb keine Bauarbeit, sondern eine Kostenfrage:* zweiter
      Durchgang für alle 46, oder `-O2` nur für die Einheiten mit `restrict`. **Bleibt offen.**

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
      hält das Register die Zahl gegen `./pruefe-konstrukte.py`.
      **Woran das schärfere Maß hängt:** es müsste je Item-Art fragen, ob eine ABSAGE an ihr
      fällt — das ist Maß 2 (Giftprobe je Konstrukt, heute 0 von 19 ohne) *je Zusage* statt
      *je Konstrukt*. **Dieselbe Größenordnung wie die Kombinationstafel oben. Bleibt offen.**

- [ ] **~~Die 161 zerbrochenen Meldungen hat kein Waechter gesehen~~ — GEBAUT 2026-08-20.**
      Beim Übersetzen ins Englische verloren die Zeilenfortsetzungen ihr Leerzeichen —
      *„that isa compile error"*. **Gefunden, weil ich eine Meldung gelesen habe.**
      `pruefe-englisch.py` prüfte die SPRACHE eines Textes, nicht seine Lesbarkeit.
      **Die Probe war billig und steht jetzt drin:** Rusts Zeilenfortsetzung frisst den Umbruch
      *und die Einrückung*, also hängt die Trennung an genau einem Zeichen — dem letzten davor.
      Heute **778 Zeilenfortsetzungen** in den Quellen, **0 kleben**.
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
      Bauform, keine Zahl:** `pruefe-zahlen.py` liest heute 34 Werkzeugausgaben mit einem
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
      `./pruefe-klauseln.py` liest 147 Feldnamen aus `ast.rs` gegen 29 Leserdateien und bucht
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
      GEBAUT 2026-08-20** (`./zaehle-theorien.py`). Die alte Buchung sagte *„zehn Theorien,
      1 639 Zeilen, 48 Sätze, 86 Beweisschritte"* und ließ die Frage offen, was davon Prosa
      ist. Heute: **2 317 Zeilen** in dreizehn Theorien, **70 Sätze** darin — und klassifiziert:

      | | | |
      |---|---:|---|
      | Gerüst | 418 | 18,0 % — `theory`/`imports`/`begin`/`end` und Leerzeilen |
      | Prosa | 1 062 | **45,8 %** — Kommentare, `text`-Blöcke, Überschriften |
      | Modell | 166 | 7,2 % — Definitionen, Datentypen |
      | Beweis | 671 | 29,0 % — Sätze samt ihren Beweisen |

      **Fast die Hälfte ist Fließtext, und damit ist die Verwechslung beziffert:**
      **837 Zeilen Modell und Beweis** sind das, was einer Verus-Zeilenzahl gegenübersteht —
      **36,1 % statt 100 %.** *Wer 2 317 gegen eine Verus-Zahl hält, überschätzt die eigene
      Seite um den Faktor 2,8.* Dieselbe Verwechslung, an der `1,90` am 2026-08-19
      zurückgezogen wurde, eine Ebene tiefer.
      *Und was das NICHT heißt:* die Einteilung liest Zeilenanfänge; ein `text`-Block über ein
      Modell zählt als Prosa. **Eine Näherung mit benannter Kante, kein Parser** (W10).

- [ ] **`C001` sagt „keine Absenkung" und wird fuer FALSCHES mitbenutzt** *(gefunden
      2026-08-19 an «B24»)*. Eine Bitlage jenseits der Wortbreite ist kein *„das koennen wir
      noch nicht"*, sondern ein *„das ist falsch"* -- bis dahin trug beides dieselbe Kennung.
      Zwei der drei Faelle sind mit `N007`/`N008` in den Pruefer gezogen; **die Luecke im Wort
      bleibt bewusst `C001`**, weil erst die Absenkung eine bestimmte Wortgrenze braucht.
      **Nachgezählt 2026-08-20: `C001` steht an sechs Stellen im Prüfer und wird an fünfzehn
      Stellen im Korpus erwartet** — und `./pruefe-gruende.py` führt `C001` als **verdächtig**
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
      Heute neun Widerrufe gebucht, acht Fundstellen geschlossen. **Er findet nur, was jemand
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

- [ ] **The mutation probe covers the checker today, not the emission.**
      `./mutiere-pruefer.py` beschädigt eine Regel des Prüfers und sieht nach, ob eine Probe
      fällt. Mutationskatalog: **234 von 234 Ankern** greifen (`--anker`, 2026-08-20) — die
      Zahl stand hier als *24 von 24* und in `CLAUDE.md` als *159*, beide aus früheren Läufen.
      *Ein Katalog, der wächst, macht jede Zahl daneben zu einer Jahreszahl.*
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
      **Closed are:** `pub` at 13 item kinds (`P034`), `pub const` in the `table` body (was
      too strict), `type T = { };` as an empty sum type (`P035`, poison 61), and
      the comma rule — `entrydecl`, `slotdecl` and `reg … fields` carried **three different
      rules for the same thing**; now one: separating comma obligatory, trailing comma
      optional.
      **Und die Messschicht sagt, warum die drei stehenbleiben:** `./pruefe-syntax.sh` hält
      146 EBNF-Regeln und 216 Terminale gegen die Wortschatztabelle — *er misst die Grammatik
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
      hält 216 Terminale gegen die Tabelle. **Was fehlt, ist ein Urteil**, und der Preis steht
      in beiden Richtungen daneben.* Bleibt offen.

- [ ] **Per template at least one mutation that falls ONLY if the once-obligation is really
      checked.** Today: **0 of 21** — die meisten Schablonen sind entworfen, und was kein Code
      ist, fängt keine Mutation. **Die Kopplung der zwei Register ist die Bedingung dafür, dass
      das Schablonenregister mehr ist als eine Liste.**
      *Berichtigt 2026-08-20: hier stand „0 of 19", das Register führt 21.* **Woran es hängt:**
      eine solche Mutation muss die **erzeugte** Einmal-Pflicht beschädigen, und die entsteht
      erst in der Annotationsemission — derselbe fehlende Kanal wie zwei Punkte tiefer.

- [ ] **The annotation emission needs template entries of its own and mutations of its own.**
      Der Mutationskatalog misst heute den Prüfer (234 Anker); über den **Wunschform-Kanal**
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

- [ ] **Mutation probe on the ANNOTATION EMISSION**, not only on the code emission. The coherently
      weakened case (code **and** contract) is caught by **no** proof — only by the
      differential test against the handwriting. That is its named task.
      *Derselbe Posten wie zwei Punkte höher, von der anderen Seite. **Woran es hängt: die
      Annotationsemission existiert nicht** — es gibt nichts zu beschädigen. Kein Messposten,
      und er bleibt so lange stehen, bis der Kanal steht.*

- [ ] **Emit the assumption set into the artefact** ("proved under A1…An"), as a **set of names**
      with a class, not as a number. A ratchet over a cardinal number does not bite against exchange.
      **Halb gebaut, gemessen 2026-08-20:** `gabbro annahmen` druckt 32 Annahmen als **Namen**
      mit Klasse (`assume`/`axiom`), Falsifizierbarkeit und Sonde — genau die verlangte Form.
      **Was fehlt, ist der zweite Halbsatz: „into the artefact".** Die Namen stehen im Bericht
      des Prüfers, nicht im erzeugten C. *Woran es hängt: an einer Zeile im Erzeuger* — der
      Kanal dorthin steht seit dem 2026-08-17, denn `pruefe-emission.sh` findet die Annahmen im
      erzeugten C wieder. **Der kleinste offene Posten dieses Abschnitts.**

- [ ] **~~Every falsifier needs its own speech test:~~ *can it fail at all?* — GEBAUT
      2026-08-20.** Das ist wörtlich die zweite Forderung von `./pruefe-waechter.py`, und sie
      wird an **25 von 25** Instrumenten geprüft: eine saubere und eine kaputte Quelle, beide
      erfunden, und der Wächter muss die eine melden und die andere durchlassen.
      **Was der Punkt meinte und was gemessen wird, ist nicht dasselbe, und der Unterschied
      gehört hierher:** geprüft wird, ob der Wächter *überhaupt* rot werden kann — nicht, ob er
      an **seinem** Gegenstand rot wird. `pruefe-zahlen.py` schließt diese Lücke für seine 34
      Einträge (jede Zahl wird verstellt, jeder Eintrag muss fallen); für die übrigen Wächter
      ist die Sprechprobe eine **Selbstauskunft im Quelltext**, und dass sie dasteht, heißt
      nicht, dass sie an der richtigen Stelle steht. *Das Werkzeug sagt genau das über sich
      selbst.* **Der Rest ist damit benannt, nicht offen.**

- [ ] **The scope in [`dokumente/SPRACHE.md`](dokumente/SPRACHE.md) is new — run a counter-probe:** look for a construct
      whose line is too strong. The table has the same prehistory as the two
      overreaches in `dokumente/HISTORIE.md`.
      **Und die Gegenprobe hat seit dem 2026-08-20 zwei Werkzeuge, die sie zur Hälfte fahren:**
      `./pruefe-reichweite.py` (0 ungelesen, zwei Bauteile von genau einem Pass gelesen) und
      `./pruefe-klauseln.py` (22 Klauseln gebucht, sechs ungelesen). *Beide finden eine Zeile,
      die zu stark ist, nur dann, wenn niemand sie liest — nicht, wenn ein Pass sie liest und
      zu wenig tut.* **Woran der Rest hängt: an W13** (Berührung ist keine Prüfung), und die
      Antwort darauf ist dieselbe wie beim groben Maß oben — eine Probe je ZUSAGE.
      Bleibt offen.

---

# STUFE 1 — DER MASSSTAB

**Der Befund:** `H = 12` wird gelesen als *„so viel Klempnerei ist in Gabbro noch übrig"*.
Sieben Zwölftel davon sind die **Vollständigkeit des Korpus**: 41 Stellen nennen 20 Namen, die
niemand deklariert, neun `let … else` rufen Rümpfe, die es nicht gibt, sechs Bitlagen sind
unbenannt. **Die Absenkungsspalte fällt um keinen Punkt**, ohne in eine eingefrorene Datei zu
schreiben.

**Die Entscheidung:** Weg **(b)** — `messung/fragmente/`, dieselben zehn um ihre ~60 fehlenden
Zeilen ergänzt, ausführbar, mit einer Kopfzeile, die sagt was ergänzt wurde. `FRAGMENTE.md`
bleibt Bericht. *Derselbe Zug wie «K2»: nachgebildet, nicht übersetzt — und dort ausdrücklich
gesagt.*

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



- [ ] **Die zwei Fragmente tragen ihre Bitlücken, weil sie AUSSCHNITTE sind.** Ein
      ausgeschnittener `format`-Block nennt die Bits, um die es dem Ausschnitt geht, und nicht
      die des ganzen Wortes. *Ob ein Ausschnitt vom Kacheln ausgenommen gehört, ist eine
      Entscheidung über die Messform und keine über die Sprache* — und sie fällt erst, wenn
      jemand sagt, was ein Ausschnitt zusagt.

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

- [ ] **A5 — acceptance:** fragments through the compiler afresh, the count over
      **Gabbro source text** instead of over Rust (**only then is the mark ≤ 24 really
      decidable** — see the report of the invalid measurement further below), and the four never
      written-out areas.

---

# STUFE 2 — NUTZBARKEIT BEKOMMT IHR ERSTES INSTRUMENT

**Ziel 3 hat als einziges keine Zahl.** Ohne sie ist „möglichst gut nutzbar" eine Meinung — und
„keine Klempnerei beim Endnutzer" ist eine Nutzbarkeitsaussage.

**`gabbro zeremonie`**, je Datei. Und die Kalibrierung gehört **in** das Instrument, sonst wird
das erste Nutzbarkeitsmaß sofort zum Optimierungsziel:

| Spalte | | darf sie sinken? |
|---|---|---|
| **ableitbar** | der Typ steht in der Deklaration daneben — `let i = d.ST.IDX` | **ja, das ist echte Zeremonie** |
| **redundant** | dieselbe Wahrheit zweimal deklariert | **ja** |
| **tragend** | eine Aussage, die nirgends sonst steht — `effects`, `costs`, die Paarungsklauseln | **NEIN** |

> **Ohne die dritte Spalte misst „Nutzbarkeit" die Menge aller Klauseln und drängt langfristig
> gegen die Zusage der Sprache.** `effects` und `costs` sind nicht Zeremonie, sie sind der
> *Gegenstand*; ihre Zahl fallen sehen zu wollen wäre, wie die Schablonenfläche als Rückstand zu
> buchen. **Die dritte Spalte ist der Preis, den die Sprache bewusst nimmt**, und sie gehört
> ausgewiesen, damit niemand sie später für Rückstand hält.

Und dieselbe Doktrinzeile wie bei den drei anderen Zählern: *was 0 Befunde hat, ist nicht nutzbar,
sondern ungemessen.*

### K100 — der Weg auf 100 % Klempnereiabdeckung ([`dokumente/PLAN.md`](dokumente/PLAN.md)) *(Teil)*

- [ ] **Der Erzeuger raet den Typ eines `let` nicht, obwohl er ihn ablesen koennte**
      *(gesehen 2026-08-17 an `beispiele/21`)*. `let c : Completion = fertig(k, 7);` braucht
      die Annotation, weil `ctyp` nur die geschriebene Form kennt -- die Signatur des
      Gerufenen stuende daneben. **Die Weigerung (`C001`) ist die sichere Richtung**, aber sie
      kostet an jeder Bindung eines zusammengesetzten Werts eine Zeile. *Entweder aus der
      Signatur ablesen (kein Raten, ein Nachschlagen) oder die Zeile als Absicht aufschreiben.*

### Syntax — open decisions (details in [`dokumente/SYNTAX.md`](dokumente/SYNTAX.md)) *(Teil)*

- [ ] **Error propagation:** without `?` every call becomes three lines, with `?` there is hidden
      control flow. Both contradict a design rule.

- [ ] **`on_exceeded <reason>` ist ein gemessener Bedarf, den die Sprache nicht hat**
      *(2026-08-19)*. `FRAGMENTE.md`:902 schreibt `on_exceeded DeviceSilent`. Der Erzeuger:
      *„a `reason` value would need an error-return convention, and that is not decided."*
      **`S006` schweigt dort**, weil es „Reason-Variante" nicht von „unbekannter Name"
      unterscheiden kann (W10) -- *nur der Erzeuger faellt.* Erst die Entscheidung ueber die
      Fehlerrueckgabe, dann die Regel.

### Aus «H2» *(ausgefuehrt 2026-08-19, `H = 17 → 15`)* — der Rest, den der Lauf hinterliess *(Teil)*

- [ ] **Gabbro unterdrueckt FOLGEFEHLER nicht, und niemand hat das je aufgeschrieben**
      *(gefunden 2026-08-19 an `M112`)*. Der Ausschnitt `SYNTAX.md`:533 scheitert am Parser
      («B8»: ein Ruf in einem `place`), damit wird seine `spec fn` nie erklaert, und
      `maintains` meldet einen Namen, den es sehr wohl gibt. **Nach einem `P001` laufen alle
      Paesse weiter, und was sie melden, kann Rauschen sein.** *Entweder die Paesse
      anhalten, oder die Entscheidung aufschreiben -- heute steht sie nur in einer
      Testliste.*

---

# STUFE 3 — DIE OFFENEN LESARTEN ENTSCHEIDEN

**Der billigste Posten des ganzen Plans.** Drei Konstrukte stehen in der Grammatik und werden in
der Spezifikation in **zwei Lesarten** benutzt. Eine Entscheidung kostet **keine neue Grammatik
und keine neue Schablone** — also **keine Vertrauensfläche**. Jede entsperrt ein Fragment und
eine Schleifenfamilie.

* **`elems of`** — bindet es ein ELEMENT oder einen INDEX? `SYNTAX.md` benutzt beides («B12»).
* **`mappings of`** — ein Pfad oder die Blattmenge? Sieben Größenordnungen Unterschied.
* **`by consuming`** — leert es die ganze Schlange? Heute ja, und das ist ein anderes Programm («B10»).

*Das ist der einzige Posten, der Ziel 1 und 4 bedient, ohne Ziel 2 zu belasten. Deshalb steht er
vor allem Bauen.*

### Die drei Lesarten, je als eigener Punkt

- [ ] **«B12»: bindet `elems of` ein ELEMENT oder einen INDEX?** *(offen seit 2026-08-14,
      `FRAGMENTE.md`:619-622)*. `SYNTAX.md` **benutzt beide Lesarten und legt keine fest** —
      und daneben steht `slots of`, das einen Index bindet. *Zwei Domaenen, die gleich
      aussehen und Verschiedenes binden, sind die stillste Fehlerform, die eine Spezifikation
      hat.* Der Erzeuger sagt es beim Namen ab (`C001`, F6), also ist der Bedarf gemessen und
      nicht entworfen. **Kosten der Entscheidung: kein Terminal, keine Schablone.**
- [ ] **«B10»: `by consuming` leert die GANZE Schlange, und das ist ein anderes Programm**
      *(gemessen an F3)*. `traverse` liefert keinen Wert und kennt kein `break` — wer eine
      Nachricht entnehmen will, entnimmt alle. **Die Frage ist nicht, ob das ein Fehler ist,
      sondern ob es die gewollte Bedeutung ist**; heute steht die Antwort nirgends, und der
      Erzeuger weigert sich deshalb zu Recht. *Zusammen mit dem Leser-Befund in Stufe 5
      (`by consuming` liest kein Pass) ist das dieselbe Sache von zwei Seiten: die eine Haelfte
      fehlt in der Bedeutung, die andere im Pruefer.*

### From the emitter (2026-08-17) — the cost pass carries the typical case


- [ ] **`mappings of`: the cost pass under-counts by seven orders of magnitude.**
      [`dokumente/SPRACHE.md`](dokumente/SPRACHE.md):786 says it quantifies over **ALL
      reachable leaf entries** of a `walk`; the pass bounds it at `levels × node length`
      (`kosten.rs`:362, `walkschranken`) — **2 048** for four levels of 512, where the leaves
      number **512^4 = 68 719 476 736**. *The pass counts one descent PATH and calls it the
      domain.*
      **This is the class the folder has paid for twice** — `revoke` promised 200 ops and costs
      16 452 480, A4 promised 4 096 and costs 831 488. **Both times a HUMAN wrote the typical
      case instead of the bound and the pass caught it. Here it is the pass itself.**
      Either the domain means a path (then `SPRACHE.md`:786 is wrong and the name misleads) or
      it means the set (then no `walk` traversal can carry a cost promise). *The emitter
      refuses rather than pick the smaller reading.*

---

# STUFE 4 — PROGRAMME SCHREIBEN, NICHT KONSTRUKTE

**Das Herz des Plans.** Der Korpus ist von der Sprache nach außen geschrieben — eine Datei je
Konstrukt — und **die Fehler sitzen an den Kombinationen**: 80 blinde Zellen von 285. Jedes echte
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

Darunter steht die **Ernte** der bisherigen Programme und Werkzeugläufe: jeder Posten hier ist ein
Loch, das ein Programm oder ein Messwerkzeug gefunden hat, nicht ein Entwurf.

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

- [ ] **`ops insert, remove, relabel` ist ENTSCHIEDEN und nicht gebaut** *(2026-08-19)*. Die
      drei Woerter stehen im Lexer, in der EBNF und in der Wortschatztabelle. **Was fehlt, ist
      der Erzeuger** -- und mit `relabel` schuldet er eine Bedingung, die `insert` und `remove`
      nicht brauchen: `Table_Ops_Erhaltung.thy` fuehrt das Gegenbeispiel (`umhaengen_faellt`).
      *Genau deshalb ist es aufgenommen: eine Sprache, die nur die leichten Operationen deckt,
      verschiebt die Arbeit.*

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

- [ ] **`group` steht an EINER Korpusstelle** *(2026-08-19)*. `beispiele/17` ist die einzige;
      die vier Verbindungsinvarianten des Sweeps vom 2026-08-16 (V1-V4) sind gemessen, aber
      nicht geschrieben. **Zwei bewiesene Schablonen ueber einem Konstrukt mit einer
      Fundstelle** -- das ist der Grund, warum die Amortisationszahl heute zweimal gestiegen
      ist. *Solange V1-V4 nicht als `group` dastehen, misst die Zahl den Beweisvorlauf und
      nicht die Amortisation.*

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

- [ ] **P6 ist EROEFFNET, nicht erledigt** *(2026-08-19)*. `maintains` hat einen Leser
      (`M112`-`M114`), und `gabbro pflichten` zaehlt die erzeugten Pflichten: **18 ueber 33
      Beispiele** (nachgemessen 2026-08-19; `gabbro pflichten` OHNE Datei druckt „no file
      named" und keine Null -- *wer den Aufruf fuer die Messung haelt, liest 0 statt 18*). *Was fehlt, ist die zweite Haelfte:* die Pflicht muss in
      einer Form dastehen, die ein Beweiser lesen kann -- heute ist sie eine Zeile im
      Bericht. **Und die K/A/W-Einordnung bleibt Handarbeit**, ausdruecklich: ein Werkzeug,
      das sie raet, waere die stille Antwort, gegen die dieser Ordner sonst schreibt.

- [ ] **P6 ist die Grundlage der Kennzahl, nicht ihr Zubehoer** *(geschaerft 2026-08-19)*.
      Die Zahl ist zurueckgezogen (`unbekannt, > 0,5`), weil `w` an VERUS-Zeilen gemessen war.
      Ein Isabelle-verankertes `w` braucht **eine W-Pflicht, die ENTSTANDEN ist** -- und
      erzeugt wird sie von P6, der Verfeinerungspflicht aus `spec fn`/`impl fn`. **Keine
      Sprachsemantik noetig:** die Absenkung nach C ist die Bedeutung, und beide Seiten stehen
      in einer Sprache. *Solange P6 fehlt, muesste man die Pflicht erfinden, die man dann
      misst -- genau die Bewegung, gegen die R7 und W3 stehen.*

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

# STUFE 5 — DIE BEWEISE TRAGEND MACHEN *(parallel zu Stufe 4)*

**`L = 1` sieht gut aus und heißt wenig.** Daneben stehen **9 Prämissen ohne Pass** — ein Beweis,
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

### K100 — der Weg auf 100 % Klempnereiabdeckung ([`dokumente/PLAN.md`](dokumente/PLAN.md)) *(Teil)*

- [ ] **K100.4 — die STARKE Fassung von (b) fehlt noch.** `gabbro zeugnis` zaehlt auf, worauf
      eine Uebersetzung ruht (gebaut 2026-08-17, acht Einheiten, je Befund gebucht). *Es sagt
      nicht, dass sie haelt.* Die starke Fassung waere ein maschinell geprueftes Zeugnis je
      Uebersetzung -- **und die Vorstufe ist als Vorstufe benannt**, damit die Zahl nicht mehr
      verspricht, als sie misst.

- [ ] **Eine parametrische `costs`-Zusage ist heute schreibbar und VOLLSTAENDIG LEER**
      *(gemessen 2026-08-18)*. `costs <= 0 * n ops` an einem Rumpf, der 1 op kostet:
      **3 Items, 0 Fehler, 0 Hinweise.** `kosten.rs` sagt es im eigenen Kopf (*„die Schranke
      darf von Eingaben abhaengen … in dem Fall schweigt der Pass"*), und `gabbro kosten`
      druckt ehrlich `zugesagt --`. **Damit steht der Preis der wertgetragenen Schranke nicht
      in der Grammatik, sondern in Pass 9: er muss symbolische Ausdruecke VERGLEICHEN statt
      zu schweigen.** *Was schon passt: `Kosten::Zahl(i128)` traegt `40 * 2^64` muehelos.*

- [ ] **Unter einer Sperre darf der Rahmen NICHT parametrisch sein.** `held <= N ops` ist eine
      LATENZaussage -- wie lange ein anderer Kern hoechstens wartet. Ein `held <= 40 * n` mit
      symbolischem `n` ist eine Sperre, die unbeschraenkt lange gehalten wird, und damit ist
      `rank`/`held`/`K002` leer. *Dieselbe Trennung noch einmal: die Kostenklasse vertraegt
      Symbole, die Sperrklasse nicht.* **Die Regel gehoert in die Erweiterung, bevor sie
      Grammatik wird.**

- [ ] **Eine `bank` mit `stride 0` erzeugt LEERE Zellen, und der Satz gilt trivial**
      *(ausgespuelt beim Beweis von `device.konstruktor`, 2026-08-17)*. `bankeintraege_
      ueberlappen_nicht` braucht `stride > 0` nicht als Praemisse -- bei null ist jede
      Bankzelle leer, und leere Mengen schneiden sich nicht. **Richtig und nutzlos ist keine
      bestandene Pruefung:** der Erzeuger sollte `stride 0` ablehnen, statt sie leerlaufen zu
      lassen. *Ein Beweis, der einen Fall trivial macht statt ihn zu decken, hat ihn gefunden.*

### The group: three forms stand — what is open is PRESERVATION


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

### Design — open decisions *(Teil)*

- [ ] **Cost figure per invariant** and at `by unbesucht`: which structure, who resets it,
      what the reset costs, whether it may live under the lock.

### Induction — entered, and the one number is missing


- [ ] **The generated scheme has to go into Isabelle once** — it is a template in the sense of L3 and
      thereby the item that **shrinks** the trust base.

- [ ] **Well-foundedness hangs on an invariant one wants to prove.** The declaration has to
      name which — and the measure (number of descendants) is a premise, not a result.

### «NL» — der Weg zu „nur noch eigene Logik" ([`dokumente/PLAN.md`](dokumente/PLAN.md)) — **PUNKT 1** *(Teil)*

- [ ] **`bedingung` hat die Klasse verlassen, ohne dass ihre Zusage gehalten wuerde**
      *(2026-08-19, und es ist ein Befund ueber den WAECHTER)*. `N012` liest die
      `where`-Klausel, um die Schranke eines `offset_into` zu finden -- damit gilt sie
      mechanisch als gelesen. **Ob die Bedingung HAELT, prueft weiterhin niemand.** *Das Mass
      des Waechters ist „ein Pass greift zu", nicht „ein Pass haelt es nach"; die
      Vergroeberung stand in seinem Kopf und zahlt hier zum ersten Mal.* Der Posten steht
      jetzt hier, wo ihn keine Ratsche traegt -- **ein Waechter, der eine Zeile aus seiner
      eigenen Liste verliert, muss sagen, wohin sie geht.**

### Aus «H2» *(ausgefuehrt 2026-08-19, `H = 17 → 15`)* — der Rest, den der Lauf hinterliess *(Teil)*

- [ ] **Die STARKE Fassung von `M115` braucht eine Entscheidungsprozedur** *(2026-08-19)*.
      Heute faellt nur, was der Bereich des Arguments AUSSCHLIESST; dass der Rufer die
      Vorbedingung HERSTELLT, prueft niemand. **M1 stellt Fakten her und entscheidet keine
      Praedikate** -- die starke Fassung ist ein eigenes Stueck Maschinerie und zerlegte
      ausserdem den Korpus. *Vorher zaehlen, an wie vielen Rufstellen eine Vorbedingung heute
      unbewiesen bleibt.*

- [ ] **Drei der sieben haengenden Praemissen brauchen keine Pruefarbeit, sondern eine
      SPRACHFORM** *(gemessen 2026-08-19 beim Fuellen von `braeuchte`)*. `ops` braucht eine
      Wortmenge, `by consuming` einen genannten Zeitpunkt fuer die Leerheit,
      `accumulates.monoid` die Ausfuehrungskontexte. **Die haengenden Praemissen sind
      mehrheitlich keine vergessene Pruefarbeit, sondern nicht getroffene Entscheidungen** --
      und das aendert, wer sie schliessen kann.

- [ ] **Der Beweis, dass `bitlage::lies` die Lagen trennt, hat kein Register**
      *(2026-08-19)*. Die Praemisse `trennt f g` von `format.roundtrip` ist durch die
      KONSTRUKTION erfuellt -- sequentielle Byte-Lagen, monoton wachsender Versatz. **Das ist
      eine Aussage ueber den PRUEFER, und fuer die gibt es kein Register**; dieselbe Lage wie
      `Intervall_Aussen.thy`. *Heute steht der Grund in `durch:` als Prosa.*

- [ ] **`einfuegen` braucht ZWEI Bedingungen, und keine hat einen Pass** *(2026-08-19,
      `Table_Ops_Erhaltung.thy`)*. Der Platz ist FRISCH, der Elter ERREICHBAR. Beim Loeschen
      traegt das `requires ist_blatt(c, s)` des Rufers die Bedingung -- beim Einfuegen gibt
      es keine solche Zeile. *Ein Erzeuger, der `einfuegen` ausliefert, muesste sie
      herstellen oder verlangen.*

- [ ] **`maintains` nennt UNQUALIFIZIERT** *(2026-08-19)*. `M112` sammelt `spec fn` und
      Invarianten ueber alle Module flach ein, weil der Korpus unqualifiziert schreibt.
      **Zwei gleichnamige Invarianten in zwei Modulen sind damit ununterscheidbar** --
      dieselbe Bauart wie `typ_von_ort` vor dem 2026-08-17, nur noch nicht ausgeloest.
      *Eine Regel, die mehr verlangt als der Korpus schreibt, zerlegt ihn; die Verschaerfung
      braucht also zuerst eine Messung, wie viele Stellen qualifizieren muessten.*

- [ ] **Der PRUEFER hat kein Register** *(2026-08-18)*. `Intervall_Aussen.thy` ist die erste
      Theorie dieses Ordners, die von M1 handelt statt vom Erzeuger -- und sie steht in
      **keinem** Schablonenregister, weil das Register Erzeugerpflichten fuehrt
      (*„eine Beweispflicht, die der Erzeuger schuldet"*). **Damit gibt es jetzt zwei
      Vertrauensflaechen und nur eine Buchung.** Die zweite wird bisher nur von
      `mutiere-pruefer.py` gemessen -- Mutationen, nicht Saetze. *Ein zweites Register waere
      die naheliegende Antwort; ob es eines sein soll, ist eine Entscheidung.*

### Deklariert, exportiert, nie gelesen — die Klasse hat einen Namen und einen Waechter

**Gemessen 2026-08-18** mit `./pruefe-klauseln.py`: 131 Feldnamen aus `ast.rs` gegen 23
Leserdateien. **48 Felder gebucht** -- 21 nur getragen (nur `emit.rs`/`zeugnis.rs`/`cli`),
27 ungelesen. Nach Urteil: **17 ZUSAGE**, 6 ABSENKUNG, 25 TOT. *Die Stufe ist gemessen, die
Klasse ist ein Urteil, und das Werkzeug sagt beides getrennt an.*

Der Waechter klemmt in beide Richtungen und weist seine Messfaehigkeit nach (R14: `span` muss
als gelesen herauskommen, `section` nicht). **Die Liste unten ist eine UNTERE Schranke** --
gemessen wird je Name, nicht je Struktur (W10).



- [ ] **`leaves` und der Abstieg des `traverse` haben weiter keinen Leser**
      *(gemessen 2026-08-18)*. `progress` hat seit heute einen (`S003`/`S004`); die beiden
      anderen Schleifenzusagen nicht. **`leaves` nennt, was den Ausgang verlaesst** -- das ist
      eine Linearitaetsaussage, und M2 liest sie nicht. **Der Abstieg traegt die Terminierung
      des `traverse`**, und `schleifen.rs` steigt in den Rumpf, ohne ihn anzusehen.

- [ ] **Zahn 3: acht Praemissen ohne Hersteller** *(gemessen 2026-08-18,
      `gabbro schablonen`)*. Neun bewiesene Schablonen, siebzehn Praemissen, **acht davon
      stellt niemand her**. Die schaerfste: `device.konstruktor` ist bewiesen, und sein
      Hauptsatz setzt `getrennt r s` voraus -- *wer das Zeugnis liest, schliesst aus
      „bewiesen" auf Ueberlappungsfreiheit.* **Das ist die Umkehrung der Klausel-Klasse und
      teurer als sie:** bei einer ungelesenen Klausel weiss niemand etwas, hier weiss man
      etwas Falsches. Die Marke steht auf 8 und geht nach unten.

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

- [ ] **`pub` ist wirkungslos** *(gemessen 2026-08-18)*. Kein Pass, kein Erzeuger liest
      `oeffentlich`. Sichtbarkeit wird weder geprueft noch abgesenkt -- **und eine
      Bibliotheks-ABI beginnt bei genau diesem Wort.**

- [ ] **`ensures`/`maintains` werden GEZAEHLT, nicht gelesen** *(gemessen 2026-08-18)*.
      `zeugnis.rs:370,391` ruft `.len()` und `.is_empty()`; kein Pass haelt sie gegen den
      Rumpf oder auch nur gegen die Wohlgeformtheit. **Die Bibliotheks-ABI soll sie tragen.**

- [ ] **`invariant` und der Kleinkram: gelesen und sonst nirgends** *(gemessen 2026-08-18,
      gekürzt 2026-08-20)*. `cost`/`runs` an der `invariant`, `by` (der Induktionshinweis
      verfällt), `masked` an einer Sperre, `exhaustive`, der Ergebnistyp eines `axiom` und die
      Formatversion. *Kein Fehler, aber auch keine Sprache.*
      **Vier sind am 2026-08-20 gefallen:** der Abstieg eines `walk` (`levels`/`node`/`down`/
      `leaf` senken ab), `scale` (im `format`-Leser, und ein Setzer wird dafür benannt
      verweigert), der `can_fail`-Rumpf eines `check` (M1 **und** der Paarungspass lesen ihn)
      und der Fehlername im `let … else` (er trägt den `reason` aus `-> T or R`).

### The write-right line `by ops` — and the group proof sentence that precedes it



      *And a side finding of the sweep changes the expectation: **there is in the existing code NO
      double acquisition of the same lock class** (`system.rs`:15). The expected first test case for
      `locks ordered` thereby drops out; the one that was found is a different one — two classes with
      an ordering over two crates (V4).*

- [ ] **`by ops` is built — what stays open is ONE breakthrough: `breaking` on a
      `by ops` field.** The checker answers the question today *implicitly*: `kbedingung.rs`
      keeps the `breaking` sites per carrier, and `ist_geschlossen` demands that there be none
      — a `breaking` therefore **opens the carrier again**, instead of being a compile error.
      **That is a defensible answer and it stands stated nowhere.**
      *A property whose back door stands only in the code is a promise with a back door.*
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
### The four items to the goal — plan with gates in [`dokumente/PLAN.md`](dokumente/PLAN.md) §A *(Teil)*

- [ ] **A4 — `costs` at a RECURSIVE function stays an assumption.** A call counts
      the *declared* costs of the callee; at a cycle nobody recomputes. That is
      the intention of §7 — but it means that the termination hangs there on a promise.

---

# STUFE 6 — DIE FREMDEN RÜMPFE SPRECHEN LASSEN

**80 fremde Rümpfe im Korpus, 0 sprechen ihre Pflicht aus.** `ensures` an einer rumpflosen
Deklaration ist grammatisch seit jeher möglich — **und kein Pass liest es.**

Das ist die eine Klasse, die sich auch unter *„ganz Gabbro verifiziert"* nicht auflöst, und damit
**genau die Klempnerei, die beim Endnutzer übrig bleibt: Ziel 4 hängt hier stärker als an `H`.**
Eine Sperre schuldet gegenseitigen Ausschluss, Fortschritt und die Rangordnung, und keine Zeile
sagt das heute.

Zwei Hälften: die Zeilen hinschreiben (kostet nichts) und den Prüfer sie in die Beweispflicht des
Rufers tragen lassen (Passarbeit). Dazu die Axiomschicht — 32 Annahmen, jede mit Sonde oder Grund,
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

- [ ] **`ensures` ist wohlgeformt geprueft -- die EINLOESUNG fehlt** *(nachgemessen
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
      * **x86:** runnable against `../caprock-messbasis` (= `SEL4Lake/SEL4Lake` @ `arch/x86_64`,
        `a1bf707`). Open.
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

- [ ] **Eine überschreibende Annahme OHNE `falsifier` ist eine Absage** — nicht weil die
      Sonde beweist, sondern weil sie **widerlegbar** macht. Wer ohne sie will, schreibt
      `unfalsifiable`, und das ist im Zeugnis eine eigene Zeile (wie `A10`).

### From the criterion ([`dokumente/BEWEIS.md`](dokumente/BEWEIS.md))



- [ ] **Argue the dividing line at a borderline case.** "Names only the machine" is sharp enough for
      today's cases — the first disputed case belongs in `dokumente/BEWEIS.md`, not in a footnote.

### «NL» — der Weg zu „nur noch eigene Logik" ([`dokumente/PLAN.md`](dokumente/PLAN.md)) — **PUNKT 1** *(Teil)*

- [ ] **NL.3 -- `ensures` ueber WELTZUSTAND, die haeufigere Form** *(2026-08-19)*. Numerisch
      und relational tragen seit heute; `ensures mmu_an_zahl == 1` steht siebenmal in
      `beispiele/22` und traegt nicht. **Sie kollidiert mit U4/U5** -- ein Aufruf toetet jeden
      nichtlokalen Fakt -- und waere die erste Ausnahme davon. *Aufschreiben, bevor gebaut
      wird, wie bei «H2.1».*

### Aus «H2» *(ausgefuehrt 2026-08-19, `H = 17 → 15`)* — der Rest, den der Lauf hinterliess *(Teil)*

- [ ] **Die Axiomschicht schuldet einen Satz ueber den SPERRABDRUCK** *(benannt 2026-08-19
      von `Gruppe_Erhaltung.thy`)*. Das Locale `zug` nimmt `voll i` als *„der Abdruck ist
      gehalten"* und schliesst daraus, dass niemand hinsieht. **Dass ein gehaltener Abdruck
      einen fremden Kern wirklich fernhaelt, ist eine Aussage ueber das SPEICHERMODELL** und
      faellt nicht in diesen Satz -- dieselbe Stelle, an der `paarung` ihre
      `release`/`acquire`-Sichtbarkeit schuldet. *Vorher war die Praemisse unsichtbar; jetzt
      steht sie in der Zahl.*

- [ ] **Die HAEUFIGERE Haelfte von Punkt 4 fehlt: `ensures` ueber WELTZUSTAND**
      *(gemessen 2026-08-19)*. Von 28 fremden Deklarationen liefern nur **4** eine Ganzzahl;
      die Mehrheit spricht ueber Plaetze (`ensures mmu_an_zahl == 1`, siebenmal in
      `beispiele/22`). **Die Wiederherstellung einer Tatsache ueber einen globalen Platz nach
      einem Ruf kollidiert mit U4/U5** -- *ein Aufruf toetet jeden nichtlokalen Fakt*, und
      `mutiere-pruefer.py` fuehrt dafuer eine eigene Mutation. *Sie waere die erste Ausnahme
      von dieser Regel und gehoert gemessen, bevor sie gebaut wird.*

- [ ] **`Self` in einem `ensures` ist ungemessen** *(2026-08-19)*. `sammle_namen_pred` bindet
      seit heute Quantorbinder und steigt in Indizes ab; **`Self` kennt es nicht.** Im Korpus
      steht `Self` nur in `invariant`, wo dieser Pass nicht laeuft -- *also ist es heute kein
      Fehlalarm und morgen vielleicht einer.* Eine Zeile, sobald ein `ensures` es benutzt.

- [ ] **Die GNADENFRIST ist eine ANNAHME, keine Pruefung -- und hat noch keinen Ort**
      *(2026-08-18)*. `H011`/`H012` halten die zwei pruefbaren Haelften (nicht im eigenen
      Lesebereich, nicht ohne Schreibersperre). Dass kein Leser das alte Objekt mehr sieht,
      stellt kein statischer Pass her. **Sie gehoert dorthin, wo `progress` steht** -- und der
      Pruefer verlangt sie noch nicht: ein `rcu … reclaims` ohne eine benannte
      Gnadenfristannahme geht heute durch. *Dieselbe Regel wie `S003`, an einem anderen
      Konstrukt.*

### From wave 4 (2026-08-16) — two conditions and one candidate

- [ ] **«B38» — the side condition on the named carrier.** *"The continuation re-checks
      **or** names what it carries instead"* is the right form — **but a carrier
      `masks IRQ` holds only if the entry context carries `nested masked`.** Without this
      coupling *"the masking carries me"* is the assurance from **R15**, which is satisfied
      as soon as the checker is silent. **Mechanically checkable** via `entrydecl`; to be built.

- [ ] **«B39» — the exception rule to the hardware axiom, and it is a CANDIDATE for a new
      word.** `A`/`D` are written by the MMU itself — the GDT lesson at the page machinery. **As soon as
      group `ops` reach the page machinery, the axiom collides with the
      write-right promise**: the K condition demands that ALL write sites be generated.
      Which fields of a `walk` declaration are **hardware-writable** belongs at the
      declaration (candidate line `hardware A, D;`), the way `reserved` belongs at a
      `format` field. *`R001` does not see the MMU today — it writes past every grammar,
      only in the `normal` space instead of in the `dma` space.*
      **It burdens the convergence bet: it would be column 1, not only column 2.**

---

# STUFE 7 — WAS PROGRAMME GROSS MACHT

**`fnptr` — erst der Erzeuger, dann der Vertrag.** Ein Funktionszeiger entsperrt jede
Dispatch-Tabelle, jede Treiber-ops-Struktur, jede Scheduler-Politik — Caprocks
`&mut dyn SchedOps` ist genau das. Heute hat `fnptr` **null Korpusstellen und keinen Erzeuger**:
die Sprache kennt kein `&f`. *In der anderen Reihenfolge wäre der Vertrag eine Zusage ohne
Einlöser — die Bewegung, gegen die K100s zweites Tor steht.*

Dazu die **ABI** (Bibliotheken, die sich mischen lassen) und die **Generizität** — ohne sie
braucht jede Tabelle ihr eigenes `traverse`.

### K100 — der Weg auf 100 % Klempnereiabdeckung ([`dokumente/PLAN.md`](dokumente/PLAN.md)) *(Teil)*

- [ ] **«B9» braucht einen ERZEUGER, bevor ein Vertrag an `fnptr` etwas heisst**
      *(bewertet 2026-08-20, `PFLICHTEN.md`:613-624)*. Der Befund verlangt `requires`/`ensures`/
      `effects` am Funktionszeigertyp. **`fnptr` hat null Korpusstellen, und die Sprache kennt
      keine Form, einen Funktionszeiger HERZUSTELLEN** -- es gibt kein `&f`. Ein Vertrag an
      einem Typ, den niemand erzeugen kann, ist eine Zusage ohne Einloeser: genau die
      Bewegung, gegen die K100s zweites Tor steht. *Erst der Erzeuger, dann der Vertrag.*

- [ ] **Nachgemessen 2026-08-20: die Schnittstelle faellt LAUT, nicht lautlos.** Zwei
      Dateien in EINEM Lauf werden weiter getrennt geprueft — jede ist ihre eigene
      Uebersetzungseinheit. Ein `use bib::tu;` ueber die Dateigrenze ergibt **`E009`**
      (*„`tu` is unknown to the graph"*) und **`K003`** (*„promises costs, but `tu` is not
      declared here"*), also einen FEHLER. *Der Eintrag oben sagt „faellt lautlos auf untere
      Schranke zurueck" — gemessen faellt sie nicht durch, sie faellt.* **Was fehlt, ist
      nicht der Riegel, sondern die Bruecke.** Und `pub` hat seit dem 2026-08-19 einen Leser
      (`N025`) — die Sichtbarkeitshaelfte einer API steht damit. Der Erzeuger schreibt
      weiterhin **keinen Kopf**: eine `.c` je Einheit, Prototypen inline.

- [ ] **Eine Bibliotheks-ABI, und das Format steht schon** *(bewertet 2026-08-18,
      `PLAN.md`: „Zwei Fragen, die die Grenzen beschreiben")*. **Gabbros ganze Zusage ist eine
      Aussage ueber EINE Uebersetzungseinheit** -- jede der elf Klassen wird an einem Baum
      geprueft, den ein Lauf ganz sieht. Eine Bibliothek durchschneidet genau das, und ohne
      ABI faellt die Zusage an der Schnittstelle lautlos auf „untere Schranke" zurueck (`E009`).
      **`gabbro zeugnis` schreibt bereits, was sie tragen muss:** Annahmenmenge, Schablonen mit
      Beweisstand, `effects`/`costs`/`Held`, und die SPERRRAENGE -- *der schaerfste Posten:
      zwei Bibliotheken mit unabhaengig vergebenen Raengen ergeben einen Zyklus, den keine von
      beiden allein sehen kann.* Was fehlt: `gabbro pruefe` liest die Zeugnisse der gerufenen
      Bibliotheken mit und vereinigt sie -- mit denselben Weigerungen, die es innerhalb einer
      Einheit schon gibt. **Der erste Posten, bei dem Gabbro etwas gewinnt, ohne eine Klasse
      zurueckzugeben.**

### Syntax — open decisions (details in [`dokumente/SYNTAX.md`](dokumente/SYNTAX.md)) *(Teil)*

- [ ] **Genericity** — without it every table needs its own `traverse`; with it the question
      of how contracts are parameterised.

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

- [ ] **Darf eine `pub`-Signatur einen privaten Namen nennen?** Heute ja — und `gabbro abi`
      zieht den privaten Typ dann in die Schnittstelle nach, weil die Alternative eine
      Schnittstelle mit toten Namen wäre. **Das ist die ehrliche Folge einer Entscheidung,
      die niemand getroffen hat.** Die andere Lesart wäre eine Absage im Namenspass (wie
      Rusts `private_interfaces`). *Eine Sprachentscheidung, keine Bauarbeit* — sie steht
      hier, damit die Nachziehschleife nicht als Absicht durchgeht.

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

---

# STUFE 8 — PL: DIE LOGIK DES PRÜFERS

**Zwölf Pässe entscheiden über jedes Programm, und keiner schuldet einen Satz** (`struct Pass`
hat kein Feld dafür). **Ohne die Sätze ist „Gabbro formal verifiziert" nicht einmal
formulierbar** — man wüsste nicht, was zu beweisen wäre.

Dieselbe Bauart wie `schablonen.rs`, mit denselben zwei Zähnen; ~22 Sätze geschätzt. Zweiter Zahn
sofort: *kein neuer Absagecode ohne seinen Satz* (heute 189 Codes, null Sätze).

### K100 — der Weg auf 100 % Klempnereiabdeckung ([`dokumente/PLAN.md`](dokumente/PLAN.md)) *(Teil)*

- [ ] **PL.1 — das PASSREGISTER anlegen** ([`dokumente/PLAN.md`](dokumente/PLAN.md), PL).
      **Zehn Paesse entscheiden ueber jedes Programm, und keiner schuldet einen Satz** --
      dieselbe Lage, in der die Schablonen vor ihrer Auszaehlung waren. Wie `schablonen.rs`,
      mit denselben zwei Zaehnen; **~22 Saetze** geschaetzt. Zweiter Zahn sofort: *kein neuer
      Absagecode ohne seinen Satz* (heute 52 Codes, null Saetze).

- [ ] **PL.2 — die drei Saetze mit der groessten Traglast:** `K001` Summation (**hat heute schon
      einen gemessenen Fehler**), `H006` Rangordnung, V2 relationale Verengung (102 Stellen).

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

# NICHT JETZT — ausdrücklich zurückgestellt, mit Grund

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

- [ ] **Version evolution:** does an `@version 3` reader also read v2 — **refusal or migration**?
      Both defensible, neither decided.

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

# Historie dieser Datei

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

# BOOKKEEPING
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
| **5** | **Stale numbers from P1**: 117 rules, 187 terminals (today 146 / 216) | taken out along with the entry |
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
