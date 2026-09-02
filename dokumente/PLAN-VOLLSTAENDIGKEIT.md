# Der Vollständigkeitsplan — jedes valide Gabbro-Programm senkt ab, und `H = 0`

*Ausgeplant am 2026-08-30, auf die Frage: **kann man beliebige Gabbro-Programme schreiben und
nach C übersetzen, ohne dass Klempnerei für den Nutzer übrigbleibt?** Der Plan wird hier
geschrieben und nicht ausgeführt.*

> **Die Grenze nach C gehört NICHT hierher.** Dass ein fremder C-Anrufer die Schranken einer
> `pub`-Funktion nicht einhalten muss, ist keine Klempnerei — es ist die Definition einer
> Grenze. *Ein Werkzeug kann nicht prüfen, was es nicht liest.* Diese Frage gilt **reinen
> Gabbro-Programmen**, und der Plan hält sich daran.

---

# 0. Die Frage zerfällt in zwei, und sie sind verschieden schwer

| | |
|---|---|
| **V** — Vollständigkeit | **Kennt der Erzeuger jedes Programm, das der Prüfer annimmt?** Eine Aussage über zwei Mengen, und beide sind endlich beschreibbar |
| **K** — Klempnerei | **Bleibt nach der Absenkung eine Pflicht am Menschen, die nicht seine eigene Logik ist?** Heute ~~`H = 5`~~ **`H = 4`** *(F6 durchgestochen 2026-08-31)* |

**Sie hängen zusammen, aber nicht so, wie es aussieht.** `V` kann vollständig sein, während `K`
offen ist: ein Erzeuger, der jede Form kennt und für keine bewiesen hat, dass sie stimmt, hat
`V` erfüllt und `K` nicht. *Umgekehrt geht es nicht* — was nicht absinkt, hat auch keine
Absenkungspflicht.

---

# 1. Der gemessene Stand, 2026-08-30

```
70 valide Programme im Korpus (Pruefer: 0 Fehler)
   68 senkt der Erzeuger ab
    2 sagt er ab, mit 3 benannten Absagen

23 Programme mit Pruefer-Fehlern
   20 davon sind ABSICHTLICH so geschrieben (fnptr-, race-, abi-Proben)
    3 sind echter Code: F01, F03, F09
```

**Die drei Absagen des Erzeugers, wörtlich:**

| | Form | wo |
|---|---|---|
| **V1** | `breaking I { … }` — *der Block ist eine BEWEISREGION: darin ist die Invariante keine Prämisse* | `beispiele/53-zwei-orte.gab`, 2× |
| **V2** | ~~`match` über etwas anderem als `option index into T`~~ | ~~`messung/fragmente/F05.gab`~~ — **GEFALLEN am 2026-08-31:** fünf `extern fn`-Zeilen nehmen die Absage weg, und ihr eigener Satz nannte die Heilung. Die Datei fällt seither an `N041` — an einem NAMEN, nicht an einer Form (`messung/F05-UNERREICHBAR.md`) |

**Und die drei echten Programme, die schon der PRÜFER abweist:**

| | Kennung | was |
|---|---|---|
| **P1** | `N029` | `F01`: ein fehlbarer Ruf steht nicht in `let … else`. **Kein Sprachloch — der Preis der Entscheidung „kein `?`"**, und er steht hier, damit er sichtbar bleibt |
| **P2** | `N035`, `N040`, `M124`, `M101`, `H011` | `F03`: 19 Fehler. `N035` ist der **Funktionszeigervertrag** (Stufe 7), `M124` ist ein echtes Loch (*ein Grundwert kann hier nicht stehen*), der Rest sind Namen, die das Fragment als Auszug nicht deklariert |
| **P3** | `K001` | `F09`: der Kostenkalkül explodiert — **137 438 953 472 ops gegen ein Versprechen von 4096.** Ein `walk … levels` multipliziert sich, und die Domänenschranke ist als `VERMUTET` gebucht |

> **BERICHTIGT am 2026-08-31, Bahn P — und alle drei Zeilen darüber sind schiefer, als sie
> aussehen.** Je Posten ein `W24`-Vorlauf gegen den unveränderten Prüfer; die Rechnungen
> stehen in [`../messung/K001-DOMAENENSCHRANKE.md`](../messung/K001-DOMAENENSCHRANKE.md) und
> [`../messung/DREI-FRAGMENTABSAGEN.md`](../messung/DREI-FRAGMENTABSAGEN.md).
>
> | | was hier stand | was gemessen ist |
> |---|---|---|
> | **P1** | *„der Preis der Entscheidung «kein `?`»"* | **schärfer:** mit `?` stünde dort `delete_leaf(…)?;` — auch eine geänderte Zeile, und die Kostenzahl bewegte sich genauso (`+80 256 ops` = eine op je Durchgang). *Keine Fehlerweitergabe lässt die Zeile stehen.* Und im Original ist `delete_leaf` **gar nicht fehlbar** — fehlbar macht sie «B29» bei `FRAGMENTE.md`:268. **Beide Hälften einer Entscheidung im selben eingefrorenen Bericht, im Widerspruch.** |
> | **P2** | `N035` „Stufe 7" · `M124` „ein echtes Loch" | `N035` ist seit dem 2026-08-21 **gebaut, gelesen und bewacht** (drei Giftproben, drei Mutationen; der Zeigertyp gibt `K001` seine Zahl und `E008` seine Wirkung). `M124` ist **kein Loch, sondern eine richtige Absage:** die Vorlage in `caprock-messbasis` führt dort `pub const … : u64`, **null Projektionen im ganzen Baum** — und die zwei Zahlenräume weichen heute schon ab (`ErrBadCap = 2` gegen `ERR_BADCAP = 1`). |
> | **P3** | *„der Kostenkalkül explodiert"* | die Zahl ist **richtig und scharf** (`Rumpf × Knotenlänge^Ebenen`, `512⁴ = 2³⁶` = die Seiten eines 256-TiB-Adressraums). Falsch ist die ZUSAGE — sie wurde mit der zurückgezogenen Lesart gerechnet. **Und `F09` blockiert nicht der Prüfer, sondern dreimal der ERZEUGER**; keine der drei `C001` hängt an `K001`. |
>
> **Damit gehört von den drei „echten Programmen, die schon der PRÜFER abweist" keines mehr
> in diese Liste** — `F09` in die Erzeugerliste, `F01` und `F03` zu den Befunden IM Bericht.
> *Die Menge, die dieser Plan sucht, war an dieser Stelle um drei zu groß.*

---

# 2. Warum eine Korpuszahl die Frage **nicht** beantwortet

**„68 von 70" ist keine Antwort auf „jedes valide Programm".** Der Korpus ist von der Sprache
nach außen geschrieben; wer ihn zählt, misst, was jemand hinschreiben konnte, während er auf
die Sprache sah. *Das ist Falle 80, und sie gilt hier genauso wie bei `H`.*

> **Die ehrliche Form der Aussage ist nicht „kein Programm im Korpus fällt", sondern
> `C001` ist für ein angenommenes Programm UNERREICHBAR.**

Und das ist **endlich prüfbar**, ohne einen einzigen weiteren Korpus:

```
crates/gabbro-check/src/emit.rs   136 Aufrufe von `weigere(…)`, 127 VERSCHIEDENE Formen
```

> *~~22 Stellen~~ — **berichtigt am 2026-08-30, noch vor dem ersten Schritt.** Die 22 waren
> `grep C001`, und das zählt die Kommentare mit. `C001` entsteht an genau EINER Stelle
> (`fn weigere`); was zählt, sind ihre **Aufrufer**. Die erste Zahl dieses Plans war um den
> Faktor sechs zu klein, und sie ist gefallen, weil jemand sie nachgerechnet hat, statt sie
> zu benutzen.*

**Hundertsiebenundzwanzig Fragen statt zweiundzwanzig.** Für jede: *welche Form sagt sie ab,
und weist der PRÜFER dieselbe Form schon vorher ab?* Fällt die Antwort für alle auf „ja",
dann ist `V` **nicht gezählt, sondern gezeigt** — über der Sprache statt über einem Korpus.

Fällt sie für eine auf „nein", ist genau das die Lücke, und sie hat eine Adresse.

**Und die Frage ist eine Spur schärfer, als sie eben noch war.** Am 2026-08-30 wurde gemessen:
**`messung/fragmente/F06.gab` emittiert 161 Zeilen, und `cc -Werror` weist sie zurück.** Die
Eigenschaft heißt deshalb nicht *„der Erzeuger kennt jede Form"*, sondern:

> **Für jedes Programm, das der Prüfer annimmt, erzeugt der Erzeuger C — und dieses C
> übersetzt.** *Ein Erzeugnis, das kein C ist, ist keine Absenkung, es ist eine stille
> Absage.*

**Das Werkzeug dafür steht schon zur Hälfte da.** `gabbro blindstellen` rechnet FORM × POSITION
über einen Korpus und benennt die leeren Zellen — *„was 0 Fundstellen hat, ist nicht geprüft,
sondern unerreichbar."* Was fehlt, ist dieselbe Tafel **aus der Grammatik statt aus dem
Korpus**: `dokumente/SYNTAX.md` führt 154 Regeln und 219 Terminale, und das ist die
Grundgesamtheit, die „beliebig" meint.

---

# 3. Die Schritte für **V**

### V1 — Die 22 `C001`-Stellen aufschlüsseln *(Messung, kein Bau)*

Je Stelle: die abgesagte Form, die Position in der Grammatik, und **die Prüferkennung, die sie
schon vorher abweist** — oder ein Kreuz, wenn es keine gibt. Ergebnis ist eine Tafel mit
22 Zeilen und einer Spalte, die leer sein muss.

*Erwartung, aus dem heutigen Lauf: mindestens drei Kreuze* (V1, V2 oben und der `bounded … ops`-Fall,
dessen Text im Erzeuger schon steht).

### V2 — FORM × POSITION aus der GRAMMATIK

`gabbro blindstellen` bekommt eine zweite Quelle: statt der Fundstellen eines Korpus die
Produktionen der EBNF. Jede Zelle bekommt genau einen von vier Zuständen:

```
gesenkt        der Erzeuger hat einen Arm
abgesagt       der Erzeuger sagt benannt ab  -- und der Pruefer AUCH
vom Pruefer    der Pruefer weist die Form ab; der Erzeuger sieht sie nie
UNGEDECKT      keiner von beiden -- und das ist die Menge, die leer sein muss
```

> **`UNGEDECKT` ist die ganze Frage.** Alles andere ist Buchhaltung.

### V3 — Die gefundenen Lücken schließen oder benennen

Je `UNGEDECKT`-Zelle **eine** Entscheidung, mit `W24`-Vorlauf davor: die naheliegende Form
hinschreiben, durch den unveränderten Prüfer laufen lassen, und erst danach entscheiden.

* **Absenken**, wenn die Form gemessenen Bedarf hat (Regel A).
* **Im PRÜFER absagen**, wenn nicht — dann wandert die Zelle von `UNGEDECKT` nach `vom Pruefer`,
  und das ist ein vollwertiger Ausgang. *Eine Sprache, die eine Form nicht hat, ist
  vollständig, solange sie das sagt.*

**Was NICHT geht: die Zelle offen lassen.** Ein Programm, das der Prüfer annimmt und der
Erzeuger nicht kennt, ist der einzige Zustand, den dieser Plan verbietet.

### V4 — Der Wächter, der es hält

`V2` als Instrument, nicht als einmalige Messung: ein Lauf, der `UNGEDECKT > 0` rot meldet.
**Sonst ist V eine Zahl von einem Tag** — und dieser Ordner hat heute siebenmal erlebt, was
eine Zahl ohne Befehl daneben wert ist.

Mit Sprechprobe in beide Richtungen: eine künstlich entfernte Absenkung muss die Tafel rot
machen, und eine künstlich erfundene Form auch.

---

# 4. Die Schritte für **K** (`H = 0`)

~~`H = 5`~~ **`H = 4`**, und alle vier sind **dieselbe** Pflicht: *das erzeugte C rechnet, was
das Fragment sagt* — offen für F1, F3, F5, F9. Für F2, F4, **F6**, F7, F8, F10 ist sie **durch
Ausführung** eingelöst: erzeugt, übersetzt, ausgeführt, gegen eine Handschrift verglichen.

> **F6 ist am 2026-08-31 dazugekommen, und es ist das erste der fünf, das den Weg gehen
> konnte.** Was es gekostet hat, war kein Bau am Fragment, sondern eine Zeile im Erzeuger: der
> Feldindex von `elems of` senkte als `uint32_t` ab — eine Kopie aus `slots of` —, und
> `w != MUSTER` mit `MUSTER = 0xdead_beef_dead_beef` fiel damit an
> `-Wextra`s *comparison is always true due to limited range*. **Mit `uint64_t` übersetzt
> dasselbe C.**

### K1 — Die fünf offenen auf denselben Weg bringen

Je Fragment: eine Handschrift daneben, dieselben Eingaben, Ausgaben verglichen, in
`pruefe-emission.sh` gebucht. **Das ist der billige Weg, und er ist heute schon fünfmal
gegangen.**

**Aber drei der fünf gehen so nicht**, und das ist der eigentliche Inhalt dieses Abschnitts:

* **F3 und F9 sind für den Prüfer gar keine gültigen Programme** (P2, P3 oben). *Eine
  Absenkungspflicht an einem Programm, das nicht übersetzt, ist keine offene Pflicht, sondern
  eine falsch gebuchte.* Erst P2/P3, dann K1.
* ~~**F5** senkt nicht ab (V2 oben). Erst V, dann K.~~ **BERICHTIGT am 2026-08-31, Bahn F5 —
  und die Reihenfolge stimmte, das Hindernis nicht.** `V2` (`match` über etwas anderem als
  `option index into T`) ist **nicht mehr die Ursache**: fünf `extern fn`-Zeilen nehmen den
  `C001` weg, und danach stehen 31 Items, 0 Fehler, 199 Zeilen C. Das eigentliche Hindernis
  ist ein NAME: `exit` gehört C, der eingefrorene Ausschnitt ruft ihn neunmal, und `cc`
  weist die Einheit zurück. **Seit heute weist der PRÜFER sie zurück** (`N041`,
  [`../messung/C-NAMEN.md`](../messung/C-NAMEN.md)) — *damit ist `F05` in derselben Klasse
  wie F1 und F3: ein Programm, das Gabbro nicht annimmt.* Und es ist **unerreichbar**, nicht
  bloß offen: umbenennen hieße neun eingefrorene Zeilen weglassen, und C führt
  `void exit(int)` gegen ein `exit()` ohne Argument
  ([`../messung/F05-UNERREICHBAR.md`](../messung/F05-UNERREICHBAR.md)).

> **Damit ist `H = 0` nicht vor `V` erreichbar**, und das ist der Grund, warum dieser Plan
> zwei Hälften hat und nicht zwei Pläne ist.
>
> **Und seit dem 2026-08-31 ist die Lage schärfer, als dieser Abschnitt sie beschreibt:
> ALLE VIER offenen Absenkungspflichten hängen an Programmen, die Gabbro nicht annimmt.**
>
> | | weist wer ab | Kennung |
> |---|---|---|
> | **F1** | der PRÜFER | `N029` |
> | **F3** | der PRÜFER | `N035`, `N040`, `M124`, `M101`, `H011` |
> | **F5** | der PRÜFER — *seit heute* | `N041` |
> | **F9** | der ERZEUGER, dreimal | `C001` |
>
> *Der eigene Satz dieses Abschnitts — „eine Absenkungspflicht an einem Programm, das nicht
> übersetzt, ist keine offene Pflicht, sondern eine falsch gebuchte" — trifft damit nicht zwei
> der vier, sondern alle.*
>
> **Und die Bewegung ging am selben Tag noch zweimal in dieselbe Richtung** — beide Male von
> `cc` zum Prüfer bzw. vom stillen C zur benannten Absage:
>
> | | vorher | seit dem 2026-08-31 |
> |---|---|---|
> | ein `format`-Feld, das `gueltig` heisst | Prüfer 0 Fehler, `emit` ohne `C001`, `cc` sagt *Redefinition* | **`N042`** — und es sind NEUN Kollisionsformen, nicht zwei ([`../messung/ERZEUGERNAMEN.md`](../messung/ERZEUGERNAMEN.md)) |
> | `device … at port` | Prüfer 0 Fehler, `emit` schreibt die PORTNUMMER als Speicherversatz, `cc` nimmt an | **`C001`** — die Absage statt einer Absenkung, die es nicht gibt ([`../messung/ADRESSRAEUME.md`](../messung/ADRESSRAEUME.md)) |
>
> Die zweite ist der schärfere Fall: dort war das C nicht *abwesend*, sondern **falsch**, und
> kein Werkzeug der Kette hat es gemeldet. **Die Umbuchung ist EINE Entscheidung über alle vier und gehört dem
> Ordner;** eine Bahn, die `F5` allein umbucht, senkt `H` um eins und lässt drei gleichgelagerte
> Zeilen stehen. *Das ist Umtopfen.*

### K2 — Und was „durch Ausführung eingelöst" nicht ist

**Eine Messung über Eingaben, kein Satz über alle.** Zehn Fragmente, ausgeführt, verglichen —
das schließt aus, dass die Absenkung *offensichtlich* falsch ist, und mehr nicht.

`beweise/Absenkung_Parametrisch.thy` zeigt, wie das andere Ende aussieht: der Satz steht
parametrisch über sechs Eigenschaften der Zielsemantik — **und er ist an einem Zweig falsch**
(`relabel` berechnet `umhaengen` nur am belegten Platz). *Genau das findet keine Ausführung,
die den freien Platz nie trifft.*

**Die Entscheidung, welcher der drei Wege gegangen wird, steht aus** und ist die Vorbedingung
von allem hier: `messung/ABSENKUNG.md`, drei Formen.

---

# 5. Was `V = vollständig` und `H = 0` **beweisen** — und was nicht

**Sie beweisen nicht, dass das Konzept stimmt.** Zwei benannte Gründe, beide gemessen:

1. **Falle 80.** Die zehn Fragmente sind **nach ihrer Schwierigkeit gewählt** und geschrieben,
   während jemand auf die Sprache sah. `H = 0` über ihnen ist eine Aussage über zehn
   Programme. *Der Zähler sagt es selbst, in seiner eigenen Ausgabe.*
2. **`H = 0` heißt „keine Pflicht steht offen", nicht „die Absenkung ist richtig".** Der
   Unterschied ist eine Beweisschicht, und `Absenkung_Parametrisch.thy` hat gezeigt, dass er
   nicht theoretisch ist.

**Was sie sehr wohl beweisen, und es ist nicht wenig:**

> **Dass die Sprache eine Grenze hat, die man aufschreiben kann.** Heute ist „was Gabbro
> kann" die Menge dessen, was jemand hinschreiben konnte. Nach `V` ist es eine Tafel mit
> vier Zuständen und einer leeren Spalte — *und eine Sprache, deren Grenze man kennt, ist
> eine andere Sache als eine, deren Grenze man vermutet.*

**Und was den Beweis wirklich brächte, steht schon gebucht:** ein zweiter Korpus, den beim
Schreiben niemand mit den Sprachdokumenten daneben geschrieben hat. *Er ist die einzige
Messung, die Falle 80 auflöst*, und er ist als Teil des `caprock-part`-Laufs gebucht — mit
seiner Bedingung.

---

# 6. Die Reihenfolge, und woran sie hängt

```
  V1  die 22 C001-Stellen aufschluesseln          Messung, billig, sofort
  V2  FORM x POSITION aus der GRAMMATIK           Bau, ein Instrument
  P2  der Funktionszeigervertrag (N035)           Stufe 7, unabhaengig
  P3  die Kostendomaenenschranke (K001)           gemessen 2026-08-31, alle fuenf
  V3  je UNGEDECKT-Zelle eine Entscheidung        haengt an V2
  V4  der Waechter                                haengt an V3
  ---------------------------------------------------------------
  ABSENKUNGSENTSCHEIDUNG                          haengt an nichts -- sie ist faellig
  ---------------------------------------------------------------
  K1  die fuenf offenen Fragmente ausfuehren      haengt an V3, P2, P3
  K2  H = 0 buchen -- mit dem Satz aus 5 daneben
```

**Der erste Schritt ist reine Messung und kein Bau.** *Hundertsiebenundzwanzig Fragen an eine
Datei, die schon geschrieben ist* — und wo die Antwort „der Prüfer weist es vorher ab" lautet,
ist die Zelle heute schon zu und niemand wusste es. **Die interessante Menge ist der Rest.**

---

# 7. Der Durchlauf — zwei Bahnen, und die Reihenfolge ist die Aussage

*Aufgesetzt am 2026-08-30. **Die Bahnen sind so geschnitten, dass sie sich nicht berühren:**
Bahn V arbeitet am ERZEUGER und an der Grammatiktafel, Bahn P am PRÜFER. Der einzige
gemeinsame Boden ist `TODO.md`, und dort sind Konflikte additiv.*

## Schritt 0 — V1, seriell, vor beiden Bahnen

Die **127 Absageformen** in `emit.rs` aufschlüsseln (136 Aufrufe von `weigere`). Je Stelle drei Spalten:

```
Form            was die Stelle absagt, in der Sprache der Grammatik
Pruefer         die Kennung, die dieselbe Form schon vorher abweist -- oder ein KREUZ
Zustand         gesenkt | abgesagt (Pruefer auch) | UNGEDECKT
```

**Diese Tafel ist die Arbeitsliste beider Bahnen.** Ohne sie arbeiten beide gegen eine
Vermutung. *Sie kostet mehr als einen Nachmittag — 127 Formen — und keinen Bau.*

## Bahn V — der Erzeuger kennt jede Form

| | |
|---|---|
| **V-a** | `gabbro blindstellen` bekommt die **Grammatik** als zweite Quelle (§3, V2). Vier Zustände je Zelle, `UNGEDECKT` muss leer sein |
| **V-b** | Die zwei bekannten Absagen entscheiden: `breaking I { … }` (Beweisregion) und `match` über etwas anderem als `option index into T`. **W24-Vorlauf zuerst** |
| **V-c** | Je weitere `UNGEDECKT`-Zelle eine Entscheidung: absenken (bei gemessenem Bedarf) oder **im PRÜFER absagen** — beides ist ein voller Ausgang |
| **V-d** | Der Wächter (§3, V4): `UNGEDECKT > 0` ist rot, mit Sprechprobe in beide Richtungen |

## Bahn P — der Prüfer nimmt jedes Programm an, das er annehmen soll

| | | Stand 2026-08-31 |
|---|---|---|
| **P-a** | **`K001`, die Kostendomänenschranke.** `F09` verspricht 4096 ops, der Kalkül rechnet 137 438 953 472. *Sieben Größenordnungen, und die Schranke steht als `VERMUTET` gebucht.* Der teuerste Posten und der einzige, der ein echtes Programm blockiert | **gemessen.** Die Zahl ist richtig und scharf; die Zusage ist falsch. `F09` bleibt (der Erzeuger blockiert es dreimal). Zwei Proben + eine Mutation schließen die Lücke, die der Satz selbst nannte; Stand bleibt `VERMUTET` (1 von 5 Domänen gemessen) |
| **P-b** | **`N035`, der Funktionszeigervertrag.** `fn(#1) -> …` ohne `effects`/`costs`; Stufe 7 | **war schon gebaut** (2026-08-21) — beide Vertragshälften haben einen LESER, drei Giftproben und drei Mutationen. Nichts gebaut, Buchung berichtigt |
| **P-c** | **`M124`** — *ein Grundwert kann hier nicht stehen*. Drei Fundstellen in `F03`. **Erst messen, ob es ein Loch ist oder eine richtige Absage** | **richtige Absage**, außen belegt (Regel B). Eine Zahlprojektion hätte die falsche Zahl gefahren |
| **P-d** | `F01`s `N029` benennen: **kein Loch, sondern der Preis der Entscheidung „kein `?`"** — und `F01` entsprechend schreiben oder die Buchung berichtigen | **Buchung berichtigt und geschärft.** `F01` bleibt: die Form gibt es, aber sie kostet ZWEI eingefrorene Zeilen |

> **Und ein Nebenfund aus P-as Vorlauf ist repariert:** `umgebung.rs` entschied die Existenz
> eines `walk`-TYPS über die **Kostenkarte**, also über die Frage, ob seine Blattzahl in
> `u128` passt. `walk W levels 0`, `node : [Pte; 0]` und `512¹⁵` sagten alle drei
> **`N040`: `W` names no type** — zwei davon gewöhnliche Tippfehler. *Zwei Fragen, eine
> Karte* (W7); jetzt zwei Karten, mit Probe und Mutation.

## Schritt 6 — seriell, nach beiden Bahnen

`K1`: die fünf offenen Absenkungspflichten ausführen und vergleichen. **Erst hier, weil drei
von fünf an V und P hängen** — F3 und F9 sind heute für den Prüfer keine gültigen Programme,
F5 senkt nicht ab. Dann `H = 0` buchen, **mit dem Satz aus §5 daneben.**

> ## Und genau hier steht seit dem 2026-08-31 eine Wand, die keine Bahn einreißt
>
> **Bahn P hat gemessen, dass F1, F3 und F9 nicht deshalb fallen, weil dem Prüfer etwas
> fehlt, sondern weil ihre eingefrorenen Zeilen falsch sind.** Damit ist der Satz *„erst
> P2/P3, dann K1"* für diese drei nicht bloß unvollständig — er hat kein Ziel:
>
> | | was das Fragment bräuchte | wie viele EINGEFRORENE Zeilen |
> |---|---|---|
> | **F1** | `:337` in ein `let … else`, `:328` von `16452480` auf `16532736` | **2** |
> | **F3** | Vertrag IN die fünf `fn(…)`-Zeilen, drei `set_reg`-Argumente auf `const` | **8** |
> | **F9** | `:79` von `4096` auf die ehrliche Zahl — *und danach immer noch drei `C001`* | **1**, und es hilft nicht |
>
> Die Regel dieses Ordners lautet: *„Ergänzt werden **nur** Deklarationen, die der Ausschnitt
> ruft und nicht nennt. Nichts wird umgeschrieben."* **Solange sie gilt, ist `H = 0` über den
> AUSFÜHRUNGSweg für diese drei nicht erreichbar** — nicht schwer, sondern ausgeschlossen.
>
> *Das ist kein Grund, die Regel zu lockern.* Sie ist der Maßstab, und ein Maßstab, der
> nachgibt, wo er drückt, misst nichts mehr. **Was folgt, ist eine Entscheidung des Ordners
> und keine Aufgabe einer Bahn:** entweder `H` wird über sieben Fragmente statt über zehn
> gebucht — *mit der Bezugsgröße daneben*, wie `W17` es verlangt — oder die drei wandern in
> eine eigene Spalte: **„Pflicht an einem Programm, das der Bericht nicht hergibt."**
>
> *Was NICHT geht, ist sie als „offen" weiterzuführen.* Eine Pflicht, deren Erfüllung eine
> Regel verbietet, ist keine offene Pflicht — sie ist eine falsch gebuchte, und das ist
> dieselbe Klasse wie `F09` in der Prüferliste, eine Ebene höher.

> **Und was in diesem Durchlauf ausdrücklich NICHT steckt:** die Absenkungsentscheidung
> (`messung/ABSENKUNG.md`, drei Formen). `H = 0` ist über den AUSFÜHRUNGSweg erreichbar, den
> dieser Ordner fünfmal gegangen ist; welcher der drei Wege zum BEWEIS gegangen wird, ist eine
> Entscheidung des Ordners und keine Aufgabe einer Bahn.

---

# 8. Berichtigung, 2026-08-31: es sind nicht vier Entscheidungen, sondern EINE

**Die Tafel schrieb drei Wörtern eine Absage zu, die es nicht gibt.** Nachgemessen, je
kleinstes Programm, durch den unveränderten Prüfer und Erzeuger:

| | `pruefe` | `C001` | was es ist |
|---|---|---|---|
| `chain(a,b) in place` | 0 Fehler | **0** | Quantorendomäne |
| `queue place` | 0 Fehler | **0** | Quantorendomäne |
| `threads` | 0 Fehler | **0** | Quantorendomäne |
| `state Ident { transition … }` | 0 Fehler | **1, mit Grund** | Deklaration |

**Quantorendomänen stehen in `requires`/`ensures` — Annotationen senken nicht nach C ab.**
Die drei sind `UNGEDECKT`, weil sie **niemand im Baum je geschrieben hat**, und das ist kein
Sprachloch, sondern eine Korpuslücke. *Dieselbe Klasse wie die 25 einsamen Wörter: drei
fehlende Programme.*

## Und der Fehler steckt im Werkzeug

```python
if t in absage:
    woher.append("der Erzeuger sagt ab, der Pruefer nicht")
```

`absage` ist die Menge der Wörter, **die in einem Absagetext VORKOMMEN** — nicht die Menge
der Formen, deren Absage jemand gemessen hat. `queue` steht in fremden Absagetexten, also
schrieb die Tafel ihm eine Absage zu.

> **Ein Wächter, der eine Erwähnung für eine Messung nimmt.** Klasse W16, und diesmal ist der
> Schaden nicht die Zahl — die Klassifikation `UNGEDECKT` war richtig —, sondern **der Satz
> daneben.** Er hat drei Korpuslücken vier Tage lang wie eine Sprachentscheidung aussehen
> lassen.

## Die eine echte Absage sagt selbst, was ihr fehlt

> `no lowering:` **`state`** — *the transitions are a proof device over a carrier that is
> declared ELSEWHERE; **which C object holds the state, and whether a transition is a check
> or an assignment, the declaration does not say***

**Der Erzeuger kann sie nicht annehmen, weil die Deklaration die Information nicht enthält.**
Was fehlte: ein benannter Träger (`state Lauf over p`) und je Transition die Angabe, ob sie
prüft oder schreibt.

**Was es brächte:** `state` ist *dieselbe Konstruktion wie `device`s `transition`, eine Ebene
höher* — die untere ist gebaut und läuft. Die obere machte die Zustandsmaschine eines
gewöhnlichen Wertes prüfbar, nicht nur die eines Registers.

**Was dagegen steht: null gemessener Bedarf.** Kein Programm im Baum schreibt `state`.
*Regel A sagt dann nein* — und der ehrliche Zwischenschritt ist, die Absage stehen zu lassen
und die Deklaration zu ergänzen, sobald jemand sie braucht.

---

# 9. Der offene Rest — geplant am 2026-08-31

*Nach der Berichtigung in §8 steht der Task auf **einer** Entscheidung und **drei** fehlenden
Programmen. Alles Übrige ist Sediment, das dieser Task freigelegt hat — `TODO.md` ist an einem
Tag von 242 auf 264 gewachsen, und fast jeder neue Punkt ist ein Befund und keine Absicht.*

## A — Was den Task ABSCHLIESST *(klein, und es ist der Rest)*

| | | Kosten |
|---|---|---|
| **A1** | **Drei Programme für `chain`, `queue`, `threads`** — Quantorendomänen, also in `requires`/`ensures` eines Programms, das einen Gegenstand hat. Danach ist `UNGEDECKT = 1`. | eine Bahn |
| **A2** | **Den Satz der Tafel berichtigen** — sie darf eine Absage nur behaupten, wenn sie eine **gemessen** hat. Heute leitet sie ihn aus dem Vorkommen eines Wortes in einem fremden Absagetext ab. | eine halbe |
| **A3** | **`state`: die Absage stehen lassen und im TODO ausschreiben**, was der Deklaration fehlt (Träger, Prüfen-oder-Schreiben). *Kein Bau — null gemessener Bedarf.* | eine Zeile |
| **A4** | **`H` buchen.** Alle vier verbliebenen Absenkungspflichten hängen an Programmen, die Gabbro nicht annimmt, und jede Absage ist als richtig nachgemessen. **Entscheidung des Ordners.** | eine Entscheidung |

> **Nach A1–A4 ist der Task zu**, und was dann dasteht, ist eine Sprache mit einer Grenze, die
> man aufschreiben kann — nicht eine, deren Grenze man vermutet.

## B — Was der Task freigelegt hat, nach Gewicht

**B1 · Der Erzeuger bildet Namen, die sich treffen können.** Neun Kollisionsformen sind
geheilt, **eine zehnte findet `cc` nicht** (`lock TOR` neben `extern fn TOR_nimm()` — zwei
Deklarationen, ein Symbol, kein Wort). `N042` fängt sie; was offen bleibt, ist die
Vollständigkeit der Aufzählung über die 21 Muster.

**B2 · Fünf Adressräume verschwinden in der Absenkung.** `ctyp` liest `z.raum` für keinen.
Einer davon (`port`) ist falsch und jetzt abgewiesen; die vier anderen sind einzeln
nachgerechnet und kein Mangel. **Offen ist die Frage, ob ein Raum ohne Absenkung überhaupt im
Typ stehen soll.**

**B3 · Sieben verdeckte Giftproben**, benannt und mit Grund; fünf davon sind eine Aussage über
die Sprache (`finite` nur hinter `narrow … to`, `N027` im `can_fail` untrennbar, …).

**B4 · `N021` liest die Tore eines `check` nicht** — ungesucht gefunden, als eine Heilung eine
Datei völlig stumm machte.

**B5 · 180 unbewachte Zellen**, davon vier ohne Befehl und ohne Grund.

**B6 · Der Rumpfkanal: 66 von 76 Pflichten abgesagt**, und 60 davon haben nie eine
Übersetzung gesehen. *Die Deckungszahl ist 10 von 16 über das, was der Kanal versucht.*

## C — Was ausdrücklich NICHT in diesem Plan steht

* **Die Absenkungsentscheidung** (`messung/ABSENKUNG.md`, drei Formen) — sie gehört dem Ordner
  und ist seit dem 2026-08-28 fällig.
* **Der zweite Korpus** — gebucht als Teil des `caprock-part`-Laufs, mit seiner Bedingung.
* **Die Bezeichnerhälfte der Übersetzung** — 328 von 1058 tragen einen deutschen Stamm, und
  `mutiere-pruefer.py` trägt 383 Anker (`--anker`, 2026-09-02), die wörtliche Quellzeilen sind.

## D — Die Reihenfolge, und woran sie hängt

```
  A2  den Satz der Tafel berichtigen        sofort, haengt an nichts
  A1  drei Programme                        haengt an nichts
  A3  `state` ausschreiben                  haengt an nichts
  ------------------------------------------------------------
  A4  `H` buchen                            ENTSCHEIDUNG des Ordners
  ------------------------------------------------------------
  B1  die Aufzaehlung vollstaendig machen   haengt an nichts
  B2  Raum ohne Absenkung -- Entscheidung   haengt an B2s Messung
  B4  `N021` und die Tore                   haengt an nichts
  B5  vier Zellen ohne Grund                haengt an nichts
  B6  der Rumpfkanal                        haengt an der Absenkungsentscheidung
```

**Drei Posten hängen an nichts und schließen den Task** (A1, A2, A3). *Die vierte ist eine
Entscheidung, und sie ist die einzige, die eine Bahn nicht treffen kann.*

---

# 10. `A1` und `A2` sind eingelöst — und `A1` hat drei Befunde abgeworfen

*Gefahren am Abend des 2026-08-31, lokal (`free -g`: 31 GB gesamt, 15–17 GB verfügbar,
20 Kerne). Die Messung im Einzelnen: [`messung/QUANTORENDOMAENEN.md`](../messung/QUANTORENDOMAENEN.md),
der neue Tafelstand: `messung/GRAMMATIKTAFEL.md` §10.*

```
vorher   gesenkt 214 · abgesagt 0 · vom Pruefer 1 · UNGEDECKT 4
nachher  gesenkt 217 · abgesagt 0 · vom Pruefer 1 · UNGEDECKT 1   (nur `state`)
```

| | | Stand |
|---|---|---|
| **A1** | drei Programme — `beispiele/55-kindkette.gab`, `56-auftragsring.gab`, `57-faedenhalt.gab` | **eingelöst**, je 0 Prüferfehler, 0 `C001`, `cc -Werror` bei `-O0` und `-O2` |
| **A2** | der Satz der Tafel behauptet nur noch Gemessenes | **eingelöst**, `herkunft()` + fünfte Sprechproberichtung |
| **A3** | `state` ausschreiben | **offen** |
| **A4** | `H` buchen | **Entscheidung des Ordners** |

## Der Ertrag ist nicht die Zahl — es sind die drei Neins

**Der Auftrag verbot ausdrücklich, eine Zelle zu füllen, weil sie leer ist.** Also: erst der
Gegenstand, dann die Zusicherung, dann die Frage, ob die Domäne sie trägt. Bei zweien von
dreien lautet die Antwort nein, und *das* ist das Ergebnis:

1. **`chain(a, b)` — die beiden Feldnamen liest kein Pass.** `chain(gibtsnicht, auchnicht)`,
   `chain(belegt, belegt)` (ein `bool`, also gar keine Kante) und die vertauschte Kante
   prüfen alle mit 0 Fehlern und emittieren. `tree { child gibtsnicht }` fällt an derselben
   Datei an `D006`. *Die eine Domäne, die ihre Kante am Durchlauf nennt, ist die eine, deren
   Kante niemand prüft* — und `SYNTAX.md`:1060 begründet den Umzug der Baumkante an die
   `table` mit genau dem Argument, das auf `chain` nie zurückgefallen ist.
2. **`queue` sagt in einer Annotation nichts, was `elems of` nicht auch sagt** — das erzeugte
   C ist byteidentisch. Die Eindeutigkeitsregel des einen Feldarrays ist eine Regel des
   KOSTENPASSES und greift nur an einem `traverse`. Und was `queue` hinzufügen sollte — die
   LEBENDEN Einträge zwischen `kopf` und `zahl` — kann es nicht sagen: es nennt keines der
   beiden Felder.
3. **`threads` bindet eine Variable, die kein Pass liest.** `Domaene::Threads => {}` steht
   dreimal wortgleich (`wirkungen.rs`, `m1.rs`, `gruppe.rs`). Jede andere Domäne hängt an
   einer Deklaration (`count N`, `tree {…}`, `walk … levels`, das eine Feldarray); `threads`
   hängt an nichts, und der Erzeuger sagt genau das.

> **Keiner der drei ist hier gebaut.** Ein Programm misst den Bedarf nicht (Regel A), und
> zwei davon sind Entscheidungen über die SPRACHE. *Eine benannte Absage ist ein Ergebnis.*

## Und `A1` hätte `A2` fast unwirksam gemacht

`chain`, `queue` und `threads` senken als **Quantorendomäne** ab und werden als
**Traversierungsdomäne** namentlich abgesagt (gemessen: `messung/proben/probe-vier-zellen.gab`).
Ihre Zelle sprang auf `gesenkt` — **und vier gemessene Absagen wären hinter einer grünen Zelle
verschwunden.** Die Tafel druckt den Unterschied seither mit beiden Adressen: *`gesenkt` ist
eine Aussage über das WORT, nicht über jede Stellung, die die Grammatik ihm erlaubt.*
