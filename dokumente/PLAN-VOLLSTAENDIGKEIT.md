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
| **K** — Klempnerei | **Bleibt nach der Absenkung eine Pflicht am Menschen, die nicht seine eigene Logik ist?** Heute `H = 5` |

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
| **V2** | `match` über etwas anderem als `option index into T` | `messung/fragmente/F05.gab` |

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

`H = 5`, und alle fünf sind **dieselbe** Pflicht: *das erzeugte C rechnet, was das Fragment
sagt* — offen für F1, F3, F5, F6, F9. Für F2, F4, F7, F8, F10 ist sie **durch Ausführung**
eingelöst: erzeugt, übersetzt, ausgeführt, gegen eine Handschrift verglichen.

### K1 — Die fünf offenen auf denselben Weg bringen

Je Fragment: eine Handschrift daneben, dieselben Eingaben, Ausgaben verglichen, in
`pruefe-emission.sh` gebucht. **Das ist der billige Weg, und er ist heute schon fünfmal
gegangen.**

**Aber drei der fünf gehen so nicht**, und das ist der eigentliche Inhalt dieses Abschnitts:

* **F3 und F9 sind für den Prüfer gar keine gültigen Programme** (P2, P3 oben). *Eine
  Absenkungspflicht an einem Programm, das nicht übersetzt, ist keine offene Pflicht, sondern
  eine falsch gebuchte.* Erst P2/P3, dann K1.
* **F5** senkt nicht ab (V2 oben). Erst V, dann K.

> **Damit ist `H = 0` nicht vor `V` erreichbar**, und das ist der Grund, warum dieser Plan
> zwei Hälften hat und nicht zwei Pläne ist.

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
  P3  die Kostendomaenenschranke (K001)           gebucht als VERMUTET
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

> **Und was in diesem Durchlauf ausdrücklich NICHT steckt:** die Absenkungsentscheidung
> (`messung/ABSENKUNG.md`, drei Formen). `H = 0` ist über den AUSFÜHRUNGSweg erreichbar, den
> dieser Ordner fünfmal gegangen ist; welcher der drei Wege zum BEWEIS gegangen wird, ist eine
> Entscheidung des Ordners und keine Aufgabe einer Bahn.
