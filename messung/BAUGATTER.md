# Das Baugatter — `when` hatte keinen Leser, und das war die teuerste Stelle des Baums

*Entschieden am 2026-08-28. Jede Zahl nennt den Befehl, der sie nachrechnet.*

> **Der Befund zuerst, und er hat zwei Hälften.** Die erste ist eine Null:
>
> ```bash
> $ grep -rc 'TESTBUILD' crates/ --include='*.rs' | awk -F: '{s+=$2} END{print s}'
> 0
> ```
>
> `dokumente/SPRACHE.md` bucht `check … when TESTBUILD` **zweimal** (Zeile 1402 und 1487),
> `dokumente/BEWEIS.md` ein drittes Mal (Zeile 1057) — als **Bestand**, nicht als Plan. In
> Grammatik, Lexer, Prüfer und Erzeuger stand es nirgends.
>
> **Die zweite Hälfte ist schlimmer als die Null.** `when` war nicht abwesend, es war
> *geparst*:
>
> ```bash
> $ grep -rn '\.when' crates/ --include='*.rs' | grep -v parse.rs
> crates/gabbro-check/src/namen.rs:872:    if item.when.is_some() {
> crates/gabbro-check/src/namen.rs:876:        if f.when.is_some() {
> ```
>
> **Zwei Fundstellen im ganzen Baum, und beide schalten `N001` AB** (`Auswahl::Bedingt`).
> `SYNTAX.md` sagte dazu *„es senkt zu `#if` ab und ist konstant auswertbar"* — und
> `emit.rs` las das Feld nie: **ein Item mit `when` erzeugte genau dasselbe C wie eines
> ohne.**

*Eine Klausel, die niemand prüft, ist schlimmer als keine* — der Befund, mit dem
`beispiele/05` seine `lock BERICHT protects { … }` verloren hat (`H007`/`H008`). Hier war es
eine Klausel, die niemand **absenkt**, und das ist dieselbe Form ein Stockwerk tiefer: das
Wort stand in der Grammatik, in der Prosa und in drei Buchungen, und es tat nichts.

---

## 1. Warum das der größte Einzelposten ist — und die Zahl ist nachgerechnet

`messung/GEGENRECHNUNG.md` §8 ist der **eine** Posten der Caprock-Messung, den die
Nachrechnung ohne Abzug bestätigt. Er wurde dabei *größer*:

| | Zeilen | Anteil an 66 658 |
|---|---:|---:|
| Gerüst, Kommentar | 4 695 | 7,0 % |
| **Gerüst, Code** | **15 154** | **22,7 %** |
| **Gerüst gesamt** | **19 849** | **29,8 %** |

```bash
cd ../caprock-messbasis && python3 ../Gabbro/messung/gegenrechnung/vier-toepfe.py \
  $(find kernel/src crates/*/src programs -name '*.rs' | sort)
```

**Der Ordner bucht 15,7 %; gemessen sind 29,8 %.** Code gegen Code gestellt ist das Gerüst
so groß wie der nebenläufige Kern und die Tabellen **zusammen** (8 445 + 7 410 = 15 855) und
fast zehnmal so groß wie die 1 545 Zeilen Beweis im ganzen Baum. Und §8 sagt den Satz, um den
es hier geht:

> *Rust sagt dazu nichts, Verus sagt dazu nichts, Loom sagt dazu nichts.*

Gabbro sagte bis heute auch nichts dazu. **Ohne Baugatter existiert jede Prüfzusage im
ausgelieferten C** — nicht als Ergonomiefrage, sondern als Vertrauensfläche: der Kunde bekommt
das Messgerüst mitgeliefert und kann an keiner Stelle nachsehen, ob er es bekommen hat.

*Und die Klasse ist bekannt.* `messung/ORDNUNGSSTICHPROBE.md` Zeile 52 führt sie als **K4** —
*„die Stelle steht in Mess- und Selbsttestgerüst: in Gabbro `check … when TESTBUILD`, im
ausgelieferten C nicht vorhanden"*. Die Stichprobe hat also **gegen eine Form gezählt, die es
nicht gab.**

---

## 2. Die drei Formen, beide Seiten je Form

### (a) Ein neues Wort — `testonly check … { }`

| | |
|---|---|
| **dafür** | ein Wort, eine Aufgabe. Der Leser sieht das Gatter am Itemkopf, ohne einen reservierten Namen kennen zu müssen. Und ein Schlüsselwort kann der Lexer halten — es kann nie ein Bezeichner sein, den jemand daneben erklärt |
| **dagegen** | **der Wortschatz ist geschlossen** (218 Terminale, 218 Tabellenwörter), und ein neues Wort kostet `kw.rs`, die Tafel, `pruefe-wortschatz.py`, `tests/wortschatz.rs`, die Terminalzählung. *Und es kostet einen zweiten Namen für einen Begriff, den die Sprache schon hat:* „nur in Bau X übersetzen" ist wörtlich das, wofür `when` in der Grammatik steht — `SYNTAX.md` §1 sagt es mit diesen Worten. **Was fehlte, war kein Wort, sondern ein LESER** |
| | *Zusatzkosten, die erst beim Hinsehen auffallen:* ein eigenes Wort ist **binär**. `when` hält die Stelle für ein zweites Gatter offen, ohne ein drittes Wort zu verlangen |

### (b) `when TESTBUILD` — `when` wiederverwenden, `TESTBUILD` als **G6-Sonderform**

| | |
|---|---|
| **dafür** | **kein neues Wort.** `when` behält eine Aufgabe: *dieses Item gehört in Bau X.* Die Grammatik trägt die Form schon, der Leser nimmt sie schon an — es fehlt der Erzeuger und eine Regel. `TESTBUILD` ist ein **Bezeichner in fester Stellung**, genau die Klasse, die `SYNTAX.md` seit «G6» führt: `O` in einem `costexpr`, `Held` in einem `heldpred`. *Und die Form steht seit Monaten in drei Buchungen dieses Ordners — sie zu bauen kostet keine Umgewöhnung* |
| **dagegen** | **drei Kosten, und alle drei sind bezahlt, nicht wegerklärt.** (1) `TESTBUILD` ist ein Name, den ein Benutzer nicht mehr vergeben darf — eine unsichtbare Reservierung, solange sie niemand aufschreibt und niemand hält. **`G003` hält sie.** (2) Die Sonderformklasse wächst von **3 auf 4**, und ihr eigener Wächter zieht die Grenze bei fünf (`pruefe-wortschatz.py`: *„ab fünf verlangt die Klasse eine eigene Regel"*). Der Platz ist da, und er ist jetzt knapper. (3) **Zwei Schreibweisen:** `when` steht vor dem `item` **und** am Ende einer `fndecl`. Beide sind älter als diese Entscheidung, beide werden gelesen — der Korpus schreibt die Item-Form, weil sie bei allen 23 Item-Arten dieselbe ist |

### (c) `when` allgemein lassen — `TESTBUILD` ist eine gewöhnliche Konstante der Einheit

Also `const TESTBUILD : bool = false;` im Quelltext, und `when <constexpr>` wird zur
Übersetzungszeit ausgewertet. Das ist die Form, die `SYNTAX.md` bis heute versprach.

| | |
|---|---|
| **dafür** | kein reservierter Name, keine Sonderform, volle Allgemeinheit — die 335 `cfg`-Stellen Caprocks wären eins zu eins abbildbar. Und das Programm sagt selbst, welche Bauten es kennt |
| **dagegen** | **drei Einwände, und der erste allein trägt.** (1) **Das Gatter läge im Quelltext, nicht im Bau.** Umschalten hieße die Quelle ändern; Auslieferungsbau und Prüfbau wären zwei verschiedene Bäume. *Genau das, wogegen ein Baugatter existiert.* (2) **Eine `const` wird EMITTIERT** — `ItemArt::Konst` schreibt `#define TESTBUILD …` ins C. Der Name des Gatters stünde im ausgelieferten Erzeugnis, und ein Gatter, dessen Name im C steht, hat seinen Zweck zur Hälfte verfehlt. (3) **Zwei Einheiten könnten sich uneins sein und trotzdem binden** — der Prüfer hat keinen einheitenübergreifenden Blick auf Konstanten, und `N039` spricht über Namen, nicht über Werte. Der Binder bekäme ein halbes Gerüst |

---

## 3. Die Entscheidung: **(b)**, `when TESTBUILD`

**Der Grund ist der Begriff, nicht der Preis.** `messung/SCHLEIFENINVARIANTE.md` §3 trägt ihn
wörtlich:

> **Ein zweites Wort für einen vorhandenen Begriff ist teurer als eine zweite Fundstelle für
> ein vorhandenes Wort.** Der Wortschatz misst, wie viel eine Sprache *kann*; er soll nicht
> messen, an wie vielen Stellen sie dasselbe kann.

„Bedingte Übersetzung" ist kein neuer Begriff dieser Sprache. `when` steht dafür seit der
ersten Grammatik da, mit derselben Begründung, die dieses Dokument oben zitiert. Ein zweites
Wort hätte gesagt, `testonly` sei etwas anderes als `when` — und das ist nicht wahr.

**Und (c) fällt nicht an den Kosten, sondern an der Sache:** ein Gatter, das in der Quelle
steht, ist keine Aussage über den Bau. Der Bau steht auf der Befehlszeile, also gehört die
Bedingung dorthin, und die Sprache nennt nur *welchen* Bau sie meint.

### Die Form

```ebnf
item       = [ buildgate ] ( … ) ;
buildgate  = "when" "TESTBUILD" ;
fndecl     = … [ "section" string ] [ "arch" ident ] [ buildgate ]
             ( block | "=" pred ";" | "=" asmrumpf ";" | ";" ) ;
```

```bash
gabbro emit             datei.gab   # Auslieferungsbau -- das Gatter ist ZU
gabbro emit --testbuild datei.gab   # Pruefbau         -- das Gatter ist AUF
```

**Das geschlossene Gatter ist der Standard, und das ist eine Entscheidung.** Wer die Fahne
vergisst, verliert Prüfcode aus einem Prüfbau — ein fehlendes Symbol, laut und sofort. Der
andere Standard hätte das Gerüst ausgeliefert, und **nichts hätte es gesagt.**

---

## 4. Wo das Gatter WIRKT — und warum es nicht im Erzeuger steht

**Es ist ein Filter VOR dem Erzeuger, kein Zweig darin.** `gatter::ohne_gatter` liefert den
Baum ohne die gegatterten Items; `emit::emittiere_mit` läuft darauf.

```rust
let baum = match bau {
    Bau::Auslieferung => { gefiltert = gatter::ohne_gatter(baum); &gefiltert }
    Bau::Pruefbau     => baum,
};
```

Der Grund ist gemessen und steht in `emit.rs` selbst: der Erzeuger geht **zwanzigmal** über
die Itemliste (`grep -c 'fuer_jedes_item' crates/gabbro-check/src/emit.rs` → 23). Ein
`if item.when …` an zwanzig Stellen ist zwanzigmal die Gelegenheit, eine zu vergessen — und
eine vergessene Stelle emittiert still. *Dasselbe Argument, mit dem die Geisterlöschung in
`ist_geist` liegt und nicht an den drei Orten, die sie sonst je einzeln hätten wissen müssen.*

**Und ein Nebenertrag, der ausgesprochen gehört:** ein gegattertes Item wird im
Auslieferungsbau **nicht** gegen `C001` gehalten. Es erzeugt kein C, also ist es keine Frage
über das Erzeugnis, ob der Erzeuger es absenken könnte. Im Prüfbau ist es wieder eine, und
dort kommt die Weigerung.

---

## 5. Was das Wort NICHT fail-open lassen darf

`when` war vor heute **fail-open in Reinform**: geparst, gebucht, nirgends gelesen. Ein Gatter
zu bauen, das genau *einen* Namen versteht und jede andere Bedingung weiter stillschweigend
ignoriert, hätte das Loch nicht geschlossen, sondern verkleidet — die Klausel sähe an 335
Stellen eingelöst aus und wäre es an einer.

Darum drei Kennungen, und jede hat ihre Giftprobe:

| | | |
|---|---|---|
| **`G001`** | ungegatterter Code ruft eine gegatterte Funktion | `gift/311` |
| **`G002`** | eine `when`-Bedingung, die nicht `TESTBUILD` ist | `gift/312` |
| **`G003`** | `TESTBUILD` wird als Name erklärt | `gift/313` |

`G001` ist **die Richtung, die bricht**, und nur sie: im Auslieferungsbau gibt es den
Gerufenen nicht, der Binder findet kein Symbol, und der Bau, den das Gatter kleiner machen
sollte, kommt gar nicht mehr zustande. *Die Gegenrichtung — ein gegattertes Item ruft in den
Auslieferungsteil hinein — ist erlaubt und steht in `beispiele/52`: den Auslieferungsteil gibt
es in beiden Bauten.*

`G002` ist die Zeile, die dieses Modul davon abhält, ein neues Fail-open zu sein. **Eine Zusage
soll so breit sein wie ihre Einlösung.** Die Grammatik schreibt deshalb `buildgate` und nicht
`when constexpr`: sie soll sagen, was der Übersetzer *tut*.

---

## 6. Der Beleg — 39 Zeilen gegen 77

`beispiele/52-baugatter.gab` ist die erste Korpusstelle, die die Form schreibt: ein
Auslieferungsteil (`stand`, `ablegen`, `table Puffer`) und ein Gerüst darüber
(`hoechstmarke`, `kerne_gemessen`, `hoechstmarke_melden`, `abnahme`, `freigabe`, und ein
`check puffer_haelt`).

```bash
$ gabbro emit             beispiele/52-baugatter.gab | grep -c ''
39
$ gabbro emit --testbuild beispiele/52-baugatter.gab | grep -c ''
77
$ gabbro emit             beispiele/52-baugatter.gab \
    | grep -c 'hoechstmarke\|kerne_gemessen\|abnahme\|freigabe\|puffer_haelt'
0
$ gabbro emit --testbuild beispiele/52-baugatter.gab \
    | grep -c 'hoechstmarke\|kerne_gemessen\|abnahme\|freigabe\|puffer_haelt'
16
```

**Null gegen sechzehn.** Nicht „auskommentiert", nicht „unter `#if`" — der Name des
Messgerüsts kommt im ausgelieferten C nicht vor. Der Prüfbau trägt daneben ein
`bool pruefe_puffer_haelt(void)`, das der Auslieferungsbau nicht kennt.

`instrumente/pruefe-emission.sh` führt beide Läufe und hält sie gegeneinander; damit ist die
Aussage kein Handgriff, sondern ein Tor.

---

## 7. Was diese Entscheidung ausdrücklich NICHT kauft

**(a) Sie macht `when` nicht zur bedingten Übersetzung.** Die 335 `cfg`-Stellen Caprocks
sind damit **nicht** abgedeckt — genau eine davon ist es. `G002` sagt das im Absagetext,
statt dass eine Tabellenzeile es verspricht. *Was danach noch fehlt, ist gezählt und nicht
geschätzt.*

**(b) Sie sieht keinen indirekten Ruf.** `G001` folgt Rufen **beim Namen**. Ein
Funktionszeiger (`t->senden()`) trägt einen gegatterten Rumpf über das Gatter, und das `&f`,
das ihn dort hineingelegt hat, ist kein Ruf und wird auch nicht geprüft. *Dieselbe Grenze,
die `messung/FNPTR.md` an anderen Regeln schon führt.*

**(c) Sie sieht keine Typnennung.** Eine ungegatterte Signatur, die einen gegatterten `type`,
eine gegatterte `table` oder eine gegatterte `const` nennt, fällt hier nicht — im
Auslieferungsbau ist das ein Übersetzungsfehler statt eines Binderfehlers. Laut, aber nicht
benannt.

**(d) `N001` sieht ein gegattertes Item gar nicht.** Das steht seit dem 2026-08-21 als erstes
Loch im Satz `namen.doppelung`: *„ein `when`-Item schaltet die Doppelungsprüfung ganz ab."*
Mit dem Baugatter wird dieses Loch **benutzt** — eine gegatterte und eine ungegatterte
Funktion dürfen denselben Namen tragen, und im Auslieferungsbau ist genau eine da. Im Prüfbau
sind es zwei, und das ist eine doppelte C-Definition. **Wer das sagt, ist `cc`, nicht dieser
Pass.** *Es ist laut, nicht still — aber es ist nicht geprüft, und darum steht es hier.*

**(e) Sie sagt nichts darüber, ob das Geprüfte auch geprüft WIRD.** Ein `check`, den niemand
ruft, gattert genauso gut wie einer, den jemand ruft. Das Gatter ist eine Aussage über das
**Erzeugnis**, nicht über den Prüflauf.

**(f) Es gibt EINE Schnittstelle, und es ist die des Auslieferungsbaus.** Das ist die eine
Stelle, an der das Gatter beim Bauen selbst noch geleckt hat, und sie ist gemessen:

```bash
$ gabbro abi /tmp/abi-probe.gab        # vor der Korrektur
pub extern fn geruest_melden(v : u32) -> u32   -- das `when TESTBUILD` ist WEG
```

Der Grund war eine Spanne: der Kopf einer Funktion wird aus der `FnDecl` geschnitten, und das
`when` steht davor. Der Verbraucher hätte ein `.gabi` geladen, das ein Symbol verspricht, das
der Auslieferungsbau nicht definiert — und `emit --with` senkt genau das zu einem
**C-Prototypen** ab. *Das Gatter hätte in der Einheit gehalten und durch ihre Schnittstelle
geleckt.*

**Die Antwort ist ein Filter und keine Fahne:** ein `.gabi` nennt keinen Bau. Eine
Schnittstelle verspricht, was BINDET; ein gegattertes Item bindet nur in einem Bau, den die
Schnittstelle nicht nennen kann. *Was das nicht kauft:* eine Schnittstelle für den Prüfbau.
Das Prüfgerüst eines Verbrauchers kann einen gegatterten Helfer einer Bibliothek nicht rufen.

---

## 8. Der Preis in Zahlen

| | vorher | nachher |
|---|---:|---:|
| Wortschatzwörter | 218 | **218** |
| EBNF-Terminale | 218 | **218** |
| G6-Sonderformen (Grenze 5) | 3 | **4** |
| EBNF-Regeln | 152 | 153 |
| Kennungen | 225 | 228 |
| Giftproben | 285 | 288 |
| Sätze im Passregister | — | +1 (`namen.baugatter`) |

**Null Wortschatzzuwachs, eine Sonderform, drei Kennungen.** Der Buchstabe `G` war frei; die
Regel liegt in einer eigenen Datei (`crates/gabbro-check/src/gatter.rs`), weil
`pruefe-kennungen.py` die Datei als die Regel führt.
