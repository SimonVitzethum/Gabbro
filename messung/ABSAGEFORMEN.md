# Die Absageformen des Erzeugers — 139 Stellen, 130 Formen, drei Mengen

*Gemessen am 2026-08-31 mit `./instrumente/zaehle-absagen.py --korpus`, Bahn V, Schritt V-1
des `dokumente/PLAN-VOLLSTAENDIGKEIT.md`. **Nachgemessen nach V-3 und V-4 desselben Tages** —
die Zahlen unten sind der Stand NACH den zwei Entscheidungen.*

> **Die Frage, wörtlich:** für jedes Programm, das der Prüfer annimmt, erzeugt der Erzeuger C.
> Gleichbedeutend: **`C001` ist für ein angenommenes Programm UNERREICHBAR.** Diese Tafel
> zählt die Stellen, an denen `C001` entsteht, und fragt je Stelle, ob der Prüfer dieselbe
> Form schon vorher abweist.

---

## 0. Die Zahlen des Plans waren zweimal falsch, und hier steht die dritte

| Zahl | woher | was sie zählte |
|---|---|---|
| ~~22~~ | `grep -c C001 emit.rs` | **die Kommentare mit.** Um den Faktor sechs zu klein |
| ~~136 / 127~~ | `grep -c 'weigere('` | **die Definition mit** — und die Formen hinter einer Fallunterscheidung als eine |
| **135 / 139 / 130** | `zaehle-absagen.py` | 135 Aufrufe · davon 134 mit eigenem Text und **einer hinter einem `match` mit fünf Textzweigen** → **139 Absagestellen, 130 verschiedene Formen** |

Der `match` steht in `emit.rs` (`let grund = match &x.domaene`): fünf Domänen, die absagen
(`queue`, `mappings of`, `chain in`, `fields of`, `threads`), und zwei, die absenken. *Eine
Weigerung hinter einer Fallunterscheidung ist so viele Formen, wie die Unterscheidung
Textzweige hat* — wer den Aufruf zählt, zählt fünf Formen als eine.

**Die Zahl steht jetzt in einem Werkzeug und nicht in einem Satz.** Sie kann nicht mehr
veralten, ohne dass es jemand sieht.

---

## 1. Wie gemessen wird — und warum ein Lauf beide Hälften gibt

`gabbro emit` ruft `emittiere_mit` **auch dann**, wenn der Prüfer Fehler gefunden hat
(`main.rs`:667–669). Ein Lauf über eine Datei liefert damit in derselben Ausgabe

* die **Prüferkennungen** (`N011`, `M124`, `S001`, …) und
* die **`C001`-Texte** des Erzeugers.

Daraus folgt das Urteil je Datei mechanisch:

```
0 Pruefer-Fehler  +  mindestens ein C001   ->  UNGEDECKT, und es ist ein PROGRAMM, kein Argument
n Pruefer-Fehler  +  mindestens ein C001   ->  gesehen, aber die Deckung ist NICHT gezeigt
kein C001 in 418 Dateien                   ->  ungemessen -- und das ist keine Auskunft
```

> **Die mittlere Zeile ist die, an der man sich betrügen kann.** Dass in derselben Datei ein
> Prüferfehler steht, heißt nicht, dass er *dieselbe Form* trifft.
> `beispiele/gift/94-long-double.gab` fällt bei `F006` und der Erzeuger sagt `parameter type`
> ab — dort ist es dieselbe Form. `beispiele/gift/342-stilllegung-andere-marke.gab` fällt bei
> `O011` und der Erzeuger sagt ebenfalls `parameter type` — dort ist es **eine andere**. *Die
> Spalte trägt darum die Datei und ihre Kennungen mit, damit jede Zeile einzeln nachrechenbar
> bleibt.*

---

## 2. Das Ergebnis: 15 · 24 · 91

```
418 .gab-Dateien gefahren, 92 davon ohne einen Pruefer-Fehler

 15 FORMEN gemessen UNGEDECKT      der Pruefer nimmt an, der Erzeuger sagt ab
 24 FORMEN nur neben einem Fehler  gesehen, Deckung nicht gezeigt
 91 FORMEN vom Korpus nie erreicht ungemessen -- Falle 80, und sie gilt hier voll
```

**Ungemessen ist nicht gedeckt.** Der Korpus ist von der Sprache nach außen geschrieben; sein
Schweigen über eine Form ist eine Aussage über den Korpus und keine über die Sprache. Die
91 stehen darum als eigene Menge und nicht als grüner Rest.

> **Die Zahl stand am Morgen des 2026-08-31 auf 11 und steht am Abend auf 15 — und der Baum
> ist nicht schlechter geworden, die MESSUNG ist schärfer geworden.** Zwei Zellen sind
> geschlossen (`breaking`, `match` über einem `tagged type`), eine ist **umbenannt** worden,
> weil ihr Text das Falsche sagte, und **fünf sind neu, weil eine W24-Probe sie überhaupt
> erst erreichbar gemacht hat**: `let` ohne auflösbaren Typ (U11) und die vier Formen, die
> `pruefe-grammatiktafel.py` aus der Grammatik heraus benannt hat (U12–U15).
>
> *Eine Zahl, die steigt, weil jemand hingesehen hat, ist kein Rückschritt* — aber sie ist
> auch kein Fortschritt, und beides zu unterscheiden ist der Grund, warum diese Tafel
> Adressen führt und nicht nur eine Zahl.

### 2.1 Die fünfzehn gemessenen `UNGEDECKT`-Zellen

| # | Form | wo | Anmerkung |
|---|---|---|---|
| U1 | `retry` without `until` | `beispiele/gift/166-wachhund-nennt-nichts.gab` | Probe erwartet **`Hinweis S007`** — ein Hinweis ist kein Fehler, also nimmt der Prüfer an |
| U2 | `exchange update(v) { … }` ohne `bounded … ops on_exceeded …` | `beispiele/gift/194-…` | Probe erwartet `C001` |
| U3 | ein Bitwort eines `format` ohne Ganzzahlfeld | `beispiele/gift/197-…` | Probe erwartet `C001` |
| U4 | Bitfeld eines Registers, das nicht `class rw` ist | `beispiele/gift/215-…` | Probe erwartet `C001` |
| U5 | `old(place)` außerhalb eines Vergleichstauschs | `beispiele/gift/220-…` | Probe erwartet `C001` |
| U6 | `in a .. b` an einem `reserved`-Feld | `beispiele/gift/291-…` | Probe erwartet `C001` |
| U7 | `in a .. b` zusammen mit `scale` | `beispiele/gift/292-…` | Probe erwartet `C001` |
| U8 | `transition`-Ziel, das keine Menge von Feldnamen ist | `beispiele/gift/294-…` | Probe erwartet `C001` |
| U9 | `ops relabel` an einer Tabelle ohne `parent`-Kante | `beispiele/gift/333-…` | Probe erwartet `C001` |
| U10 | `match` über einen Ruf, den diese Einheit nicht deklariert | `messung/fragmente/F05.gab` | **war U2 des Plans und ist NICHT dieselbe Form** — siehe `ZWEI-ABSAGEN.md`. **2026-08-31 ausgemessen: die Absage ist EINE Ergänzung weit von zu** (fünf `extern fn`, gemessen: 0 Fehler, 0 Hinweise, 199 Zeilen C) — *sie wurde nicht angewandt, siehe den Kasten unten* |
| U11 | `let` ohne auflösbaren Typ | `messung/proben/probe-unbekannter-ruf.gab` | **neu gemessen am 2026-08-31** — sie stand vorher unter „nur neben einem Fehler" |
| U12 | `state` | `messung/proben/probe-vier-zellen.gab` | aus der GRAMMATIK gefunden — siehe `GRAMMATIKTAFEL.md` |
| U13 | `queue` | `messung/proben/probe-vier-zellen.gab` | dito |
| U14 | `chain in` | `messung/proben/probe-vier-zellen.gab` | dito |
| U15 | `threads` | `messung/proben/probe-vier-zellen.gab` | dito |

**U12–U15 sind der Ertrag von V-2, und sie waren beinahe ein Werkzeugbefund.**
`pruefe-grammatiktafel.py` schloss aus dem Schweigen der Prüferfehlertexte, dass der Prüfer
sie annimmt — *ein Schluss aus einem Text ist keine Messung* (W16). Nachgemessen:

```
mit Kostenzusage    K003 faellt: „die Domaene `queue` … hat keine Schranke aus der Deklaration"
ohne Kostenzusage   0 Fehler, und erst der Erzeuger sagt ab
```

Die Meldung baut den Domänennamen mit `format!` aus einer Variablen — darum stand `queue`
in keinem Literal, und die Textlesung sah ihn nicht. **Die Vergröberung ging in die sichere
Richtung** (sie meldete zu viel), und die Messung hat das Urteil bestätigt: in einem
`divergent fn` ohne Kostenzusage prüfen alle vier mit **0 Fehlern** und fallen an vier
`C001`.

> **Damit haben U10 bis U15 dieselbe Wurzel wie U11.** `K003` ist die einzige Regel, die
> zwischen den Absagen des Erzeugers und dem Prüfer steht — *und sie hängt an einer
> Kostenzusage, die ein `divergent fn` nicht trägt.*
>
> **Die Wurzel ist am 2026-08-31 ausgerechnet: [`messung/K003-TOR.md`](K003-TOR.md).** Das Tor
> ist EINE Zeile (`kosten.rs`:296), `K003` greift bei einem `divergent fn` MIT Zusage tadellos
> (gemessen, in beide Richtungen), und drei Formen einer torlosen Regel kosten über die 418
> Dateien **9 · 4 · 2** Programme, die heute durchgehen. *Keine einzelne schließt alle sechs;
> `state` erreicht gar keine.*

> **Neun der ersten elf sind Giftproben, die `C001` ERWARTEN** — der Ordner hat für sie schon
> entschieden, dass der Erzeuger der Absager ist. **Das macht sie nicht zu gedeckten Zellen.**
> Der Plan kennt für eine `UNGEDECKT`-Zelle zwei volle Ausgänge, absenken oder *im Prüfer*
> absagen, und „der Erzeuger sagt es benannt" ist keiner von beiden: die Eigenschaft, um die
> es geht, lautet **Prüfer nimmt an ⇒ es gibt C**. *Eine benannte Absage ist ein Ergebnis;
> sie ist nur nicht dieses Ergebnis.*
>
> Der Weg für alle neun ist derselbe und billig: die Regel wandert in einen Prüferpass, die
> Probe erwartet dessen Kennung statt `C001`, und die Zelle steht auf `vom Pruefer`. **Er
> gehört Bahn P** und ist hier als Arbeitsmenge gebucht, nicht als erledigt.

> ### U10 ist ausgemessen, und die Antwort ist eine Ergänzung — die trotzdem nicht dasteht
>
> **Gemessen am 2026-08-31.** `F05`s Dienstrumpf ruft fünf Namen, die die Datei nicht nennt:
> `decode_op`, `request_flush`, `serve_rw`, `serve_scan`, `bump_served`. Fünf `extern fn`-Zeilen
> — Name und Stelligkeit stehen an der Rufstelle, der Rückgabetyp folgt aus der Verwendung
> (`capacity = r` bei `capacity : u32`), und `tagged type Op` steht schon im eingefrorenen
> Ausschnitt (`FRAGMENTE.md`:950). **Das ist eine Ergänzung und keine Erfindung**, dieselbe
> Runde wie die sieben, die die Datei am 2026-08-15 bekam. Ergebnis:
>
> ```
> 31 Items, 0 Fehler, 0 Hinweise      und `gabbro emit` schreibt 199 Zeilen C
> ```
>
> **Der `C001` verschwindet, und er hatte recht** — sein Satz seit dem 2026-08-31 nennt die
> Heilung selbst: *„A call whose return type IS a `tagged type` lowers."*
>
> **Sie steht trotzdem nicht im Baum, und der Grund ist gemessen:** `cc -Werror` nimmt die 199
> Zeilen nicht an, und der erste der drei Gründe ist eine Wand aus dem eingefrorenen Text:
>
> ```
> error: conflicting types for built-in function 'exit'; expected 'void(int)'
>    97 | _Noreturn void exit(void);
> ```
>
> **`exit()` steht im Ausschnitt**, und C hat den Namen vergeben. Das ist weder eine Ergänzung
> noch eine Erfindung — *es ist eine Namenskollision mit der Zielsprache, und Gabbro hat keine
> Regel dagegen.* Die anderen zwei (`m->op` auf einem Skalar, eine ungenutzte `let`-Bindung)
> stehen mit ihr im `TODO.md`.
>
> **Damit hätte die Ergänzung `pruefe-emission.sh` Stufe 9 rot gefärbt** — *jede Datei, die
> emittiert, muss auch übersetzen* —, und die Ausnahmeliste dieser Stufe ist seit dem
> 2026-08-20 LEER. *Eine Zelle zu schließen, indem man die erste Ausnahme seit elf Tagen
> einträgt, ist kein Tausch, den eine Bahn allein macht.* Die Zeilen sind gemessen, der Preis
> ist benannt, und beides steht hier statt im Diff.
>
> ### NACHGETRAGEN am 2026-08-31: der Preis ist weg, und die Zelle bleibt trotzdem offen
>
> **`N041` ist gebaut** (`messung/C-NAMEN.md`): der PRÜFER weist jetzt einen Namen ab, den C
> schon vergeben hat — 558 Namen in drei gemessenen Klassen, drei Giftproben, eine
> Gegenprobe, eine Mutation. **Damit emittiert `F05` gar nicht mehr**, und Stufe 9 hat nichts
> zu beanstanden: die leere Ausnahmeliste bleibt leer. *Der Preis, der die vorige Bahn
> umkehren ließ, existiert nicht mehr.*
>
> **Nur senkt `F05` damit auch nicht ab, und diesmal ist die Wand vermessen statt geschätzt**
> (`messung/F05-UNERREICHBAR.md`): `exit` steht **neunmal** im eingefrorenen Block —
> die Deklaration bei `FRAGMENTE.md`:1028 und acht Rufstellen —, der
> `verlorene_zeilen`-Riegel macht jede Umbenennung zu neun Weglassungen, und **die Stelligkeit
> stimmt ohnehin nicht**: C führt `void exit(int)`, der Ausschnitt ruft `exit()`.
>
> *Die Zelle `U10` ist damit nicht mehr `UNGEDECKT` an einer `match`-Form — sie ist `vom
> Pruefer`, an einem Namen.* Und `H` bleibt bei 4, mit einer Kennung statt einer Vermutung.

**U10 und U11 haben eine gemeinsame Wurzel, und sie ist gemessen** (`messung/proben/`):

```
mit Kostenzusage    `K003` faellt: „`f` promises costs, but X is not declared here"
ohne Kostenzusage   nur `E009`, ein HINWEIS -- und der Pruefer nimmt an
```

Ein `divergent fn` trägt keine Kostenzusage, an der `K003` hängen könnte. **Damit gibt es
genau eine Stelle, an der ein unbekannter Name durch den Prüfer kommt** — und beide Zellen
fallen zusammen mit ihr. *Der Befund gehört dem Prüfer, nicht dem Erzeuger.*

### 2.2 Die 24 nur neben einem Prüferfehler gesehenen

Je Form die Datei und ihre Prüferkennungen. **Wo die Kennung dieselbe Form trifft, ist die
Zelle `vom Pruefer`; wo nicht, ist sie ungeklärt und keine der beiden.**

| Form | Datei `Kennungen` | trifft dieselbe Form? |
|---|---|---|
| `leave`/`next` ohne umschließende Schleife | `210-marke-ausserhalb-jeder-schleife` `S001` | **ja** — `S001` ist genau diese Regel |
| `match` über `tagged` nicht erschöpfend | `159-match-nicht-erschoepfend` `D005` | **ja** |
| zwei Bitlagen überlappen | `106-bitlage-ueberlappt` `N008` | **ja** |
| Bitlage jenseits der Wortbreite | `105-bitlage-jenseits-des-wortes` `N007`, `122-embeds-…` `N013` | **ja** |
| `bit {hi}` jenseits der Registerbreite | `107-registerbit-jenseits` `N007` | **ja** |
| `return <reason>` ohne `or <reason>` | `232-grund-ohne-deklaration` `M126`, `234-grund-ohne-kanal` `M122` | **ja** |
| `let … else` über eine Funktion ohne `or <reason>` | `192-let-else-ohne-fehlerkanal` `N028`, `25-…` `N028` | **ja** |
| `parameter type` | `94-long-double` `F006,N040` | **ja** an dieser Datei; `342-…` `O011` ist eine ANDERE Form |
| `return type` | `104/108/112-…` je `N040` | **ja** — `N040` ist der unauflösbare Name |
| `field type` | `119-geist-im-speicher` `N011` | **ja** — ein Geist hat keine Darstellung |
| `static` eines unauflösbaren Typs | `206-geist-als-static` `N011` | **ja** |
| `static` mit nicht-konstantem Initialisierer | `229-tippfehler-unter-der-negation` `M109,M111` | **ungeklärt** — die Kennungen sind Bereichsregeln |
| `state` | `135-state-doppelte-transition` `N001` | **ungeklärt** — `N001` ist der Doppeleintrag, nicht die Form |
| Lücke zwischen den Bitlagen eines Wortes | `130-walk-doppelte-invariante` `N001` | **ungeklärt** — dieselbe Bauart |
| `bounded … ops` ohne feste Durchgangskosten | `136-retry-rumpf-ueber-schranke` `K006` | **ungeklärt** — `K006` ist die Schranke, nicht die Form |
| `on_exceeded` muss `never` liefern | `10-marke-fehlt` `S001`, `182-…` `L108,S003` | **ungeklärt** |
| `ancestors of` über Tabelle ohne `parent` | `69-vorfahren-ohne-schranke` `K003` | **ungeklärt** |
| `table` ohne `count` | `69-vorfahren-ohne-schranke` `K003` | **ungeklärt** |
| `descendants of` ohne `tree` | `195-descendants-ohne-tree` `S008` | **ungeklärt** |
| `descendants of` braucht alle drei Kanten | `196-descendants-nur-mit-elter` `S008` | **ungeklärt** |
| `device … at dma` ohne `assume` | `401/402-registerklasse-…` `R006` | **ungeklärt** |
| `device … at normal` | `messung/fragmente/F09.gab` `K001` | **ungeklärt** — `K001` ist die Kostenexplosion |
| `mappings of` | `messung/fragmente/F09.gab` `K001` | **ungeklärt** |
| `walk … levels` keine Zahl | `messung/fragmente/F09.gab` `K001` | **ungeklärt** |
| `queue` | `messung/fragmente/F03.gab` `H011,M101,M124,N035,N040` | **ungeklärt** |
| unäres Minus | `219-unaeres-minus` `M101` | **ungeklärt** — `M101` ist die Bereichsregel |

**Elf `ja`, dreizehn ungeklärt.** *`queue` und `chain in` standen bis heute Abend hier und
sind heraus: die Messung von §2.1 hat sie als U13/U14 entschieden.* Die dreizehn sind keine
`UNGEDECKT`-Zellen und keine gedeckten: sie sind **nicht gemessen**, weil kein Programm sie ohne einen fremden Fehler
danebengestellt hat. *Jede einzelne braucht dasselbe wie U10 und U11: das kleinste Programm,
das nur sie enthält, durch den unveränderten Prüfer.* Wie das aussieht, steht in
`messung/proben/`.

### 2.3 Die 91 vom Korpus nie erreichten

Sie stehen vollständig in §5. **Gruppiert nach dem, was sie absagen**, um zu zeigen, wo die
Arbeit liegt:

| Gruppe | Zahl | Bemerkung |
|---|---|---|
| `bank` — Basis, Schrittweite, Register | 7 | eine geschlossene Familie über einer Geräteerklärung |
| `transition` / `transset` / `mirrors` | 8 | dieselbe Familie, eine Ebene weiter |
| `format` — Endianness, Feldtyp, `where`, `scale`, Bitwort | 9 | |
| `walk` — `levels`, `node`, Prädikate | 7 | |
| `ancestors of` / `descendants of` / `by consuming` | 8 | Domänen einer Traversierung |
| `let … else` — Ort, indirekter Ruf, unauflösbarer Typ | 4 | |
| `atomic` / `publishes` / `awaits` / `exchange` / `when` | 8 | |
| `static`-Feld als Reihung | 4 | |
| `option` / `Some` / `None` / `match` über Option | 5 | |
| Architektur ≠ x86_64 (`entry`, `entrust`, `boot`) | 3 | **`aarch64` ist versiegelt** — die Absage IST die Entscheidung |
| Rest (Typauflösung, `asm`, `ops`, `result`, `sizeof`, …) | 30 | |

---

## 3. Was V-3 entschieden hat

`messung/ZWEI-ABSAGEN.md` — die beiden Zellen des Plans, jede mit `W24`-Vorlauf, **beide
durch ABSENKEN**:

* `breaking I { … }` senkt ab und trägt seine Region als Kommentar ins C; die
  Erhaltungspflicht steht in `gabbro pflichten` und stand dort schon.
* `match` über einem Ruf, dessen erklärter Rückgabetyp ein `tagged type` ist, senkt ab — mit
  **einmaliger** Auswertung des Gegenstands.

Was an `F05` übrig bleibt, hat seit heute seinen eigenen Satz und ist U10.

---

## 4. Was diese Tafel NICHT sagt

1. **Sie sagt nichts über die Richtigkeit einer Absenkung.** Eine Form, die absinkt, kann
   falsches C erzeugen; `messung/fragmente/F06.gab` emittierte 161 Zeilen, die `cc -Werror`
   zurückwies. Das ist eine `UNGEDECKT`-Zelle *der anderen Art*, und sie steht in
   `messung/UEBERSETZUNGSREICHWEITE.md`.
2. **Sie ist über den Korpus gemessen, nicht über die Grammatik.** Die 91 ungemessenen sind
   der Beweis, dass ein Korpus die Frage nicht beantwortet. Die Tafel aus der Grammatik ist
   V-2 (`messung/GRAMMATIKTAFEL.md`).
3. **Ein `ja` in §2.2 ist ein gelesener Zusammenhang und keine Messung.** Es steht in der
   Spalte, damit jemand es widerlegen kann.

---

## 5. Die vollständige Tafel — 139 Stellen

*Erzeugt aus `emit.rs`. `(wdh.)` heißt: dieselbe Form an einer zweiten Stelle.*

| Zeile | Form | Zustand | wo gemessen |
|---|---|---|---|
| `1423` | const with a non-constant value | ungemessen |  |
| `1554` | `static` of a `tagged` type or a record initialised with a plain number -- which variant the zero is, the declaration does not say, and a record ha… | ungemessen |  |
| `1564` | `static` of an unresolvable type | mit Fehler | beispiele/gift/206-geist-als-static.gab `N011` |
| `1596` | `static` with a non-constant initialiser | mit Fehler | beispiele/gift/229-tippfehler-unter-der-negation.gab `M109,M111` |
| `1660` | `accumulates` of an unresolvable type | ungemessen |  |
| `1664` | `accumulates` without `per cpu <constexpr>` -- the lowering is one cell per core, and how many cores there are is not in the declaration | ungemessen |  |
| `1747` | `atomic` of an unresolvable type | ungemessen |  |
| `1795` | `atomic` of an unresolvable type | ungemessen (wdh.) |  |
| `1797` | `atomic` with a payload but no ordering -- a payload without an ordering is a publication nobody can pair | ungemessen |  |
| `1940` | `state` -- the transitions are a proof device over a carrier that is declared ELSEWHERE; which C object holds the state, and whether a transition i… | UNGEDECKT | messung/proben/probe-vier-zellen.gab |
| `2077` | a `type` record carries no bit position and no `offset_into` -- those are statements about a layout, and a `format` makes them | ungemessen |  |
| `2091` | array field type -- element or length | ungemessen |  |
| `2106` | function pointer field type | ungemessen |  |
| `2112` | field type | mit Fehler | beispiele/gift/119-geist-im-speicher.gab `N011` |
| `2176` | `tagged` variant payload type | ungemessen |  |
| `2193` | table without `count` -- the array would have no size | mit Fehler | beispiele/gift/69-vorfahren-ohne-schranke.gab `K003` |
| `2207` | field type | mit Fehler (wdh.) | beispiele/gift/119-geist-im-speicher.gab `N011` |
| `2244` | `count {n}` fills the index word: the `option` sentinel would be `2^32`, which collides with slot 0 -- see beweise/Option_Sonderwert.thy, M-1 | ungemessen |  |
| `2252` | `count` does not resolve to a number, so the `option` sentinel cannot be checked against the index word | ungemessen |  |
| `2420` | `ops relabel` on a table whose `tree` names no `parent` edge -- there is no field to re-hang. `umhaengen_erhaelt` is a statement about the parent c… | UNGEDECKT | beispiele/gift/333-ops-relabel-ohne-elternkante.gab |
| `2428` | `ops {other}` -- no generated meaning for this word | ungemessen |  |
| `2487` | `device … at normal` -- an access into the ordinary space is not a device access, and what a `device` block would mean there is not decided | mit Fehler | messung/fragmente/F09.gab `K001` |
| `2496` | `device … at dma` without `assume {ANNAHME_DMA}` -- which barrier a DMA access needs is a statement about the MEMORY MODEL, and this generator does… | ungemessen |  |
| `2520` | bit {hi} lies outside the declared register width of {breite} | ungemessen |  |
| `2571` | `bank` with a non-constant `stride` or `count` | ungemessen |  |
| `2584` | `bank` register at a non-constant offset | ungemessen |  |
| `2637` | `bank` base over a place that is not `REGISTER.field` of this device | ungemessen |  |
| `2645` | `bank` base over a register this device does not declare | ungemessen |  |
| `2650` | `bank` base over a field this register does not declare | ungemessen |  |
| `2659` | `bank` base over a place that is not `REGISTER.field` of this device -- the address has to be computable from this device's own register block | ungemessen |  |
| `2685` | `bank` base expression form -- only a number, a parenthesis, a binary operation and `REGISTER.field` of this device lower to an address | ungemessen |  |
| `2789` | `transition` without a step | ungemessen |  |
| `2794` | `transset` across two different registers -- there is no single write that hits both, and that is «B17» one level up | ungemessen |  |
| `2805` | `transition` on something that is not a register | ungemessen |  |
| `2848` | `mirrors` from a register this device does not declare | ungemessen |  |
| `2872` | `transition` on an unknown register field | ungemessen |  |
| `2876` | `transition` on a multi-bit field | ungemessen |  |
| `2912` | `transition` target that is not a set of field names | UNGEDECKT | beispiele/gift/294-ganzwort-zug-nennt-keinen-feldnamen.gab |
| `2922` | `transition` on an indexed place -- a step names ONE bit of ONE register, and which register an index picks is a run time question | ungemessen |  |
| `2943` | `transition` through a pointer (`->`) -- a step names a field of THIS device's register block, and the block is reached through `d->basis`, not thr… | ungemessen |  |
| `2998` | `format` without `endian` -- the byte order is the point | ungemessen |  |
| `3048` | `format` field type | ungemessen |  |
| `3074` | `in a .. b` at a `reserved` field -- a reserved field has no reader, so there is no place at which the bound could be established | UNGEDECKT | beispiele/gift/291-formatbereich-an-reserviertem-feld.gab |
| `3103` | `where` clause form in a `format` | ungemessen |  |
| `3149` | a bit word of a `format` takes its width from an integer field, and this group names none -- a `bool @N` says which BIT, never which WORD | UNGEDECKT | beispiele/gift/197-bitgruppe-ohne-ganzzahlfeld.gab |
| `3173` | a `bool` over more than one bit -- a truth value has one bit, and which of several it would be is not a question with an answer | ungemessen |  |
| `3185` | `format` bit field type | ungemessen |  |
| `3190` | bit position beyond the word width -- «B24» is decided: a position lies inside the field's OWN word, and beyond it there is nothing to mean | mit Fehler | beispiele/gift/105-bitlage-jenseits-des-wortes.gab `N007` · beispiele/gift/122-embeds-jenseits-des-wortes.gab `N013` |
| `3204` | two bit positions overlap -- a word says which bits exist, and twice is not an answer | mit Fehler | beispiele/gift/106-bitlage-ueberlappt.gab `N008` |
| `3230` | the bit positions of this word leave a gap -- name it `reserved`; a format says which bits EXIST, and the emitter does not count along | mit Fehler | beispiele/gift/130-walk-doppelte-invariante.gab `N001` |
| `3241` | `in a .. b` at a `reserved` field -- a reserved field has no reader, so there is no place at which the bound could be established | UNGEDECKT (wdh.) | beispiele/gift/291-formatbereich-an-reserviertem-feld.gab |
| `3269` | `scale` that is not a constant | ungemessen |  |
| `3310` | `in a .. b` together with `scale` -- the reader hands out the SCALED value, and which of the two the bound speaks about is not said | UNGEDECKT | beispiele/gift/292-formatbereich-mit-skalierung.gab |
| `3341` | `where` clause form in a `format` | ungemessen (wdh.) |  |
| `3587` | a `where` clause of a `format` names FIELDS of that format -- a place with `.`, `->` or `[…]` names something the generated accessor has no object for | ungemessen |  |
| `3643` | table length | ungemessen |  |
| `4364` | return type | mit Fehler | beispiele/gift/104-ensures-index-tippfehler.gab `M109,N040` · beispiele/gift/108-maintains-ins-leere.gab `M112,N040` |
| `4384` | parameter type | mit Fehler | beispiele/gift/342-stilllegung-andere-marke.gab `O011` · beispiele/gift/94-long-double.gab `F006,N040` |
| `4415` | return type | mit Fehler (wdh.) | beispiele/gift/104-ensures-index-tippfehler.gab `M109,N040` · beispiele/gift/108-maintains-ins-leere.gab `M112,N040` |
| `4477` | `asm` body returns a value but names no `out { result : … }` | ungemessen |  |
| `4850` | `return <reason>` in a function that declares no `or <reason>` | mit Fehler | beispiele/gift/232-grund-ohne-deklaration.gab `M126` · beispiele/gift/234-grund-ohne-kanal.gab `M122` |
| `4892` | `return <reason>` in a function that declares no `or <reason>` | mit Fehler (wdh.) | beispiele/gift/232-grund-ohne-deklaration.gab `M126` · beispiele/gift/234-grund-ohne-kanal.gab `M122` |
| `4975` | a `format` field followed by more suffixes | ungemessen |  |
| `4982` | a compound assignment to a `format` field -- it would be a read and a write through two separate calls, and over a buffer a device also writes, whe… | ungemessen |  |
| `5042` | a compound assignment to a bank register -- it would be two accesses to a place the device also writes | ungemessen |  |
| `5076` | a bit field of a register that is not `class rw` -- writing one bit means reading the word first, and this register does not give a reading. That i… | UNGEDECKT | beispiele/gift/215-bitfeld-links-vom-gleich.gab |
| `5087` | a compound assignment to a register bit field -- it would be two accesses to a place the device also writes | ungemessen |  |
| `5197` | `let` without a resolvable type | UNGEDECKT | messung/proben/probe-unbekannter-ruf.gab |
| `5220` | `publishes` on something that is not an atomic | ungemessen |  |
| `5236` | `awaits` on something that is not an atomic | ungemessen |  |
| `5295` | `exchange` on something that is not a declared `atomic` -- without a declaration there is no memory ordering, and choosing one would mean inventing it | ungemessen |  |
| `5325` | `exchange update(v) { … }` without `bounded … ops on_exceeded …` -- SPRACHE.md lowers it to a BOUNDED CAS loop, and an unbounded one is exactly wha… | UNGEDECKT | beispiele/gift/194-cas-schleife-ohne-schranke.gab |
| `5336` | `on_exceeded` must name a function returning `never` -- a bound whose exit returns would let the loop run on, and then the bound is a number withou… | ungemessen |  |
| `5424` | `when` comparison that is not `old(X) == <expr>` -- a compare-exchange swaps on EQUALITY with one expected value; an ordering or a bit test would h… | ungemessen |  |
| `5445` | `when` condition that is not a comparison -- a compare-exchange carries ONE expected value into the instruction, and a conjunction, a quantifier or… | ungemessen |  |
| `5534` | `leave`/`next` naming no enclosing loop | mit Fehler | beispiele/gift/210-marke-ausserhalb-jeder-schleife.gab `S001` |
| `5584` | `let … else` over a PLACE -- «B14b» opened the form for an option-valued place, and there the failure is `None`, which carries no reason for `e` to… | ungemessen |  |
| `5605` | `let … else` over an INDIRECT call -- a `fn(…)` type carries a contract but no `or R` error channel, so nothing binds `e` | ungemessen |  |
| `5614` | `let … else` over a call this unit does not declare | ungemessen |  |
| `5620` | `let … else` over a function that declares no `or <reason>` -- the `else` branch could never run, and `e` would name nothing | mit Fehler | beispiele/gift/187-can-fail-schreibt.gab `M104,M119,N021,N027,N028` · beispiele/gift/192-let-else-ohne-fehlerkanal.gab `N028` |
| `5648` | `let … else` whose call has no resolvable type | ungemessen |  |
| `5764` | `retry` without `until` -- nothing bounds the condition | UNGEDECKT | beispiele/gift/166-wachhund-nennt-nichts.gab |
| `5768` | `until` predicate form | ungemessen |  |
| `5772` | `bounded … ops` -- the per-pass cost is not fixed, so the budget yields no iteration count | mit Fehler | beispiele/gift/136-retry-rumpf-ueber-schranke.gab `K006` · beispiele/gift/188-schritt-in-locks-in-schleife.gab `K002,K006,L107,L108,O006,S003` |
| `5782` | `on_exceeded` must name a function returning `never` -- a `reason` value would need an error-return convention, and that is not decided | mit Fehler | beispiele/gift/10-marke-fehlt.gab `S001` · beispiele/gift/182-verbrauch-in-der-schleife.gab `L108,S003` |
| `5826` | `static` array over an unresolvable element type | ungemessen |  |
| `5836` | `static` array whose length is not constant | ungemessen |  |
| `5840` | `static` array of length zero -- C has no such object | ungemessen |  |
| `5844` | `static` array with a non-constant initialiser | ungemessen |  |
| `5906` | `on_exceeded` must name a function returning `never` -- a `reason` value would need an error-return convention, and that is not decided | mit Fehler (wdh.) | beispiele/gift/10-marke-fehlt.gab `S001` · beispiele/gift/182-verbrauch-in-der-schleife.gab `L108,S003` |
| `6052` | statement in an `update` body -- it computes old -> new and is PURE; only `return <expr>` and `if <expr> { … }` say that | ungemessen |  |
| `6175` | `ancestors of … by consuming` -- consuming your ancestors while walking up them is a different program, and the grammar does not say which | ungemessen |  |
| `6184` | `ancestors of` over a place that names no table | ungemessen |  |
| `6188` | `ancestors of` over a table whose `tree` names no `parent` edge -- «B41b»: the edge stands at the table, and a missing one is an ANSWER, not a gap | mit Fehler | beispiele/gift/69-vorfahren-ohne-schranke.gab `K003` |
| `6197` | `ancestors of` over a table without `count` -- no sentinel | ungemessen |  |
| `6262` | `descendants of … by decreasing` -- a measure over a tree walk is not decided: which of the two orders it constrains is not written anywhere | ungemessen |  |
| `6272` | `descendants of` over a place that names no table | ungemessen |  |
| `6276` | `descendants of` over a table with no `tree` -- «B41b»: the edge stands at the table, and this one names none | mit Fehler | beispiele/gift/195-descendants-ohne-tree.gab `S008` · beispiele/gift/296-schleifeninvariante-nennt-nichts.gab `M133` |
| `6285` | `descendants of` needs all three edges -- `child` and `sibling` to walk down, `parent` to come back WITHOUT a stack (one as deep as the tree is hig… | mit Fehler | beispiele/gift/196-descendants-nur-mit-elter.gab `S008` |
| `6295` | `descendants of` over a table without `count` -- no sentinel | ungemessen |  |
| `6371` | `by consuming` -- the run form is the same walk PLUS the removal, and the removal is a generated `ops` operation this emitter does not have | ungemessen |  |
| `6437` | `elems of … by consuming` -- an array element is not removed; consumption needs a carrier with generated `ops` | ungemessen |  |
| `6506` | `queue` -- «B10»: `traverse` yields no value and knows no `break`, so `by consuming` drains the WHOLE queue; that is a different program | UNGEDECKT | messung/proben/probe-vier-zellen.gab |
| `6532` | `mappings of` -- the reading is DECIDED (the leaf SET, because W^X is a statement about the set), and the cost bound now says so. What is missing i… | mit Fehler | messung/fragmente/F09.gab `K001` |
| `6537` | `chain in` -- the sibling chain needs its own bound | UNGEDECKT | messung/proben/probe-vier-zellen.gab |
| `6538` | `fields of` -- a register field list is not a runtime domain | ungemessen |  |
| `6539` | `threads` -- the thread set is not declared in a translation unit | UNGEDECKT | messung/proben/probe-vier-zellen.gab |
| `6574` | `match` over a `tagged type` must name every variant exactly once -- there is no catch-all branch, and a `switch` with a missing case falls through… | mit Fehler | beispiele/gift/159-match-nicht-erschoepfend.gab `D005` |
| `6622` | `tagged` variant payload type | ungemessen (wdh.) |  |
| `6802` | `match` over a call this unit does not declare -- the type of the scrutinee stands in the callee's declaration, and there is none. A call whose ret… | UNGEDECKT | messung/fragmente/F05.gab |
| `6813` | `match` over something other than an `option index into T` | ungemessen |  |
| `6818` | `match` over an option needs exactly `Some` and `None` | ungemessen |  |
| `7103` | `Some` without an argument | ungemessen |  |
| `7109` | `Some` without an argument | ungemessen (wdh.) |  |
| `7228` | `option` constructor -- `option` has no representation yet | ungemessen |  |
| `7252` | labelled call to something this unit does not declare as a record | ungemessen |  |
| `7271` | a device handle takes exactly its declared parameters -- the base and every further one the declaration names | ungemessen |  |
| `7308` | `transition` call whose argument is not a handle of THAT device -- the transition belongs to a declaration, and which one is not a guess | ungemessen |  |
| `7358` | `None` where the emitter cannot see WHICH table's sentinel is meant -- the sentinel is `count` itself (beweise/Option_Sonderwert.thy), so it needs … | ungemessen |  |
| `7442` | device register access form | ungemessen |  |
| `7461` | a `format` field followed by more suffixes -- a reader returns a VALUE, and a value has no place inside the bytes | ungemessen |  |
| `7633` | unary minus -- in C `-x` on an unsigned operand stays UNSIGNED (the usual conversions do not promote it), so the emitted program would compute some… | mit Fehler | beispiele/gift/219-unaeres-minus.gab `M101` |
| `7668` | `lenof` over a place whose type is not a fixed-length array -- the length would have to come from somewhere other than the declaration, and there i… | ungemessen |  |
| `7680` | `sizeof` / `aligned` outside a `format` predicate -- inside one they lower against the buffer (`v->len`), and outside one there is no object to mea… | ungemessen |  |
| `7692` | `old(place)` outside a compare-exchange -- it names the value BEFORE the call, and nothing in the emitted C keeps it. The one place it does lower i… | UNGEDECKT | beispiele/gift/220-old-in-einem-rumpf.gab |
| `7703` | `result` -- it names the return value of the surrounding function inside an `ensures`, and a contract is checked at compile time (W6). There is no … | ungemessen |  |
| `7886` | `walk … levels` that is not a number -- the descent's step count IS the declaration's one statement about the run, and it cannot be guessed | mit Fehler | messung/fragmente/F09.gab `K001` |
| `7895` | `walk` whose `node` array has no constant length -- the index bound would then come from nowhere | ungemessen |  |
| `7904` | `walk` with a non-positive `levels` or node length | ungemessen |  |
| `7912` | `walk` whose `node` element is not a named type | ungemessen |  |
| `7916` | `walk` whose `node` element has no name | ungemessen |  |
| `7920` | `walk` whose `node` element is not a `format` -- `down`/`leaf` read FIELDS of an entry, and only a `format` says which bytes they are | ungemessen |  |
| `7929` | `walk … down … when` predicate form | ungemessen |  |
| `7933` | `walk … leaf` predicate form | ungemessen |  |
| `8012` | `entry` for an architecture other than x86_64 -- register footprint, stack switch and nesting are different per architecture, and `arch` stands in … | ungemessen |  |
| `8121` | `entrust` for an architecture other than x86_64 -- the guest's entry contract is a register contract, and which registers those are is what `arch` … | ungemessen |  |
| `8200` | `boot` for an architecture other than x86_64 -- a boot step sets machine registers, and how wide they are is what `arch` says | ungemessen |  |
| `8316` | a fallible register read whose width the emitter cannot resolve | ungemessen |  |
| `8331` | a `requires … else` at a register whose condition is not a RUN TIME condition -- a quantifier, `reaches`, `Held` or an implication is proved, not e… | ungemessen |  |
