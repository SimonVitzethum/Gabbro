# W24 — die zehn Fragmente durch `gabbro emit`, einzeln gemessen

**Gemessen am 2026-08-30 auf `ki-pc-fisch-101`** (110 GB, 16 Kerne), Binärprogramm aus
`cargo build --release` desselben Standes, `cc` = GCC unter `LC_ALL=C`.

```bash
for f in messung/fragmente/F*.gab; do ./target/release/gabbro emit "$f" > /tmp/$(basename $f .gab).c; done
for n in F02 F04 F06 F07 F08 F10; do cc -std=c11 -Wall -Wextra -Werror -O0 -c /tmp/$n.c -o /dev/null; done
for n in F02 F04 F06 F07 F08 F10; do cc -std=c11 -Wall -Wextra -Werror -O2 -c /tmp/$n.c -o /dev/null; done
```

---

## 0. Die Frage war falsch gestellt, und das ist der erste Befund

Der Auftrag zitierte die Flächentabelle von `mutiere-pruefer.py`:

<!-- widerruf:aus -->
> `code 86 Mutationen` — Die C-Emission. **ZWEI Übersetzungseinheiten gebaut und mutierbar**
> (ein Beispiel und Fragment F7, die Geistlöschung); **acht Fragmente ungeprüft**.
<!-- widerruf:an -->

**Beide Zahlen sind seit dem 2026-08-17 nicht nachgeführt worden.** Nachgezählt am
2026-08-30 über `instrumente/pruefe-emission.sh`:

| | im Satz | gemessen |
|---|---|---|
| Übersetzungseinheiten gebaut und gelaufen | zwei | vierundzwanzig |
| davon Fragmente | eins (F7) | fünf — F02, F04, F07, F08, F10 |
| Fragmente, die niemand läuft | acht | fünf — F01, F03, F05, F06, F09 |
| davon emittieren heute überhaupt | — | **eins**, F06 |

> **Ein zweites Register über derselben Sache** (W7). Die Zeile darunter in derselben Datei
> trägt die Heilung schon im Wortlaut — *„Diese Zahl wird NICHT hier gepflegt"* — und die
> `code`-Zeile stand daneben und pflegte ihre.

*Eine veraltete Zahl neben einem lebenden Katalog liest sich nicht wie veraltet, sondern wie
eine Messung.* **Gebaut, siehe §5:** die Zeile liest ihre Zahl jetzt aus
`pruefe-emission.sh`, mit Sprechprobe in `--anker`.

---

## 1. Die Tabelle der zehn

`pruefe` = `gabbro pruefe`, `emit` = `gabbro emit`, `cc` = `cc -std=c11 -Wall -Wextra -Werror`.

| | `pruefe` | `emit` | `cc -O0` / `-O2` | die gemessene Absage, wörtlich |
|---|---|---|---|---|
| **F01** | 1 Fehler | keine C-Datei | — | `[N029]` :355 — ``delete_leaf` can fail with `Fehler`, and this call does not stand in a `let … else`` |
| **F02** | sauber | 176 Zeilen C | übersetzt / übersetzt | — *läuft in `pruefe-emission.sh`* |
| **F03** | 19 Fehler | keine C-Datei | — | `[N040]`×9, `[N035]`×5, `[M124]`×3, `[M101]`, `[H011]`; dahinter `[C001]`×2 |
| **F04** | sauber | 150 Zeilen C | übersetzt / übersetzt | — *läuft in `pruefe-emission.sh`* |
| **F05** | sauber (1 Hinweis) | keine C-Datei | — | `[C001]` :173 — ``match` over something other than an `option index into T`` |
| **F06** | sauber | 161 Zeilen C | **FEHLER** / **FEHLER** | `cc`: `comparison is always true due to limited range of data type` an `F06.c:102` |
| **F07** | sauber | 37 Zeilen C | übersetzt / übersetzt | — *läuft in `pruefe-emission.sh`* |
| **F08** | sauber (1 Hinweis) | 64 Zeilen C | übersetzt / übersetzt | — *läuft in `pruefe-emission.sh`* |
| **F09** | 1 Fehler | keine C-Datei | — | `[K001]` :79 — ``rechte_pruefen` promises <= 4096 ops, the body costs 137438953472`; dahinter `[C001]`×3 |
| **F10** | sauber | 66 Zeilen C | übersetzt / übersetzt | — *läuft in `pruefe-emission.sh`* |

**Sechs von zehn emittieren heute** — nicht eins. Fünf davon übersetzen unter `-Werror` bei
`-O0` und `-O2`; das sechste ist F06.

---

## 2. `C001` ist nicht das Tor — bei dreien von vier fällt vorher etwas anderes

Die Frage lautete, *ob die acht acht verschiedene Gründe haben oder zwei*. Gemessen:
**vier Fragmente weigern sich, und `C001` ist bei genau EINEM die erste und einzige Absage.**

| | erste Absage | Kennung | Schicht |
|---|---|---|---|
| F01 | eingefrorene Ausschnittzeile ruft fehlbar ohne `let … else` | `N029` | Korpus, eingefroren |
| F03 | `Frame` und `RegNr` deklariert niemand | `N040` | Korpus, fehlende Deklaration |
| F05 | `match` über einem Ruf | `C001` | **Erzeuger** |
| F09 | die zugesagte Schranke ist nachrechenbar falsch | `K001` | Korpus, eingefroren |

Die sechs `C001`, die über alle zehn Dateien fallen, tragen **sechs verschiedene Gründe** —
kein Sammelurteil:

```
F03 :174  `queue` -- «B10»: `traverse` yields no value and knows no `break`, so `by
          consuming` drains the WHOLE queue; that is a different program
F03 :208  parameter type                       (der Typ heisst `RegNr`, den niemand deklariert)
F05 :173  `match` over something other than an `option index into T`
F09 :61   `device … at normal` -- an access into the ordinary space is not a device access,
          and what a `device` block would mean there is not decided
F09 :70   `walk … levels` that is not a number -- the descent's step count IS the
          declaration's one statement about the run, and it cannot be guessed
F09 :81   `mappings of` -- the reading is DECIDED …, what is missing is the lowering
```

> **Die Absage ist hier nicht das Problem, sondern die Auskunft.** Jeder der sechs Sätze sagt
> die Form UND den Grund; keiner von ihnen ist ein Wort, unter dem sich etwas anderes
> versteckt. *Das ist der Gegenfall zu `messung/RUF-TOR.md`* — dort standen siebzehn Absagen
> unter einem Wort und keine einzige war ein Ruf.

Und die sechs verteilen sich auf **drei** Klassen, nicht auf sechs:

1. **Entschieden, nicht gebaut** — `mappings of` (F09:81) und `queue` (F03:174). Die Lesart
   steht fest, die Absenkung ist ein Bauposten und die Absage sagt das wörtlich.
2. **Unentschieden** — `device … at normal` (F09:61) und `walk … levels` ohne Zahl (F09:70).
   Was die Form dort bedeutet, ist nicht beschlossen; **eine Absenkung wäre geraten.**
3. **Erzeugerlücke hinter einem Korpusloch** — `parameter type` (F03:208) und `match` über
   einem Ruf (F05:173). Beide fallen nur, weil die Datei einen Namen ruft, den sie nicht
   deklariert.

---

## 3. F06: es emittiert, es läuft niemand, und sein C übersetzt nicht

**Das ist der schärfste Befund dieser Messung.** F06 prüft sauber, emittiert 161 Zeilen C —
und `cc -Werror` weist sie ab:

```
/tmp/F06.c:102:15: error: comparison is always true due to limited range of data type
  102 |         if (w != MUSTER) {
```

Der Grund steht seit dem 2026-08-26 im Kopf von `messung/fragmente/F06.gab` und ist
korpusseitig: «B12» bindet `elems of` an einen **Index**, der Ausschnitt vom 2026-08-14
benutzt die Elementlesart, `w` läuft bis 8192 und `MUSTER` ist `0xdead_beef_dead_beef`.

**Was daran neu ist, ist nicht der Fehler, sondern wo der Wächter aufhört.** Die Regel
dafür gibt es seit dem 2026-08-20 und sie ist scharf formuliert — Stufe 9 von
`pruefe-emission.sh`:

> *JEDE Datei, die durch `emit` kommt, MUSS `cc -Werror` bestehen.*

**Sie läuft über `beispiele/*.gab` und über nichts sonst.** Für die Fragmente gilt nur, was
in den vierundzwanzig `lauf`-Einträgen einzeln benannt ist, und F06 steht dort nicht;
`cargo test` ruft `emittiere` über `beispiele/`, prüft aber weder den erzeugten TEXT noch
übersetzt es ihn. **Zwischen „emittiert" und „übersetzt" liegt für F06 niemand** — nicht,
weil die Regel fehlt, sondern weil ihre REICHWEITE an `beispiele/` endet.

*Das ist dieselbe Gestalt wie W16, eine Ebene höher: der Wächter misst seinen eigenen
Ordner und sieht dabei vollständig aus.*

> Und darin steckt der Befund, den F06s eigener Kopf bereits benennt und den niemand gebaut
> hat: *M1 trägt Bereichstypen und hätte den Vergleich als konstant-wahr erkennen können.
> Der fremde Übersetzer hat gesagt, was der Prüfer wusste und nicht aussprach.*
> **Nicht gebaut** — siehe §6.

---

## 4. Zwei Blindstellen, an einer eigens gebauten Probe nachgemessen

### 4.1 Ein Feldzugriff auf einer Zahl fällt bei keinem Pass auf

`recv` in F05 ist als `-> u64` deklariert, und der Ausschnitt schreibt `m.op`. Die Probe
trennt das vom Fragment ab:

```gabbro
extern fn hole(ep : u64) -> u64 or Fehlt effects { reads ep } costs <= 2 ops;
impl fn t(ep : u64) -> u64 effects { reads ep } costs <= 16 ops {
    let m = hole(ep) else (e) { return 0; }
    let z = m.feld_das_es_nicht_gibt;
    nutze(z);
    return 1;
}
```

```
$ gabbro pruefe probe-feld.gab
probe-feld.gab: 5 Items, 0 Fehler, 0 Hinweise

$ gabbro emit probe-feld.gab
Fehler: [C001] probe-feld.gab:13:5: no lowering: `let` without a resolvable type
```

**Ein Bestimmer, den es auf einem `u64` nicht geben kann, und der einzige Pass, der etwas
sagt, ist der Erzeuger** — und der spricht über das `let`, nicht über das Feld. Dieselbe
Gestalt wie Befund 7 in `messung/fragmente/README.md`, wo drei Namen in einem
`check … can_fail` an denselben einzigen Leser fielen.

### 4.2 `match` über einem Grund gibt es nur an EINER Stelle

Der Erzeuger senkt `match g { … }` über einem `reason` ab — aber `gruendewerte` wird
ausschließlich für den Fehlerbinder eines `let … else (e) { … }` gefüllt (`emit.rs`:5670,
:8231). Jede andere Herkunft desselben Wertes fällt:

```gabbro
extern fn entschluessle(o : u64) -> Op effects { pure } costs <= 2 ops;

impl fn ueber_ruf(o : u64) -> u64 … { match entschluessle(o) { Lesen => … } }
impl fn ueber_ort(o : u64) -> u64 … { let g = entschluessle(o); match g { Lesen => … } }
```

```
$ gabbro pruefe probe-match.gab
probe-match.gab: 6 Items, 0 Fehler, 0 Hinweise

$ gabbro emit probe-match.gab
Fehler: [C001] probe-match.gab:16:5: no lowering: `match` over something other than an `option index into T`
Fehler: [C001] probe-match.gab:27:5: no lowering: `match` over something other than an `option index into T`
```

**Auch die Ortsform fällt** — nicht nur der Ruf. Der Erzeugerkommentar an `match_grund`
sagt, ohne diese Absenkung *„wäre `match e` eine Form, die `gabbro pruefe` annimmt und
`gabbro emit` ablehnt"*; gemessen gilt das heute für jede Herkunft außer der einen.

---

## 5. Was gebaut wurde

**Genau eines, und es ist ein Wächter, kein Konstrukt:** die `code`-Zeile der
Flächentabelle in `instrumente/mutiere-pruefer.py` **liest** ihre Zahlen jetzt, statt sie zu
nennen. `emissionseinheiten()` zählt die `lauf "…"`-Zeilen von `pruefe-emission.sh` und
gleicht die gelaufenen Fragmentnummern gegen `messung/fragmente/` ab.

```
$ ./instrumente/mutiere-pruefer.py --anker
  Emissionsflaeche liest:    ok -- 24 Einheiten, 5/10 Fragmenten, 5 ohne Lauf
```

**Mit Sprechprobe in beide Richtungen** (R11): `emissionsflaeche_sprechprobe()` streicht eine
`lauf`-Zeile aus einer Kopie und verlangt, dass die Zahl fällt; und sie verlangt, dass
gelaufene plus ungelaufene Fragmente zehn ergeben. *Eine Zeile, die eine Zahl liest, ist erst
dann mehr wert als eine, die sie nennt, wenn jemand sie hat fallen sehen.*

> **Und die erste Fassung war selbst ein zweites Register.** Sie zählte nur die
> `lauf "…"`-Zeilen und kam auf 23, während `pruefe-emission.sh` in derselben Stunde
> *„24 durchgestochen"* druckte: die Bibliothekskette (Stufe 10) ist eine Einheit ohne
> `lauf`-Ruf und erhöht denselben Zähler noch einmal. **Ein Wächter, der eine Zahl über eine
> ANDERE Rechnung nachbildet, ist genau das Register, das er entfernen sollte** — also rechnet
> er jetzt so, wie die Schale rechnet, und die Sprechprobe hält fest, dass genau eine
> Erhöhung innerhalb von `lauf()` steht.

---

## 6. Was NICHT gebaut wurde — und warum, je Fragment

**Kein Fragment wurde emittierbar gemacht.** Keines der vier verweigernden lässt sich mit
wenig Arbeit öffnen, und für drei von ihnen wäre die Arbeit gar nicht Gabbros:

| | was fehlt | warum nicht gebaut |
|---|---|---|
| **F01** | ein `or <reason>` an `delete_leaf` — und danach fällt `N029` an `FRAGMENTE.md`:1 Zeile des Ausschnitts | **eingefroren.** Die Zeile stammt vom 2026-08-14; sie zu ändern verschiebt den Maßstab, statt die Pflicht zu schließen |
| **F03** | `type Frame`, `type RegNr` — plus fünf `fn(…)`-Verträge an Ausschnittzeilen (`N035`, Pflicht seit 2026-08-21) | die zwei Typen wären erlaubt (Regel des Ordners), die fünf Verträge nicht: sie stehen im eingefrorenen Ausschnitt. **Ein Fragment kann unter einer neueren Regel veralten**, und das wird ausgehalten |
| **F05** | ein Nachrichtentyp für `recv` — heute `-> u64`, und der Ausschnitt liest `m.op` — plus die Deklaration von `decode_op` | **das wäre Erfindung, nicht Vervollständigung.** Der Ausschnitt nennt weder das Format noch die Operationsmenge; sie zu schreiben hieße, ein Programm zu entwerfen und es dann zu messen |
| **F06** | nichts an Gabbro — es emittiert | der `cc`-Fehler hängt an einer eingefrorenen Ausschnittzeile mit der Elementlesart von `elems of`. **Der Durchstich bleibt offen, die Absenkung ist erreicht** (so steht es seit 2026-08-26 in der Datei) |
| **F09** | eine Absenkung für `mappings of` (entschieden), eine Entscheidung für `device … at normal` (offen), und `costs <= 4096 ops` ist im Ausschnitt falsch | die falsche Zusage ist eingefroren; die offene Entscheidung ist **Axiomschicht** — was ein `device`-Block im gewöhnlichen Raum bedeutet, ist eine Aussage über das Speichermodell. *Ein Erzeuger, der rät, hebt jeden Pass vor sich auf* |

**Ebenfalls nicht gebaut, mit Grund:**

* **`match` über einem Grund aus beliebiger Herkunft** (§4.2). Die Lücke ist scharf benannt
  und wäre klein — der einzige Korpusort ist `F05`:173, und der liegt hinter dem Korpusloch
  darüber. **Regel A: kein Konstrukt ohne ein Programm, das es gebraucht hat.**
* **Eine M1-Absage für einen bereichskonstanten Vergleich** (§3). Sie hätte den `cc`-Fehler
  in F06 einen Pass früher gefangen. Sie kostet eine Kennung, einen Satz und eine Giftprobe
  — und sie nähme F06 aus der Spalte *„prüft sauber"*, also aus einer Zahl, die niemand
  darum gebeten hat. **Das ist eine Entscheidung und keine Nachlässigkeit;** sie steht hier,
  damit sie jemand treffen kann.
* **Stufe 9 auf `messung/fragmente/` ausgedehnt.** Die Regel steht schon da (§3), nur ihre
  Reichweite endet an `beispiele/`. Sie zu erweitern hieße heute: **dauerhaft rot wegen
  F06**, und zwar aus einem Grund, der korpusseitig und eingefroren ist — *genau die
  Bauform, gegen die der zweite Posten dieses Auftrags steht.* Wer sie erweitert, braucht
  zuerst die Ausnahmeform, die Stufe 9 schon hat (`ausnahme_grund`, heute leer): **eine
  benannte Ausnahme mit Grund, die auffällt, sobald sie abläuft.** Das ist eine Entscheidung
  über den Umfang und keine Zeile Code — sie steht hier, damit sie jemand trifft.
* **Kein neuer Eintrag in `mutiere-pruefer.py`s Katalog.** Eine Mutation gehört zu einem
  Konstrukt, das gebaut wurde; gebaut wurde ein Wächter, und der trägt seine Sprechprobe.
