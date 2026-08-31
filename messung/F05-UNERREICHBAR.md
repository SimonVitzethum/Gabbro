# `F05` senkt nicht ab, und der Grund ist eine Zeile im eingefrorenen Text

*Gemessen am 2026-08-31, Bahn F5, Posten 3. **Das Ergebnis ist eine benannte Umkehr:** `H`
bleibt bei 4, und es bleibt mit einem Grund, den man nachrechnen kann statt ihn zu glauben.*

---

## 1. Was der Auftrag erwartet hat, und was dagegen steht

Der Weg war ausgemessen: fünf `extern fn`-Zeilen ergänzen (`decode_op`, `request_flush`,
`serve_rw`, `serve_scan`, `bump_served`), dann **31 Items, 0 Fehler, 0 Hinweise, 199 Zeilen
C** — und `cc -Werror` weist drei Dinge zurück, deren erstes `exit` ist.

**Die Erwartung war, dass `N041` den Preis wegnimmt.** Sie tut es, und zwar so, wie es
gedacht war: `pruefe-emission.sh` Stufe 9 verlangt *„jede Datei, die emittiert, muss auch
übersetzen"*, und ihre Ausnahmeliste ist seit dem 2026-08-20 leer. Mit `N041` **emittiert
`F05` gar nicht mehr** — die Stufe hat nichts zu beanstanden, und die leere Liste bleibt leer.

**Nur senkt `F05` damit auch nicht ab.** Und das ist kein Umweg, den man noch findet:

---

## 2. Die drei Türen, und alle drei sind zu

### 2.1 Umbenennen — der `verlorene_zeilen`-Riegel hält

`dokumente/FRAGMENTE.md`:932–1033 ist EIN ```gabbro-Block, und `exit` steht darin **neunmal**:

```
1028   extern fn exit() -> never effects { diverges };      -- die Deklaration
 968   … else (e1) { signal(NTFN, 0xD1A6_0001); exit(); }   -- und acht Rufstellen
 969   970   971   973   974   997   1019
```

`instrumente/pruefe-emission.sh`:345 schneidet den Block und vergleicht ihn Zeile für Zeile
mit der Arbeitsfassung:

```bash
verlorene_zeilen() { diff "$1" "$2" > "$ARB/f2-diff" || true; grep '^<' "$ARB/f2-diff" || true; }
```

*Ergänzen ist erlaubt, weglassen nicht.* **Eine Umbenennung ist neunmal ein Weglassen.**

### 2.2 Die Zeile ist nicht „ergänzt", sie ist eingefroren

Der Kommentar über ihr liest sich wie eine Ergänzung — *„Nachgetragen 2026-08-15: `exit` und
`signal` wurden benutzt und nie erklaert"* —, und genau das hat sie so lange harmlos aussehen
lassen. **Sie steht INNERHALB des Blocks**, und `FRAGMENTE.md`:14 sagt, was das heißt:

> *„Everything after this note is a record of 2026-08-14 and stays untouched."*

**Am 2026-08-15 wurde eine Zeile in einen Bericht nachgetragen, der eingefroren ist, und sie
hat das Einfrieren geerbt.** *Was nachgetragen wurde, ist damit so unantastbar wie das, was
schon dastand.*

### 2.3 Eine Ausnahme in Stufe 9 — der Preis, den der Auftrag ausgeschlossen hat

Die Ausnahmeliste ist seit elf Tagen leer, und der Wächter meldet abgelaufene Einträge selbst.
*Ein Eintrag dort wäre kein Durchstich, sondern eine Buchung.*

---

## 3. Und der Ruf meint gar nicht C's `exit`

Das ist der Befund unter dem Befund, und er schließt die letzte Tür.

| | |
|---|---|
| C11 | `_Noreturn void exit(int status);` |
| `F05` | `extern fn exit() -> never effects { diverges };`, gerufen als `exit()` |

**Die Stelligkeit stimmt nicht.** Selbst eine Deklaration, die C's Signatur träfe, ließe die
acht Rufstellen falsch: `exit()` ohne Argument ist kein Ruf von `void exit(int)`. *Der
Ausschnitt meint „diese Funktion kehrt nie zurück", nicht „beende den Prozess mit diesem
Status" — und der Name, den er dafür gewählt hat, gehört C.*

> **Damit ist `F05` nicht an Gabbro gescheitert und auch nicht an `cc`, sondern an einer
> Namenswahl von 2026-08-15 in einem Text, der nicht mehr geändert werden darf.** Der
> Unterschied ist nicht kosmetisch: eine Sprachlücke baut man zu, eine eingefrorene Zeile
> nicht.

---

## 4. Was das für `H` heißt — und die Zahl bewegt sich NICHT

`./instrumente/zaehle-pflichten.py --haengend` liest weiter:

```
    F1   0 + 1 = 1
    F3   0 + 1 = 1
    F5   0 + 1 = 1
    F9   0 + 1 = 1
  H                 4
```

**`H` fällt nicht, und es zu senken wäre hier nur über eine Umbuchung gegangen.** Die läge
sogar nahe — `PLAN-VOLLSTAENDIGKEIT.md` §K1 schreibt selbst: *„Eine Absenkungspflicht an einem
Programm, das nicht übersetzt, ist keine offene Pflicht, sondern eine falsch gebuchte."*

**Sie wird hier trotzdem nicht vorgenommen, und der Grund ist die Symmetrie:**

| | weist wer ab | Kennung |
|---|---|---|
| **F1** | der PRÜFER | `N029` |
| **F3** | der PRÜFER | `N035`, `N040`, `M124`, `M101`, `H011` |
| **F5** | der PRÜFER — **seit heute** | `N041` |
| **F9** | der ERZEUGER, dreimal | `C001` |

**Alle vier offenen Absenkungspflichten hängen an Programmen, die Gabbro nicht annimmt.** Wer
`F5` allein umbucht, senkt eine Zahl um eins und lässt drei gleichgelagerte Zeilen stehen —
*das ist Umtopfen, und dieser Ordner hat dafür ein Wort.* Die Umbuchung ist EINE Entscheidung
über alle vier, sie gehört dem Ordner, und sie steht hier als Vorschlag und nicht als Vollzug.

> **Was sich stattdessen bewegt hat, ist die Qualität der 4.** Bis heute stand bei `F5`
> *„senkt nicht ab (V2)"* — eine Erzeugerabsage über eine `match`-Form, die seit dem
> 2026-08-31 gar nicht mehr die Ursache ist. Heute steht dort eine Prüferkennung, eine Datei,
> eine Zeilennummer und ein Satz, der sagt, warum die Zeile nicht zu ändern ist. *Eine Zahl,
> die sich nicht bewegt, ist nicht dieselbe Zahl wie gestern, wenn ihr Grund gemessen ist.*

---

## 5. Was diese Messung NICHT sagt

* **Sie sagt nicht, dass `F05` unabsenkbar ist.** Sie sagt, dass es unabsenkbar ist, *solange
  `FRAGMENTE.md` eingefroren bleibt*. Ein Ordner, der den Einfriersatz für diese eine Zeile
  aufhebt und es dazuschreibt, bekommt `F05` — und zahlt mit dem Satz, auf dem die
  Glaubwürdigkeit aller zehn Fragmente steht.
* **Sie sagt nichts über die zwei anderen `cc`-Gründe.** `m->op` auf einem Skalar und das
  ungenutzte `let` stehen unabhängig davon offen und sind in `messung/ZWEI-BLINDSTELLEN.md`
  gemessen — *sie treffen nicht nur `F05`.*
* **Sie ist mit EINEM Binärprogramm und EINEM `cc` gemessen.** GCC unter `LC_ALL=C`, lokal.
