# Die 66 Absagen des Rumpfkanals, einzeln gebucht — und 60 davon haben nie eine Übersetzung gesehen

> Gemessen am 2026-08-30, nach Bahn B und nach den drei geheilten Erzeugerfehlern des Tages.
> **Die Frage war, wie viele der 66 eine fehlende SPRACHFORM des Modells sind und wie viele
> ein fehlendes TOR im Kanal. Die Messung gibt eine dritte Antwort, und sie gilt für
> fünf Sechstel:** *keins von beidem.* Sechzig Absagen fallen an der **ART** der Pflicht,
> bevor ein einziger Ausdruck angesehen wird.

---

## 1. Der Stand, neu gemessen

```
./instrumente/zaehle-lean.py
== BODY CHANNEL: 75 obligations, 9 goals, 66 refused (23 units with errors, no register) ==
```

**Die Absagegründe einzeln** — und die Aufteilung ist der Punkt, nicht die Summe:

| Grund | Anzahl |
|---|---:|
| `call-site` | 20 |
| `device-promise` | 15 |
| `foreign-body` | 12 |
| `table-invariant` | 8 |
| `loop` | 6 |
| `carrier-not-a-table` | 2 |
| `no-shape-for-field` | 2 |
| `call-not-compositional` | 1 |
| **die übrigen 24 Gründe** | **je 0** |
| **Summe** | **66** |

*Vierundzwanzig von zweiunddreißig Zeilen des Registers stehen auf null.* Der Kanal scheitert
heute an acht Dingen, nicht an zweiunddreißig.

---

## 2. Der Befund: die Frage hat eine dritte Antwort, und sie trägt 60 von 66

`lean.rs::verdicts` entscheidet **zuerst nach der ART der Pflicht**, in einem `match p.art`
mit sieben Armen. **Fünf davon sagen pauschal ab** — ohne `judge`, ohne `block_term`, ohne
`expr_term`. Nur zwei erreichen die Übersetzung überhaupt.

```
-- Refused BY KIND, before an expression is looked at --

   V    20   a precondition at a CALL SITE                by kind
   D    15   a device promise at a register               by kind
   F    12   a foreign duty -- there is no body           by kind
   E     8   preservation of a table invariant            by kind
   S     5   an invariant across the passes of a loop     by kind
   N     6   a POSTCONDITION                              translated
   R     0   a REFINEMENT of a specification              translated
```

> **60 von 66 Absagen haben nie eine Übersetzung gesehen.**

### 2.1 Warum das die Zahl umdreht

Der Grund, der neben so einer Absage steht, **nennt ein Gabbro-Konstrukt** — `loop`,
`table-invariant`, `device-promise` — und liest sich damit wie eine fehlende Form. Er ist
aber nicht gemessen worden, sondern aus der Art abgeleitet: *dieselbe Zeile stünde da, wenn
das Modell die Form vollständig trüge.*

Was er wirklich benennt, ist die **einzige ZIELGESTALT, die dieser Kanal schreibt**:

```
∃ s' v, finalState (exec ρ body s) = some s'  ∧  …  ∧  eval s' post = some (.bool true)
```

*Der Rumpf läuft, danach gilt die Nachbedingung.* Eine Vorbedingung an einer Rufstelle
spricht über einen Zustand **mitten im Rumpf**; eine Schleifeninvariante braucht die
Schleifen**regel**, ein Satz über den Rumpf der Schleife und nicht über den der Routine; eine
`maintains`-Erhaltung ist über **jeden Slot** quantifiziert. Keine davon passt in die eine
Gestalt — und keine davon scheitert an einem Wert.

### 2.2 Und damit ist die Deckungszahl eine andere

**9 von 75 ist nicht die Deckung dieses Kanals.** Von den 75 Pflichten gehören 15 den beiden
Arten, die er überhaupt versucht — und davon trägt er **9**.

| | |
|---|---:|
| Deckung über das Register | 9 von 75 · **12 %** |
| **Deckung über das, was er VERSUCHT** | **9 von 15 · 60 %** |

*Beide Zahlen sind wahr, und die zweite sagt, woran gearbeitet werden müsste.*

### 2.3 Die Messung steht im Werkzeug, nicht in diesem Absatz

Der Artbuchstabe wird vom Zeugnis **schon geschrieben** (`duty_1  N  lies :: ensures #1`);
`zaehle-lean.py` liest ihn jetzt und rechnet die Spalte gegen die Absagen auf. **Kein
Urteil, kein neues Werkzeug** — und die Zahl veraltet nicht in einem Fließtext.

---

## 3. Die sechs, die die Übersetzung erreicht haben

| Einheit | Routine | Grund |
|---|---|---|
| `beispiele/02-geraet.gab` | `scharfschalten` | `carrier-not-a-table` |
| `messung/netz/udp-echo.gab` | `summe_1071` | `carrier-not-a-table` |
| `beispiele/09-ohne-zeiger.gab` | `blatt_loeschen` | `no-shape-for-field` |
| `messung/caprock/kapraum.gab` | `blatt_loeschen` | `no-shape-for-field` |
| `messung/fragmente/F06.gab` | `unberuehrt` | `loop` |
| `beispiele/01-tabelle.gab` | `blatt_loeschen` | `call-not-compositional` |

### 3.1 Und alle sechs sind am RUMPF gescheitert, keine an der Nachbedingung

Gemessen mit dem **Ausfuhrkanal**, der Rumpf und Klausel getrennt absagt (`gabbro lean` bucht
einen Rumpf als `-- REFUSED <name> (<grund>)` und eine Klausel als
`ensures #k (<grund>)`). Alle sechs Routinen erscheinen dort als **Rumpfabsage**.

*Das ist ein eigener Befund*: der Grund nennt eine Form, aber nicht die STELLE, an der sie
getroffen wurde. Ein `carrier-not-a-table` neben `summe_1071 :: ensures #1` liest sich wie
eine Nachbedingung, die der Kanal nicht sagen kann — die Nachbedingung lautet
`result <= 4294967295` und ist trivial übersetzbar. **Dieselbe Klasse wie
`result-in-ensures` heute früh** (`messung/ERGEBNIS-ZWEI-NAMEN.md`), eine Ebene höher.

### 3.2 Die Gegenprobe, und sie ist die schärfste Zahl des Tages

Über den **ganzen Korpus** wirft der Ausfuhrkanal **14 Klauseln** ab:

| | Anzahl |
|---|---:|
| `requires` — `lock-witness` | 11 |
| `requires` — `call-in-expression` | 1 |
| `requires` — `builtin` | 1 |
| **`ensures` — `result-in-ensures`** | **1** |

**Genau EINE Nachbedingung im ganzen Korpus ist unübersetzbar** — und sie ist es nur im
Ausfuhrdatum, das sie absichtlich fallen lässt; der Pflichtenkanal TRÄGT sie (§1.1 von
`ERGEBNIS-ZWEI-NAMEN.md`).

> **Die Sprache der Nachbedingungen ist nicht das, was fehlt.** Keine einzige der 66 Absagen
> ist eine Nachbedingung, die dieser Kanal nicht aussprechen kann.

Und die elf `lock-witness` sind nach eigener Buchung **gar keine Lücke** — die Sperrpässe
lösen sie ein (`H005`, `H006`, `H012`, `H016`).

---

## 4. Die Frage, wie sie gestellt war — und wo das Urteil anfängt

Erst jetzt lässt sich „fehlende Sprachform" gegen „fehlendes Tor" halten, und **nur für
sechs Absagen ist die Frage überhaupt wohlgeformt.** Für die sechs, mit dem Konstrukt des
Modells daneben, das sie tragen müsste:

| Absage | woran genau | Modell trägt es? | Lesart |
|---|---|---|---|
| `carrier-not-a-table` ×1 (`Vtd`) | `v.GSTS.TES` — ein Bitfeld in einem Register eines `device` | `Place` hat `slot`/`field`/`global`, **kein Geräteregister und keine Bitentnahme** | **Sprachform** |
| `carrier-not-a-table` ×1 (`Kopfworte`) | `k.wort[i]` — ein Element eines ARRAY-Feldes in einem Verbund | `Place.slot` indiziert nur über eine `table`; **ein indiziertes Verbundfeld hat keine Form** | **Sprachform** |
| `no-shape-for-field` ×2 | `Objekte.slot.art : ObjektArt`, ein `tagged type` | `Value` ist `int │ bool │ absent │ present`; **keine Summe** | **Sprachform** |
| `loop` ×1 (`F06 :: unberuehrt`) | die Traversierung trägt `by decreasing …`, aber **kein `invariant`** | `Stmt.loop (id) (inv) (body)` — das Modell VERLANGT eine Invariante | **fehlende Angabe in der QUELLE** |
| `call-not-compositional` ×1 | `blatt_loeschen` ruft, `allow_calls` steht auf `false` | `Stmt.call`/`bindCall`/`retCall` stehen im Modell | **Tor im Kanal** |

**Also, für die sechs: vier Sprachform, eine Quellangabe, ein Tor.**

### 4.1 Und das eine Tor ist schon nachgemessen — es kauft nichts

`beispiele/01-tabelle.gab :: blatt_loeschen` steht im Pflichtenkanal unter
`call-not-compositional` und im Ausfuhrkanal, wo `allow_calls` offen ist, unter
**`no-shape-for-field`**. Die Absage wandert, sie fällt nicht. `messung/RUF-TOR.md` hat genau
das am 28. gemessen (*„`duty_8` wandert von `call-not-compositional` nach
`no-shape-for-field`"*) — **das Tor zu öffnen kauft im Pflichtenkanal null Ziele**, und die
Wanderung deckt eine Sprachform auf, die darunter lag.

*Eine Absage kann eine andere verdecken, und dann zählt die obere für zwei.*

### 4.2 Wo die Zweiteilung nicht trägt, und das ist gesagt und nicht versteckt

**Die Grenze zwischen „das Modell kann es nicht sagen" und „der Kanal gibt es nicht aus" ist
kein Messwert.** Ein Modell lässt sich erweitern und ein Kanal belehren; wer die Grenze zieht,
sagt damit, was er für den natürlichen Umfang von `Gabbro.Body` hält. **Ein mechanisches Maß
dafür wäre ein Urteil in Werkzeugform** und stellte dieselbe Frage eine Ebene tiefer.

Gemessen — ohne Urteil — ist deshalb dreierlei, und alle drei stehen oben:

1. **die ART der Pflicht** (§2), aus dem Zeugnis gelesen: 60 zu 6;
2. **Rumpf oder Klausel** (§3.1), aus dem Ausfuhrkanal gelesen: 6 zu 0;
3. **welcher Konstruktor des Modells fehlt** (§4), aus `Body.lean` abgelesen und namentlich
   genannt — nachprüfbar, auch wenn die Einordnung daneben es nicht ist.

Was in der Tabelle von §4 ein **Urteil** ist, ist allein die letzte Spalte. *Die Spalte davor
nennt eine Zeile in `programmlogik/Gabbro/Body.lean`, und die kann jeder nachschlagen.*

### 4.3 Und für die 60 wäre die Frage falsch gestellt

Sie der Vollständigkeit halber, mit demselben Vorbehalt:

* **`foreign-body` (12) — überhaupt keine Lücke, in keiner Richtung.** Es gibt keinen Rumpf.
  Ein `ensures` an einem `extern fn` ist eine ANNAHME, und keine Erweiterung von Modell oder
  Kanal macht daraus je ein Ziel. *Dieselbe Buchung wie `lock-witness`.*
* **`call-site` (20)** — braucht ein Ziel an einem ZWISCHENZUSTAND. Das Modell hat `Stmt.call`;
  es ist eine Zielgestalt, keine Wertform. **Und der Isabelle-Kanal trägt sie schon.**
* **`device-promise` (15)** — dem Modell fehlt der GEGENSTAND, nicht die Form: es kennt keine
  Hardware. Derselbe Grund wie beim `Vtd`-Fall in §4.
* **`table-invariant` (8)** — über jeden Slot quantifiziert, und `eval` hat keinen Quantor.
  **Sprachform**, aber an einer Pflicht, die ohnehin nach Art abgesagt wird.
* **`loop` (5, Art `S`)** — die Schleifen**regel**. Das Modell hat `Stmt.loop` MIT Invariante;
  was fehlt, ist der Satz darüber. **Zielgestalt im Kanal.**

---

## 5. Was das NICHT heißt

* **Die 60 sind keine Fehlbuchung.** Jede nennt einen wahren Grund, warum die Pflicht kein
  Ziel wird. Was sie nicht sagt, ist, dass die Entscheidung vor der Übersetzung fiel — und
  genau das trennt „der Kanal kann es nicht" von „der Kanal versucht es nicht".
* **`9 von 15` ist keine bessere Zahl, sondern eine andere.** Wer nur sie nennt, verschweigt,
  dass vier Fünftel des Registers gar nicht angefasst werden.
* **Die 23 Einheiten mit Fehlern tragen kein Register**, und sie stehen in keiner der Zahlen
  oben. Das ist dieselbe Regel, der `gabbro pflichten` folgt — keine übersprungene Datei,
  sondern eine ohne Antwort.
* **Ein Ziel ist keine bewiesene Pflicht.** Es heißt, die Pflicht steht GESCHLOSSEN da; ob sie
  durchgeht, sagt `./instrumente/pruefe-lean-beweis.sh`.

---

## 6. Nachgezogene Zahlen

Die Bilanz stand an fünf Stellen veraltet da, aus drei verschiedenen Ständen:

| Datei | stand | steht |
|---|---|---|
| `messung/RUF-TOR.md`:36, :85 | `70 obligations, 4 goals, 66 refused` | **75 · 9 · 66** |
| `messung/RUF-TOR.md`:193 | Ziele (Pflichtenkanal) `4 │ 4` | **9** |
| `messung/SCHLEIFENZUSAGEN.md`:70 | „von **70 auf 74**" | **75** |
| `dokumente/PLAN-VERIFIKATION.md`:24 | `71 Pflichten, 4 Sätze, 67 abgesagt` | **75 · 9 · 66** |
| `dokumente/PLAN-VERIFIKATION.md`:69 | „**23 von 70** Einheiten" | 23 stimmt, der Nenner nicht |

**Und eine Erwartung hat sich nicht bestätigt:** `TODO.md` führt **keine** Bilanzzeile des
Rumpfkanals. Gesucht wurde nach `75/9/66` und nach jeder älteren Fassung — die Zeile steht in
`dokumente/MESSUNGEN.md`:11535, und dort war sie schon richtig. *Eine Zahl, die man nicht
findet, ist nicht immer falsch gebucht; manchmal steht sie woanders.*
