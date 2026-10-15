# Die Schleifeninvariante — das Maß trägt die Sprache, die Aussage nicht

*Entschieden am 2026-08-28. Jede Zahl nennt den Befehl, der sie nachrechnet.*

> **Der Befund zuerst, und er hat dieselbe Form wie der vom 2026-08-24:** der Rumpfkanal sagt
> **23 Routinen** mit `loop` ab, und das ist keine Korpuslücke. **Es gibt keine Form**, in der
> eine Schleife sagt, was über ihr gilt — weder ein Wort noch eine Produktion.

```bash
$ grep -c 'invariant' beispiele/*.gab messung/*/*.gab | paste -sd+ | bc
18
$ grep -A3 'pub struct Traverse' crates/gabbro-syntax/src/ast.rs
      variable, gegenstand, domaene, abstieg, touches, rumpf, span
$ grep -A8 'pub struct Tabelle' crates/gabbro-syntax/src/ast.rs
      name, kapazitaet, hinterlegt, konstanten, slot, invarianten, …
```

**Die 18 Fundstellen sitzen alle an `table`-Deklarationen** und tragen `cost O(n) runs
offline`. `Traverse`, `Retry` und `Forever` haben kein solches Feld. *Ein Korpuseintrag hätte
also gar nicht geschrieben werden können.*

---

## 1. Was die Sprache schon trägt, und was nicht

| | |
|---|---|
| **das MASS** | trägt sie. `traverse … by consuming`/`… decreases e`, `retry … bounded 1024 ops`, `forever … per_pass bounded 60000 ops on_exceeded …`. Dazu `K008`/`K009` an der Rekursion. **Terminierung ist Sprachsache und steht.** |
| **die AUSSAGE** | trägt sie nicht. Was *über* der Schleife gilt — die Invariante — hat kein Wort. |

**Und genau darum kann ein Beweiser über den Ausgang einer Schleife nichts sagen.** Nicht,
weil sie nicht terminiert, sondern weil niemand hingeschrieben hat, was danach gilt.

---

## 2. Die drei Formen, beide Seiten je Form

### (a) Ein neues Wort — `traverse … loop_invariant P { … }`

| | |
|---|---|
| **dafür** | ein Wort, eine Aufgabe. Keine Doppelbelegung, keine Frage, wo es hingehört |
| **dagegen** | **der Wortschatz ist geschlossen**, und ein neues Wort kostet: `kw.rs`, die Tafel in `SYNTAX.md`, `pruefe-wortschatz.py`, `tests/wortschatz.rs`, die Terminalzählung. *Und es kostet einen zweiten Namen für einen Begriff, den die Sprache schon hat* |

### (b) `invariant` wiederverwenden — `traverse … invariant P { … }`

| | |
|---|---|
| **dafür** | **kein neues Wort, und `invariant` behält EINE Aufgabe:** *ein Prädikat, das durchgehend gilt.* An einer `table` durchgehend über ihre Lebenszeit, an einer Schleife durchgehend über ihre Durchläufe. **Derselbe Begriff, anderer Geltungsbereich** — nicht dieselbe Schreibweise für zwei Dinge |
| **dagegen** | ein Leser muss am Ort erkennen, worüber quantifiziert wird. *Das ist aber schon heute so:* eine Tabelleninvariante quantifiziert über Slots, ohne es zu schreiben |

### (c) `maintains` wiederverwenden — es steht schon an `fndecl`

| | |
|---|---|
| **dafür** | auch kein neues Wort |
| **dagegen** | **`maintains` nennt heute eine BENANNTE Tabelleninvariante**, keinen Ausdruck (`maintains baum_wohlgeformt`). An einer Schleife müsste es ein Prädikat nehmen — dieselbe Schreibweise für zwei verschiedene Argumentarten. *Das ist die Form, gegen die `VERFEINERUNG.md` §2(c) entschieden hat* |

---

## 3. Die Entscheidung: **(b)**, `invariant` an der Schleife

**Der Grund ist der Begriff, nicht der Preis.** `refines` bekam ein eigenes Wort, weil eine
Verfeinerungspflicht eine *neue* Aussage war, die es in der Sprache nicht gab. Eine
Schleifeninvariante ist keine neue Aussage — es ist **dieselbe** Aussage wie an einer Tabelle,
an einem anderen Ort.

> **Ein zweites Wort für einen vorhandenen Begriff ist teurer als eine zweite Fundstelle für
> ein vorhandenes Wort.** Der Wortschatz misst, wie viel eine Sprache *kann*; er soll nicht
> messen, an wie vielen Stellen sie dasselbe kann.

*Und der Präzedenzfall steht:* «C3a» `or <reason>` in der Signatur trägt den Vermerk
**„Kein neues Wort: `or` steht schon im Wortschatz."**

### Die Form

```ebnf
traverse = "traverse" ident [ "of" expr ] "over" domain "by" descent
           [ "touches" efflist ] [ "invariant" pred ] block
retry    = "retry" [ ident ] [ "until" pred ] "bounded" expr
           [ "progress" ident ] "on_exceeded" ident [ "effects" … ]
           [ "invariant" pred ] block
forever  = "forever" [ ident ] "per_pass" "bounded" expr "on_exceeded" ident
           "effects" efflist [ "progress" ident ] [ "leaves" identlist ]
           [ "invariant" pred ] block
```

**`invariant` steht unmittelbar vor dem Rumpf**, bei allen dreien — weil es das letzte ist,
was ein Leser braucht, bevor er den Rumpf liest, und weil eine feste Stelle bei drei Formen
billiger ist als drei Stellen.

---

## 4. Was das Wort NICHT fail-open lassen darf

**Eine Klausel, die niemand prüft, ist schlimmer als keine** — das ist wörtlich der Befund,
mit dem `beispiele/05` seine `lock BERICHT protects { … }` verloren hat (`H007`/`H008`).

Darum zweierlei, und beides ist gebaut:

1. **`M133`** — eine Schleifeninvariante muss mindestens einen Namen nennen. `invariant true`
   ist ein Versprechen über nichts und sieht aus wie eines über etwas.
2. **Sie wird GEZÄHLT.** `gabbro pflichten` führt sie als eigene Art `S`, genau wie `refines`
   die Art `R` bekam. *Eine Zusage, die in keinem Register steht, ist keine Schuld, sondern
   eine Behauptung.*

---

## 5. Was diese Entscheidung nicht kauft

**Eine Form ist keine Pflicht.** Sobald `invariant` an einer Schleife steht, stellt sich die
Frage, die der Rumpfkanal schon misst: kann er das Ziel schließen? Die Antwort hat zwei
Hälften, und beide sind Ertrag:

| | |
|---|---|
| er **schließt** es | die 23 `loop`-Absagen fallen, und die Schleifen des Korpus kommen an |
| er **sagt ab, mit Namen** | die Absage benennt, was eine Schleifensemantik zusätzlich liefern müsste — gemessen statt geschätzt |

*Was diese Entscheidung ausdrücklich nicht behauptet:* dass eine Schleifeninvariante damit
**bewiesen** wird. Sie stellt her, dass eine **entstehen** kann.
