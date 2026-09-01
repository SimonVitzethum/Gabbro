# Die Domänenregel, gerechnet — sie ersetzt VIER von neun Formen, nicht siebzehn Wörter

*Gemessen am 2026-09-01 über dem Stand `56455f9`, lokal (`free -g`: 31 GB gesamt, 9 GB
verfügbar, 20 Kerne). Werkzeuge: `instrumente/zaehle-wortschatz.py` (neu), der unveränderte
Prüfer `target/debug/gabbro`, und die Quellen selbst.*

`PLAN-HARDWARE.md` §12 und `PLAN.md` `OA2` tragen den Posten mit diesem Satz:

> **Eine Domäne als deklarierte Erreichbarkeit über einem Tabellenfeld, mit
> Wohlfundiertheitsnachweis an der Deklaration.** *Ein Wort statt siebzehn, ein parametrischer
> Absenkungssatz statt siebzehn einzelner.*

**Die Ratsche steht seit heute** (`instrumente/zaehle-wortschatz.py`, Marke 221), und eine
Regel, die siebzehn Wörter ablöst, wäre ihre beste denkbare Eröffnungsprobe. Deshalb ist die
Regel hier gegen sie gerechnet worden, **vor jedem Bau** — Regel A.

> **Das Ergebnis: der Posten ist richtig und seine Zahl ist es nicht.** Die Regel ist
> baubar, sie kostet vermutlich **null neue Wörter**, und sie löst **drei bis vier** ab —
> nicht siebzehn. *Der Ertrag liegt nicht im Wortschatz, sondern in der Schranke.*

---

## 1. Die siebzehn sind keine Messung

`§12` listet sechzehn Einträge und nennt sie siebzehn (`ancestors of` und `descendants of`
sind je zwei Wörter). **Sie sind nicht die Wörter der Domänenproduktion.** Die Produktion
`domain` in `SYNTAX.md`:696–707 nennt **elf** Terminale:

```
slots · of · chain · in · descendants · ancestors · queue · fields · elems · threads · mappings
```

Die Liste in §12 enthält **acht Wörter, die nicht darin stehen** (`child`, `parent`,
`sibling`, `tree`, `observed`, `occupied`, `reaches`, `levels`) und **verliert zwei, die
darin stehen** (`fields`, `in`).

**`of` und `in` können ohnehin nicht fallen:** `in` steht in **9** EBNF-Regeln, `of` in
mehreren; sie sind die weitesten Wörter der Sprache nach `pub`. Damit ist die tatsächliche
Ablösemasse der Domänenproduktion **neun Wörter**, nicht siebzehn.

---

## 2. Nur VIER der neun Formen sind erklärte Erreichbarkeit

Je Form gefragt: *ist sie ein Weg über ein Feld einer Tabelle?* Die Schranke daneben ist
aus `crates/gabbro-check/src/domaene.rs::domaenenschranke` abgelesen, nicht behauptet.

| # | Form | was sie ist | Erreichbarkeit? | Schranke heute | Korpus |
|---|---|---|---|---|---|
| 1 | `slots of <ort>` | der Indexraum `0 .. count` | **nein** | `count` der Tabelle | 43 |
| 2 | `chain(a, b) in <ort>` | Kette über Feld `b`, Start Feld `a` | **JA** | **keine** | 8 |
| 3 | `descendants of <ort>` | Weg über `child`/`sibling` | **JA** | `count` der Tabelle | 12 |
| 4 | `ancestors of <ort>` | Weg über `parent` | **JA** | `count` der Tabelle | 10 |
| 5 | `queue <ort>` | Ringpuffer über Kopf/Schwanz | **nein** — modularer Nachfolger | Länge des einzigen Feldarrays | 10 |
| 6 | `fields of <pfad>` | statische Feldliste eines `format` | **nein** — keine Laufzeitdomäne | **keine** | 3 |
| 7 | `elems of <ort>` | Elemente eines Feldarrays | **nein** — Indexbereich | Länge im Typ | 10 |
| 8 | `threads` | die laufenden Fäden | **nein** — Aussage über die MASCHINE | **keine** | 7 |
| 9 | `mappings of <ort>` | Blattmenge eines `walk` | **JA**, über Ebenen | aus der `walk`-Deklaration | 10 |

*Korpusstellen über 160 saubere `.gab` (`beispiele/*.gab` + `messung/**/*.gab`, ohne
`gift/`), Wortgrenzenabgleich ohne Kommentarzeilen.*

**113 Domänenstellen, davon 40 (35 %) in den vier ersetzbaren Formen und 73 (65 %) in den
fünf, die die Regel nicht erreicht.** Und die fünf sind nicht ein Rest, sondern **drei
verschiedene Dinge**: zwei Indexbereiche (`slots of`, `elems of` — zusammen 53 Stellen, die
meistbenutzte Form überhaupt), eine statische Liste (`fields of`) und eine Maschinenaussage
(`threads`).

> **Eine Regel, die 35 % der Stellen ersetzt, ist kein „ein Wort statt siebzehn".** Sie ist
> eine Vereinheitlichung von drei bis vier verwandten Formen — was gut ist, und was etwas
> anderes ist.

---

## 3. Die vier Baumkantenwörter können NICHT fallen — und das ist gemessen

§12 zählt `tree`, `parent`, `child`, `sibling` zu den siebzehn. Sie tragen aber mehr als die
Domänen:

| Leser | Stelle | wozu |
|---|---|---|
| `opsruf.rs:244` | `t.baum…elter` | die Vorbedingung am **Rufort** einer erzeugten `ops`-Operation |
| `emit.rs:2488`, `:2613` | `t.baum…elter` | der **Erzeuger für `relabel`** — `t->slots[s].elter = p;` |
| `kbedingung.rs:693` | `baumkanten()` | `T001`–`T003`, die Prüfung der Kante selbst |
| `emit.rs:6803`, `:6898` | `u.baeume` | `ancestors of` / `descendants of` |

**`Table_Ops_Erhaltung.thy` und `Absenkung_Parametrisch.thy` beweisen über genau dieser
Kante.** Wer `tree { parent … }` streicht, streicht die Voraussetzung des einzigen
Absenkungssatzes im Baum. *Die vier Wörter sind nicht Domänenwortschatz, sie sind
Strukturdeklaration — «B41b» hat das am 2026-08-20 ausdrücklich so entschieden: „die Kante ist
eine Eigenschaft der STRUKTUR, nicht des Durchlaufs".*

---

## 4. Die Regel kostet vermutlich NULL neue Wörter — und das ist der eigentliche Fund

**Gabbro hat die deklarierte Erreichbarkeit schon. Als Prädikat.**

```ebnf
reach = place "reaches" place "via" ident ;          (* SYNTAX.md:709 *)
```

```gabbro
forall s in slots of Self : Self.slots[s] reaches WURZEL via elter;   -- beispiele/01:78
requires o.slots[p] reaches WURZEL via elter,
         !(o.slots[p] reaches o.slots[s] via elter)                   -- beispiele/47:201
```

`reaches` und `via` stehen **im Wortschatz** (`kw.rs`:364 und :309, beide `res`), der Prüfer
liest sie an fünf Stellen (`PredArt::Erreicht` in `gruppe.rs`, `opsruf.rs` ×2, `lib.rs`,
`refinement.rs`), und `beispiele/47` benutzt sie für genau die Aussage, für die es sonst
`ancestors of` bräuchte — die Datei sagt es selbst:

> *„Und genau darum steht hier `!(… reaches …)` und nicht `forall a in ancestors of … : a != s`"*
> (`beispiele/47-ops-wortmenge.gab`:194)

**§12s Vorschlag ist damit nicht, etwas Neues zu erfinden, sondern eine vorhandene Form aus
der Prädikat- in die Domänenseite zu heben:**

```ebnf
domain = … | "reaches" place "via" identlist ;
```

Ein Alternativzweig, drei vorhandene Wörter, **null neue.** Er löst ab:

| fällt | weil |
|---|---|
| `chain` | `chain(a, b) in p` ist `reaches p via a, b` |
| `descendants` | `descendants of p` ist `reaches p via child, sibling` |
| `ancestors` | `ancestors of p` ist `reaches p via parent` |

**Drei Wörter: 221 → 218.** `mappings of` bliebe: seine Domäne ist die *Blattmenge* eines
`walk`, und die Ebenenzahl ist keine Feldkante — *das ist nachzumessen und hier nicht
entschieden.* Fiele es mit, wären es vier: 221 → 217.

> **Und die Gegenzahl hält.** Der Wortschatz verlöre drei; die Stellungen fielen von 333 auf
> **332** (`reaches` und `via` bekämen je eine dazu, `chain`/`descendants`/`ancestors`
> verschwänden mit je einer). **332 auf 219 Terminale sind 1,52 je Terminal gegen heute 1,50.**
> *Genau die Gestalt, in der der Handel einer ist* — dieselbe wie beim Fall von `decreasing`
> heute: der Nenner fällt schneller als die Summe.

---

## 5. Der Absenkungssatz: es gibt keine siebzehn, die abzulösen wären

§12: *„ein parametrischer Absenkungssatz statt siebzehn einzelner."*

**Nachgezählt: es gibt EINEN Absenkungssatz im ganzen Baum** (`Absenkung_Parametrisch.thy`),
und er handelt von `ops relabel`, nicht von einer Domäne. **Über keiner der neun Domänen steht
ein Absenkungssatz.** Die siebzehn, die abzulösen wären, existieren nicht.

> **Die Bewegung ist also 0 → 1, nicht 17 → 1.** Das ist ein Gewinn und keine Einsparung —
> und der Unterschied ist genau der zwischen *„die Regel spart Beweisarbeit"* und *„die Regel
> ermöglicht Beweisarbeit, die es heute nicht gibt"*. Die zweite Lesart ist die wahre, und sie
> ist die bessere Begründung.

*Der Absenkungssatz hätte auch einen Gegenstand:* `zeugnis.rs`s `EINORDNUNG` führt heute
**neun** Begründungen je Domäne, drei davon lauten *„die Deklaration gibt KEINE Länge her"*.
Eine parametrische Schranke über `reaches … via` würde drei Prosabegründungen durch einen Satz
ersetzen — und die vorhandene Begründung von `ancestors of` ist bereits die parametrische:

> *„eine aufsteigende Kette kann ohne Zyklus nicht länger sein, als die Tabelle Slots hat.
> Die Abwesenheit dieses Zyklus ist die Hypothese der Tabelle."*

**Derselbe Satz trägt `chain(…) in` — und dort steht heute `None`.**

---

## 6. Der Nebeneffekt `mappings of` ist echt, und er ist SCHÄRFER als beschrieben

§12: *„`mappings of` bekommt seine Schranke aus derselben Regel statt aus dem Kostenpass."*

Gemessen: `domaenenschranke` hat **genau einen Aufrufer** — `kosten.rs`:665. (`zeugnis.rs`
zitiert sie nur im Bericht.)

> **Also wird die Schranke einer Domäne nur dort erhoben, wo eine `costs`-Zeile die Frage
> erzwingt.** Ein `forall x in mappings of w : …` in einer Funktion ohne `costs` läuft über
> eine Domäne, deren Schranke niemand ansieht.

`domaene.rs` sagt es an einer anderen Domäne selbst, mit Datum:

> *„Der Fall stand nie auf: `unberuehrt` trägt keine `costs`-Zeile, also fragte der Kostenpass
> nie. **Erst der Zähler hat ihn ausgelöst.**"*

**Ein Wohlfundiertheitsnachweis an der Deklaration verlegt die Schranke von „wird gefragt,
wenn `costs` dasteht" nach „steht fest, sobald die Domäne deklariert ist".** Das ist mehr wert
als drei Wörter — *und es ist die Begründung, mit der die Regel sich gegen die Ratsche
rechtfertigt.* Nicht der Wortschatz trägt den Posten, sondern die Schranke.

---

## 7. Was an §12 überholt ist

> *„Es ist kein Zufall, dass `zeugnis.rs:758` als einzige Stelle fünf Fälle hatte"*

**Diese Stelle gibt es nicht mehr.** Seit `e5e555d` (2026-08-31) führt `traversenausweis`
neun einzelne Zweige (`zeugnis.rs`:515–526) und `EINORDNUNG` neun Begründungen; der
Kommentar darüber nennt den Grund wörtlich: *„a certificate that vouches for two different
programs vouches for neither."* **§6 und §12 sind dieselbe Sache von zwei Seiten — und §6 ist
eingelöst.** Was von der Begründung bleibt, ist die andere Hälfte: *drei Domänen ruhen auf gar
keiner Schranke*, und das steht jetzt je Form im Zeugnis statt hinter einer Wildcard.

---

## 8. Die Rechnung, in einer Tafel

| | §12 behauptet | gemessen |
|---|---|---|
| Wörter, die fallen | 17 | **3** (`chain`, `descendants`, `ancestors`), evtl. 4 mit `mappings` |
| Wörter, die dazukommen | 1 | **0** — `reaches`, `via` stehen schon, als Prädikat |
| Formen, die die Regel ersetzt | alle | **4 von 9** — 40 von 113 Korpusstellen |
| Absenkungssätze, die zusammenfallen | 17 → 1 | **0 → 1** |
| `zeugnis.rs:758` | fünf Fälle unter einer Wildcard | **seit `e5e555d` neun Zweige** |
| `mappings of`-Schranke | „aus dem Kostenpass" | **richtig, und schärfer:** der Kostenpass ist ihr EINZIGER Leser |

> **Urteil: bauen — aber mit der richtigen Begründung.** Die Regel rechtfertigt sich nicht
> über den Wortschatz (drei von 221, 1,4 %), sondern über die **Schranke**: sie macht die
> Terminierung von `chain(…) in` zum ersten Mal deklarativ und nimmt sie bei allen dreien aus
> der Abhängigkeit von einer `costs`-Zeile. *Das ist ein Beweisargument und kein Zählargument
> — und die Ratsche hat es genau deshalb erzwungen.*

**Nicht gebaut, und der Grund ist Regel A plus die Bahngrenze.** Der Eingriff läge zu je
einem Drittel in `gabbro-syntax/` (meins), `gabbro-check/` (zweite Bahn: `domaene.rs`,
`kosten.rs`, `emit.rs`, `zeugnis.rs`, `opsruf.rs`) und im Korpus: **30 Stellen in 13 sauberen
Dateien, dazu 11 Stellen in 10 Giftproben — 41 in 23.** *Der Fall `decreasing` heute war 11
Korpusstellen in 11 Dateien und 4 Prüferstellen; dieser ist das Vierfache und trifft den
ERZEUGER, nicht nur seine Leser.*

---

## 9. Was ungemessen bleibt

* **Ob `reaches place via ident` als Domäne parsbar ist, ohne die Prädikatform mehrdeutig zu
  machen.** `member = expr "in" domain` und `reach = place "reaches" place "via" ident` stehen
  beide unter `pred`; ein `x in reaches p via f` ist ein Vorschlag und kein Grammatiklauf.
* **Ob `mappings of` mitfällt.** Die Blattmenge eines `walk` ist eine Erreichbarkeit über
  Ebenen, und ob `via` eine Ebene benennen kann, ist nicht gemessen.
* **Der Wohlfundiertheitsnachweis selbst.** Dass die Zyklenfreiheit die Hypothese der Tabelle
  ist, steht als Prosa in `zeugnis.rs`; **kein Isabelle-Satz sagt es.** Der parametrische
  Satz ist der Bau, nicht die Rechnung — und er ist der teure Teil.
* **Ob `queue` doch mitkann.** Ein Ringpuffer ist ein modularer Nachfolger; ob das eine
  „Kante" im selben Sinn ist, entscheidet, ob aus vier Formen fünf werden. Nicht gemessen.
* **Die Korpusstellenzahl ist ein Wortgrenzenabgleich**, kein Parserlauf: `queue` als
  Feldname zählt hier wie `queue` als Domäne (W10, obere Schranke).
