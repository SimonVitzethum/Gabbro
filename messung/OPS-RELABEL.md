# `relabel` bekommt eine Bedingung statt eines Verbots — und die Form stand schon da

*Entschieden am 2026-08-28, abends. Jede Zahl nennt den Befehl, der sie nachrechnet.*

> **Der Befund zuerst, und er ist zum dritten Mal derselbe.** `ops` hat eine GESCHLOSSENE
> Wortmenge — `insert | remove | relabel`. Seit dem Vormittag erzeugt `emit.rs::ops` Rümpfe
> für zwei davon. Das dritte sagte der Erzeuger ab, mit Satznamen:
>
> ```text
> Fehler: [C001] no lowering: `ops relabel` -- beweise/Table_Ops_Erhaltung.thy proves
>                `umhaengen_faellt` … A generated `relabel` would owe a condition nobody
>                has written down
> ```
>
> **Damit stand `relabel` als Wort einer geschlossenen Menge da, das nichts erzeugt und
> niemand rufen kann — eine Klausel ohne Einlöser.** Genau die Stellung, die `ensures` am
> Zeigertyp gekostet hat (`N037`) und `beispiele/05` seine `protects`-Klausel (`H007`/`H008`).
> *Und der Bedarf ist gemessen: 127 Korpusstellen (`umhaengen`, `kernel/` + `mm/`,
> 2026-08-19). „Kein gemessener Bedarf" war hier nie der Ausweg.*

Die Absage war nicht falsch. Sie war **unvollständig**: sie sagte, dass das Umhängen fällt,
und nicht, **woran**.

---

## 1. Der Beweis kam zuerst — K100s zweites Tor, wörtlich befolgt

`verbund.konstruktor` hat den Präzedenzfall gebucht (`DONE.md`): *„der Beweis kam zuerst"*,
weil das Bauen sonst die verbotene Bewegung ENTWORFEN → GETRAGEN ohne Beweis gewesen wäre.
Hier ebenso. `beweise/Table_Ops_Erhaltung.thy` trägt seit heute Abend:

| Satz | Aussage |
|---|---|
| `ueber` (induktiv) | `s` liegt auf `x`s Elternkette, **`x` selbst eingeschlossen** |
| `U-1` `umhaengen_ausserhalb` | eine Kette, die `s` nicht berührt, überlebt das Umhängen |
| `U-2` `umhaengen_durch_s` | wer `s` erreicht, kommt hinterher über `s` weiter |
| **`U-3` `umhaengen_erhaelt`** | **`wohlgeformt σ` ∧ `erreicht σ p` ∧ `¬ ueber σ p s` ⟹ `wohlgeformt (umhaengen σ s p)`** |
| `G-1` `gegenbeispiel_erfuellt_die_alten` | `wohlgeformt zwei ∧ erreicht zwei 1` |
| `G-2` `gegenbeispiel_verletzt_die_neue` | `ueber zwei 1 0` |

```bash
rsync -a beweise/ ki-pc-fisch-101:gabbro-r-beweise/
ssh ki-pc-fisch-101 'cd gabbro-r-beweise && ~/Isabelle2025-2/bin/isabelle build -D . -o threads=12'
# Finished Gabbro (0:00:05 elapsed time, 0:00:23 cpu time, factor 4.09)
```

**`umhaengen_faellt` bleibt stehen, und `G-1`/`G-2` sagen, wozu.** Das Gegenbeispiel erfüllt
die ersten zwei Voraussetzungen von `U-3` und verletzt **genau die dritte**. *Ein Satz, dessen
Voraussetzung nie verletzt sein kann, ist eine Zierde; dieser hat seine Bruchstelle gemessen.*

### Was am vorgeschlagenen Zuschnitt NICHT trug

Der Auftrag schlug vier Voraussetzungen vor; **`σ s = Some sl` ist entbehrlich.** `umhaengen`
SETZT den Platz — auf einem freien `s` ist es dasselbe wie `einfuegen`. Der Satz steht ohne
sie; die vorgeschlagene Fassung steht als `corollary umhaengen_erhaelt_am_belegten_platz`
daneben und fällt aus der bewiesenen heraus.

*Und ein zweiter Anlauf ist an der Beweistechnik gescheitert, nicht am Zuschnitt:* die
naheliegende Zerlegung („`ueber` bleibt beim Umhängen erhalten" + „Erreichbarkeit wandert die
Kette abwärts") gibt `s` **zwei Rollen** — Induktionsargument und Ergebnisparameter — und
`induct` verallgemeinert dann nur `x`. `U-2` in der jetzigen Fassung braucht `ueber`
überhaupt nicht.

---

## 2. Was gemessen wurde, BEVOR entschieden wurde (W24)

**W24 sagt: schreib die naheliegende Form hin und lass sie durch den UNVERÄNDERTEN Prüfer
laufen.** Getan, mit beiden Kandidaten in einer Datei, gegen `master` ohne eine Zeile
Änderung:

```gabbro
impl fn form_a(o : ptr<normal, rw> Ordner, s : index into Ordner, p : index into Ordner)
    requires !(o.slots[p] reaches o.slots[s] via elter)          -- (a)

impl fn form_b(o : ptr<normal, rw> Ordner, s : index into Ordner, p : index into Ordner)
    requires p != s, forall a in ancestors of o.slots[p] : a != s -- (b)
```

```text
Fehler: [D001] `form_a` writes `Ordner` by hand although the table declares `ops`
Fehler: [D001] `form_b` writes `Ordner` by hand although the table declares `ops`
5 Items, 2 Fehler, 0 Hinweise
  M1 saw 7 expressions, 0 of them without a type (100 % coverage)
```

> **BEIDE Formen parsen und typen heute schon. Kein `P00x`, kein `M1`-Loch.** Die zwei Fehler
> sind `D001` am RUMPF — die Handmutation, gegen die es `relabel` überhaupt geben soll.

Und die Rufform ebenso, mit demselben Ergebnis wie am Nachmittag bei `insert`:

```text
Fehler:  [K003] `form_a` promises costs, but `relabel` is not declared here
Hinweis: [E009] the call effects of `form_a` are undecidable: `Ordner::relabel` is unknown
```

**Vierte Instanz, gleiche Stelle, gleiche Antwort: gefehlt hat nicht die Form, sondern der
GERUFENE.** (Nach «B35», dem `transition`-Graphen und `OPS-RUFFORM.md` §1.)

---

## 3. Die drei Formen, beide Seiten je Form

### (a) `!(t.slots[p] reaches t.slots[s] via elter)` — die Negation eines `reaches` mit benanntem Ziel

| | |
|---|---|
| **dafür** | **EINE Klausel, und sie ist `¬ ueber σ p s` Zeichen für Zeichen.** `reaches` ist reflexiv-transitiv gemeint — die Invariante `forall s in slots of c : c.slots[s] reaches WURZEL via elter` gilt auch von der Wurzel selbst — und genau das ist `ueber`. Kein Wort, keine Produktion, keine Zeile Grammatik |
| **dagegen** | **die erste NEGIERTE Voraussetzung, die `D012` liest.** `aus_pred` kannte bis heute nur `Nicht(Vergleich) → Frei`; jetzt kommt `Nicht(Erreicht)` dazu. Und `reaches` trägt hier ein *bestimmtes* Ziel, während `Forderung::Erreichbar` das Ziel absichtlich ignoriert (*„die Wurzel wählt der Rufer"*) — zwei Lesarten desselben Wortes an derselben Regel, und der Unterschied muss dastehen |

### (b) `p != s, forall a in ancestors of t.slots[p] : a != s` — der Allquantor über der Vorfahrendomäne

| | |
|---|---|
| **dafür** | dieselbe Bauart wie die Blattheit von `remove` (`forall x in slots of t : …`), also eine Form, die `D012` schon liest (`blattform`). `ancestors of` ist seit «B41» eine gemessene Domäne |
| **dagegen** | **ZWEI Klauseln, und die zweite ist genau die, die ein sorgfältiger Leser vergisst.** `ancestors of` ist STRIKT — der Erzeuger schreibt es wörtlich ins C: *„A node is not its own ancestor, so the chain starts at the PARENT"*. Wer `p != s` weglässt, hat eine Voraussetzung, die den Fall `relabel(t, s, s)` durchlässt: **die Schlinge, und die bricht `wohlgeformt` genauso wie der Zweislotzyklus.** *Fail-open an der einen Stelle, an der der Satz der ganze Ertrag ist* — dieselbe Klasse wie das schwächere `ist_blatt` aus `beispiele/01` |

### (c) Ein eigenes Wort — `notunder p, s` o. ä.

| | |
|---|---|
| **dafür** | eine Klausel, die genau eine Sache sagt, und kein Leser muss `reaches` zweimal lesen |
| **dagegen** | **`SCHLEIFENINVARIANTE.md`, wörtlich:** *„ein zweites Wort für einen vorhandenen Begriff ist teurer als eine zweite Fundstelle für ein vorhandenes Wort."* Und hier trägt ein vorhandenes Wort den Begriff — anders als bei `occupied`, wo elf Korpusnamen belegten, dass keines ihn trug. `kw.rs`, `SYNTAX.md`, `pruefe-wortschatz.py`, `tests/wortschatz.rs`, die Terminalzählung: alles für etwas, das (a) heute schon sagt |

---

## 4. Die Entscheidung: **(a)**

**Und die Reflexivität ist der Ausschlag, nicht die Klauselzahl.** (b) ist nicht bloß
umständlicher, es ist an einer Stelle *anders*: `ancestors of` schneidet den Knoten selbst
weg, `ueber` schließt ihn ein. Eine Form, die die Schlinge nur über eine ZWEITE, leicht
vergessene Klausel abdeckt, ist an der gefährlichsten Stelle die schwächere.

> Das ist derselbe Grund, aus dem `D012` beim Löschen die Blattheit des SATZES verlangt
> (`forall x in slots of t : t.slots[x].elter != Some(s)`) und nicht die schwächere
> Kindliste von `beispiele/01`.

### Die Voraussetzungen, die `relabel` seinem Rufer schuldet

```text
requires t.slots[p] reaches <root> via <parent>          -- erreicht σ p
requires !(t.slots[p] reaches t.slots[s] via <parent>)   -- ¬ ueber σ p s
```

Beide gehen durch `opsruf.rs::koepfe` — **ein Erzeuger, fünf Leser**, wie die anderen zwei
Operationen. `D012` hält sie an jeder Aufrufstelle.

**Und das ZIEL des zweiten `reaches` wird streng gelesen, das des ersten nicht** — das ist
kein Versehen, sondern der Unterschied der beiden Sätze. `erreicht σ p` meint *eine* Wurzel,
also wählt der Rufer sie; `¬ ueber σ p s` meint genau `s`. Vier Giftproben messen es:

| Probe | was sie schreibt | Kennung |
|---|---|---|
| `331` | die Kettenbedingung fehlt ganz | `D012` |
| `332` | die STRIKTE Fassung über `ancestors of` | `D012` |
| `333` | `ops relabel` ohne `parent`-Kante | `C001` |
| `334` | die Kettenbedingung über einem ANDEREN Zielplatz | `D012` |

*W23: diese vier zählen in die Trefferzählung und in keine Bedarfsmessung.*

---

## 5. Was NICHT gefordert wird, und beides ist eine Aussage

**1. Keine Belegtheit von `s`.** `U-3` verlangt sie nicht, und der Ertrag ist gemessen: der
erzeugte Rumpf schreibt `t->slots[s].<parent> = p;` und **sonst nichts**. Auf einem freien
`s` bleibt die Belegung frei — der C-Zustand hat damit *weniger* belegte Plätze als der
Modellzustand, und `wohlgeformt` ist ein `∀` über den belegten. **Ein Allsatz über eine
kleinere Menge fällt nicht.** Eine erfundene Belegtheitsklausel hätte strenger ausgesehen und
weniger bedeutet — derselbe Satz, den `remove` an der Tabelle ohne `parent`-Kante trägt.

**2. Keine Erzeugung ohne `parent`-Kante.** Eine `table … ops relabel` ohne
`tree { parent … }` hat kein Feld, an dem umgehängt werden könnte. Der Erzeuger sagt es mit
`C001` ab, statt ein Feld zu raten. *«B41b», wörtlich: eine fehlende Kante ist eine ANTWORT,
keine Lücke.*

---

## 6. Was diese Entscheidung nicht kauft

**Die Absenkung ist weiter unbewiesen.** Dass `t->slots[s].<parent> = p;` die Funktion
`umhaengen` aus dem Modell IST, steht in keinem Satz — dieselbe Lücke, die
`Table_Absenkung.thy` mit eigenen Worten nennt und die `insert`/`remove` seit heute Vormittag
tragen. Was sich geändert hat: die Menge der emittierten Operationen und die Menge der
bewiesenen sind wieder dieselbe Menge — **jetzt mit drei Elementen statt zwei.**
