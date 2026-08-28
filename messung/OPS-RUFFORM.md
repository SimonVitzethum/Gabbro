# Die Rufform für eine erzeugte Operation — und die Voraussetzungen kommen an

*Entschieden am 2026-08-28, nachmittags. Jede Zahl nennt den Befehl, der sie nachrechnet.*

> **Der Befund zuerst, und er ist derselbe Satz wie heute Morgen, eine Ebene höher.**
> `messung/OPS-ERZEUGER.md` §1 hat den Erzeuger gegen diese Stellung gebaut: *„das ist die
> eine Stellung, in der ein Konstrukt schlechter ist als keines"* — `D001` verbietet ab `ops`
> jede Handmutation, und an ihre Stelle tritt nichts. **Am Vormittag trat der Erzeuger an
> ihre Stelle. Und niemand konnte ihn rufen.**

```bash
$ grep -c '__attribute__((unused))' <(./target/debug/gabbro emit beispiele/47-ops-wortmenge.gab)
# vor diesem Auftrag: die erzeugten Operationen trugen es, JEDE
```

Der Emissionswächter hat es erzwungen: `cc -Werror=unused-function` sagt über eine `static`
Funktion, die in ihrer Übersetzungseinheit niemand ruft, die Wahrheit. **Das Attribut war
nicht der Fehler, sondern seine sichtbare Form** — *ein Verbot mit einem Ersatz, den niemand
erreicht.*

**Und die zweite Hälfte war die teurere.** `einfuegen_erhaelt` verlangt zwei Dinge vom Rufer,
`blatt_loeschen_erhaelt` eines. Der Erzeuger schrieb sie als **Kommentar** ins C:

```c
/* The caller owes the theorem's two premises, and M1 holds them at the
   call site: the slot is FRESH (`sigma n = None`) … */
```

M1 hielt gar nichts — es gab keine Aufrufstelle. *Ein Kommentar, der behauptet, ein Pass
prüfe etwas, ist die Klasse, gegen die dieser Ordner `H007`/`H008` gebaut hat.*

---

## 1. Was gemessen wurde, BEVOR entschieden wurde

**Die Rufform stand schon in der Grammatik.** Das ist keine Vermutung; die Datei ist durch den
Prüfer gelaufen, bevor eine Zeile Entwurf geschrieben war:

```gabbro
impl fn belegen(v : ptr<normal, rw> Verzeichnis, i : index into Verzeichnis) … {
    Verzeichnis::insert(v, i);
}
```

```text
Hinweis: [E009] the call effects of `belegen` are undecidable:
                `Verzeichnis::insert` is unknown to the graph
Fehler:  [K003] `belegen` promises costs, but `insert` is not declared here
```

**Kein `P00x`.** Der Parser hat es gelesen: `path = pathseg { "::" pathseg }`, und
`parse.rs::erwarte_feldname` nimmt hinter einem `::` jedes Wortschatzwort an — seit jeher, und
die EBNF sagte es nicht.

> **Gefehlt hat nicht die Rufform, sondern der GERUFENE.** Dieselbe Bauart wie «B35» (`Some`
> parste als gewöhnlicher Aufruf) und wie der `transition` (der Graph meldete
> `uebersetzung_an ist unbekannt` und es war *„eine Lücke im GRAPHEN, nicht im Programm"*).
> **Dritte Instanz, gleiche Stelle, gleiche Antwort.**

---

## 2. Die drei Formen, beide Seiten je Form

### (a) Eine eigene ANWEISUNG — `insert v.slots[n] under p;`

| | |
|---|---|
| **dafür** | liest wie der Beweis (`einfuegen σ n p`), und `insert`/`remove` sind reservierte Wörter — die Anweisung kann sie tragen, ohne dass der Wortschatz wächst |
| **dagegen** | **`under` gibt es nicht**, also wächst er doch (`kw.rs`, die Tafel in `SYNTAX.md`, `pruefe-wortschatz.py`, `tests/wortschatz.rs`, die Terminalzählung). Dazu eine neue `StmtArt`, und die ist an **30 Fundstellen** ein Übersetzungsfehler (`grep -c 'StmtArt::Ruf' crates/gabbro-check/src/*.rs`) — jede davon müsste die Wirkungs-, Kosten-, Sperr- und Phasenfrage für die neue Form **einzeln** beantworten. *Ein Ruf beantwortet sie einmal.* |

### (b) Ein Ruf über den TRÄGER — `v->insert(n, p);`

| | |
|---|---|
| **dafür** | kein neues Wort, keine neue Produktion: «B8» hat `call = ( path \| place ) "(" … ")"` schon gebaut, und `t->senden(b)` steht im Korpus |
| **dagegen** | **`CallTarget::Place` heißt in diesem Prüfer: der Gerufene ist zur Übersetzungszeit NICHT bekannt.** Der Kommentar an der Variante sagt es wörtlich. Eine erzeugte Operation ist das Gegenteil davon — sie ist statisch bekannt, sie hat einen Kopf, sie hat Kosten. Über einen `place` gerufen bräuchte sie einen `fn(…)`-Vertrag am Ort, den niemand schreibt, und der Kosten- wie der Wirkungspass läsen sie als Kante ins Unbekannte. *Die Form wäre da und die Aussage weg.* |

### (c) Ein Ruf über den TRÄGERTYP — `Verzeichnis::insert(v, n, p);`

| | |
|---|---|
| **dafür** | **kein neues Wort, keine neue Produktion, keine neue Anweisungsart — und der Gerufene ist ein `CallTarget::Path`, also statisch bekannt.** Damit fällt er in *jede* vorhandene Maschinerie: `Umgebung::funktionen` gibt ihm eine Signatur, der Aufrufgraph einen Knoten mit `writes t.slots`, `kosten.rs` eine Zahl. Und die C-Absenkung ist eins zu eins: `Verzeichnis_insert(v, n)` heißt die Funktion dort ohnehin |
| **dagegen** | ein Pfadsegment, das ein Wortschatzwort ist, sieht auf den ersten Blick nach einer Ausnahme aus. **Ist aber keine** — `u64::max` steht seit «G5» genauso da. Und die EBNF muss richtiggestellt werden: `pathseg` nannte diesen Fall nicht, obwohl der Parser ihn seit jeher liest |

---

## 3. Die Entscheidung: **(c)**

**Der Grund ist derselbe Grundsatz wie bei der Schleifeninvariante, an einem anderen
Gegenstand.** Dort hieß er: *„ein zweites Wort für einen vorhandenen Begriff ist teurer als
eine zweite Fundstelle für ein vorhandenes Wort."* Hier heißt er:

> **Eine zweite Form für einen vorhandenen Vorgang ist teurer als ein zweiter Gerufener für
> eine vorhandene Form.** Ein Ruf ist ein Ruf. Was eine erzeugte Operation von einer
> geschriebenen unterscheidet, ist nicht, WIE man sie ruft, sondern **wer ihren Rumpf
> schreibt** — und das steht in der `table`-Deklaration, wo es hingehört.

Die Zahl dahinter ist die 30: dreißig Fundstellen behandeln `StmtArt::Ruf` heute schon, und
Form (a) hätte jede einzelne zu einer offenen Frage gemacht. *Das ist keine Bequemlichkeit,
sondern dieselbe Amortisation, auf der Zuschnitt (c) des Erzeugers ruht.*

### Die Form

```ebnf
pathseg = ident | "u8" | … | "i64" | opname ;
```

```gabbro
T::insert(t, n)        -- Tabelle ohne `tree`
T::insert(t, n, p)     -- Tabelle mit `tree { parent … }`
T::remove(t, s)
```

**`relabel` bekommt keine Rufform**, weil es keinen Rumpf bekommt (`umhaengen_faellt`). *Eine
Rufform für eine Operation, die nie emittiert wird, wäre dasselbe Loch eine Ebene höher.*

---

## 4. Der eigentliche Ertrag: **`D012`**, und warum nicht `M115`

Die Rufform allein wäre Ergonomie. Der Auftrag war die andere Hälfte: **die Voraussetzungen
des Beweises müssen an der Aufrufstelle ankommen.**

### 4.1 Was der Beweis verlangt, und was Gabbro davon sagen kann

| Satz | Voraussetzung | in Gabbro |
|---|---|---|
| `einfuegen_erhaelt` | `σ n = None` | `!t.slots[n].<occupied>` — und `occupied` ist genau darum heute Morgen entstanden |
| `einfuegen_erhaelt` | `erreicht σ p` | `t.slots[p] reaches <wurzel> via <parent>` — `PredArt::Erreicht`, seit jeher in der Sprache |
| `blatt_loeschen_erhaelt` | `blatt σ s` | `forall x in slots of t : t.slots[x].<parent> != Some(s)` |

**Die WURZEL wählt der Rufer, nicht die Deklaration.** `erreicht` im Beweis ist die
Erreichbarkeit *einer* Wurzel; welcher Platz sie spielt, steht in der
Erreichbarkeitsinvariante der Tabelle (`beispiele/01`: `reaches WURZEL via elter`) und nicht
in der `tree`-Zeile. *Eine bestimmte Wurzel hier zu verlangen wäre eine Behauptung, die der
Satz nicht macht* — und ein Grund gewesen, `insert` an Bäumen ganz abzusagen, den es nicht
gibt.

**Und die Blattheit steht als `forall` da und nicht als `t.slots[s].<child> == None`.**
`beispiele/01` schreibt letzteres von Hand (`ist_blatt`), und es ist **schwächer**: es gilt
auch von einem Platz, dessen Kindliste von den Elternzeigern abgewandert ist. *Eine
schwächere Voraussetzung als die des Satzes ist fail-open genau dort, wo der Satz der ganze
Ertrag ist.* Die Gegenprobe ist `beispiele/gift/324`.

### 4.2 Warum `M115` hier schweigt, und die Regel deshalb woanders steht

`M115` ist die **schwache** Lesart einer Vorbedingung, und sie sagt es selbst:

> *„Diese Regel weist ab, wo der Bereich des Arguments die Bedingung AUSSCHLIESST, und
> schweigt sonst."* Gedeckt ist die Form `<parameter> <op> <zahl>`.

**Keine der drei Voraussetzungen ist eine Bereichsaussage.** Sie in `Signatur::requires`
einzutragen hieße, eine Klausel in eine Karte zu legen, deren Leser sie nicht lesen kann —
und dann stünde sie da und prüfte nichts. *Genau die Bewegung, die `beispiele/05` seine
`lock … protects`-Klausel gekostet hat.*

### 4.3 Was `D012` stattdessen fragt

> **Steht die Voraussetzung irgendwo ÜBER diesem Ruf?**

Drei Orte zählen, und es sind die drei, an denen diese Sprache eine Tatsache aufschreibt, die
dort gilt, wo der Ruf steht:

| Ort | warum er zählt |
|---|---|
| das eigene `requires` der Routine | die Pflicht wandert einen Rahmen nach außen, und `gabbro pflichten` bucht sie dort als `V` |
| die Bedingung eines umgebenden `if` | der Zweig wird nur betreten, wenn sie gilt |
| die `invariant` einer umgebenden Schleife | *„was über den Durchläufen gilt"* (2026-08-28 früh) |

Verglichen wird **die Stelle, nicht die Form**: `requires !v.slots[j].benutzt` neben
`Verzeichnis::insert(v, i)` fällt (`beispiele/gift/322`). *Das ist der teurere der beiden
Fehler, weil er jede Prüfung passiert, die nur die Anwesenheit einer Klausel zählt.*

---

## 5. Was das NICHT kauft — und die Liste ist die Hälfte des Eintrags

1. **`D012` beweist keine Voraussetzung.** Ein stehendes `requires` ist die Pflicht einen
   Rahmen weiter außen, wörtlich so, wie `blatt_loeschen` sein `ist_blatt(c, s)` seit
   `beispiele/01` trägt. **Was sich ändert, ist, dass die Pflicht überhaupt existiert.**
2. **Die Negation eines vorangehenden `if`-Zweiges liest die Regel nicht.** Sie ist eine
   Tatsache, und sie steht hier als ungelesene da statt als halb gelesene.
3. **Eine Voraussetzung unter `||` oder hinter `=>` gilt nicht als stehend.** Die
   fail-open-Richtung wäre, sie mitzunehmen.
4. **Der Schritt vom Isabelle-Modell zum erzeugten C bleibt offen.** Dieselbe Lücke, die
   `Table_Absenkung.thy` mit eigenen Worten nennt; sie ist durch diesen Auftrag weder größer
   noch kleiner geworden.
5. **Die erzeugten Operationen stehen NICHT in `gabbro pflichten`.** `pflichten.rs` liest
   `FnDecl`s des Baums, und ein erzeugter Kopf ist keiner. Die `V`-Zahl zählt sie damit nicht
   mit — *gebucht als offen, nicht wegdefiniert.*

---

## 6. Gemessen

```text
cargo test                     15 Testsammlungen gruen (97 + 19 + 33 + 21 + …)
pruefe-emission.sh             ALL PASS -- 23 durchgestochen, 51 von 51 uebersetzen
beispiele/gift/321..324        4 Proben auf `D012`, jede faellt mit ihrem Code
beispiele/47                   ruft alle VIER erzeugten Operationen; im C steht
                               `Verzeichnis_insert(v, i);` und kein `unused` mehr
pruefe-syntax.sh               ALL PASS -- 152 EBNF-Regeln, 218/218 Terminale
                               (unveraendert: `pathseg` bekommt eine Alternative,
                                keine Regel und kein Wort)
pruefe-kennungen.py            ALL PASS -- 226 Kennungen, jede in genau einer Datei
mutiere-pruefer.py --anker     316 von 319 (vorher 314 von 317; zwei Mutationen auf
                               `opsruf.rs` dazu, die drei toten sind alt)
pruefe-schablonen.py           7 -> 6 haengende Praemissen; die Marke ist nachgezogen
```

**Und die zwei neuen Mutationen sind GEFAHREN, nicht nur eingetragen** (von Hand auf
`ki-pc-fisch-101`, `cargo test --test beispiele` je Mutation):

```text
gefangen   ops-ruf-braucht-keine-voraussetzung        (D012 schweigt -> 321..324 gehen durch)
gefangen   ops-ruf-haelt-nur-die-erste-voraussetzung  (nur `frisch`; 323 geht durch)
```

*Die zweite ist die schärfere:* eine Aufrufstelle, die einen halben Satz erfüllt, sieht
sorgfältig aus.

### Zwei Wächter waren schon vor diesem Auftrag rot, und bleiben es

| Wächter | Stand | wessen |
|---|---|---|
| `pruefe-englisch.py` | `1079 in den Instrumenten, gebucht sind 1072` | **nicht dieser Auftrag.** Gemessen mit `git stash` gegen `master`: dort steht dieselbe 1079. Die deutschen Kommentarzeilen im Prüfer stehen bei 7910 = Marke, vorher wie nachher — die 212 neuen Zeilen sind englisch |
| `pruefe-saetze.py` | `47 Kennungen ohne Satz, gebucht sind 45` | **nicht dieser Auftrag.** Die 47 sind `C001`, sieben `L00x`, `M133` und 38 `P0xx`; `D012` hat seinen Satz (`d.opsruf`). `M133` kam mit `ce5c23f`, `P040` mit `c13eb67` — beide von heute Morgen, beide ohne Satz |

*Beide Zahlen sind gemessen und nicht geschätzt; die Marken sind bewusst nicht angefasst
worden.* Eine Ratsche, deren Marke man hochzieht, wenn sie bricht, ist keine.

**Und die Zahl, die das Attribut betrifft:** `__attribute__((unused))` steht an einer
erzeugten Operation ab heute genau dann, wenn die Einheit sie **wirklich** nicht ruft. *Es
ist eine Messung geworden, wo es eine Gewohnheit war.*
