# `K001` an `F09` — die Rechnung, Faktor für Faktor

*Gemessen am 2026-08-31, Bahn P, Posten P-a. **Der W24-Vorlauf steht vor der Entscheidung, und
er hat sie umgedreht.***

> **Das Ergebnis zuerst.** `137 438 953 472` ist **richtig**, und `4096` ist **falsch**.
> `F09` ist damit **kein Prüferfehler**, sondern eine korrekte Absage über einer Zusage, die
> mit der *zurückgezogenen* Lesart gerechnet wurde. Die Buchung „drei echte Programme weist
> der Prüfer ab" trägt `F09` zu Unrecht.
>
> **Und die Reparatur, die naheliegt, kauft nichts:** selbst mit der ehrlichen Zahl bleibt
> `F09` unabgesenkt — der ERZEUGER weist dieselbe Datei **dreimal** ab (`C001`), und keine
> dieser drei Absagen hängt an `K001`. *Gemessen, nicht vermutet; die Ausgabe steht in §5.*

---

## 1. Die Kette — drei Stellen, drei Faktoren

`F09`:79 sagt `costs <= 4096 ops` zu. Der Pass rechnet `137 438 953 472`. Die Zahl entsteht an
genau drei Stellen, und jede trägt genau einen Faktor:

| # | Stelle | was sie beiträgt | Wert bei `F09` |
|---|---|---|---|
| **1** | `crates/gabbro-check/src/umgebung.rs`:757‑767 | `walkschranken[W] = Knotenlänge ^ Ebenen`, über `checked_pow` | `512^4 = 68 719 476 736` |
| **2** | `crates/gabbro-check/src/domaene.rs`:88‑103 | `mappings of w` schlägt den Walknamen über den TYP von `w` nach und liefert die Zahl aus (1) durch | `68 719 476 736` |
| **3** | `crates/gabbro-check/src/kosten.rs`:591‑593 | `Kosten::Zahl(Rumpf).mal(Schranke)`, über `checked_mul` | `2 × 68 719 476 736` |

Der Rumpffaktor `2` kommt aus dem Rumpf der Traversierung:

```gabbro
if abbildung.level == 3 {   -- 1 op: die Bedingung
    return true;            -- 1 op
}
```

**Die ganze Rechnung in einer Zeile:**

```
  Rumpf x Knotenlaenge ^ Ebenen  =  2 x 512^4  =  2 x 68 719 476 736  =  137 438 953 472
```

## 2. Und das ist nicht hergeleitet, sondern gemessen

Fünfzehn Läufe über vierzehn verschiedene Programme (die vorletzte Zeile wiederholt die
sechste absichtlich als Anker), je ein Faktor allein bewegt, alle über denselben `walk`.
Gelesen wird der **Text** der Absage (`the body costs N`), nicht eine Bilanzzahl:

| `Ebenen` | `Knotenlänge` | Rumpf | gedruckt | `Rumpf × l^e` |
|---|---|---|---|---|
| 1 | 2 | 2 | `4` | `2 × 2` |
| 2 | 2 | 2 | `8` | `2 × 4` |
| 3 | 2 | 2 | `16` | `2 × 8` |
| 4 | 2 | 2 | `32` | `2 × 16` |
| 1 | 8 | 2 | `16` | `2 × 8` |
| 2 | 8 | 2 | `128` | `2 × 64` |
| 3 | 8 | 2 | `1 024` | `2 × 512` |
| 4 | 8 | 2 | `8 192` | `2 × 4 096` |
| 1 | 512 | 2 | `1 024` | `2 × 512` |
| 2 | 512 | 2 | `524 288` | `2 × 262 144` |
| 3 | 512 | 2 | `268 435 456` | `2 × 134 217 728` |
| **4** | **512** | **2** | **`137 438 953 472`** | **`2 × 68 719 476 736`** |
| 2 | 8 | 0 | *(keine Absage)* | `0 × 64 = 0` |
| 2 | 8 | 2 | `128` | `2 × 64` |
| 2 | 8 | 4 | `256` | `4 × 64` |

**Der Exponent ist ein Exponent und kein Faktor** — `e` von 1 auf 4 bei `l = 2` verdoppelt
viermal (`4 → 8 → 16 → 32`), nicht viermal *dasselbe*. Die alte Lesart `e × l` hätte
`4 → 8 → 12 → 16` gedruckt.

---

## 3. Ist die Zahl richtig? — **ja, und sie ist scharf**

`mappings of` quantifiziert über die **erreichbaren Blätter** eines `walk` (`SPRACHE.md` §6,
Zeile 900). Die Frage ist also: *ist `l^e` die Mächtigkeit dieser Menge?*

**Obere Schranke.** Ein `walk` mit `e` Ebenen und Knoten zu `l` Einträgen ist ein Baum, dessen
Wurzel `l` Einträge hat, jeder davon höchstens einen Knoten der nächsten Ebene öffnet. Auf
Ebene `k` gibt es also höchstens `l^k` Knoten und `l^(k+1)` Einträge. Ein Blatt ist ein
Eintrag; die tiefsten Einträge sind `l^e` viele. Ein Eintrag auf einer *höheren* Ebene kann
Blatt sein (`leaf : EINTRAG.PS == 1` — die Großseite), aber dann öffnet er keinen Unterbaum
und ersetzt `l^(e-k)` mögliche Blätter durch **eines**. *Jede Großseite senkt die Zahl.*
Also `|mappings| ≤ l^e`.

**Sie wird angenommen.** Belegt man jeden Eintrag der tiefsten Ebene mit `PS == 1` und jeden
darüber mit `PS == 0`, sind es genau `l^e`. **Die Schranke ist scharf, nicht großzügig.**

**Gegenprobe an der Hardware.** `512^4 = 2^36`, und `2^36` 4‑KiB‑Seiten sind `2^48` Bytes —
die 256 TiB, die vierstufiges x86‑64‑Paging adressiert. *Die Zahl ist die Adressraumgröße
geteilt durch die Seitengröße, und das ist sie auch dann, wenn man sie von der anderen Seite
her ausrechnet.*

## 4. Ist der Kalkül zu grob? — **ja, und in der ungefährlichen Richtung**

`rechte_pruefen` kehrt beim **ersten** Blatt mit `level == 3` zurück, und in einem
vierstufigen `walk` liegt jedes Blatt auf `level == 3`. **Der wirkliche Lauf kostet 2 ops.**
Der Pass rechnet `2 × 512^4`. Der Schlupf ist ein Faktor `6,9 × 10^10`.

> **Das ist Grobheit und kein Fehler.** `K001` ist eine OBERE Schranke; ein `traverse`, das
> vorzeitig zurückkehrt, kostet höchstens so viel wie eines, das durchläuft. Die einzige
> Fehlerrichtung, die zählt, ist die **Unterzählung** — und die tritt hier an keiner Stelle
> auf: beide Multiplikationen laufen über `checked_pow`/`checked_mul` und weichen bei
> Überlauf nach `K003` aus statt still zu wickeln (§6).

**Ein Frühausstieg im Kostenmodell wäre ein neues Konstrukt, und der Bedarf ist eine einzige
Fundstelle.** Nach Regel A wird er nicht gebaut. *Er stünde auch nicht für sich: „das erste
Element trifft die Bedingung" ist eine Aussage über die Belegung des Baums zur Laufzeit, und
die kennt der Pass nicht — er müsste sie annehmen.*

## 5. Warum die naheliegende Reparatur nichts kauft

Der Plan (`dokumente/PLAN-VOLLSTAENDIGKEIT.md` §6) bucht `F09` als Sperre vor `K1`: *„F3 und
F9 sind für den Prüfer gar keine gültigen Programme … Erst P2/P3, dann K1."*

**Für `F09` ist das unvollständig.** Eine Sonde mit derselben `walk`-Form, aber leerem
Traversierungsrumpf, geht durch den Prüfer (`0 Fehler`) — und der Erzeuger weist sie dreimal
ab:

```
[C001] device … at normal -- an access into the ordinary space is not a device access …
[C001] walk … levels that is not a number -- the descent's step count IS the declaration's
       one statement about the run, and it cannot be guessed
[C001] mappings of -- the reading is DECIDED (the leaf SET …). What is missing is the
       lowering: it needs a generated recursive descent along down and leaf
```

*Keine dieser drei hängt an `K001`.* Sie stehen alle drei in `emit.rs` und gehören damit
**Bahn V**. Würde man `F09`:79 auf `costs <= 137438953472 ops` heben, prüfte `F09` sauber und
senkte trotzdem nicht ab. **Die Zusage zu heben, kauft eine Zahl in einer Bilanz und keine
Absenkung.**

Und sie **kostet** etwas: die Zeile `costs <= 4096 ops` samt ihrer Begründung
(`-- Die Schranke faellt aus levels mal node-Laenge`) ist heute der einzige Ort im Baum, an
dem die zurückgezogene Lesart **im Wortlaut** steht und **von einem Werkzeug angezeigt wird**.
*Ein Marker, den ein Werkzeug jeden Tag ausdruckt, ist mehr wert als ein Satz in einem
Dokument.*

> **Entschieden: `F09` bleibt, wie es ist.** Das ist eine benannte Absage und ein voller
> Ausgang. Was fällt, ist die BUCHUNG — `F09` gehört nicht in die Liste „echte Programme, die
> der Prüfer abweist", sondern in die Liste „Programme, die der Erzeuger nicht kennt".

## 6. Was der Vorlauf nebenbei gefunden hat — die Walkidentität hängt an der Zahl

`umgebung.rs`:1094 löst den *Typnamen* eines `walk` so auf:

```rust
Traegerart::Walk => self.walkschranken.contains_key(*k),
```

**Ein `walk` IST ein Typ, genau dann, wenn seine Blattzahl in `u128` passt.** Gemessen an zwei
Sonden mit identischer Deklaration bis auf `levels`:

| `levels` | `512^levels` | was der Prüfer sagt |
|---|---|---|
| 14 | `2^126` — passt | `K003`: *the cost calculation overflows … so nothing is promised here* |
| 15 | `2^135` — passt nicht | `N040`: **`W` names no type** ⟵ *und danach* `K003`: *die Domäne hat keine Schranke aus der Deklaration (fehlt der Tabelle ihr `count`?)* |

Bei `levels 15` ist die Deklaration tadellos, der Name steht da, und der Prüfer sagt, es gebe
ihn nicht — und schickt den Leser anschließend nach einem `count` an einer Tabelle suchen, die
es nicht gibt. **Dieselbe Klasse wie `W16`: das Werkzeug misst etwas anderes als seinen
Gegenstand.** Der Schlüssel `walkschranken` beantwortet *„wie groß ist die Blattmenge"*; die
Auflösung fragt *„gibt es diesen `walk`"*. Zwei Fragen, eine Karte.

> **NACHGEMESSEN UND REPARIERT, noch am selben Tag — und die Reichweite war größer als der
> Fund.** Hier stand *„nicht dringend, weil die Erreichbarkeit an `512¹⁵` hängt"*. **Es sind
> drei Wege, und zwei davon sind gewöhnliche Tippfehler:**
>
> | Deklaration | warum kein Eintrag in `walkschranken` | vorher |
> |---|---|---|
> | `walk W levels 0 { node : [Pte; 512] … }` | die Wache `e > 0 && l > 0` | `N040` |
> | `walk W levels 4 { node : [Pte; 0] … }` | dieselbe Wache | `N040` |
> | `walk W levels 15 { node : [Pte; 512] … }` | `checked_pow` läuft über | `N040` |
>
> Repariert: `walknamen` wird beim Lesen der Deklaration **unbedingt** gefüllt, die Auflösung
> fragt sie, `walkschranken` bleibt die Zahl. Probe
> `ein_walk_ohne_brauchbare_blattzahl_bleibt_ein_typ` (kein `N040`, dafür `K003` an allen
> dreien), Mutation `walkname-haengt-an-der-zahl` — von Hand gesetzt, gebaut, **genau eine
> fallende Probe**.
>
> **Und die Absage war nicht nur deutsch, sondern falsch.** Sie fragte bei JEDER Domäne nach
> dem `count` einer Tabelle. Jetzt nennt sie alle drei Quellen. *Eine Absage, die den falschen
> Gegenstand nennt, kostet mehr als eine, die keinen nennt.*
>
> Nebenbei aufgefallen: **`pruefe-englisch.py` sieht diese Meldung gar nicht.** Er misst
> `Absage::fehler`, `::hinweis` und `.mit_notiz`; ein Text, der über `Kosten::Unbekannt` in
> den `K003`-Text kommt, ist ihm unsichtbar. Zwei deutsche Meldungen standen so da — gedruckt,
> nicht gezählt. *Gebucht in `TODO.md`; die Fläche ist 13 `Kosten::Unbekannt` im Prüfer, und
> dieselbe Frage gilt für jeden anderen Weg.*

---

## 7. Was daraus für das Satzregister folgt

`saetze.rs::kosten.domaenenschranke` steht auf `VERMUTET`, und sein `gemessen_an` sagte:

> *„**No probe and no mutation measures the bound against the domain.** `K003` has 2 probes,
> but they measure that a MISSING bound is refused — not that a PRESENT one is right. That is
> the difference the 2 048/512^4 error lived in."*

**Genau diese Lücke schließt §2.** Die Sonden messen eine ANWESENDE Schranke gegen die
Deklaration, und zwar so, dass die historisch falsche Lesart auffällt: bei `l = 2, e = 3`
sagt `e × l` die Schranke `6` und `l^e` die Schranke `8` — gedruckt `12` gegen die gemessenen
`16`. Bei `l = 512, e = 4` trennen dieselben zwei Lesarten `4096` von `137 438 953 472`.

**Der Stand blieb an dieser Stelle `VERMUTET`, und das war kein Versehen.** Der Satz
spricht über *alle* Domänen — `count` einer Tabelle, das einzige Feldarray eines
`queue`-Verbunds, `elems of`, `index into T`. Gemessen war nach §1–§7 **eine** davon.
*Die anderen vier stehen in §8, und erst damit fällt der Stand.* *Der Vorbehalt im Satz sagt das selbst:
„Every other domain bound in this pass has exactly the same shape and exactly as little
checking."* Er wird um den Satz ergänzt, welche Domäne jetzt Proben hat — **eine Marke, die
fällt, nicht eine, die steigt.**

---

## 8. Die anderen vier — gemessen am 2026-08-31, Bahn K

> **Das Ergebnis zuerst.** Alle fünf Domänen tragen jetzt Probe und Mutation, und der Stand
> steigt von `VERMUTET` auf `measured` — *nicht, weil jemand es entscheidet, sondern weil die
> Grundgesamtheit voll ist.* **Und die Messung hat den Satz vorher KORRIGIERT:** er sagte
> „die Schranke IST die Mächtigkeit", und für zwei der fünf ist sie es nicht.

### 8.1 Die fünf Domänen einzeln — Mächtigkeit, Herkunft, und ob sie abgeleitet ist

| Domäne | Schranke, die der Pass nimmt | woher sie kommt | angenommen / abgeleitet |
|---|---|---|---|
| `mappings of w` | `Knotenlänge ^ Ebenen` | `walk W levels E { node : [T; L], … }` → `umgebung.rs::walkschranken`, `checked_pow` | **abgeleitet und SCHARF** — §3: jede Ebene multipliziert mit `L`, eine Großseite (`PS == 1`) ersetzt einen Unterbaum durch *ein* Blatt und senkt die Zahl; belegt man die tiefste Ebene ganz mit `PS == 1`, sind es genau `L^E`. Gegenprobe: `512⁴ = 2³⁶` 4-KiB-Seiten = `2⁴⁸` Bytes = 256 TiB |
| `slots of p` | `count N` der Tabelle | `table T count N` → `umgebung.rs::kapazitaeten` → `domaene.rs` über `Typ::Tabelle` | **abgeleitet und SCHARF** — die Tabelle IST ihre `N` Slots, und `by unvisited` besucht jeden genau einmal. Definitorisch |
| `descendants of x`, `ancestors of x` | dieselbe `count N` | derselbe Weg | **abgeleitet, aber nur OBERE Schranke** — die Nachfahren eines Knotens sind höchstens `N−1`, nie `N`. Die Schranke folgt nicht aus der Baumform, sondern aus `by unvisited`: kein Slot zweimal. *Grob nach oben, und die Kostenzusage hält trotzdem* |
| `queue p` | Länge des **einzigen** Feldarrays des Verbunds | `type Q = { buf : [u32; n], … }` → `domaene.rs::arraylaenge_im_verbund` | **abgeleitet als OBERE Schranke, mit einer ANGENOMMENEN Zuordnung** — dass das einzige Array der Puffer der Warteschlange *ist*, prüft nichts. Es ist eine Regel: bei zwei Arrays liefert die Funktion `None`, und der Pass sagt `K003` statt zu raten. Die Warteschlange hält zur Laufzeit höchstens `n`, nicht notwendig `n` |
| `elems of a` | Länge im FELDTYP | `Typ::Feld { laenge: Some(n) }` — der Tabellenzweig wird nie erreicht | **abgeleitet und SCHARF** — genau `n` Elemente |
| `index into T` | `count` der Tabelle, die der TYPNAME nennt | `domaene.rs::tabellenname`, Präfix `"index into "` | **abgeleitet, gleiche Schärfe wie der Weg, an dem sie hängt** (`slots of` scharf, `descendants of` obere Schranke). *Der Weg selbst war bis zum 2026-08-17 tot: kein Beispiel hatte die Stelle je ausgelöst, weil der Korpus `descendants of` nur in PRÄDIKATEN führt, wo kein Kostenpass läuft* |

**Es sind fünf Schrankenquellen und neun `Domaene`-Varianten.** `KetteIn`, `FelderVon` und
`Threads` liefern gar keine Schranke — sie fallen in `_ => return None` und damit auf `K003`.
*Das ist keine Lücke, sondern die vierte Antwort: der Pass rät nicht.*

### 8.2 Die Probe — ein Regler je Domäne, gelesen wird der `K001`-TEXT

`crates/gabbro-check/tests/rechenwerk.rs`,
`die_vier_uebrigen_domaenenschranken_kommen_aus_ihrer_deklaration`:

| Domäne | Regler | gedruckt | Rumpf |
|---|---|---|---|
| `slots of` | `count` = 3, 7, 13 | 3, 7, 13 | 1 op |
| `elems of` | `[u32; n]`, n = 2, 9, 31 | 2, 9, 31 | 1 op |
| `queue` | `[u32; n]`, n = 3, 5, 16 | 6, 10, 32 | 2 ops |
| `index into T` | `count` = 4, 6, 11 | 4, 6, 11 | 1 op |

**Die vier sind vier LESEWEGE und nicht einer**, und deshalb bekommt jeder seinen eigenen
Regler: `slots of` löst über `Typ::Tabelle` auf, `index into T` über das Namenspräfix in
`tabellenname`, `queue` über `arraylaenge_im_verbund`, und `elems of` kehrt zurück, bevor der
Tabellenzweig überhaupt erreicht wird. *Eine Probe über einen davon sagt nichts über die
anderen drei — genau der Zustand, den das hier ersetzt.*

### 8.3 Die Mutationen — OFF-BY-ONE, und das ist der ganze Punkt

| Mutation | Anker in `domaene.rs` | gefangen von |
|---|---|---|
| `count-schranke-um-eins-daneben` | `.map(\|n\| n as i128)` → `- 1` | **1** Probe |
| `elems-schranke-um-eins-daneben` | `return Some(*n as i128);` → `- 1` | **1** Probe |
| `queue-schranke-um-eins-daneben` | `gefunden = laenge.map(…)` → `- 1` | **1** Probe |
| `index-into-tabelle-verloren` | `if name.starts_with("index into ")` → `if false && …` | **2** Proben |

**Warum off-by-one und nicht Entfernung:** eine Schranke, die GANZ FEHLT, sagt `K003` und ist
seit langem von zwei Giftproben gedeckt (`36-kosten-ueber-unbekanntem.gab`,
`69-vorfahren-ohne-schranke.gab`). Die Lücke war eine Schranke, die DA IST und falsch ist —
und genau das waren die 2 048 gegen `512⁴`. *Eine Mutation, die entfernt, misst die schon
gemessene Hälfte.*

**Die vierte ist die Ausnahme und wird zweimal gefangen** — von dieser Probe und vom
Korpuslauf, weil `beispiele/39-auftragsdienst.gab` die Stelle trägt. Der Leseweg `index into`
lässt sich nur durch Entfernen beschädigen; seine Falsch-Zahl-Hälfte deckt
`count-schranke-um-eins-daneben` ab, mit dem er sich das letzte `.map` teilt. *Das ist keine
schwache Mutation, sondern eine Aussage über den Korpus: die Stelle ist tragend geworden,
seit sie 2026-08-17 gefunden wurde.*

### 8.4 Was daraus für das Satzregister folgt — der Satz wurde korrigiert, dann gehoben

`saetze.rs::kosten.domaenenschranke` sagte:

> *„…and that bound is the **cardinality** of the domain as it follows from the declaration"*

**Für zwei der fünf ist das falsch, und das ist der eigentliche Fund dieser Messung.**
`descendants of x` besucht höchstens `count`−1 Slots; eine `queue` hält höchstens ihr Array.
Die Zeile heißt seit heute **`an UPPER bound on the cardinality`**. *Nach oben grob hält eine
Kostenzusage; die 2 048 waren nach UNTEN grob, und das ist die Richtung, die lügt.*

Erst danach steigt `Satzstand::Vermutet` auf `Satzstand::Gemessen`. Die Bilanz von
`gabbro paesse` geht damit von `63 measured, 2 ARGUED, 6 CONJECTURED` auf
**`64 measured, 2 ARGUED, 5 CONJECTURED`**.

> **Und was `measured` NICHT heißt.** Es misst die UMSETZUNG an geprüften Fällen, nicht die
> Regel und nicht alle Fälle — das steht in `Satzstand::Gemessen` selbst. Die drei
> Domänensätze aus §6 fehlen weiter; `PROVED` bleibt bei 0 von 71.

---

## 9. `F09`s Zusage — zum zweiten Mal geprüft, und sie bleibt bei `4096`

**Die Frage war gestellt: liefert die Messung der vier übrigen Domänen einen Grund, `F09`:79
auf `137 438 953 472` zu heben?** Sie liefert keinen — und das ist ein Ergebnis, kein
Aufschub.

Was §8 dazu beiträgt, geht in die andere Richtung: die vier Nachbarschranken lesen **genau so**
aus ihrer Deklaration wie `mappings of`, und jede von ihnen ist jetzt an einem Regler gemessen.
*Die `137 438 953 472` stehen damit nicht mehr allein, sondern als eine von fünf Zahlen
desselben Baus.* Die Rechnung aus §1–§3 wird dadurch bestätigt, nicht erschüttert.

Die drei Gründe aus §5 stehen unverändert:

1. Der ERZEUGER weist `F09` **dreimal** ab (`C001`), und **keine der drei hängt an `K001`**.
   Eine gehobene Zusage prüfte sauber und senkte trotzdem nicht ab.
2. Die Zeile `costs <= 4096 ops` ist heute der **einzige Ort im Baum, an dem die
   zurückgezogene Lesart im Wortlaut steht und von einem Werkzeug jeden Tag angezeigt wird**.
3. Ein Frühausstieg im Kostenmodell wäre ein neues Konstrukt mit **einer** Fundstelle —
   Regel A.

**Eine Zahl zu heben, damit ein Zähler stimmt, ist genau das, was dieser Ordner nicht tut.**
Die Buchung bleibt: `F09` ist kein Prüferfehler, sondern eine korrekte Absage über einer
Zusage, die mit der zurückgezogenen Lesart gerechnet wurde.
