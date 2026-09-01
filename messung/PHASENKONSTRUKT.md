# `§42` nachgerechnet: EIN Wort fiele, nicht vier — und der Absenkungssatz ist NULL, nicht einer

*Gerechnet am 2026-09-01, lokal (`free -g`: 31 GB gesamt, 13 GB verfügbar, 20 Kerne). Jede
Zahl nennt den Befehl, der sie nachrechnet. **Kein Bau** — die Rechnung trägt nicht, und
die Absage ist das Ergebnis. Gegenstück zu `messung/DOMAENENREGEL.md`, gleiche Form,
gleicher Ausgang.*

Ratschenmarken **vorher wie nachher** (nichts gebaut, nichts bewegt):

```
221 Woerter · 13 mit Grund (208 ohne) · 333 Stellungen
./instrumente/zaehle-wortschatz.py
```

---

## 1. Die vier Zahlen von `§42` sind über dem GIFTKORPUS erhoben

`PLAN-HARDWARE.md` §42 schreibt eine Tafel hin (14 / 31 / 6 / 102) und nennt keine
Grundgesamtheit. Sie ist rekonstruierbar, und das Ergebnis ist der erste Befund:

```bash
grep -rE 'advances +[A-Za-z_]+ *-> *[A-Za-z_]+' --include='*.gab' . | wc -l        # 31
grep -rE 'advances +[A-Za-z_]+ *-> *[A-Za-z_]+' --include='*.gab' \
     --exclude-dir=gift . | wc -l                                                 # 12
```

**Die Population ist `**/*.gab` — alle 526 Dateien, darunter die 357 in `beispiele/gift/`.**
Die Ratsche, gegen die `§42` sich rechtfertigen muss, misst über **164** Dateien
(`zaehle-wortschatz.py::korpusdateien`: *„`beispiele/*.gab` + `messung/**/*.gab`, ohne
`gift/`"*).

| Muster | alle 526 | davon `gift/` | Ratschenkorpus (164) | Anteil Gift |
|---|---|---|---|---|
| `linear ghost type … order {` | **14** | 11 | **3** | **79 %** |
| `advances <a> -> <b>` | **31** | 19 | **12** | **61 %** |
| `class <k> in <stufe>` | 7 *(6 ohne den Kommentar in `F04`:97)* | 4 | **3** | 57 % |
| `consumes <x>` | **104** *(§42 bucht 102)* | 50 | **52** | 48 % |

> **Elf der vierzehn `order`-Deklarationen stehen in Giftproben.** Das Konstrukt liegt in
> **drei** echten Programmen: `beispiele/02-geraet.gab`, `beispiele/22-bootstrecke.gab`,
> `messung/treiber/virtio-net.gab`.

**Eine Giftprobe ist ein Programm, das FALLEN soll.** Wie oft ein Konstrukt in Programmen
vorkommt, die abgelehnt werden, ist keine Aussage darüber, wie oft es gebraucht wird —
es ist eine Aussage darüber, wie gründlich es begiftet wurde. *Dieselbe Klasse wie `W16`:
ein Messgerät, das seinen eigenen Prüfstand mitzählt.*

---

## 2. Die Rechnung je Wort — **fällt / zieht um / bleibt**

Die Grundlage ist nicht der Korpus, sondern die Wortliste und die Grammatik:

```bash
./instrumente/zaehle-wortschatz.py          # 221 / 208 / 333
grep -n 'Order\|Advances\|Consumes\|Retires' crates/gabbro-syntax/src/kw.rs
sed -n '333,335p;792p;1308p;1323p' dokumente/SYNTAX.md
```

| Wort | Stellungen heute | was `§42` mit ihm vorhat | **Befund** |
|---|---|---|---|
| `order` | 1 (`markorder`) | `phase T { … }` ersetzt `linear ghost type T order { … }` | **fällt** −1 |
| `advances` | 1 (`fndecl`) | `phase <a> -> <b>` an derselben Stelle | **fällt** −1 |
| `phase` | — | neu | **kommt** +1 |
| `in` an `regphasen` | 1 von 9 | `class rw in setup` | **bleibt — es kostet heute NULL** |
| `class` | 2 (`regdecl`, `regfeld`) | ebenso | **bleibt — kostet heute NULL** |
| `consumes` | 1 (`eff`) | *„die Handkombination, 102 Mal"* | **bleibt** — s. 2.2 |
| `linear`, `ghost`, `type` | je 1 (`typedecl`) | trüge `phase` mit | **bleiben** — s. 2.3 |
| `retires` | 1 (`fndecl`) | nicht genannt | **bleibt** — beendet eine Marke, ist kein Schritt |

> ### **Netto: −2 +1 = EIN Wort. 221 → 220.**
>
> Nicht vier, nicht siebzehn, nicht drei Bereiche mal ein Wort. **Eins.**

`phasen.rs` sagt es in seinem eigenen Kopf, und zwar seit «B37»:

> *„Der Wortschatz waechst um `order` und `advances` — einmal, nicht je Schritt."*
> — `crates/gabbro-check/src/phasen.rs`:29

**Zwei Wörter sind der ganze Bestand, den `§42` ablösen kann.** Alles andere, was seine
Tafel aufzählt, kostet heute schon nichts.

### 2.1 `class … in <phase>` ist bereits der Nullfall — es gibt dort nichts zu senken

`SYNTAX.md`:1323 führt `regphasen = "in" ident { "," regklasse "in" ident } ;` und schreibt
den Grund daneben: *„KEIN neues Terminal: `in` ist seit jeher reserviert, `class` steht
schon hier."* `§42` zählt die sechs Fundstellen als Posten seiner Rechnung. **Sie sind
keiner.** Ein Wort, das nie gekauft wurde, lässt sich nicht zurückgeben.

*Es ist die teuerste Zeile der Tafel und die einzige, die schon gratis ist.*

### 2.2 `consumes`: von 104 Stellen haben **30** eine Phase — und die haben das Konstrukt schon

**Die Zerlegung ist je `fn`-Deklaration, nicht je Datei** — eine Datei, die irgendwo eine
Phase führt, färbte sonst jedes `consumes` darin ein:

```bash
# je Deklaration getrennt, dann `advances` im selben Stueck gesucht
python3 - . <<'PY'
import re, pathlib, sys
root = pathlib.Path(sys.argv[1])
kopf = re.compile(r"^\s*(?:pub\s+)?(?:impl|extern|spec|raw|prim|divergent)?\s*fn\s", re.M)
adv  = re.compile(r"\badvances\s+[A-Za-z_]+\s*->\s*[A-Za-z_]+")
con  = re.compile(r"\bconsumes\s+[A-Za-z_]")
alle = [p for p in sorted(root.glob("**/*.gab")) if "/target/" not in str(p)]
korp = [p for p in sorted(set(list(root.glob("beispiele/*.gab"))
                              + list(root.glob("messung/**/*.gab"))))
        if "/gift/" not in str(p)]
for label, files in (("alle .gab", alle), ("Ratschenkorpus", korp)):
    a = c = mit = ohne = 0
    for p in files:
        t = p.read_text(encoding="utf-8", errors="replace")
        a += len(adv.findall(t)); c += len(con.findall(t))
        g = [m.start() for m in kopf.finditer(t)] + [len(t)]
        ohne += len(con.findall(t[:g[0]]))
        for i in range(len(g) - 1):
            s = t[g[i]:g[i + 1]]
            k = len(con.findall(s))
            if adv.search(s): mit += k
            else:             ohne += k
    print(f"{label:16s} n={len(files):4d} advances={a:4d} consumes={c:4d} "
          f"mit={mit:4d} ohne={ohne:4d}")
PY
```

| | alle 526 | Ratschenkorpus |
|---|---|---|
| `advances <a> -> <b>` | 31 | 12 |
| `consumes <x>` | 104 | 52 |
| **`consumes` IN einer `fn` mit `advances`** | **30** | **12** |
| **`consumes` OHNE `advances` in derselben `fn`** | **74** | **40** |

Und die Gestalt der dreißig steht in `beispiele/22-bootstrecke.gab`:83–86:

```gabbro
extern fn mmu_an(p : BootPhase) -> BootPhase
    advances roh -> mmu
    effects  { consumes p, writes mmu_an_zahl } costs <= 4096 ops;
```

> **`§42` nennt die 102 „die Handkombination von `consumes` plus Phase". Umgekehrt:** wo
> eine Phase steht, steht `advances` daneben — das *ist* das Konstrukt, nicht seine
> Handnachbildung. Die **74**, die keine Phase haben, sind gewöhnliche Linearität: eine
> Sperre, ein Zeuge, ein weggegebener Puffer. **Kein `phase`-Konstrukt berührt sie.**

Selbst wenn ein `phase`-Schritt den Verbrauch der Marke *implizit* machte — 30 Textstellen
verschwänden und **das Wort bliebe**, weil 74 es weiter brauchen. *Ein Wort fällt, wenn seine
LETZTE Fundstelle geht, nicht wenn ihre Zahl sinkt.* Genau die Verwechslung hat die
Domänenrechnung ihren Faktor sechs gekostet.

### 2.3 `linear ghost type` fällt nicht mit — es trägt neun Zehntel seiner Last woanders

```bash
grep -rEc 'linear +ghost +type' --include='*.gab' --exclude-dir=gift . | \
    awk -F: '{s+=$2} END {print s}'                                    # 20
grep -rE  'linear +ghost +type[^\n]*order' --include='*.gab' --exclude-dir=gift . | wc -l  # 3
```

**Zwanzig `linear ghost type` im Korpus, drei davon mit `order`.** Die anderen siebzehn sind
`Held(L)`, `Griff`, Veröffentlichungsmarken. Ein `phase T { … }`, das `linear ghost type T
order { … }` ersetzt, lässt `linear`, `ghost` und `type` **unangetastet** stehen.

---

## 3. Die Gegenprobe — was `advances` kann, das ein allgemeines `phase` nicht könnte

*Pflicht laut Auftrag, und sie ist die Hälfte, an der der Vorschlag hängt: **ein Wort, das
mehr kann als sein Ersatz, wird nicht abgelöst, sondern verloren.***

**Drei Dinge, und alle drei sind gebaut und gemessen.**

### (a) `advances` nennt ZWEI Stufen und wird auf Vorwärtsgang geprüft

`O002` macht aus der Liste eine Ordnung (`phasen.rs`:256–262). Ein `phase <s>` an einer
`table` oder an einem `ops`-Block nennt **eine** Stufe — der Vergleich „geht es vorwärts"
existiert dort nicht, weil es kein Paar gibt. **Die Stelligkeit ist verschieden**, und ein
Wort mit zwei Stellen durch eines mit einer zu ersetzen, ist kein Tausch.

### (b) Die Marke wird über den TYP gefunden, nicht genannt — daran hängt die Komposition

`phasen.rs::markenordnung`:91–112 sucht die Marke unter den Parametern und den `let`-Bindungen
nach ihrem Typ. `advances setup -> live` schreibt `QueuePhase` **nirgends hin**. Genau
deshalb trägt der Fluss über die Rufgrenze:

* `O003` — beim Ruf steht die Marke auf der Ausgangsstufe *(„die Zeile, die die 720
  Reihenfolgen auf eine reduziert", `phasen.rs`:595)*
* `O004` — der Rumpf setzt sich zu seiner eigenen Zusage zusammen
* `O006` — alle Zweige erreichen dieselbe Stufe; ein Schritt in einer Schleife fällt

**Ein `phase` an einer `table` oder einem `ops`-Block hat keinen Wert in einer Signatur, durch
den etwas fließen könnte.** `PHASENKLASSE.md` §2 hat diesen Fall schon entschieden, unter
dem Namen *Form 3*, und die Absage ist wörtlich anwendbar:

> *„Es ist eine BEHAUPTUNG des Rufers, keine Tatsache. `in setup` sagt nicht, dass die Marke
> auf `setup` steht; es sagt, dass jemand das glaubt. Um daraus etwas zu machen, müsste jede
> Aufrufstelle geprüft werden — und dann ist der Träger doch wieder die Marke."*

Und der zweite Halbsatz derselben Absage ist der eigentliche Preis:

> *„Es ist ein ZWEITER Mechanismus neben der Ordnung (W7: zwei Register über einer Sache)."*

**`§42` will `phase` auf `table`, `ops`, `fn` und `reg`.** Zwei davon (`fn`, `reg`) sind die
Marke. Die anderen zwei (`table`, `ops`) haben keine — dort ist `phase` entweder eine
Behauptung oder ein zweiter Mechanismus. *Der Vorschlag verallgemeinert nicht ein Konstrukt
über vier Träger; er verallgemeinert einen Namen über zwei Mechanismen.*

> **Und `fn` steht in beiden Lagern, je nachdem was `phase` dort heißt** — die Unterscheidung
> ist die von `PHASENKLASSE.md` §2 und gehört ausgesprochen, nicht verwischt:
>
> * `fn … phase <a> -> <b>` **ist** `advances` unter neuem Namen. Die Marke fließt weiter
>   durch die Signatur, `O003`/`O004`/`O006` greifen unverändert. **Zulässiger Tausch** —
>   und genau dieser Zweig ist es, der das eine Wort senkt.
> * `fn … phase <s>` — die Funktion behauptet eine Stufe, ohne einen Schritt zu tun. **Das
>   ist Form 3 wörtlich**, und §2 hat es am 2026-08-28 abgelehnt.
>
> `§42` schreibt nicht hin, welchen der beiden es meint. **Die Rechnung oben nimmt den
> günstigeren an** — den Tausch —, und selbst unter dieser Annahme kommt sie auf ein Wort.

### (c) Was `order` trägt, braucht `class … in` gar nicht — und umgekehrt

`class rw in setup, r in live` braucht die **Stufenmenge** und die Vollständigkeit (`R009`).
`advances` braucht die **Ordnung** (`O002`). Ein einziges `phase` müsste beides tragen und
wäre an der Registerzeile stärker, als die Registerzeile verlangt. *Von streng lässt sich
lockern, umgekehrt nie* — aber hier läuft es andersherum: die Verallgemeinerung ist an einer
Stelle **strenger** als der Sonderfall, den sie ersetzt.

---

## 4. Die zweite Marke — sie STIEGE, und das rettet den Vorschlag trotzdem nicht

Die Regel des Werkzeugs: *„Fällt die erste, ohne dass die zweite steigt, wurde Ausdruck
verloren statt getauscht. Bei einer Verallgemeinerung MUSS sie steigen."*

Stellungen heute, ausschließlich der Phasenmaschinerie zurechenbar:

```
order      1   in ['markorder']
advances   1   in ['fndecl']
                       -- in/class an regphasen/regdecl gehoeren nicht dazu:
                          sie stehen dort ZUSAETZLICH, nicht ausschliesslich
```

| Bauform | Wörter | Stellungen | Urteil der Ratsche |
|---|---|---|---|
| **heute** | 221 | 333 | — |
| `phase` nur an `fn`+`typedecl` (das, was gebaut ist) | **220** | 333 − 2 + 2 = **333** | *erste fällt, zweite steht* → **Ausdruck verloren** |
| `phase` zusätzlich an `table`+`ops` (das, was `§42` verspricht) | **220** | 333 − 2 + 4 = **335** | grün — **aber die zwei neuen Stellungen sind Form 3** |

> **Die einzige Bauform, unter der die zweite Marke steigt, ist genau die, die `PHASENKLASSE.md`
> §2 vor vier Tagen abgelehnt hat.** Die Ratsche ist damit erfüllt und der Begriff verletzt —
> und der Begriff war der Grund, aus dem Form 1 gewählt wurde: *„nicht weil es billiger war,
> sondern weil `FSTS` je Feld etwas anderes ist."*

---

## 5. Der teure Teil: **`§42` verspricht EINEN Absenkungssatz statt vier. Es sind NULL statt null.**

`§42` schreibt: *„Ein Konstrukt `phase` … bekommt EINEN Absenkungssatz statt vier."* Das ist
der größte Einzelposten von Teil VI. **Er ist leer, und zwar messbar.**

```bash
grep -n 'if t.ghost' crates/gabbro-check/src/emit.rs        # 764
sed -n '44,45p' crates/gabbro-check/src/emit.rs
```

> *„…**ghost types (they lower to NOTHING)**…"* — `emit.rs`:44

Und `PHASENKLASSE.md` §4, geschrieben am 2026-08-28, sagt dasselbe über die andere Hälfte:

> *„**Sie senkt nichts ab.** Der Erzeuger sieht die Phase nicht; `class` war noch nie eine
> Absenkung, sondern eine Ablehnung. Der phasenklassierte Zugriff ist geprüft oder gar nicht
> — er wird nicht anders übersetzt."*

**Eine Geistmarke erzeugt keine Zeile C. Eine Registerklasse erzeugt keine Zeile C.** Es gibt
heute *keine* vier Absenkungssätze für vier Bereiche, die ein Konstrukt zu einem
zusammenzöge — es gibt **keinen**, weil es nichts Erzeugtes gibt, worüber einer reden könnte.
*Viermal nichts ist nichts, und einmal nichts auch.*

### Welche Form der Satz HÄTTE, und woran er hängt

*Auftragsgemäß hingeschrieben und nicht gebaut — `beweise/` ist nicht dieses Revier.*

Es wäre **kein Absenkungssatz**. Die Bauform von `Absenkung_Parametrisch.thy` — *„das
erzeugte C berechnet die Modellfunktion"* — hat keinen Gegenstand, wo nichts erzeugt wird.
Die tragfähige Form ist die von `Table_Ops_Erhaltung.thy`: **ein Erhaltungssatz über der
Stufenverfolgung.**

```
Satz (phasen_pass_ist_korrekt).
  Sei P ein Programm, das `phasen::pass` ohne Absage passiert.
  Sei sigma eine Ausfuehrung von P und z ein Registerzugriff in sigma auf ein Register
  mit `class k_1 in s_1, …, k_n in s_n`.
  Dann gilt: entweder steht bei z KEINE Marke der zugehoerigen Ordnung im Sichtbereich
  -- dann liegt die Zugriffsart im SCHNITT aller k_i --,
  oder die Marke steht auf genau einer Stufe s_j, und die Zugriffsart liegt in k_j.
```

**Er hängt an vier Dingen, und drei davon existieren nicht:**

1. **Einer operationalen Semantik des Phasenflusses.** `phasen.rs` ist ein Datenflusspass
   über dem AST; „die Stufe, auf der die Marke bei `z` steht" ist heute nur als Zustand
   dieses Passes definiert und nicht als Aussage über einen Lauf. *Ohne sie ist der Satz
   eine Umschreibung des Codes und kein Satz über ihn.*
2. **Der Löschungsaussage** *(„ein Geistwert existiert zur Laufzeit nicht")*. Sie steht in
   `emit.rs`:20 als Kommentar und in keiner Theorie. **Sie ist die Brücke zwischen „die Marke
   steht auf `s_j`" und irgendetwas, das die Maschine tut** — und sie fehlt.
3. **Dem Schnitt als Teil der Aussage.** `PHASENKLASSE.md` §3 hält fest, dass eine lineare
   Marke eine **Erlaubnis** ist, die niemand halten muss. Der Satz ist also dort, wo keine
   Marke steht, **leer** — und ein Satz, dessen erster Zweig vakuum ist, muss diesen Zweig
   im Wortlaut tragen, sonst liest ihn jemand als Zusage.
4. **`Consuming.thy`**, das schon liegt und die Linearität hält — der einzige der vier, den
   es gibt.

> **Und darum ist er kein Posten für `§42`, sondern einer für `§31`.** Er ließe sich heute
> schreiben, ohne dass ein einziges Wort dazukäme oder fiele. *Ein Satz über eine gebaute
> Maschinerie ist unabhängig davon, wie ihre Schlüsselwörter heißen.*

---

## 6. Die vier „weiteren Stellen" — **zwei haben das Konstrukt schon, eine braucht keines**

| `§42`s Stelle | nachgeschlagen | **Befund** |
|---|---|---|
| **`boot`** — vor/nach `bss_nullen` | `beispiele/22-bootstrecke.gab`: `linear ghost type BootPhase order { roh, mmu, caps, eps, autoritaet, dienste }` + **6× `advances`** | **hat das Konstrukt.** Keine Handkombination |
| **Speicher Kern↔Gerät** | 30 von 104 `consumes` in einer `fn` mit `advances` (Abschnitt 2.2) | **hat das Konstrukt.** Die 74 anderen haben keine Phase |
| **`count`/`backed`** | `dokumente/PLAN.md`:2578–2580 | **braucht keines** — s. unten |
| **Capability im CDT** | `dokumente/SPRACHE.md`:1554 | **einzige echte Lücke — und `phase` schließt sie nicht** |

### `count`/`backed`: `PLAN.md` hat die Frage vor Wochen beantwortet

> *„Also entweder **monoton** — die einfache, ehrliche Fassung — oder das Verkleinern ist ein
> Phasenschritt, nach dem kein alter Index überlebt. **Für das Zweite gibt es die
> «B37»-Maschinerie schon (`order`/`advances`), und für das Erste braucht es nichts.**"*
> — `dokumente/PLAN.md`:2578–2580

**Beide Zweige sind versorgt, und keiner davon durch ein neues Wort.** `§42` zählt die Stelle
als fünfte Rechtfertigung; sie ist keine.

### Die CDT ist die einzige offene — und sie ist keine Kette

`SPRACHE.md`:1554 bucht *CapSpace/CDT einschließlich `revoke`* als `table … ops` + `by
consuming` + `by induction over`. Der Grund, warum `order`/`advances` dort nicht greift, ist
**nicht** ein fehlendes Wort:

* **Eine `order` liegt auf EINER linearen Marke.** Eine CDT hat *n* Capabilities, jede mit
  eigenem Zustand, und `phasen.rs` verfolgt Marken **je Rumpf, je Variable**
  (`markenordnung`, `sammle_markenordnung`).
* **„abgeleitet → delegiert → widerrufen" ist kein linearer Gang, sondern ein BAUM.** Ein
  Widerruf läuft rekursiv über den Teilbaum; `O002` prüft einen Vorwärtsschritt zwischen zwei
  Stufen und kennt keine Rekursion über Kinder.
* `PHASENKLASSE.md` §4 hält es schon fest: *„Sie macht die Stufe nicht modulübergreifend
  genau."*

**Ein Wort `phase` ändert daran nichts.** Was fehlt, ist eine Erreichbarkeitsaussage über
eine verlinkte Struktur — und die ist, wie `messung/proben/probe-zeugenpflicht.gab` es
formuliert, *„keine lokale Eigenschaft"*.

---

## 7. `§42` × `§43`: sie machen einander **teurer**, nicht billiger

*Auftragspunkt 4, und der Befund geht in die andere Richtung als die Frage.*

### `§43`s Prämisse ist im Baum schon widerlegt

`§43` schreibt: *„die Absenkung ist trivial — der Index steht ohnehin im C."*
`messung/proben/probe-zeugenpflicht.gab`:33–58, gemessen am **2026-08-31**, also *einen Tag
vor* `§43`:

> *„**Gemessen stimmt das nicht.** `Griff` ist `ghost` und wird vor der Codeerzeugung
> geloescht — sein Nutzdatenwert mit ihm. … Der Zeuge ist weg; der Index ueberlebt **nur,
> weil er als eigenes Argument danebensteht.** … **Drei fehlende Absenkungen, nicht eine**,
> und die tragfaehige kostet ein Maschinenwort je Zeuge."*

```
linear type Griff(index into Arena);
[C001] no lowering: return type       (`-> Griff`)
[C001] no lowering: parameter type    (`g : Griff`)
[C001] no lowering: `match` over something other than an `option index into T`
```

### Und `§43` kostet gar kein Wort — weil die Grammatik es schon schreibt

```bash
sed -n '333,334p' dokumente/SYNTAX.md
# typedecl = [ "pub" ] [ "opaque" ] [ "linear" [ "ghost" ] ] [ "tagged" ] "type" …
```

**`ghost` hängt schon heute optional an `linear`.** `linear type Griff(index into Arena);`
parst und typt — die Probe misst `8 items, 0 errors, 0 hints`. Die Unterscheidung, die `§43`
als neues Wort `witness` einführen will, **steht bereits in der Grammatik als das Weglassen
von `ghost`.** Was fehlt, sind drei `C001` im Erzeuger.

> **Kein neues Wort schließt ein `C001`.** `§43` ist kein Wortschatzposten, sondern ein
> Erzeugerposten — und er gehört unter `§31` („Absenkungsabdeckung — alle erzeugten Formen"),
> nicht in eine Liste, die sich gegen die Ratsche rechtfertigen muss.

### Die Wechselwirkung, und sie ist ein Aufschlag

Heute ist **alles**, was `§42` anfasst, `ghost` — und darum senkt die ganze Phasenmaschinerie
nichts ab und schuldet keinen Satz (Abschnitt 5). Eine Phase an einem `witness` ist eine
Phase an einem Wert, **der ins C überlebt.** Damit trägt die Phasenmaschinerie zum ersten Mal
eine Absenkungsschuld — genau die, die sie heute nicht hat.

> **`§42` ist billig, weil er unsichtbar ist. `§43` macht ihn sichtbar. Zusammen sind sie
> teurer als einzeln.**

---

## 8. Das Ergebnis, und es ist eine Absage

| `§42`s Behauptung | gemessen |
|---|---|
| *„der einzige, der den Wortschatz SENKT"* | **stimmt — um EINS** (221 → 220), nicht um vier |
| *„ersetzt Sonderregeln in vier Bereichen"* | **zwei haben das Konstrukt schon, einer braucht keins, einer ist kein Gang, sondern ein Baum** |
| *„bekommt EINEN Absenkungssatz statt vier"* | **null statt null** — eine Geistmarke senkt nichts ab |
| *„auf `table`, `ops`, `fn` und `reg` anwendbar"* | **zwei davon sind `PHASENKLASSE.md`s Form 3**, vor vier Tagen mit Begründung abgelehnt |
| die Tafel 14 / 31 / 6 / 102 | **über 526 Dateien erhoben, 357 davon Giftproben.** Im Ratschenkorpus: 3 / 12 / 3 / 52 |

> ### **Regel A: nicht gebaut.**
>
> Ein Wort für ein Wort ist ein zulässiger Handel — aber `§42` verlangt dafür, eine
> Entscheidung zurückzunehmen, die vier Tage alt ist und einen Begriff und keinen Preis als
> Grund hatte. **Ein Wort ist zu wenig dafür.**

**Was `§42` behalten sollte:** die Beobachtung, dass der Mechanismus allgemein ist, und den
Namen — *Typestate*. `SPRACHE.md`:100 bucht ihn seit jeher als **M2**, *„linear value whose
type carries the state"* — **eine Ableitung, kein Konstrukt.** Genau dort steht er richtig.

---

## 9. Was ungemessen bleibt — benannt, nicht verschwiegen

* **Ob ein `phase` an `table`/`ops` sich doch bauen ließe, ohne Form 3 zu sein.** Gemessen
  ist, dass dort kein Wert in einer Signatur steht, durch den die Stufe fließen könnte;
  **nicht** gemessen ist, ob eine dritte Bauform existiert, die `PHASENKLASSE.md` §2 nicht
  betrachtet hat. Die dortige Tafel führt drei Formen, und drei ist keine Vollständigkeit.
* **Ob die 74 `consumes` ohne Phase wirklich alle phasenfrei sind.** Gezählt ist die
  Abwesenheit von `advances` in derselben Deklaration — ein Textabgleich über einer
  Regex-Zerlegung nach `fn`-Köpfen, nicht über dem Parser (W10). Eine Funktion, deren Phase
  in einer *anderen* Funktion steht, zählt hier als phasenfrei.
* **Der K9-Befund zu `count`/`backed`** (`setzen(100); setzen(200); narrow i to
  0..<hinterlegt; return h.slots[i].wert;` bei `i = 150` → 0 errors, 0 hints) **ist in diesem
  Baum nicht auffindbar** — weder in `dokumente/` noch in `messung/`. `PLAN.md`:2578 trägt die
  *Entscheidung*, nicht die Messung. **Nachgerechnet ist hier die Entscheidung, nicht der
  Befund.**
* **Die zwei Zahlen, die um zwei danebenliegen** (`§42`: 6 und 102; hier: 7 bzw. 5 und 104
  bzw. 100, je nach Kommentarbehandlung). Die Grundgesamtheit ist rekonstruiert und die
  Größenordnung damit belegt; **die exakte Kommentarregel von `§42` ist es nicht.**
* **Ob `phase` an `reg` die Vollständigkeitspflicht `R009` überhaupt behalten könnte.**
  Nicht durchgerechnet — der Vorschlag fällt vorher.
* **Nichts gebaut heißt: nichts gegengeprüft.** Keine Gegenrichtung über den Korpus, keine
  zwei Binärprogramme, kein byteweiser Vergleich. *Die Absage braucht sie nicht, und sie
  ersetzt sie auch nicht.*
