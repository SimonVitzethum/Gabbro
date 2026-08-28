# «B13» — die Zählung über einem zweiten Träger: **eine Lücke, nicht zwei**

*Gemessen am 2026-08-28. Kein Konstrukt gebaut — und der Grund steht in §4, nicht zwischen
den Zeilen.*

> **W24 zuerst, und die Zeile hat sich halbiert.** `PFLICHTEN.md`:50 führt «B13» so:
>
> > *„`pred` knows no aggregation **and no cross-table domain**. The core of the capability
> > system's bookkeeping."*
>
> **Die zweite Hälfte blockiert das Beispiel nicht.** Sechs Proben durch den unveränderten
> Prüfer sagen: die trägerübergreifende Aussage ist schreibbar und geht durch, an einer
> `group` wie an einer `table … invariant`. Was fehlt, ist **genau eine** Sache — und ihre
> Ursache ist enger, als die Zeile vermuten lässt.

---

## 1. Die Proben

Alle durch `./target/release/gabbro pruefe`, Binärprogramm `4dd17209`, Server
`ki-pc-fisch-101:gabbro-i`.

| Probe | geschrieben | gemessen |
|---|---|---|
| **J** | die Verbindungsaussage an einer `group` — quantifiziert über `Kappenraum`, liest `Objekte` | **0 Fehler** (2 `H008`-Hinweise, weil die Probe keine Funktion hat, die die Sperren nimmt) |
| **N** | **dieselbe Aussage an einer `table … invariant`**, mit `Objekte.slots[…]` im Prädikat | **0 Fehler, 0 Hinweise** |
| **K** | die Buchführung wörtlich: `… == count(s in slots of Kappenraum : Kappenraum.slots[s].objekt == o)` | `Fehler: [P012] Praedikat erwartet, Bezeichner `Objekte` gefunden` |
| **L** | drei Vergleiche, sonst byteweise gleich: `== 3` · `== anzahl(o)` · `== count(o)` | die ersten beiden parsen, **der dritte nicht** |
| **M** | nur `== anzahl(o)` — ein Ruf auf eine Funktion, die es nicht gibt | **0 Fehler, 0 Hinweise** |
| **O** | derselbe Ruf ins Leere an drei Stellen: Tabelleninvariante · `spec fn`-Rumpf · `requires` | Invariante **still**, `spec fn` **still**, `requires` → `E009` |

### Was daraus folgt, Zeile für Zeile

**(1) Die trägerübergreifende Aussage ist schreibbar** (J, N) — und zwar **nicht erst seit
`group`**. Ein Prädikat nennt Orte, ein fremder Tabellenname ist ein Ort, und `place` in
`pred` hat das nie eingeschränkt. *Was `group` am 2026-08-16 gebracht hat, ist nicht die
Form, sondern ihr geprüftes Zuhause*: `U007` verlangt, dass eine Gruppen-Invariante
mindestens zwei Träger nennt, `U002`/`U003`/`U005`/`U006` halten die Sperrordnung darüber.
**Die Zeile in `PFLICHTEN.md` sagt „nicht schreibbar", gemeint war „nicht gehalten".**

**(2) Die Aggregation fällt am WORT, nicht an der Produktion.** Probe L ist der ganze Beweis:
`anzahl(o)` parst, `count(o)` nicht — der einzige Unterschied ist, dass `count` im Wortschatz
steht (`kw.rs`:168, `res`) und darum in Ausdrucksstellung kein Bezeichner sein darf. **Ein
Ruf steht in einem Prädikat also längst**; was fehlt, ist die Produktion, die `count` dort
eine Bedeutung gibt. *Und weil das Wort schon reserviert ist, kostet die Form kein neues* —
`SCHLEIFENINVARIANTE.md` §3, die billigste Seite, die eine Erweiterung haben kann.

**(3) Und die Messung schwächt sich selbst ab, ausdrücklich.** Probe M und O zeigen: ein Ruf
auf eine Funktion, **die es nicht gibt**, geht in einer Tabelleninvariante und in einem
`spec fn`-Rumpf mit null Meldungen durch; nur im `requires` einer `impl fn` fällt `E009`, und
das über den Aufrufgraphen. **„Parst und geht durch" heißt an dieser Stelle also weniger als
anderswo** — die Namen in einem Invariantenprädikat werden kaum aufgelöst. *Das ist derselbe
Befund wie `D013` heute Abend, eine Fläche weiter*, und es steht hier, damit diese Messung
nicht dieselbe Überdehnung begeht wie die Zeile, die sie korrigiert (W10).

---

## 2. Der Bedarf — gemessen, und er ist echt

**W23: saubere Beispiele und Giftproben getrennt.** Gezählt ist die Bauform *„Tabelle A hat
ein Zählfeld, Tabelle B trägt `index into A`"* — die Gestalt von «B13».

| Topf | Stellen |
|---|---:|
| `beispiele/` (sauber) | **2** — `01-tabelle.gab` und `09-ohne-zeiger.gab`, beide `Kappenraum.objekt → Objekte.zaehler` |
| `beispiele/gift/` | *nicht gezählt* — gehört in keine Bedarfsmessung |
| `dokumente/FRAGMENTE.md` F1 (:174-177) | 1, und es ist der teuerste Befund an F1 |
| Caprock, gemessen 2026-08-14 (`MESSUNGEN.md`, Antwort 1) | **K2 von drei Verbindungs-Invarianten** — *„`refcount(o)` == number of slots pointing at it — that is «B13» literally"*, und `cap_space.rs` führt sie **von Hand in Verus** als Teil von `cap_inv` |

**Das ist mehr Bedarf, als die meisten gebauten Konstrukte dieses Ordners vorweisen.** Die
Absage unten stützt sich deshalb **nicht** auf Regel A.

---

## 3. Zwei Formen, gegeneinander

### Form 1 — `count(x in domain : pred)` als Atom in `pred`/`expr`

```gabbro
invariant zaehler_stimmt cost O(n) runs offline :
    forall o in slots of Objekte :
        Objekte.slots[o].zaehler == count(s in slots of Kappenraum : Kappenraum.slots[s].objekt == o);
```

**Dafür**

* **Kein neues Wort** (Probe L): `count` ist reserviert, seit es `table T count N` gibt.
* Sie liest sich wie `forall`/`exists` und benutzt dieselbe `domain`-Produktion — **acht
  Domänen ohne eine neunte**.
* Sie sagt genau das, was Caprocks Prüfsumme sagt, und die steht dort schon formal
  (`cap_inv`, Verus). *Die Vorlage ist da, nicht der Entwurf.*

**Dagegen**

* **Die Kostenzeile wird falsch, und niemand merkt es.** `cost O(n)` an einer Invariante mit
  einem geschachtelten `count` über einen zweiten Träger ist **O(n·m)**. Solange `cost` eine
  vom Menschen geschriebene Zahl ohne Prüfer ist, erzeugt die neue Form **stillschweigend
  falsche Kostenzusagen** — dieselbe Bewegung wie eine Klausel ohne Leser, nur mit einer
  Zahl daneben.
* **Der Erzeuger schuldet eine Doppelschleife.** Eine `runs offline`-Invariante gehört in das
  Prüfgerüst; `count` heißt dort zwei ineinanderliegende Läufe über zwei Träger. Das ist
  Erzeugerarbeit mit einer Erhaltungsfrage, also **eine Schablone** — und K100s zweites Tor
  verlangt den Beweis **davor**.
* **Und Isabelle muss mit.** `gabbro pflichten --isabelle` schreibt das Pflichtenregister als
  Theorie; ein `count` braucht dort sein Gegenstück, sonst steht eine Pflicht im Register,
  die die Theorie nicht ausdrücken kann.

### Form 2 — die Zählung als `spec fn` mit einem Rumpf

```gabbro
spec fn refs(c : ptr<normal, r> Kappenraum, o : index into Objekte) -> u32
    effects { pure }
    = ??? ;
```

**Dafür**

* Sie erfindet gar nichts: `spec fn` gibt es, `maintains` nimmt sie, `M131` prüft sie.
* Sie hält die Aggregation **aus dem Prädikat heraus** und damit aus `cost`.

**Dagegen — und das ist tödlich**

* **Der Rumpf einer `spec fn` ist ein `pred`.** Ein Prädikat liefert `bool`, keine Zahl; eine
  Rekursion über Slots gibt es nicht, und `traverse` ist eine Anweisung. **Die Form kann die
  Zählung genau so wenig aussprechen wie die Invariante** — sie verschiebt die Lücke nur eine
  Deklaration weiter.
* Probe M zeigt die Falle dazu: `== anzahl(o)` geht heute mit **null Meldungen** durch. Wer
  Form 2 „benutzt", ohne die Funktion schreiben zu können, bekommt eine grüne Datei und eine
  Invariante, die nichts behauptet.

### Und die dritte, die keine ist: `accumulates … merge add`

`accdecl` (`SYNTAX.md`:282) ist eine **Laufzeit**-Zelle je Kern mit einem Verknüpfer — sie
zählt, was das Programm tut, nicht, was in einer Tabelle steht. *Ein Zähler, der mitzählt,
ist keine Aussage über einen Zustand.* Sie steht hier, weil sie beim Wortschatzdurchgang wie
eine Antwort aussieht.

---

## 4. Die Absage, benannt

**«B13» bleibt offen, und zwar in der geschärften Fassung: nur die Aggregation, nicht die
trägerübergreifende Domäne.** Gebaut wurde heute nichts, und die Gründe sind zwei, keiner
davon „kein Bedarf":

1. **Der Schwanz ist länger als die Form.** Die Grammatikzeile kostet kein Wort und einen
   Nachmittag; was daran hängt, sind eine **Kostenregel** (sonst lügt `cost O(n)`), eine
   **Erzeugerschablone** mit Erhaltungsfrage und ein **Isabelle-Gegenstück**. K100s zweites
   Tor steht vor dem mittleren Stück, und das heißt: **erst der Beweis.**
2. **Und `PLAN.md`:946 hat «B13» ausdrücklich AUSSORTIERT** — *„out. `o.refcount == count(…)`
   names the subject, not the machine — that is logic."* Diese Messung widerlegt das nicht;
   sie widerlegt nur den Grund, mit dem die Lücke bisher beschrieben wurde. **Ein Posten, der
   auf der Planebene draußen ist, wird nicht durch eine billige Grammatikzeile hereingeholt.**

**Was die Messung dagegen sofort ändert:** die Zeile in `PFLICHTEN.md` nennt zwei Ursachen,
und eine davon trägt nicht. Sie ist berichtigt — *dieselbe Bewegung wie bei «B9» am
2026-08-25 und «B17» heute Abend, und es ist die dritte innerhalb von vier Tagen.*

> **Die Bauart, zum dritten Mal:** ein Befund von 2026-08-14 wird in eine Zeile
> zusammengezogen, die Zeile wird elf Tage lang gelesen und nie gegen den Prüfer gehalten.
> *Was ein einziger Lauf gekostet hätte, hat drei Zeilen lang eine Sprache beschrieben, die
> es nicht mehr gab.*

---

## 5. Wenn es doch gebaut wird — die Reihenfolge steht fest

1. **Der Beweis zuerst** (K100, zweites Tor): dass die erzeugte Doppelschleife die Zählung
   wirklich liefert, und unter welcher Voraussetzung. Vorbild: `Table_Ops_Erhaltung.thy`.
2. **Die Kostenregel**, bevor die Form da ist — sonst steht am ersten Tag eine falsche
   `cost O(n)` im Korpus, und sie fällt bei keinem Pass.
3. **Dann die Grammatikzeile**, und sie kostet kein Wort.
4. **Giftprobe zuerst, Beispiel danach** — nicht umgekehrt: eine `count`-Form ohne Regel wäre
   genau die stille Datei, die Probe M vorführt.
