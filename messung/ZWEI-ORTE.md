# «B17» — zwei Orte in einem Zug: die Form stand da, die falsche Hälfte auch

*Entschieden am 2026-08-28. Jede Zahl nennt den Befehl, der sie nachrechnet.*

> **W24 zuerst, und es hat die Frage zum vierten Mal umgedreht.** `PFLICHTEN.md` führte
> «B17» zweimal als offene Lücke, und die erste der beiden Zeilen las:
>
> > *„`transition` schreibt genau EINEN `place`. Die ganze Aussage des Fragments, und sie ist
> > nicht schreibbar."*
>
> **Das ist falsch, und es war es immer.** `transset = placeshift { "," placeshift }` steht
> in `SYNTAX.md`:1256 mit dem Kommentar *„MEHRERE Orte in EINEM Zug"*, `parse.rs::transition`
> trägt die Komma-Schleife (`if !self.friss_z(Z::Komma) { break; }`), und
> `beispiele/02-geraet.gab`:42 **benutzt die Form seit jeher**:
>
> ```gabbro
> transition irq_umlenken { GCMD.IRE: 0 -> 1, GCMD.SRTP: 1 -> 1 }
> ```
>
> Dieselbe Klasse wie «B9» am 2026-08-25: **eine Zeile, die nur nicht mitgeführt wurde.**

---

## 1. Was der unveränderte Prüfer wirklich sagt

Sieben Proben, alle durch `./target/release/gabbro pruefe` **vor** jeder Änderung
(Server `ki-pc-fisch-101:gabbro-i`, `4dd17209`).

| Probe | geschrieben | gemessen |
|---|---|---|
| **A** | die Form des Fragments wörtlich, `state Rendezvous **over** Endpoint { … }` | `Fehler: [P001] `{` erwartet, `over` gefunden` — **ein einziges Token** |
| **B** | dieselbe Form ohne `over`, zwei Orte, `Some(cl)`/`Some(sv)` im Ziel | **0 Fehler, 0 Hinweise** |
| **C** | zwei Orte, keine frischen Namen (die Form aus `beispiele/02`) | **0 Fehler, 0 Hinweise** |
| **D** | die zwei nackten Zuweisungen aus `FRAGMENTE.md`:690-691, Tabelle mit `invariant … runs online` | **0 Fehler** (nur `K001`, eine zu kleine Kostenzusage) |
| **E** | dieselben zwei Zuweisungen **in einem `breaking`-Block** | **exakt dieselbe Ausgabe wie D** |
| **F** | `breaking gibt_es_gar_nicht { … }` — eine Invariante, die es nicht gibt | **0 Fehler, 0 Hinweise** |
| **G** | `breaking` auf eine Invariante von `Endpoint`, daneben `Objekte` **mit `ops`** | `[D009] `breaking` lets `paarig in oeffnen` rest, and **`Objekte`** declares `ops`` |

**Drei Befunde, und keiner davon ist „eine fehlende Form".**

1. **Die Mehrfachform parst** (B, C). Auch die dritte Klage des Fragments — *„`Some(cl)` im
   Zielausdruck bindet einen frischen Namen, dafür gibt es keine Produktion"* — trifft am
   Parser nicht zu; was fehlt, ist nicht die Produktion, sondern **jeder Leser**: `state`
   wird von `namen.rs` auf Doppelnamen geprüft und sonst von niemandem, und `emit.rs`:1894
   weigert sich benannt. *Ein `state`-Rumpf ist heute eine Deklaration ohne Prüfung.*
2. **Der Zwischenzustand wird von NIEMANDEM geprüft** (D). Es gibt keinen Pass, der eine
   `invariant … runs online` an einer Anweisungsgrenze ansieht — `Laeuft::Online` wird
   geparst, gespeichert und in `emit.rs`:7672 als Kommentarwort wieder ausgegeben. **Die
   zweite «B17»-Zeile beschreibt damit keine Sprachlücke, sondern eine Prüferlücke** — und
   eine, für die der Korpus zwei saubere Fundstellen hat (`grep -c 'runs online'
   beispiele/*.gab` → 2).
3. **`breaking` verspricht heute nichts** (E, F) und **sagt einmal das Falsche** (G).

---

## 2. Die zwei Formen, gegeneinander

### Form 1 — `state <N> over <Träger> { transition … }`, und der Übergang wird gerufen

So wollte es das Fragment: `open(e, caller, picked);` schreibt beide Orte in einem Zug.

**Dafür**

* Es steht an EINER Stelle, und die Stelle ist die Deklaration des Trägers — nicht der Rumpf.
* Der Wortschatz führt `transition` und `state` bereits; `over` steht schon im Wortschatz
  (`by induction over`), es kostet **kein neues Wort** (`SCHLEIFENINVARIANTE.md` §3).
* Die Absage des Erzeugers benennt die fehlende Zeile von selbst: *„the transitions are a
  proof device over a carrier that is declared **ELSEWHERE**"*. Der Erzeuger weiß, was fehlt.

**Dagegen — und die dritte Zeile entscheidet**

* **Es ist nicht ein Token, sondern sechs Baustellen.** `over` in `statedecl`; Namensauflösung
  der `placeshift`-Orte gegen die Slotfelder des Trägers; die frischen Namen im Ziel
  (`Some(cl)` bindet `cl` — woher?); Rufbarkeit (heute registriert `umgebung.rs`:602 nur
  `d.uebergaenge`, also **Geräte**-Übergänge, als Funktionen); Argumente (das Fragment ruft
  mit dreien, ein `transition` hat `parameter: Vec::new()`); eine Absenkung, wo heute eine
  Weigerung steht.
* **Die Zusage, die dabei herauskäme, ist nicht haltbar.** Die Schablone dafür gibt es schon
  (`schablonen.rs::transition.transset`, `Stand::Entworfen`), und ihre Pflicht sagt es selbst:
  *„kein Zwischenzustand ist beobachtbar **für einen benannten Beobachter** … Ohne benannten
  Beobachter ist die Zusage auf einem Mehrkerner leer."* Ein `transition`, der zwei Orte
  „atomar" schreibt, senkt zu **zwei `store`** ab. Auf einem Kern deckt der Kontrollfluss den
  Zwischenzustand; auf mehreren deckt ihn nur eine Sperre — und die steht dann woanders.
* **K100s zweites Tor steht davor.** `transition.transset` dürfte von *entworfen* nach
  *getragen* nur wandern, wenn der Beweis vorher steht. Der Beweis wäre eine Aussage über das
  Speichermodell, nicht über eine Tabelle — dieselbe Ecke, in die `exchange.rmw` seine
  Atomaritätshälfte ausdrücklich abgeschoben hat (*„KEINE Schablonenpflicht, sondern eine
  Annahme der Axiomschicht"*).
* **Und der Bedarf ist nicht gemessen.** Fundstellen für einen Mehrort-Übergang **an einer
  Tabelle** im sauberen Korpus: **0**. Die eine Fundstelle der Mehrfachform steht an einem
  `device` und trägt dort schon.

### Form 2 — `breaking I { … }`: der Bereich wird benannt statt geleugnet

```gabbro
breaking antwortpflicht_paarig {
    e.slots[kern].anrufer     = Some(ruft);
    e.slots[kern].antwortende = Some(dient);
}
```

**Dafür**

* **Es ist kein neues Wort und keine neue Produktion.** `breakstmt = "breaking" identlist
  block` steht seit jeher in `SYNTAX.md`:882, `SPRACHE.md` §8.3 spezifiziert es samt
  Buchungsregel, der Parser trägt es, `kbedingung.rs` sammelt es, `D009` sagt darüber ab.
  **Sieben Leser, null saubere Korpusstellen.**
* **Die Zusage ist haltbar, weil sie die umgekehrte ist.** Form 1 verspricht, dass es keinen
  Zwischenzustand gibt — und braucht dafür einen Beobachter, den sie nicht hat. Form 2 sagt:
  *der Zwischenzustand IST da, hier steht er, und die gehaltene Sperre sagt, wer ihn nicht
  sieht.* Der Beobachter ist damit nicht weggelassen, sondern **die `requires Held(EPS)`
  danebenstehende Zeile**. Das ist genau der Preis, den `TODO.md`:1424 nennt: *Sichtbarkeit
  statt Verstecken.*
* **Die Buchhaltung ist schon verdrahtet.** `Traeger::k_haelt()` verlangt
  `breaking.is_empty()`; ein Bereich, in dem ein Satz ruht, fällt aus der Zählung *„K hält"*
  heraus, und `SPRACHE.md` §10.2.1 hat das am 2026-08-20 gemessen. **Eine Menschenpflicht,
  die als Menschenpflicht gezählt wird.**

**Dagegen — und es wird nicht kleingeredet**

* **`breaking` legalisiert eine Verletzung.** Ob Sichtbarkeit dafür genug ist, ist offen
  (`TODO.md`:1424, `SPRACHE.md`:2627 führt es als einen der zwei unbequemen Posten). Diese
  Messung entscheidet das **nicht**; sie entscheidet nur, welche der beiden Formen die
  Stelle heute schreiben kann.
* **Es steht im Rumpf, nicht an der Deklaration.** Zwei Rümpfe, die dieselbe Paarung
  schreiben, nennen sie zweimal. Form 1 nennt sie einmal. *Das ist der ehrliche Vorteil der
  verworfenen Form, und er bleibt einer.*
* **`breaking` hat keine Absenkung.** `emit.rs`:5569 weigert sich benannt und sagt warum.
  Damit ist `beispiele/53-zwei-orte.gab` eine Datei, die **prüft** und nicht **erzeugt** —
  ausgewiesen, nicht verschwiegen.

---

## 3. Die Wahl, und was daraus wirklich gebaut wurde

**Gewählt ist Form 2 — und der Bau ist kleiner als beide Formen, weil er unter ihnen liegt.**

Was `breaking` fehlte, war nicht eine Regel über Bereiche, sondern **sein Gegenstand**:
`SPRACHE.md` §8.3 hängt drei Zusagen an den Namen `I` (Prämisse gesperrt, `requires I`/
`maintains I` nicht rufbar, am Ende wiederhergestellt oder gebucht) — und **`I` wurde nie
nachgeschlagen** (Probe F).

| gebaut | |
|---|---|
| **`D013`** | `breaking I` nennt nichts, was diese Einheit als Invariante erklärt. Fünftes Glied der Klasse *eine Klausel, deren Gegenstand nirgends steht* — `M133`, `N033`, `S007`, `N020` |
| **`D009` verengt** | der Bruch wird dem Träger zugeschrieben, **dessen** Invariante er nennt. Probe G zeigte die alte Fassung: sie nannte `Objekte`, während `paarig` an `Endpoint` steht und der Block `Objekte` nie anfasst. *Eine Absage, die plausibel klingt und den falschen Träger nennt* — dieselbe Klasse wie `W16` |

Die Quelle der Auflösung ist **dieselbe Liste, die `maintains` annimmt**
(`m1.rs::sammle_spezifikationen`): `table`-, `group`- und `walk`-Invarianten sowie `spec fn`.
*Zwei Listen für denselben Begriff wären die Stelle, an der die beiden Klauseln
auseinanderlaufen.*

**Und die Verwandtschaft der beiden Hälften ist keine Kosmetik:** die Verengung von `D009`
war **erst möglich**, nachdem der Name auflöst. Die fehlende Regel und die falsche hatten
eine Ursache.

---

## 4. Was NICHT gebaut wurde, und warum

| nicht gebaut | Grund |
|---|---|
| `state <N> over <Träger>` | sechs Baustellen für eine Zusage, die ohne benannten Beobachter leer ist; K100s zweites Tor steht davor; **0 gemessene Korpusstellen** |
| ein rufbarer `state`-Übergang mit Argumenten | dasselbe, plus: `transition` hat weder `parameter` noch `costs` in der Grammatik |
| eine Regel *„zwei Schreibzugriffe auf Felder derselben Online-Invariante ohne `breaking`"* | **Regel A.** Der saubere Korpus hat **2** Dateien mit `runs online` (`beispiele/07`, `/47`); eine Regel, die auf zwei Stellen zielt und an keiner fällt, ist eine Vermutung. *Und sie wäre die einzige, die «B17» wirklich erzwingt* — sie steht deshalb als benannte Absage hier und nicht als stille Auslassung |
| eine Regel *„der `breaking`-Block muss den Träger auch schreiben"* | §8.3 sperrt im Block auch **Rufe** (`requires I`/`maintains I`); ein Bereich ohne eigenen Schreibzugriff ist damit sinnvoll, und die Regel wäre zu eng |
| die Absenkung von `breaking` | `emit.rs` weigert sich benannt und mit Grund; die Weigerung ist heute richtig, weil der Bereich im C verschwände und das Erzeugnis wie ein Programm ohne Pflicht aussähe |

---

## 5. Die Fundstellen

* `beispiele/53-zwei-orte.gab` — **die erste saubere Korpusstelle von `breaking` überhaupt.**
  Bis heute: null saubere, eine giftige (`beispiele/gift/226`). *W23: sie zählt als Stelle,
  nicht als Bedarf* — sie ist für diese Regel geschrieben.
* `beispiele/gift/351-breaking-nennt-nichts.gab` — `-- erwartet: D013`.
* `crates/gabbro-check/src/kbedingung.rs` — `invariantentraeger`,
  `breaking_nennt_eine_invariante`.
* `crates/gabbro-check/src/saetze.rs` — `kbedingung.breaking-nennt-etwas`, mit Vorbehalt.
* `instrumente/mutiere-pruefer.py` — `breaking-darf-ins-leere-nennen`.

### Die Proben selbst

```bash
# A -- die Form des Fragments woertlich
state Rendezvous over Endpoint {
    transition open  { caller : None -> Some(cl), reply_owner : None -> Some(sv) }
}
#   Fehler: [P001] :23:18: `{` erwartet, `over` gefunden

# B -- dieselbe Form ohne `over`
state Rendezvous {
    transition open  { caller : None -> Some(cl), reply_owner : None -> Some(sv) }
}
#   6 Items, 0 Fehler, 0 Hinweise

# F -- `breaking` nennt nichts (vor D013)
breaking gibt_es_gar_nicht { e.slots[kern].caller = 1; }
#   4 Items, 0 Fehler, 0 Hinweise
```
