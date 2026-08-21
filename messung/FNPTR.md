# `fnptr` — vier Hälften, gemessen und gebaut

*Arbeitslauf 2026-08-21. Reihenfolge nach dem TODO-Posten: **Erzeuger → Ruf über einen Ort →
Absenkung → Vertrag** — und die vierte ist nicht nachgereicht worden, weil der Ruf sie in
derselben Zeile erzwingt, in der er entsteht.*

`messung/ERZEUGER.md` §2 hat diesen Posten am selben Tag als **„NICHT gebaut"** gebucht, mit
Zahl und Grund. Die Zahl stimmt weiter (die Messung darunter rechnet sie nach); die
**Entscheidung ist überholt**, und der Grund dafür steht in §6: die Sperre war nicht der
Bedarf, sondern die Reihenfolge — und die Reihenfolge lässt sich in einem Lauf einhalten.

| # | Hälfte | vorher | heute |
|---|---|---|---|
| 1 | der **Erzeuger** — die Sprache kennt kein `&f` | `P011` / `M119` | `ExprArt::FnWert`, geprüft von `M127`/`M128` |
| 2 | der **Ruf über einen ORT** («B8») | `P017` / `P001` | `CallTarget::Place`, geprüft von `M129` |
| 3 | die **Absenkung** | `C001` | `bool (*bereit)(void);` und `t->senden(b)` |
| 4 | der **Vertrag am Zeigertyp** | — | `effects` + `costs` am `fn(…)`, `N035`–`N037` |

---

## 1. Die Messung VOR dem Bau

### 1.1 Regel B — der Bedarf steht außen

Alle Zahlen am 2026-08-21 in `/home/simon/Dokumente/caprock-messbasis` (Zweig `arch/x86_64`,
nur gelesen). **Die drei Zahlen des Auftrags reproduzieren exakt.**

| Frage | Zahl | Befehl (aus `caprock-messbasis`) |
|---|---|---|
| `fn(…)` als Typstelle | **11** | `grep -rn --include=*.rs -e ": fn(" -e "Option<fn(" . \| grep -v '/target/' \| wc -l` |
| Erzeuger (Funktionsname als Feldwert) | **4** | `grep -rno --include=*.rs -E '(bereit\|senden):\s*[A-Z][A-Za-z0-9_]*::[a-z_]+' . \| grep -v '/target/' \| wc -l` |
| Rufe **hindurch** | **4** | `grep -rn --include=*.rs -E '\(\s*(self\|t)\.[a-z_]+\s*\)\s*\(' . \| grep -v '/target/' \| wc -l` |

Die Schablone, wörtlich (`crates/caprock-hal/src/konsole.rs`:159-166 und
`x86_64/console.rs`:91):

```rust
pub(crate) struct Treiber {
    pub bereit: fn() -> bool,
    pub senden: fn(u8),
}
static TREIBER: konsole::Treiber =
    konsole::Treiber { bereit: Uart16550::bereit, senden: Uart16550::put_byte };
...
(t.senden)(b'\r');
```

**Die vier Rufe hindurch nehmen KEINE Sperre** (`(t.senden)` ×2, `(self.fence)` ×2). Diese
Beobachtung trägt später die Entscheidung in §4.2 — sie ist kein Nebensatz.

### 1.2 Der Zustand des Prüfers, nachgemessen

`fnptr` stand in der Grammatik und hatte **acht Fundstellen im Prüfer, keine davon ein Leser**:

```
grep -rn "FnZeiger" --include=*.rs crates/     -> 8 Zeilen
grep -n "fnptr" dokumente/SYNTAX.md            -> 293, 331
```

Die Zeilennummern des Auftrags stimmen alle: `SYNTAX.md`:331, `parse.rs`:945, `ast.rs`:356,
`umgebung.rs`:1013 (`TypExpr::FnZeiger(_) => Typ::Unbekannt`), `namen.rs`:1222.

### 1.3 Die vier Hälften, jede mit ihrer Absage — und eine fünfte, die nicht gebucht war

Sechs Handproben, `messung/fnptr-proben/p2.gab` … `messung/fnptr-proben/p8.gab`, jeweils
`./target/debug/gabbro pruefe <datei>`:

| Probe | geschrieben | Absage vorher |
|---|---|---|
| `p2` | `Treiber(bereit: &wahr)` | **`P011`** — *„Ausdruck erwartet, `&` gefunden"* |
| `p7` | `Treiber(bereit: wahr)` | **`M119`** — *„`wahr` is declared nowhere"* |
| `p5` | `t->senden(b);` als Anweisung | **`P017`** — *„Zuweisung oder Aufruf erwartet, `(` gefunden"* |
| `p3` | `return t->bereit();` | **`P001`** — *„`;` erwartet, `(` gefunden"* |
| `p4` | `gabbro emit` über ein `fn`-Feld | **`C001`** — *„no lowering: field type"* |

**Zwei Abweichungen von der Buchung im Auftrag**, beide nachgerechnet:

* Der Erzeuger fällt an **zwei** Stellen, nicht einer. Der Auftrag bucht `M119`; das gilt für
  den **blossen Namen** (`p7`). Die Form mit `&` fällt schon im Parser an `P011` (`p2`), weil
  `&` in Ausdrucksstellung gar nicht vorgesehen war. *Zwei Absagen, zwei verschiedene
  Reparaturen.*
* Der Ruf über einen Ort fällt an **zwei** Stellen. Der Auftrag bucht `P017`; das gilt für die
  **Anweisung** (`p5`). In Ausdrucksstellung ist es `P001` (`p3`) — eine Absage über ein
  Semikolon, die von der Sache nichts sagt.

**Und der Fund, der in keiner Buchung stand — `fnptr` war kein Loch im Wissen, sondern eines
in der Prüfung.** `messung/fnptr-proben/p8.gab`:

```gabbro
impl fn nutze(t : ptr<normal, r> Treiber) -> u32 … {
    let x : u32                    = t->bereit;
    let y : bool                   = t->bereit;
    let z : ptr<normal, r> Treiber = t->bereit;
```

```
messung/fnptr-proben/p8.gab: 3 Items, 1 Fehler, 0 Hinweise      <- der eine Fehler ist K001, die KOSTEN
  M1 saw 4 expressions, 3 of them without a type (25 % coverage)
```

**Drei unvereinbare Typen für denselben Ausdruck, in EINER Datei, ohne eine Typabsage.**
Ursache: `TypExpr::FnZeiger(_) => Typ::Unbekannt`, und `Typ::Unbekannt` verträgt sich mit
allem. Die Deckungszahl fiel auf 25 % und **stand da** — der Lauf hat es gezählt, und gefallen
ist nichts. *Genau die Klasse, gegen die dieser Ordner `Zustand::Teilgebaut` erfunden hat, nur
eine Ebene tiefer.*

---

## 2. Was gebaut wurde, Hälfte für Hälfte

### 2.1 Der Vertrag am Zeigertyp (Hälfte 4 — sie steht zuerst, weil alles andere sie braucht)

```ebnf
fnptr      = "fn" "(" [ params ] ")" [ "->" typeexpr ] fncontract ;
fncontract = [ "requires" predlist ] [ "ensures" predlist ]
             "effects" "{" efflist "}" "costs" "<=" expr "ops" ;
```

Zwei Änderungen, und beide hängen aneinander:

* **`params` statt `typelist`** — die Parameter sind jetzt BENANNT (`fn(b : u8)`). Eine
  Wirkungszeile nennt einen Ort (`writes r.slots`), und ein Ort braucht einen Namen. *Genau
  das Fehlen von Namen macht eine Wirkungsliste am Aufrufrand unübersetzbar* (siehe
  `aufrufgraph::ersetze`).
* **der Vertrag**, weil neun Passdateien den Gerufenen statisch auflösen.

**Es kostet kein neues Wort.** `requires`, `ensures`, `effects`, `costs` stehen schon im
Wortschatz; `instrumente/pruefe-wortschatz.py dokumente/SYNTAX.md` meldet unverändert
**216 EBNF-Terminale, 216 Tabellenwörter**.

### 2.2 Der Erzeuger `&f` (Hälfte 1)

```ebnf
unary   = [ "!" | "-" ] primary | fnvalue ;
fnvalue = "&" path ;
```

Es steht bei `unary` und ist **kein Operator**: `&` erwartet einen `path`, keinen Ausdruck.
*Es gibt in Gabbro keine Adresse eines Ausdrucks, und dass es sie nicht gibt, ist der Grund,
warum `ptr` überhaupt eine Herkunft trägt.*

Warum `&f` und nicht der blosse Name `f` (E3): ein blosser Name an einer Wertstelle ist ein
`place` — gemessen in `p7`, es gibt `M119`. Caprock schreibt es ohne `&`; das ist Rusts Regel,
nicht die Gestalt der Sache. C lässt beide Schreibungen zu, Gabbro lässt eine zu.

### 2.3 Der Ruf über einen Ort (Hälfte 2)

`Ruf.pfad: Pfad` wurde zu `Ruf.ziel: CallTarget`, mit

```rust
pub enum CallTarget { Path(Pfad), Place(Ort) }
```

**Das ist die zentrale Bauentscheidung dieses Postens, und sie ist gegen das stille Loch
gerichtet.** Ein `Option<Pfad>` mit einem Nebenfeld hätte gereicht, um zu übersetzen; ein
`enum` zwingt **jede Passstelle, die den Gerufenen auflöst, beide Fälle zu nennen** — und der
Rustcompiler zählt sie auf:

```
cargo check --message-format short 2>&1 | grep -cE '\.rs:[0-9]+:[0-9]+: error'
-> 72     (in 14 Dateien; davon 4 nicht-erschöpfende `match` über `ExprArt`, die `&f` aufriss)
```

**Schweigen war damit kein Standardzweig, sondern ein Übersetzungsfehler.** Was jeder der 72
Fälle antwortet, steht in §3 und §4.

### 2.4 Die Absenkung (Hälfte 3)

`gabbro emit beispiele/49-dispatch-tabelle.gab`:

```c
typedef struct {
    bool (*bereit)(void);
    void (*senden)(uint8_t);
} Treiber;

Treiber baue(void) {
    return (Treiber){ .bereit = &hart_bereit, .senden = &hart_senden };
}

void ausgeben(const Treiber *restrict t, uint8_t b) {
    (void)t;
    if (t->bereit()) {
        t->senden(b);
    }
}
```

Ein C-Funktionszeiger setzt seinen **Namen INS Innere des Typs** (C11 §6.7.6.3), also kann er
nicht durch `ctyp` gehen — das antwortet mit einem Typ, an den ein Name angehängt wird.
Dieselbe Bauform wie der Feldzweig für Arrays, aus demselben Grund. `(void)` statt `()`: eine
leere Parameterliste heisst in C *unspezifiziert* und ist ein anderer Typ.

**Der Vertrag wird NICHT emittiert** (W6): Wirkungen und Kostenschranke sind Prüferfakten,
genau wie die Grenzen eines Bereichstyps. Was ins C geht, ist die Gestalt.

---

## 3. Je Pass: wie er den unbekannten Gerufenen behandelt

**Die Tabelle ist die eigentliche Arbeit dieses Postens.** Nirgends eine stille Ausnahme.

| Pass | Antwort auf „der Gerufene ist nicht statisch bekannt" |
|---|---|
| **`aufrufgraph`** | **Trägt ihn.** `Knoten::indirect: Vec<IndirectCall>` hält Ort, Wirkungen aus dem Vertrag, die Parameternamen **des Typs** und die Argumentorte. `gehe` und `huelle_der_gerufenen` falten sie ein und übersetzen sie mit **demselben `ersetze`** wie bei einem benannten Gerufenen. Ohne Vertrag: `unvollstaendig` mit Grund → **`E009`**. |
| **`wirkungen`** (`E008`/`E010`) | Liest die Hülle — trägt damit automatisch. **Gegenprobe `gift/242` fällt an `E008`.** |
| **`kosten`** (`K001`) | **Addiert die `costs`-Schranke des Zeigertyps.** Beide Fehlerzweige sind `Kosten::Unbekannt` **mit Grund**, nie `Zahl(0)`: *eine Kostenzahl, die man nicht kennt, ist nicht null.* Gegenprobe `gift/246`. |
| **`m1`** | **Typisiert ihn** aus dem Vertrag: Argumente gegen die Parametertypen, Ergebnis aus `result`. Ein Ort ohne `fn(…)`-Typ fällt an **`M129`**. Der Erzeuger fällt an **`M127`** (kein Funktionsname) bzw. **`M128`** (verspricht mehr als sein Slot). |
| **`geteilt`** (`H005`/`H012`) | **Nimmt keine Sperre und fordert keine — und `N036` macht das zu einer Aussage.** Beide Regeln schlagen den Gerufenen unter seinem NAMEN nach. `locks` und `locks shared` sind am Zeigertyp **abgelehnt**, also kann ein so erreichter Gerufener gar keine halten. Gegenprobe `gift/243`. |
| **`m2`** (Linearität) | **Verbraucht nichts** — `consumes` ist am Zeigertyp abgelehnt (`N036`), weil die Position eines linearen Parameters aus der Signatur des Gerufenen kommt. |
| **`paarung`** (`V001`–`V004`) | **Paart nichts** — `publishes` ist abgelehnt (`N036`): eine Paarung hält zwei BENANNTE Seiten gegeneinander. |
| **`kontexte`** (`H013`) | **Maskiert nichts** — `masks` ist abgelehnt (`N036`). Die `writes` des Gerufenen erreichen `H013` weiterhin **über die Hülle**. |
| **`m3`** (Rechte) | Die eine Fundstelle betraf Gerätegriffe; ein indirekter Ruf stellt keinen her. Die `reads`/`writes` des Vertrags landen über die Argumentabbildung in der Hülle. |
| **`phasen`** (`O001`–`O007`) | **Schreitet nicht voran.** `advances a -> b` steht an einer `fn`-DEKLARATION, und die Grammatik lässt es an einem `fn(…)`-Typ nicht zu. *`false` ist hier eine Tatsache über die Sprache, kein Wegsehen.* |
| **`emit`** | Senkt ihn ab (§2.4). Ein `let … else` über einen indirekten Ruf wird **benannt abgelehnt**: ein `fn(…)`-Typ trägt keinen `or R`-Fehlerkanal, also bindet nichts das `e`. |
| **`lib::endet_immer`** | **Beendet keinen Rumpf.** `divergent` ist eine Liste von Namen; `diverges` am Typ sagt, was der Gerufene anfasst, nicht ob die Kontrolle zurückkommt. *Die sichere Richtung.* |

---

## 4. Was NICHT gelungen ist

### 4.1 Vier Wirkungswörter überqueren einen indirekten Ruf nicht

`N036` lehnt `locks`, `locks shared`, `masks`, `consumes` und `publishes` **am Typ** ab.
Die Lücke ist damit benannt und **abweisend**, nicht schweigend — aber sie ist eine Lücke:

> **Sperrordnung, Unterbrechungskontext, Linearität und Paarung überqueren keinen indirekten
> Ruf. Ein Programm, das das bräuchte, kommt nicht durch.**

*Die Alternative wäre gewesen, die Zusage durchzulassen und nirgends zu prüfen* — genau der
Ausgang, den der Auftrag den schlimmsten nennt.

### 4.2 Warum das eine gemessene Null ist und keine Bequemlichkeit

Eine Sperrordnung über einen indirekten Ruf zu tragen heisst, einen Gerufenen zu ranken, der
zur Laufzeit gewählt wird. **Caprocks vier indirekte Rufstellen nehmen keine Sperre**
(§1.1). *Das Konstrukt, das es bräuchte, gibt es im gemessenen Code nicht.*

### 4.3 Drei kleinere Kanten, ungeschminkt

* **Der `let`-Abtaster für das lokale Typbild ist FLACH.** `aufrufgraph::sammle_lets` sammelt
  jedes `let` mit Typangabe ohne Rücksicht auf Verschattung; zwei Bindungen eines Namens in
  zwei Zweigen fallen zu einer zusammen. Ein `let` **ohne** Typangabe wird gar nicht gesehen —
  dort gibt es dann keinen Vertrag, und das heisst `E009`, nicht Schweigen.
* **`M128` prüft Stelligkeit, Wirkungsmenge und Kostenzahl — nicht die Parametertypen.** Zwei
  Zeigertypen gleicher Stelligkeit mit verträglichen Verträgen, aber verschiedenen
  Parametertypen sind hier austauschbar; der Fehler taucht erst am Ruf auf (`M104`) — oder
  gar nicht, wenn niemand durch den Slot ruft.
* **`ensures` am Funktionszeigertyp wird von niemandem gelesen.** Die Klausel ist geparst und
  gespeichert; ein Rufer durch den Zeiger lernt nichts daraus. *Sie steht damit heute genau in
  der Klasse, gegen die dieser Posten gebaut wurde* — und wenn sie bis zum nächsten Lauf
  keinen Leser bekommt, gehört sie aus der Grammatik gestrichen, nicht behalten.
  **`requires` ist deshalb gar nicht erst zugelassen** (`N037`).
* **`let … else` über einen indirekten Ruf wird NUR vom Erzeuger abgelehnt, von keinem Pass.**
  Ein `fn(…)`-Typ trägt keinen `or R`-Fehlerkanal, also bindet nichts das `e`. `emit.rs` sagt
  es benannt; `N029` spricht über den umgekehrten Fall (ein Ruf, der scheitern KANN und nicht
  in einem `let … else` steht). *Eine Datei, die den Erzeuger nie erreicht, hört davon nichts.*
  **Gefunden beim Nachlesen der eigenen Kommentare** — dort stand zuerst, ein Pass sage es
  eine Ebene früher. Er sagt es nicht.
* Ein Ruf ohne Ergebnis bleibt **untypisiert** — beim indirekten Ruf genauso wie beim direkten
  (`sig.ergebnis.unwrap_or(Typ::Unbekannt)`). Gabbro hat keinen Einheitstyp; hier einen zu
  erfinden hätte den indirekten Ruf vom direkten unterschieden, ohne dass eine Regel danach
  gefragt hätte. *Die Deckungszahl zählt es, in beiden Wegen.*

---

## 5. Die Abnahme

| Prüfung | Befehl | Ergebnis |
|---|---|---|
| Übersetzung | `cargo check` | **0 Fehler, 0 Warnungen** |
| Tests | `cargo test` auf `ki-pc-fisch-101:gabbro-h` | **14 Suiten, 0 failed** |
| Beispiel prüft | `gabbro pruefe beispiele/49-dispatch-tabelle.gab` | **0 Fehler**, M1-Deckung 85 % |
| Beispiel senkt ab | `gabbro emit beispiele/49-dispatch-tabelle.gab` | 49 Zeilen C |
| C übersetzt | `cc -std=c11 -Wall -Wextra -Werror {-O0,-O2}` | **ok** |
| C unter UBSan | `cc … -fsanitize=undefined` | **ok** |
| Emission gesamt | `./instrumente/pruefe-emission.sh` | **ALL PASS, 49 von 49 übersetzen** |
| Kennungen | `./instrumente/pruefe-kennungen.py` | **ALL PASS**, 207 Kennungen |
| Eine Kennung, eine Regel | `./instrumente/pruefe-vergabe.py` | **ok**, 14 Kandidaten (unverändert) |
| Kein Code ohne Satz | `./instrumente/pruefe-saetze.py` | **45 ohne Satz** — Marke 45, unverändert |
| Klauseln haben Leser | `./instrumente/pruefe-klauseln.py` | **20 gebucht, keine neue** |
| Grammatik geschlossen | `./instrumente/pruefe-syntax.sh` | **ALL PASS**, 149 Regeln |
| Wortschatz | `./instrumente/pruefe-wortschatz.py dokumente/SYNTAX.md` | 216 / 216, **kein neues Wort** |
| Mutationsanker | `./instrumente/mutiere-pruefer.py --anker` | **268 von 268** |
| Sprachlinie | `./instrumente/pruefe-englisch.py` | **ALL PASS** |

### 5.1 Sechs neue Absagen, sieben Giftproben, vier Mutationen

| Kennung | Regel | Giftprobe |
|---|---|---|
| `N035` | ein `fn(…)`-Typ ohne `effects` / ohne `costs` | `gift/240` |
| `N036` | ein Wirkungswort, das keinen indirekten Ruf überquert | `gift/243` |
| `N037` | ein `requires` am Zeigertyp | `gift/247` |
| `M127` | `&x`, wo `x` keine Funktion ist | `gift/244` |
| `M128` | der Erzeuger verspricht MEHR als sein Slot | `gift/241` |
| `M129` | Ruf über einen Ort ohne `fn(…)`-Typ | `gift/245` |
| (`E008`) | die Hülle überquert den indirekten Ruf | `gift/242` |
| (`K001`) | die Kostenschranke des Typs wird addiert | `gift/246` |

Vier Mutationen, `# --- fnptr ---` in `instrumente/mutiere-pruefer.py`. Die erste ist die,
auf die es ankommt: `huelle-verliert-indirekten-ruf` stellt **genau den Zustand wieder her,
den dieser Posten beseitigt hat.** *Überlebt sie, ist die Wirkungshülle an jeder indirekten
Rufstelle still verloren.*

---

## 6. Der Widerspruch zur Buchung — nachgerechnet

`messung/ERZEUGER.md` §2.3 schliesst:

> *„Daraus folgt mechanisch, dass das Programm, das Regel A verlangt, heute nicht existieren
> kann."*

**Das war richtig und ist es nicht mehr — und der Unterschied ist kein neuer Befund, sondern
ein anderer Zuschnitt der Arbeit.** Der Satz gilt, solange man die Hälften **einzeln** baut:
jede einzelne ist für sich nutzlos, also kann keine für sich ein Programm rechtfertigen. Er
gilt nicht, wenn alle vier in **einem** Lauf entstehen — dann ist das Programm, das Regel A
verlangt, am Ende des Laufs da. Es ist `beispiele/49-dispatch-tabelle.gab`.

*Die Buchung war also nicht falsch, sondern an eine Reihenfolge gebunden, die sie selbst
benannt hat.* **`ERZEUGER.md` §2 gehört auf „gebaut" umgeschrieben, mit dieser Datei als
Adresse** — der Vorschlag steht in der Übergabe.

Und eine Zahl darin ist zu schärfen: §2.2 nennt **drei** Löcher. Gemessen sind es **vier** —
der Vertrag fehlte auch, und er ist derjenige, ohne den die anderen drei ein falsches Grün
ergeben hätten.
