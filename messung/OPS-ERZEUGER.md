# Der `ops`-Erzeuger — Zuschnitt (c), und der Beweis schreibt das Programm

*Entschieden am 2026-08-28. Jede Zahl nennt den Befehl, der sie nachrechnet.*

> **Der Befund zuerst:** die Wortmenge von `ops` ist seit dem 2026-08-19 geschlossen
> (`insert | remove | relabel`), `P039` hält sie, `beispiele/47` schreibt sie — **und es gibt
> keinen Erzeuger.** `grep -rn '\.ops\b' crates/` findet `kbedingung.rs` (D001/D002 verbieten
> die Handmutation) und `m3.rs`; **`emit.rs` steht nicht darunter.**
>
> Damit verbietet Gabbro heute die Handmutation an einer `table` mit `ops` — und liefert
> nichts an ihre Stelle. *Das ist die eine Stellung, in der ein Konstrukt schlechter ist als
> keines.*

---

## 1. Was der Beweis vorschreibt, und es sind nicht drei Operationen

`beweise/Table_Ops_Erhaltung.thy` (311 Zeilen) hat drei Teile, und **Teil III entscheidet
die Wortmenge des Erzeugers gegen die Wortmenge der Sprache:**

| Satz | Operation | Voraussetzungen, die der Rufer schuldet |
|---|---|---|
| `einfuegen_erhaelt` | **`insert`** | `σ n = None` (der Platz ist **frisch**) · `erreicht σ p` (der Elter ist **erreichbar**) |
| `blatt_loeschen_erhaelt` | **`remove`** | `blatt σ s` (**niemand nennt `s` als Elter**) |
| `umhaengen_faellt` | **`relabel`** | **kein Satz — ein GEGENBEISPIEL.** `¬ wohlgeformt (umhaengen zwei 0 1)` |

> **`relabel` steht im Wortschatz und darf nicht emittiert werden.** Der Erzeuger sagt es ab
> und nennt den Satz. *Eine Operation zu emittieren, von der der eigene Beweis sagt, dass sie
> die Invariante bricht, wäre die Bewegung, gegen die K100s zweites Tor steht.*

**Und der Korpus braucht genau diese Operation an 127 Stellen** (`umhaengen`, gemessen
2026-08-19 über `kernel/` + `mm/`). Das ist kein Widerspruch, sondern der Ertrag: die Absage
steht mit Adresse da, statt dass 127 Aufrufstellen einzeln bewiesen werden.

---

## 2. Die Lücke, die der Erzeuger als erstes findet: **welches Feld sagt „belegt"?**

`σ n = None` und `σ s = Some sl` sind der Kern beider Sätze. In Gabbro ist ein Slot kein
`option` — er ist ein Verbund im Feld `slots[N]`. **Also muss ein Feld die Belegung tragen,
und der Erzeuger muss wissen, welches.**

```bash
$ # jedes bool-Slotfeld im Korpus, nach Namen gezaehlt
  8 belegt · 6 benutzt · 3 used · 3 aktiv · 1 quiescing · 1 offen
  1 lebt · 1 gueltig · 1 gesperrt · 1 bereit
```

**Elf Namen. Eine Namensheuristik ist damit widerlegt, nicht bezweifelt.** Und es ist
wörtlich derselbe Befund wie «B41b»: dort führte der Slot **vier** Kandidaten für die
Baumkante (`elter`, `erstes_kind`, `naechstes`, `vorheriges`), und *„die Domaene nannte
keins"*. Gefunden hat es beide Male **der Erzeuger beim Absenken, nicht der Entwurf.**

---

## 3. Die drei Formen, beide Seiten je Form

### (a) Eine Namensregel — das erste `bool`-Feld, oder eines aus einer festen Liste

| | |
|---|---|
| **dafür** | kein Wort, keine Zeile Grammatik |
| **dagegen** | **elf Namen im Korpus.** Eine Regel, die `belegt` kennt und `quiescing` nicht, wählt bei `beispiele/31` das falsche Feld — *und ein Erzeuger, der das falsche Feld nullt, ist schlimmer als keiner.* Dieselbe Falle, die «B41b» bezahlt hat |

### (b) `tree` erweitern — `tree { parent elter, occupied benutzt }`

| | |
|---|---|
| **dafür** | kein neues Konstrukt, die Rolle steht bei den anderen Rollen |
| **dagegen** | **`beispiele/47` hat `ops` und keinen `tree`**, und ein Verzeichnis ohne Baum ist kein Sonderfall. Belegung an eine Baumkante zu hängen hieße, `ops` auf Bäume zu beschränken — eine Einschränkung, die kein Satz verlangt |

### (c) Eine eigene Rolle an der Tabelle — `occupied benutzt;`

| | |
|---|---|
| **dafür** | **dieselbe Form wie `treedecl`, aus demselben Grund:** eine Aussage über die STRUKTUR steht einmal an der `table`, wird dort einmal geprüft und gilt danach überall. Und sie ist **kontextuell** wie `tree`/`parent`/`child`/`sibling` — überall sonst bleibt `occupied` ein Bezeichner |
| **dagegen** | ein Wort mehr im Wortschatz: `kw.rs`, `SYNTAX.md`, `pruefe-wortschatz.py`, `tests/wortschatz.rs`, die Terminalzählung |

---

## 4. Die Entscheidung: **(c)**

**Und sie fällt anders aus als bei der Schleifeninvariante — aus demselben Grundsatz.**
`SCHLEIFENINVARIANTE.md` entschied gegen ein neues Wort, weil `invariant` den Begriff schon
trug: *„ein zweites Wort für einen vorhandenen Begriff ist teurer als eine zweite Fundstelle
für ein vorhandenes Wort."*

> **Hier trägt kein vorhandenes Wort den Begriff, und die elf Namen sind der Beleg.** Der
> Wortschatz misst, wie viel eine Sprache *kann*. „Welcher Slot ist belegt" ist etwas, das sie
> bisher nicht sagen kann — und `ops` ohne diesen Satz ist ein Verbot ohne Ersatz.

### Die Form

```ebnf
table    = [ "pub" ] "table" ident [ "count" constexpr ] [ "backed" ident ] "{"
             { constdecl | slotdecl | invariant | opdecl | treedecl | occdecl } "}" ;
occdecl  = "occupied" ident ";" ;
```

---

## 5. Was das Wort NICHT fail-open lassen darf

**Eine Klausel, die niemand prüft, ist schlimmer als keine** — der Satz steht seit
`beispiele/05` und `H007`/`H008` im Ordner. Darum drei Riegel, und alle drei sind gebaut:

1. **`D010`** — `occupied f` muss ein `bool`-Feld des eigenen Slots nennen. Wortgleich zu
   `D006`/`D007` an der Baumkante.
2. **`D011`** — eine `table` mit `ops` **ohne** `occupied` ist ein Fehler. *Ohne die Belegung
   hat `σ n = None` kein Subjekt, und der Erzeuger emittiert eine Operation, deren Beweis von
   etwas anderem redet.*
3. **Der Erzeuger sagt `relabel` ab, mit dem Satznamen.** `umhaengen_faellt` steht im
   erzeugten C als Kommentar an der Stelle, an der die Operation fehlt.

---

## 6. Was diese Entscheidung nicht kauft

**Der Erzeuger stellt die Voraussetzungen nicht her, er schreibt sie hin.** `σ n = None` und
`erreicht σ p` bleiben Pflichten des Rufers — sie stehen als `requires` am erzeugten `insert`
und werden von M1 gegen die Aufrufstelle gehalten, wie jede andere Vorbedingung.

*Was diese Entscheidung herstellt, ist die Amortisation:* der Beweis fällt **einmal je
Operation im Erzeuger** statt einmal je Aufrufstelle. Das ist Teil I der Theorie
(`folge_erhaelt`, `erreichbares_erhaelt`) — und es ist die Aussage, auf der Zuschnitt (c)
überhaupt ruht.
