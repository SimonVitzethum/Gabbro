# Gabbro — was fertig ist

> **Diese Datei führt ausschliesslich Erledigtes.** Offenes steht in [TODO.md](TODO.md),
> Widerlegtes in [dokumente/HISTORIE.md](dokumente/HISTORIE.md), Gemessenes in
> [dokumente/MESSUNGEN.md](dokumente/MESSUNGEN.md).
>
> **Jeder Eintrag trägt seinen Beleg** — eine Datei, eine Kennung oder eine nachfahrbare
> Befehlszeile. *Eine Erledigt-Meldung ohne Beleg ist dieselbe Zahl ohne Fundstellenliste,
> gegen die W7 steht* ([dokumente/WERKZEUGKASTEN.md](dokumente/WERKZEUGKASTEN.md)).

---

## Der Übersetzer — **zehn** Pässe, keiner offen

`cargo run --bin gabbro -- paesse` · **3 ganz gebaut, 7 teilweise, 0 offen**

> **Der zehnte ist NEU, und das ist eine Änderung an der Spezifikation.** `SPRACHE.md`
> Teil III §6 legt neun fest und sagt *„die Spezifikation ist die Passliste"* — ein zehnter
> heisst also nicht „ein Modul mehr", sondern **die Liste ist gewachsen**. Der Grund ist
> gemessen (SWEEP, V4), nicht entworfen: eine Invariante **zwischen** Trägern hat in den
> neun Pässen keine Stelle.

| # | Pass | Kennungen | Beleg |
|---:|---|---|---|
| 1 | **Namen** | `N001`–`N003` | `crates/gabbro-check/src/namen.rs` |
| 2 | D1/D2 *(teilweise)* | `D001`, `D002` | `kbedingung.rs` — die K-Bedingung, `by ops` je **Feld** |
| 3 | **M1 + V1–V3** | `M101`–`M105` | `m1.rs`, `typen.rs` |
| 4 | M3 *(teilweise)* | `R001`–`R003` | `m3.rs` — Räume, Rechte, Platzierungsregel |
| 5 | M2 *(teilweise)* | `L101`–`L105` | `m2.rs` — echte Linearität |
| 6 | **M4/Schleifen** | `S001`, `S002` | `schleifen.rs` |
| 7 | Paarung *(teilweise)* | `V001`–`V004` | `paarung.rs` |
| 8 | effects *(teilweise)* | `E001`–`E010` | `wirkungen.rs` — seit 2026-08-16 **mit Lesehälfte** (Lesart A) |
| 9 | costs *(teilweise)* | `K001`–`K004` | `kosten.rs` |
| **10** | **Gruppe** *(neu, teilweise)* | `U001`–`U007` | `gruppe.rs` — Sperrabdruck, Zug **und Verbindungsaussage** |

> **„Teilweise" heisst bei M2, M3 und Paarung nicht „halb fertig", sondern „fertig, ruht auf
> einem benannten Posten"** — Ghost-Löschung, Barriere aus dem Raum, Speichermodell. **Drei
> davon sind derselbe Posten: die Axiomschicht.**

**Dazu der Aufrufgraph** (`aufrufgraph.rs`, 268 Zeilen) — er hat drei Blocker auf einmal
gelöst: `H005`, die Aufrufwirkungen in Pass 8, und die Trennung bei der Klasse *Phase*.

## Die Klempnerei-Klassen — 7 von 11 getragen

Neu erhoben 2026-08-15, **nicht wiederhergestellt**, nur x86
([dokumente/MESSUNGEN.md](dokumente/MESSUNGEN.md), *Neuerhebung*):

| getragen | wodurch |
|---|---|
| **Index** | `index into T` erbt `count N` · `M103` |
| **Überlauf** | M1-Bereichstypen · `M101`/`M104`; gewollter Umlauf seit «B32» am Slot **und** am Register |
| **Alias** | aufgelöst statt geschlossen — Kernzustand braucht keinen Zeiger (A1); wo doch, macht `own` ihn linear. Beleg: `beispiele/09-ohne-zeiger.gab`, `beispiele/15-own-traegt-beide-rechte.gab` |
| **Sperre** | `rank`/`held`/`shared held` · `H001`–`H005` · `K002`/`K004` |
| **Terminierung** | drei Schleifenformen · `bounded`/`on_exceeded`/`progress` · `S001`/`S002` in `schleifen.rs`, `beispiele/04-schleifen.gab` |
| **Blattheit** | `descendants of` + `by consuming` mit Zeugenordnung · Domänenschranke in `kosten.rs`, `dokumente/FRAGMENTE.md` (`revoke`) |
| **Publikation** | `publishstmt` am Store · Paarungspass · `relaxed` trägt keine Nutzlast · `V001`–`V004` in `paarung.rs` |

## Konstrukte, die gebaut und belegt sind

| Konstrukt | Grund | Beleg |
|---|---|---|
| **`locks shared`** | gemessen: 33 `read()` gegen 44 `write()` — der heisseste Pfad war nicht schreibbar | `H001`–`H005`, `beispiele/10`, Gift 38–42 |
| **`wrapping` am Register** («B32») | virtios Ringzähler läuft per Entwurf um; die Absicht stand nirgends | `beispiele/12-umlaufendes-register.gab`, `beispiele/gift/48-register-ohne-umlauf.gab` |
| **`heldpred`** | die Stärke des Zeugen, ohne Aufweichung des Ausdrucks | `dokumente/SYNTAX.md` (`atompred`), `beispiele/13-zeuge-mit-staerke.gab` |
| **`Some`/`None`** («B35») | `option` hatte **keinen Konstruktor** — der Bestand schrieb es seit jeher | `optionexpr` in `dokumente/SYNTAX.md`, `beispiele/01-tabelle.gab` |
| **`table … count N`** | `index into T` erbt die Schranke | `M103` in `m1.rs`, `beispiele/01-tabelle.gab` |
| **Platzierungsregel** | ein `ops`-Träger liegt in keinem `dma`-Raum — ein Gerät schreibt an jeder Grammatik vorbei | `R001`, Gift 58 |

## Gefahrene Messungen, mit Tor und Ausgang

| Messung | Ausgang | Beleg |
|---|---|---|
| **Tor P2** — der Korpus parst | **bestanden, 7 von 7** (und `dokumente/SYNTAX.md` 6 von 6) | `gabbro fragmente dokumente/FRAGMENTE.md` |
| **Mutationsgenerator** | **bestanden** — `7 von 39` gegen `54 von 54` der Hand | `erzeuge-mutationen.py`, `dokumente/MESSUNGEN.md` |
| **Die 15 Generatorlücken** | **13 zu, 2 beweisbar äquivalent** | `./pruefe-luecken.py` |
| **`narrow`-Zählung** | **Tor verfehlt** — N = 2, und das Protokoll war widersprüchlich | `./zaehle-bereichspflichten.py` |
| **Elf Klempnerei-Klassen** | **Tor verfehlt** — `N_neu = 5` (heute 4) | `dokumente/MESSUNGEN.md`, *Neuerhebung* |
| **K/A/W über N_L** | **Tor verfehlt** — `W = 38 von 73` | `dokumente/MESSUNGEN.md`, *Buchung* |
| **Lader-Fragment, Klasse *Phase*** | **Marke trägt: 7 gegen k = 5** | `dokumente/FRAGMENTE.md` F7 |
| **Alle vier Bereichsfragmente** | **Konvergenzmetrik: 0 neue Konstrukte** | `dokumente/FRAGMENTE.md` F7–F10 |
| **`Stale(T)`** | **widerlegt** — 2 von 5 Übergängen ruhen auf `masks IRQ` | `dokumente/FRAGMENTE.md` F8, «B38» |
| **Basisrate `format`** | **trägt `format` nicht** — 5 Formate, 0 Fehler der Klasse | `dokumente/MESSUNGEN.md` |
| **`delete_leaf`** | **1,75 : 1** statt gebuchter 3,6–6 : 1 | `dokumente/BEWEIS.md` |
| **`programs/`** | Grund des Bruchs trägt nicht mehr | `dokumente/MESSUNGEN.md` |
| **N1 (Caprock)** | **`MEM` ist Blatt**, `system.rs:724` ist falsch | `arbeitsprotokoll/03-N1.md` |
| **B3 — nicht traversierbare Rümpfe** | **bestanden, `p = 0,96 %` gegen eine Latte von 5 %** — aber **R1 verfehlt** (Regel nach dem Lauf aufgeschrieben) | `./zaehle-b3.py ../caprock-messbasis`, `dokumente/MESSUNGEN.md` |

> **Der B3-Eintrag ist der einzige in dieser Tabelle, der neben dem Ausgang einen
> Protokollverstoss trägt** — und er steht hier statt in einer Fussnote, weil eine
> Erledigt-Tabelle, die nur Ausgänge führt, die teuerste Zeile verschweigt: **die Markenregel
> wurde in vier Fassungen mit sichtbaren Zahlen geschärft.** Was das Ergebnis rettet, ist
> nicht Sorgfalt, sondern **Regelinvarianz**: alle vier Fassungen (0,03 % · 4,36 % · 0,74 % ·
> 0,95 %) bestehen die Latte. *Von der Regelwahl hängt die Zahl ab, nicht das Urteil.*

## Grammatik — die Befunde aus P2

**G1–G11 geschlossen** ([dokumente/SYNTAX.md](dokumente/SYNTAX.md), `beispiele/11`, Gift 43–45):
`atomicdecl publishes` · `axiom -> typeexpr requires` · die `->`-Mehrdeutigkeit **in der
Grammatik** · Schlusskomma · `u64::max` · `O`/`@version` als benannte `Sonderform` ·
`clobbers { }` leer · `count N` · `cast` entfällt · das `forever`-Beispiel · acht Domänen.

**Etikettenkollision aufgelöst** (2026-08-16): die Gegenprüfungsbefunde in
`dokumente/MESSUNGEN.md` heissen jetzt `GP1`–`GP3`; `G1`–`G11` gehören der Grammatik.
*Zwei Etikettensysteme mit denselben Namen sind dieselbe Fehlerklasse wie zwei Prosaordnungen,
die niemand gegeneinander prüft.*

**Dazu:** die Nutzlastform nach dem Bestand entschieden (22 × `nothing`, 11 × Klammern,
2 × ohne — die Grammatik folgt den 33), die `pub`-Laxheit (`P034`), `pub const` im
`table`-Rumpf, und **`dokumente/SYNTAX.md` hält jetzt seine eigene Grammatik** (Test
`die_beispiele_der_grammatik_gehen_selbst_durch`).

## Die Wächterkette — acht, jeder mit Sprechprobe in beide Richtungen

```
./pruefe-syntax.sh        verbotene Formen, Prosa-Drift, Geschlossenheit, Erreichbarkeit,
                          Terminaldeckung — und NULL Bauwarnungen
./pruefe-wortschatz.py    Terminale gegen Tabelle, Sonderform-Zähler (3 von 5)
./pruefe-todo.py          hält die Aufgabenliste gegen sich selbst, acht Klassen
./pruefe-kennungen.py     keine Absage-Kennung in zwei Dateien
./mutiere-pruefer.py      beschädigt je eine Regel:  61 von 61
./erzeuge-mutationen.py   verdreht systematisch:      7 von 39
./pruefe-luecken.py       die benannten Lücken einzeln: 13 von 15
./commit.sh               R19 — Commit-Nachrichten nur über Datei
```

**Dazu drei Tests, die aus je einem bezahlten Fehler stammen:** kein Pass ohne Anmeldung ·
`dokumente/SYNTAX.md` gegen die eigene Grammatik · Korpus-Test am Inhalt statt an der Zeilennummer.

## Die Arbeitsregeln — W1 bis W12

Vollständig in [dokumente/WERKZEUGKASTEN.md](dokumente/WERKZEUGKASTEN.md). Jede stammt aus
einem **bezahlten Fehler in diesem Ordner**, jede nennt den Schaden.

## Proben

**18 saubere Beispiele, 66 Giftproben, 76 Tests** —
`cargo test` · `cargo run --bin gabbro -- pruefe beispiele/*.gab`
