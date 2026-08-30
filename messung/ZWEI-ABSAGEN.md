# Die zwei bekannten Absagen, entschieden — beide durch ABSENKEN

*Bahn V, Schritt V-3 des `dokumente/PLAN-VOLLSTAENDIGKEIT.md`. Gemessen und gebaut am
2026-08-31.*

> **Der Plan lässt zwei volle Ausgänge:** absenken (bei gemessenem Bedarf, Regel A) oder **im
> PRÜFER absagen** — dann wandert die Zelle nach `vom Pruefer`. *Was nicht geht: die Zelle
> offen lassen.* Beide Zellen sind zu, und beide durch denselben Ausgang.

---

## V1 — `breaking I { … }`, die Beweisregion

### Der W24-Vorlauf

```
$ gabbro pruefe beispiele/53-zwei-orte.gab
   0 Fehler
$ gabbro emit beispiele/53-zwei-orte.gab
   Fehler: [C001] :64:5  no lowering: `breaking I { … }` …
   Fehler: [C001] :80:5  no lowering: `breaking I { … }` …
```

**Ein sauberes Korpusprogramm, das kein C erzeugt.** Das ist der gemessene Bedarf, und
Regel A ist damit erfüllt — nicht durch eine Meinung darüber, ob die Form nützlich ist.

### Der Grund der Weigerung, und warum er nicht trägt

Er stand wörtlich da:

> *„emitting it would drop the region and make the C look like a program whose obligation
> nobody carries."*

**Die Prämisse stimmt, der Schluss folgt nicht.** Gemessen gegen den unveränderten Prüfer:

```
$ gabbro pflichten beispiele/53-zwei-orte.gab
E  Preservation (2)
     treffen_oeffnen :: antwortpflicht_paarig
     treffen_schliessen :: antwortpflicht_paarig
```

*Die Pflicht wird getragen, und zwar von einem Register, das es schon gibt.* Eine Region,
deren Pflicht gebucht ist, geht nicht dadurch verloren, dass man sie absenkt — sie geht
dadurch verloren, dass man sie **still** absenkt.

### Was gebaut wurde

Der Block trägt seinen Namen ins C:

```c
/* breaking antwortpflicht_paarig -- PROOF region: inside it the invariant is not a
 * premise. At run time this is its statements and nothing else; the
 * restoration is booked as a preservation obligation (`gabbro pflichten`).
 */
{
    e->slots[kern].anrufer = ruft;
    e->slots[kern].antwortende = dient;
}
```

Zur Laufzeit **ist** die Region ihre Anweisungen — ein einfacher Block ist die treue
Absenkung, und jede andere wäre der Erzeuger beim Erfinden einer Laufzeitbedeutung für ein
Beweismittel.

### Was mitziehen musste, und das ist die eigentliche Arbeit

| Ort | warum |
|---|---|
| `emit.rs::benutzte_namen` | der Arm sagte: *„`breaking` has NO lowering at all, so descending would count names the C never reads."* **Im Augenblick, in dem die Weigerung fiel, wurde er der andere Fehler** — das C nennt, was die Menge nicht kennt. Sichtbar an einer Zeile: `(void)e;` über einem Rumpf, der `e->slots` schreibt. Harmlos dort; dieselbe Auslassung über einer Tabelle verliert ihr `T_speicher` («B41b») |
| `zeugnis.rs::EINORDNUNG` | eine abgesenkte Form ohne Eintrag ist `UNZUGEORDNET` — *„entweder weigert sich der Erzeuger, oder er senkt ab, und niemand hat gebucht worauf"* |
| `zeugnis.rs::block` | buchte `breaking` auf `unzugeordnet`; jetzt auf `zaehle` |
| `rechenwerk.rs` | die Zusicherung verlangte die Absage beim Namen. Sie ist **umgedreht** und bleibt an derselben Stelle scharf: was nicht passieren darf, ist eine STILLE Absenkung |
| `beispiele.rs` | die Gegenprobe *„eine Anweisung ohne Einordnung muss auffallen"* stand auf `breaking` — **zum zweiten Mal an ihrem Gegenstand gestorben**, nach `group` («C3c», 2026-08-19). Siehe unten |
| `mutiere-pruefer.py` | zwei Mutationen umgehängt, beide von Hand gesetzt, gebaut und als **genau eine fallende Probe** nachgemessen |

> **Und ein Nebenbefund, der eine eigene Zeile verdient:** nach dieser Buchung gibt es
> **keine unbuchte Anweisungsform mehr**. Jede, die `zeugnis::block` benennt, steht in
> `EINORDNUNG`. Die Gegenprobe sucht darum nicht ein drittes Mal eine Form, die morgen
> absinkt, sondern prüft den WEG: die Anweisungslesung erreicht `zaehle` (sonst fände sie
> `breaking` nicht), und dessen `else`-Zweig hält `ein_name_ohne_einordnung_faellt_auf` fest.

---

## V2 — `match` über etwas anderem als `option index into T`

### Der W24-Vorlauf, und er hat die Absage widerlegt

`messung/fragmente/F05.gab`:173 schreibt

```gabbro
match decode_op(m.op) { Info => … Read => … Write => … Flush => … Scan => … Stop => … }
```

über `tagged type Op = { Info, Read, Write, Flush, Scan, Stop }`. **Der Gegenstand ist keine
Option.** Die Absage nannte etwas, das gar nicht dastand — und der Grund war eine einzige
Zeile: `marken_quelle` las **Orte** und nichts sonst, also fiel ein Ruf durch bis in den
Optionszweig.

*Genau dieselbe Lektion hat `wert_ctyp` am 2026-08-20 in derselben Datei gelernt:* **der
erklärte Rückgabetyp des Gerufenen war die eine von drei Quellen, die niemand fragte.** Hier
war es das dritte Mal.

### Die Messung

`messung/proben/probe-match-ruf.gab` — derselbe Bau, aber der Gerufene ist deklariert:

```
$ gabbro pruefe messung/proben/probe-match-ruf.gab
   5 Items, 0 Fehler
$ gabbro emit  … | cc -std=c11 -Wall -Wextra -Werror
   UEBERSETZT
```

```c
{
Op _m1 = entschluessle(w);
switch (_m1.marke) {
case Op_Info: { melde(1); } break;
…
}
}
```

**Der Gegenstand wird genau einmal ausgewertet, und das ist kein Schönheitsfehler.** Die
Zweige lesen `{gegenstand}.marke` und `{gegenstand}.last.{v}` — mit einem Ruf an der Stelle
des Namens wäre das ein Ruf **je Nennung**: `entschluessle` liefe noch einmal in dem Zweig,
den es ausgewählt hat. *Ein Erzeuger, der einen Ruf vervielfältigt, hat das Programm
geändert und nicht abgesenkt.* Der Optionszweig bindet `_o{tiefe}` seit jeher aus demselben
Grund; dies ist derselbe Zug unter demselben Namensschema.

### Und `F05` bleibt eine Absage — mit einem anderen Satz

`decode_op` ist in `F05` **nirgends deklariert** (`E009` sagt es eine Ebene höher als Hinweis
auf die Wirkungshülle). Ohne Deklaration gibt es keinen Rückgabetyp, und die ehrliche Absage
lautet nicht „keine Option":

```
no lowering: `match` over a call this unit does not declare -- the type of the scrutinee
stands in the callee's declaration, and there is none. A call whose return type IS a
`tagged type` lowers
```

> **Zwei Formen standen unter einer Weigerung, und ihr Grund galt für eine.** Dieselbe
> Bauart, die dieser Ordner inzwischen sechsmal bezahlt hat — `static` eines Verbunds,
> `at dma` neben `at normal`, `E008` an einem Probenrumpf, `sizeof`/`lenof`/`aligned`,
> `descendants of`. *Die Kur ist jedes Mal dieselbe: jede Hälfte bekommt ihren eigenen Satz.*

**Die Zelle U2 ist damit zu**: die Form `match` über einem `tagged type` senkt ab; was in
`F05` übrig bleibt, ist ein Ausschnitt, der seinen Gerufenen nicht nennt — und das ist eine
Aussage über den Ausschnitt.

---

## Die Bilanz

```
vorher   beispiele/  53 emittierende Dateien   messung/*/  18
nachher  beispiele/  54                        messung/*/  19
         73 von 73 uebersetzen, 0 benannte Ausnahmen
```

`beispiele/53-zwei-orte.gab` ist dazugekommen, die Probe `probe-match-ruf.gab` ebenfalls.
**Zwei gemessene `UNGEDECKT`-Zellen sind geschlossen** — die von elf auf neun.

> *Und die Gesamtzahl steht am Abend desselben Tages trotzdem auf fünfzehn.* Nicht weil etwas
> zurückgefallen wäre, sondern weil zwei weitere W24-Läufe sechs Formen erreichbar gemacht
> haben, die vorher niemand gemessen hatte. **Der Stand mit allen Adressen steht in
> `messung/ABSAGEFORMEN.md` §2**, und die Ratsche gehört dorthin und nicht hierher: dieses
> Dokument sagt, was ENTSCHIEDEN wurde, nicht wie groß die Menge gerade ist.

*Am Ende des Tages emittieren `54 + 22 = 76` Dateien, und alle 76 übersetzen* — die zwei
weiteren Zuwächse in `messung/` kommen aus `messung/grammatik/` (V-2).
