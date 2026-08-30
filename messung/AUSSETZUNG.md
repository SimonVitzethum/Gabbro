# `leave`, `breaking` — und welche der beiden Absagen wirklich eine ist

*Gemessen am 2026-08-28, Bahn B, Schritt B2. **Drei Befunde, und der teuerste steht in der
Mitte:** die Absage `non-local-exit` des Rumpfkanals trug vier Pflichten, und keine davon war
ein Ausgang.*

---

## 1. Der Befund

`dokumente/PLAN-AUTONOM.md` schneidet B2 aus zwei `PFLICHTEN.md`-Zeilen:

> * *„der Schnellpfad nimmt den ERSTEN lebenden Empfänger und hört auf"* — «B10»
> * *„die Dienstschleife hat einen BENANNTEN Ausgang"* — «B11»: *„no `leave`, no `break`,
>   no `continue`"*
>
> `leaves` und `leave` stehen im Wortschatz (`kw.rs`), `forever … leaves <identlist>` steht in
> der Grammatik. **W24-Vorlauf ist hier besonders wichtig:** es kann sein, dass die Form parst
> und der Ausgang nur keinen Leser hat — das wäre die fünfte Instanz derselben Klasse.

### 1.1 «B11» ist geschlossen, und zwar seit längerem

Die naheliegende Form, durch den **unveränderten** Prüfer:

```gab
forever runde
    per_pass bounded 64 ops
    on_exceeded watchdog
    effects  { writes b.slots, reads b.slots }
    progress tick
    invariant !b.slots[i].aktiv
{
    b.slots[i].aktiv = false;
    if b.slots[i].fertig { leave runde; }
}
```

```bash
ssh ki-pc-fisch-101 'cd gabbro-B && ./target/debug/gabbro pruefe w24-leave2.gab'
# w24-leave2.gab: 6 Items, 0 Fehler, 0 Hinweise
```

**Und der Ausgang hat sieben Leser**, nicht null: `schleifen.rs`:61 hält `leave <marke>` gegen
die Marken der umgebenden Schleifen (`ziel_pruefen`), `gruppe.rs`:401 bucht ihn als
`Ereignis::Austritt`, `kosten.rs`:529 gibt ihm Kosten 0, `m2.rs`:451 und `lib.rs`:875 zählen
ihn zu den Anweisungen, die **immer enden**, `pflichten.rs` und `phasen.rs` nennen ihn.

**Der Korpus schreibt ihn zweimal**, und einer davon ist genau die Dienstschleife, von der
die Zeile sagt, sie sei nicht schreibbar:

```bash
grep -n 'leaves\|leave ' beispiele/*.gab
# beispiele/04-schleifen.gab:80        leaves   marke
# beispiele/04-schleifen.gab:94            leave dienst;
# beispiele/39-auftragsdienst.gab:156     leaves   marke
# beispiele/39-auftragsdienst.gab:174     leave runde;
# beispiele/42-zaehlwerk.gab:370          narrow gesehen to 0 ..< VOLL else { leave runde; }
```

*Die fünfte Instanz derselben Klasse, und der Plan hat sie vorhergesagt.* **`PFLICHTEN.md`
Zeile 256 und 266 sind veraltet, nicht falsch gedacht.**

### 1.2 «B10» ist ausdrücklich gebucht und nicht gebaut

`PFLICHTEN.md`:396 trägt den Entscheid vom 2026-08-20 und die Berichtigung vom 2026-08-25:

> **«B10» `by consuming` leert die ganze Schlange, und das ist die Bedeutung.** Damit ist
> «B10» kein Lesartenposten mehr, sondern ein **KONSTRUKTposten** — *„das ist eine andere
> SCHLEIFENFORM, keine andere Lesart dieser"* — eine Schleifenform, die **einen Wert
> liefert** und verlassen werden kann. Er fällt unter Regel A und unter Tor 2: **gebucht,
> nicht gebaut.**

**Was «B10» fehlt, ist nicht der benannte Ausgang — den gibt es — sondern der WERT.** Der
Plan hat die beiden Zeilen zusammengefasst („und beide sagen dasselbe"), und sie sagen es
nicht: die eine ist erledigt, die andere ist eine offene Konstruktentscheidung mit Datum.

### 1.3 Und die Absage, die eine ist, sagt etwas anderes ab, als ihr Name sagt

```bash
ssh ki-pc-fisch-101 'cd gabbro-B && for f in beispiele/*.gab messung/*/*.gab; do
    ./target/debug/gabbro lean "$f" 2>/dev/null | grep "(non-local-exit)" | sed "s|^|$f |"; done'
# beispiele/53-zwei-orte.gab -- REFUSED  treffen_oeffnen     (non-local-exit)
# beispiele/53-zwei-orte.gab -- REFUSED  treffen_schliessen  (non-local-exit)
```

Vier Pflichten im Pflichtenkanal, zwei Routinen im Programmkanal — **und alle vier hängen an
`breaking`:**

```gab
impl fn treffen_oeffnen(…)
    ensures e.slots[kern].anrufer == Some(ruft), e.slots[kern].antwortende == Some(dient)
{
    breaking antwortpflicht_paarig {
        e.slots[kern].anrufer     = Some(ruft);
        e.slots[kern].antwortende = Some(dient);
    }
}
```

`lean.rs` sagt `Bricht`, `Leave` und `Next` in **einem Zweig** ab, unter dem Namen *„a
non-local exit out of a named loop"*. **`breaking I { … }` ist kein Ausgang.** Es ist die
AUSSETZUNG einer Tabelleninvariante über einem Block — der Rumpf sind zwei gewöhnliche
Zuweisungen, die dieses Modell seit dem ersten Tag trägt.

*Dieselbe Klasse wie B1 heute früh, eine Datei weiter*, und `breaking` hat sie an diesem Tag
schon einmal bezahlt: der Commit `624ad78` heißt **„`breaking` nannte nie etwas"**.

---

## 2. Zwei Formen, beide Seiten je Form

### Form 1 — `breaking` bleibt abgesagt, und `leave` bekommt ein Modell

Ein vierter `Outcome` (`left (label) (s)`), `exec` propagiert ihn, `.loop` fängt ihn.

* **Dafür:** es ist die Form, die ein `leave` wirklich braucht, und sie ist ehrlich: ein
  `leave` verlässt einen Block, und ein Abstieg, der das nicht sagen kann, kann über einen
  Rumpf mit `leave` nichts sagen.
* **Dagegen:** `Outcome` hat drei Formen, und jede Stelle, die auf ihm auseinandernimmt,
  bekommt einen vierten Fall — `exec`, `finalState`, `finalValue`, und jeder Beweis, der
  `gabbro_simp` fährt. **Gemessener Ertrag: null.** Kein Korpusrumpf mit `leave` erreicht
  diesen Kanal heute; jeder sitzt hinter einer Schleife ohne `invariant` (`loop`, 24 Stück,
  B5) oder hinter einem `narrow` (`narrow`, 6 Stück). Die W24-Probe oben erreicht ihn nur,
  weil sie eigens dafür geschrieben wurde — **und `beispiele/gift/` gehört in keine
  Bedarfsmessung** (W23).

### Form 2 — `breaking` wird getragen, `leave` und `next` behalten die Absage

`breaking I { … }` bedeutet, was sein Rumpf bedeutet; die Namen der ausgesetzten Invarianten
reisen ins Datum. **Wörtlich die Bauart von `.locked`**, die aus demselben Grund dasteht.

* **Dafür:** vier Pflichten und zwei Rümpfe, gemessen. Und die Absage `non-local-exit` liest
  danach die ehrliche Zahl — sie nennt dann wirklich einen Ausgang und benennt damit, was
  eine Schleifensemantik zusätzlich liefern müsste.
* **Dagegen:** ein `breaking`, das seine Aussetzung nur im Datum trägt und nicht in der
  Transition, sieht allein gelesen naiv aus. *Genau der Einwand, den `.locked` schon trägt* —
  und die Antwort ist dieselbe: die andere Hälfte wird woanders eingelöst, und der Name
  bleibt stehen, damit ein späterer Leser die Stelle findet.

---

## 3. Die Entscheidung, und ihr Grund ist ein Begriff

**Form 2.**

> **Eine Aussetzung ist kein Ausgang.** `leave` verlässt einen Block und ändert damit, WELCHE
> Anweisungen laufen; `breaking` ändert, WELCHE PFLICHT dazwischen gilt. Das erste ist eine
> Frage an die Transition, das zweite eine an das Register — und ein Modell, das beide unter
> einem Wort absagt, hat die Frage nicht gestellt.

Und die Sicherheit steht daneben, ausgeschrieben, weil sie der Preis dieser Entscheidung ist:

> **`breaking` als seinen Rumpf zu lesen ist genau so weit tragfähig, wie dieser Kanal keine
> Tabelleninvariante ausdrücken kann** — und er kann keine (`table-invariant`, quantifiziert
> über jeden Slot, acht Stück heute). Die `maintains`-Pflicht steht als **eigene** Pflicht
> daneben (`duty_1`, `duty_4` in `53-zwei-orte`) und wird dort abgesagt. *Bekommt dieser Kanal
> je einen Quantor, ist der Name im Datum die Stelle, an der ein Invariantenkanal nachlesen
> muss, wo die Aussetzung lag.* Deshalb reist er mit und ist keine Zierde.

`leave` und `next` behalten `non-local-exit`, und was ihnen fehlt, steht jetzt benannt da:
**ein vierter `Outcome`.**

---

## 4. Was die Entscheidung NICHT kauft

* **Sie baut «B10» nicht** und will es nicht: der Entscheid vom 2026-08-20 steht, und was
  fehlt, ist eine Schleifenform, die einen **Wert** liefert. Der benannte Ausgang, den B2 im
  Titel trägt, war nie das Fehlende.
* **Sie modelliert `leave` nicht.** Ein Rumpf mit einem echten `leave` bleibt abgesagt —
  gemessen an der W24-Probe, die genau dafür geschrieben wurde. *Die Absage benennt jetzt,
  was fehlt, statt drei Dinge zusammenzufassen.*
* **Sie sagt nichts über die Invariante selbst.** `antwortpflicht_paarig` bleibt in beiden
  Routinen als `table-invariant` abgesagt. Was fällt, sind die vier `ensures` daneben —
  Aussagen über zwei Plätze, die mit der Invariante nichts zu tun haben.
* **Und sie schließt «B11» nicht, sie stellt fest, dass es geschlossen war.** *Eine Zahl, die
  durch eine Berichtigung fällt, ist keine Arbeit* (§1.8), und diese fällt so.
