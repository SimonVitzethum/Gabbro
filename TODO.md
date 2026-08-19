# Gabbro — open items

> **Cut by ROLE 2026-08-16.** The file had put this question to itself in the reconciliation of
> the 14th and left it unanswered — *"a list in which half a day of paper stands next to a
> subproject no longer sorts, and a list that does not sort does not get read."* Four roles:
> **decisions · measurements · building · bookkeeping.**
> On top of that **six outdated places** have been pulled up (the five scratchpad classes, the
> 17-way split, the four domain fragments, "compiler up to P3", the call effects,
> "P2 at 1 of 6") — *exactly the class the reconciliation of the 14th has already paid for once.*
>
> **Tidied up 2026-08-16.** The eight design and measurement documents now lie in
> [`dokumente/`](dokumente/); in the root directory there stand only **README, TODO and DONE**.
> **Twenty items have been checked against the CODE and moved to [`DONE.md`](DONE.md)** —
> not against memory: per item a refusal code, a file or a command line.
>
> **Caprock items taken out 2026-08-16.** This list carries **Gabbro**. Whatever has its subject
> in Caprock's code or bookkeeping belongs there — even if it arose here. *A task list that
> carries two projects sorts for neither.*
> Taken out: eager FP, K1–K3, N2, the two open plumbing obligations,
> progress/starvation (D8). **Not deleted, but moved to
> [`dokumente/AN-CAPROCK.md`](dokumente/AN-CAPROCK.md)** — they are findings, only
> not ours.
>
> **Reconciled 2026-08-14.** This file carries **exclusively what is open**; what is done stands
> in the design files, what is refuted in [`dokumente/HISTORIE.md`](dokumente/HISTORIE.md), what is measured in
> [`dokumente/MESSUNGEN.md`](dokumente/MESSUNGEN.md). The reconciliation on 2026-08-14 found the file **untrue
> about itself in eight points** — eight done entries, six statements the folder had
> overtaken, three topics carried twice, two colliding label systems and
> stale numbers from P1. **A list that is not right costs more than none:**
> it says at every point "this is still open", and the reader believes it.
> What the reconciliation found item by item stands at the end under *Reconciliation*.

---

# THE CRITICAL PATH, in one line

> ~~**B3**~~ → ~~**K/A/W substitution**~~ → ~~**`effects` reading**~~ → ~~**closures**~~ →
> ~~**`table.induktion` into Isabelle**~~ → **group `ops` → P5 → P6 → P7**

> **The path changed its head on 2026-08-16, and against its own earlier
> statement.** Not group `ops`, but **the first proved template**. The reason is
> not effort but a curve: *the amortisation argument — a template falls
> ONCE, not per program — **holds only from the first proved template onwards.*** Until then
> the template list is structurally the same mountain as seL4's proof mountain, only unclimbed.
> **One proved out of eighteen is qualitatively something other than zero out of seventeen:** the
> register changes from *"list with a length"* to *"list with a fall direction"*.
>
> `table.induktion` is the smallest, it has been marked as an L3 item since the INDUCTION entry,
> and **it has not got its turn for days, because it competes with nothing except
> everything.**

**The first two fell on 2026-08-16** (`DONE.md`), and the substitution has **shortened** the path
rather than lengthened it: `p_B3 = 0,0096`, surcharge `≥ +0,05` — *below the resolution of the
metric.* **B3 is done as a cost item; ~~the metric stays open at `≥ 1,90`~~ — die Zahl ist am
2026-08-19 ZURUECKGEZOGEN und lautet `unbekannt, > 0,5`**, weil `w` an VERUS-Zeilen gemessen
war und Gabbro in Isabelle/HOL beweist. *Die Pflichtseite bleibt der Ort, an dem sie haengt;
nur steht dort jetzt keine Zahl.* The head position now belongs to the
decision, not to the measurement.

> **And the sentence the measurement chain produced belongs at its head:** *the expensive
> obligations are **many, but small*** — W = 38 of 73 by head count, but only 34 % of the lines; a
> W obligation is on average **half the size** of a K or A obligation (`dokumente/BEWEIS.md`).
> **The distance to the floor therefore hangs almost entirely on the W column itself**, not on
> loop forms. Whoever wants to attack the design attacks there.

**Everything else is parallelisable or a memo.** And the only item on this path that is
neither code nor a run but **a word of the folder** is the slot:

| | |
|---|---|
| **`M-effects-lesen` — direction** | **A** — redeclare the ten fragment functions (2026-08-16) |

**Justification, and it has two parts, both of them checkable:**

1. **E3 consistency.** The folder says at every other point *"nothing is implicit"*. A
   coarser frame promise (C) would be exactly the silent exception — a read that names no line
   because the line would get too long.
2. **A is the reading whose violation the pass can report PRECISELY.** C reports
   *"read somewhere outside `mmio`/`dma`/`atomic`"*; A reports **which function
   reads which place without naming it**. *What cannot be reported exactly, no
   pass enforces — the same justification reading B died on.*

**The pre-registered price was a factor of three — and it did NOT occur.** The memo
said *"A drops 10 of 32 functions, C drops three"*. Measured after the pass was built
(`dokumente/MESSUNGEN.md`, *Lesart A gebaut*): **0 of 32.** `FRAGMENTE.md` already declares its
reads; what fell were **two of my own examples**, and that is not a property of the
reading but of my care in writing.

**Reading B had already been eliminated before that** — by its own finding: it is not
mechanically separable, and *what cannot be counted, no pass can enforce.*

**The unbuild route (R12) still stands:** the read half is an addition in `wirkungen.rs` against
the same list the write side runs against. If it falls, one refusal class falls —
*no grammar change, no data type, no example has to go back.*

*The direction stands and is built (`E010`). With that the critical path is for the first time free
of items that are neither code nor a run — what remains is building and measuring.*

---

# DECISIONS — need a judgement, not a run

- [ ] **Gehoert der Rundungsmodus in den TYP?** *(offen seit 2026-08-18)*. Ein `f64<RNE>`, das
      sich mit `f64<RTZ>` nicht mischen laesst, beseitigt eine ganze Fehlerklasse
      STRUKTURELL -- ohne einen einzigen Beweis ueber Zahlenwerte. **Es waere die vierte
      Instanz eines vorhandenen Musters**: `ptr<normal, rw>`, `atomic … seq`, `format … endian
      big` stellen ihren Modus schon an den Typ statt in Umgebungszustand. Gemessen: `ptr<…>`
      ist kein allgemeiner Typparameter, sondern ein eigener Typkonstruktor mit zwei
      geschlossenen Wortmengen -- **genau diese Form haette `f64<RNE>`.** *Und die Frage haengt
      nicht daran, ob Gabbro je rechnet: auch der Gast hinter `entrust` hat einen
      Rundungsmodus, und heute sagt darueber niemand etwas.* Nicht zu verwechseln mit
      Fehlerschranken im Typ (Rosa/Daisy) -- die brauchen Refinement-Types und sind die
      wertgetragene Schranke eine Stufe schaerfer.
### K100 — der Weg auf 100 % Klempnereiabdeckung ([`dokumente/PLAN.md`](dokumente/PLAN.md))

- [ ] **Ein Traversierungszaehler erbt die Schranke seiner Domaene** — die letzte
      `narrow`-Klempnereipflicht des Korpus (`FRAGMENTE.md`:1100). Die Traversierung laeuft
      ueber `s.worte`, also kann `i` die Laenge nicht ueberschreiten; **M1 sieht es nicht**,
      weil der Zaehler eine gewoehnliche lokale Variable ist. *Eine V-Regel, keine neue
      Grammatik.* Tor danach: **`N_ritus = 0`**.
- [ ] **PL.1 — das PASSREGISTER anlegen** ([`dokumente/PLAN.md`](dokumente/PLAN.md), PL).
      **Zehn Paesse entscheiden ueber jedes Programm, und keiner schuldet einen Satz** --
      dieselbe Lage, in der die Schablonen vor ihrer Auszaehlung waren. Wie `schablonen.rs`,
      mit denselben zwei Zaehnen; **~22 Saetze** geschaetzt. Zweiter Zahn sofort: *kein neuer
      Absagecode ohne seinen Satz* (heute 52 Codes, null Saetze).
- [ ] **PL.2 — die drei Saetze mit der groessten Traglast:** `K001` Summation (**hat heute schon
      einen gemessenen Fehler**), `H006` Rangordnung, V2 relationale Verengung (102 Stellen).
- [ ] **PL.3 — die Bruecke: (c) je Satz eine Sprechprobe, die den Rust gegen das Modell faehrt.**
      Das Geschirr steht (`mutiere-pruefer.py`, 148 von 148) -- was fehlt, ist der Satz, der
      sagt, WELCHE Beschaedigung fallen muss. *Aus 132 Mutationen ohne Satz werden 132 mit
      einem.*

- [ ] **Die Spalte „of which K" in `PFLICHTEN.md` summiert sich zu 33, die Summenzeile sagt
      18** *(gefunden 2026-08-17 beim Ablesen von `H`)*. **Beide koennen nicht stimmen.** Die
      verlaessliche Zahl ist seither die abgelesene (`./zaehle-pflichten.py --haengend`,
      `H = 21` = 14 verankert + 7 Absenkungen); *bis die Herkunft jeder einzelnen Zahl dieser
      Spalte geklaert ist, ist sie Urteil und nicht Messung.* **Derselbe Vorgang hat schon
      sechs `gap:`-Zeilen produziert, die in den Summen laengst geschlossen waren** -- die
      Summe wurde gepflegt, die Quelle nicht.
- [ ] **Der Erzeuger raet den Typ eines `let` nicht, obwohl er ihn ablesen koennte**
      *(gesehen 2026-08-17 an `beispiele/21`)*. `let c : Completion = fertig(k, 7);` braucht
      die Annotation, weil `ctyp` nur die geschriebene Form kennt -- die Signatur des
      Gerufenen stuende daneben. **Die Weigerung (`C001`) ist die sichere Richtung**, aber sie
      kostet an jeder Bindung eines zusammengesetzten Werts eine Zeile. *Entweder aus der
      Signatur ablesen (kein Raten, ein Nachschlagen) oder die Zeile als Absicht aufschreiben.*
- [ ] **K100.4 — die STARKE Fassung von (b) fehlt noch.** `gabbro zeugnis` zaehlt auf, worauf
      eine Uebersetzung ruht (gebaut 2026-08-17, acht Einheiten, je Befund gebucht). *Es sagt
      nicht, dass sie haelt.* Die starke Fassung waere ein maschinell geprueftes Zeugnis je
      Uebersetzung -- **und die Vorstufe ist als Vorstufe benannt**, damit die Zahl nicht mehr
      verspricht, als sie misst.
- [ ] **Die FREMDEN RUEMPFE sind die eine Klasse, die sich auch unter „ganz Gabbro
      verifiziert" nicht aufloest** *(gemessen 2026-08-17)*. F7 -- das Fragment, das
      vollstaendig abgesenkt und an der Ausfuehrung gemessen ist -- besteht aus **sieben**
      Rufen an Ruempfe, die Gabbro nie sieht; jede Sperre bringt vier Prototypen mit.
      **`gabbro zeugnis` zaehlt sie je Datei.** *Was fehlt, ist die andere Haelfte: eine Form,
      in der der Rufer die Pflicht des fremden Rumpfes AUSSPRICHT statt sie nur zu unterstellen
      -- die Sperre etwa schuldet gegenseitigen Ausschluss, Fortschritt und die Rangordnung,
      und keine Zeile sagt das heute.*
      **Gemessen 2026-08-17: 48 fremde Ruempfe im Korpus, NULL sprechen ihre Pflicht aus.**
      `ensures` an einer Deklaration ohne Rumpf ist grammatisch seit jeher moeglich (geprueft,
      0 Fehler) -- *und kein Pass liest es.* Die Schicht hat damit zwei Haelften: die sieben
      Zeilen hinschreiben (kostet nichts) und den Pruefer sie in die Beweispflicht des Rufers
      tragen lassen (PL-Arbeit).
- [ ] **`opaque` beisst -- aber es gibt keine UMWANDLUNG** *(gebaut 2026-08-18, `D003`)*.
      Ein undurchsichtiger Typ hat die Rechnung seines Traegers nicht; Vergleiche bleiben
      erlaubt. **Null Korpusstellen fielen** -- der Beleg kommt aus Gift 79 (drei Operatoren)
      und vier Sprechproben, nicht vom Korpus. *Was jetzt fehlt, ist der Ausweg:* heute gibt
      es keine Form, einen undurchsichtigen Typ ABSICHTLICH zu oeffnen, also ist die Regel ein
      Verbot ohne Tuer. **Solange kein Korpusstueck sie braucht, ist das richtig** -- aber es
      gehoert benannt, bevor jemand `opaque` deshalb weglaesst.
- [ ] **`entrust` -- ein `code`-Raum, dessen Inhalt Gabbro nicht kennt.** Der Sprung ins
      Ungezeugte ist ein ADRESSRAUMWECHSEL, kein Kontrollflusssprung: eigener `code`-Raum
      ohne Schreibrecht (W^X, `mappings of` prueft es), eigene PD, eigener CapSpace, Rueckweg
      als `entry`. **Gabbro schuldet dem Gast nichts** -- fuer den JIT-*Compiler* gilt die
      Zusage vollstaendig (Byteemission plus Tabellen plus `recurse bounded`), fuer den Gast
      gilt Isolation statt Beweis. *Das ist keine Luecke, sondern der Zweck eines
      Mikrokernels.* Was fehlt: ein Wort, ein deklarierter Eintrittsvertrag (Register, Stapel,
      Caps) und ein `assume`-Eintrag im Zeugnis. **Kein neuer Pass.**
- [ ] **Gleitkomma-Memo: die Kosten sind eine ZWEITE FAKTENLOGIK, nicht ein zweiter
      Zahlentyp** *(2026-08-18)*. Intervallarithmetik ueber IEEE-754 ist gebaut und bekannt.
      **Was bricht, ist die NEGATION einer Vergleichsbedingung:** ist ein Operand NaN, sind
      alle Vergleiche falsch, und `!(x < y)` folgt `x >= y` nicht. `m1::fakten_aus(…,
      negiert = true)` waere unsicher -- *das ist die Maschinerie, mit der jede Verengung in
      dieser Sprache arbeitet.* Zwei Auswege, beide teuer: NaN durch Konstruktion ausschliessen
      (Laufzeitpruefung, W6) oder die Negation kein Faktum liefern lassen (sicher, und dann
      ungeprueft genau dort, wo man pruefen wollte). **Bedarf zaehlen, bevor gebaut wird.**
- [ ] **«B24» hat die beste Hebelwirkung aller offenen Posten** *(bewertet 2026-08-18)*.
      Ein Netzwerkstack ist bis auf EINE Entscheidung schreibbar: Verbindungstabelle
      (`count NCONN`), Paketpool, Pruefsumme ueber `<= MTU`, Neuuebertragung (`retry
      bounded`), Zeitgeber (`forever per_pass`) -- alles vorhanden. **Was blockiert, ist der
      IP-Kopf**, und der ist ein Feld aus Bitlagen (`version:4 IHL:4 DSCP:6 ECN:2 flags:3
      fragment_offset:13`). `format` weigert sich fuer jede davon. *Keine Bauarbeit, keine
      Beweisarbeit -- eine Entscheidung.*
- [ ] **Eine parametrische `costs`-Zusage ist heute schreibbar und VOLLSTAENDIG LEER**
      *(gemessen 2026-08-18)*. `costs <= 0 * n ops` an einem Rumpf, der 1 op kostet:
      **3 Items, 0 Fehler, 0 Hinweise.** `kosten.rs` sagt es im eigenen Kopf (*„die Schranke
      darf von Eingaben abhaengen … in dem Fall schweigt der Pass"*), und `gabbro kosten`
      druckt ehrlich `zugesagt --`. **Damit steht der Preis der wertgetragenen Schranke nicht
      in der Grammatik, sondern in Pass 9: er muss symbolische Ausdruecke VERGLEICHEN statt
      zu schweigen.** *Was schon passt: `Kosten::Zahl(i128)` traegt `40 * 2^64` muehelos.*
- [ ] **Unter einer Sperre darf der Rahmen NICHT parametrisch sein.** `held <= N ops` ist eine
      LATENZaussage -- wie lange ein anderer Kern hoechstens wartet. Ein `held <= 40 * n` mit
      symbolischem `n` ist eine Sperre, die unbeschraenkt lange gehalten wird, und damit ist
      `rank`/`held`/`K002` leer. *Dieselbe Trennung noch einmal: die Kostenklasse vertraegt
      Symbole, die Sperrklasse nicht.* **Die Regel gehoert in die Erweiterung, bevor sie
      Grammatik wird.**
- [ ] **Eine Bibliotheks-ABI, und das Format steht schon** *(bewertet 2026-08-18,
      `PLAN.md`: „Zwei Fragen, die die Grenzen beschreiben")*. **Gabbros ganze Zusage ist eine
      Aussage ueber EINE Uebersetzungseinheit** -- jede der elf Klassen wird an einem Baum
      geprueft, den ein Lauf ganz sieht. Eine Bibliothek durchschneidet genau das, und ohne
      ABI faellt die Zusage an der Schnittstelle lautlos auf „untere Schranke" zurueck (`E009`).
      **`gabbro zeugnis` schreibt bereits, was sie tragen muss:** Annahmenmenge, Schablonen mit
      Beweisstand, `effects`/`costs`/`Held`, und die SPERRRAENGE -- *der schaerfste Posten:
      zwei Bibliotheken mit unabhaengig vergebenen Raengen ergeben einen Zyklus, den keine von
      beiden allein sehen kann.* Was fehlt: `gabbro pruefe` liest die Zeugnisse der gerufenen
      Bibliotheken mit und vereinigt sie -- mit denselben Weigerungen, die es innerhalb einer
      Einheit schon gibt. **Der erste Posten, bei dem Gabbro etwas gewinnt, ohne eine Klasse
      zurueckzugeben.**
- [ ] **Zwei Blicke auf dieselbe Karte gingen auseinander, und nur einer hatte einen Test**
      *(gefunden 2026-08-17 beim Bauen von `const fn`, weil eine Giftprobe nicht fiel, die
      fallen musste -- R11)*. `typ_von_ort` schlug den globalen Traeger modulbewusst nach
      (`suche`), `index_pruefen` unqualifiziert (`get`). **`M103` schwieg damit in jedem
      `module`-Block fuer eine Tabelle, die ueber ihren globalen Namen adressiert wird.**
      Behoben und mit Gift 76 belegt. *Was fehlt, ist die allgemeine Frage: an wie vielen
      Stellen wird eine der Karten aus `umgebung.rs` DIREKT befragt statt ueber `suche`?
      Jede davon ist derselbe Fehler, und keine hat heute einen Waechter.* **Gezaehlt:
      13 direkte `.get(`-Blicke auf die Karten in `umgebung.rs`** -- wie viele davon in einem
      `module` danebengreifen, ist ungemessen.
- [ ] **`const fn` -- comptime, das WERTE rechnet und keine Schablone kostet**
      *(bewertet 2026-08-17, `PLAN.md`: „Wozu Gabbro taugen wird")*. Heute rechnet
      `konst_wert` nur Literale und `const`-Ketten; `count NSLOTS * 2` oder
      `costs <= laenge(T) + 4` sind nicht schreibbar, und der Zusammenhang dreier Konstanten
      steht in einem Kommentar. **Ein `const fn` erzeugt keinen Code, also keinen
      Schabloneneintrag** -- seine Beweispflicht ist Totalitaet, und die traegt die Sprache
      schon (drei beschraenkte Schleifenformen, `effects { pure }` erzwungen).
      *Die Linie: comptime, das Werte rechnet, ist frei; comptime, das CODE erzeugt, kostet
      eine Schablone -- und ein nutzergeschriebener Erzeuger ist einer, dessen Beweispflicht
      niemand aufgeschrieben hat.*
- [ ] **`accumulates` kann nicht absenken, und es fehlt kein Erzeugercode, sondern ZWEI
      Entscheidungen** *(gemessen 2026-08-17, nachdem `accumulates.monoid` bewiesen war)*.
      `SPRACHE.md` §11.4 sagt: *„one cell per core, merged on reading over the
      NCORES-bounded loop."* **Beide Groessen stehen nirgends:**
      1. **Die Zellenzahl.** `accdecl` nennt keine. Der Erzeuger muesste `NCORES` raten oder
         einen Namen suchen -- *genau das Raten, gegen das `C001` steht.* Der kleinste
         Ausweg ist `per cpu <constexpr>` an der Deklaration; die Woerter gibt es schon.
      2. **Der aktuelle Kern.** Es gibt in Gabbro KEINEN Ausdruck dafuer. `per cpu` steht
         allein am `stack` eines `entry`. Ohne ihn laesst sich die Schreibstelle
         `x = v` nicht in `x_zellen[kern]` absenken.
      *Die Schablone ist bezahlt (`Accumulates_Monoid.thy`) -- was fehlt, ist die Sprache.*
- [ ] **Zum ZWEITEN Mal in eine Beweissuche gelaufen -- und die Regel stand schon da**
      *(2026-08-17)*. Erst ein `metis` (9 Minuten, 6,3 GB), dann ein `blast` (12 Minuten,
      4,8 GB). **Eine Regel, die man kennt und trotzdem bricht, braucht keinen weiteren Satz
      -- sie braucht ein Werkzeug.** `./pruefe-beweise.sh` haelt jetzt bei 3 GB an. *Was
      fehlt, ist die andere Haelfte: kein Wachhund verhindert, dass ich den Schritt beim
      Schreiben suchen LASSE statt ihn hinzuschreiben.*
- [ ] **Eine `bank` mit `stride 0` erzeugt LEERE Zellen, und der Satz gilt trivial**
      *(ausgespuelt beim Beweis von `device.konstruktor`, 2026-08-17)*. `bankeintraege_
      ueberlappen_nicht` braucht `stride > 0` nicht als Praemisse -- bei null ist jede
      Bankzelle leer, und leere Mengen schneiden sich nicht. **Richtig und nutzlos ist keine
      bestandene Pruefung:** der Erzeuger sollte `stride 0` ablehnen, statt sie leerlaufen zu
      lassen. *Ein Beweis, der einen Fall trivial macht statt ihn zu decken, hat ihn gefunden.*
- [ ] **K11.2.2 ist am Korpus nicht messbar, und das ist ein Befund** *(gemessen 2026-08-17)*.
      Vier Kontextwurzeln (3 × `entry`, 1 × `boot`), **null davon mit einem Rumpf, den Gabbro
      sieht** -- jedes `dispatch`-Ziel ist ein `extern fn`. Die Huelle ueber einer
      Kontextwurzel ist leer, also kann die Regel *„jeder Platz, den zwei Kontexte beruehren,
      ist gesperrt oder atomar"* nie feuern. **Dieselbe Lage wie `E010`.** Sie haengt damit am
      ZWEITEN Korpus, der ohnehin als Bedingung ueber K11 steht.
- [ ] **`ensures` ist wohlgeformt geprueft -- die EINLOESUNG fehlt** *(nachgemessen
      2026-08-19)*. ~~Ein Tippfehler in einem `ensures` faellt nicht.~~ Er faellt seit dem
      2026-08-18 an `M109` und `M111`, an einem `impl fn` wie an einem rumpflosen
      `extern fn`; die Grundnamen loesen auf (Parameter, Globale, Konstanten, `result`).
      **Was offen bleibt, ist die andere Haelfte und sie ist die groessere:** dass der Rumpf
      die Zusage HERSTELLT, prueft niemand, und das ist Beweisersache. *Der kleinste naechste
      Schritt ist nicht der Beweis, sondern die Quantorbinder und `Self` -- die zwei
      Namensarten, die `sammle_namen_pred` heute nicht kennt.*
- [ ] **Die Absenkung fehlt fuer die meisten Formen -- und zwar als WEIGERUNG, nicht als Luecke.**
      `C001` weigert sich benannt fuer `forever`, `publishes`, `awaits`, `exchange`,
      `let … else`, `static`, `reason`, `group`, `walk`, `entry`, `boot`, `accumulates`,
      `descendants of`, `ancestors of`, `format`-Bitlagen und `match` ueber etwas anderem als
      einer `option`. *Ein verifizierter Erzeuger, der sich weigert, erzeugt nichts.*
- [ ] **Der ZWEITE Korpus gehoert in denselben Plan wie das letzte Konstrukt.** Die zehn
      Fragmente sind nach ihrer SCHWIERIGKEIT gewaehlt; `H = 0` ueber ihnen ist keine Aussage
      ueber Gabbro. **Ohne einen Korpus, den beim Bauen niemand angesehen hat, ist K100 Falle 80
      in Reinform.**

### From the emitter (2026-08-17) — two answers belong in the SPECIFICATION now

- [ ] **«B26» is answered, and the answer belongs in [`dokumente/SYNTAX.md`](dokumente/SYNTAX.md).**
      The finding read: *"ob `mirrors` damit auch den Vorzustand einer `transition` an `GCMD.TE`
      aus `GSTS.TES` bezieht, sagt `SYNTAX.md` nicht."* **The emitter answers yes and measures
      it** (`1 1 1 1`, `beispiele/20-falle-vier.gab`). *An answer that lives only in the
      generator is the same construction as a promise that lives only in a tool invocation.*
- [ ] **«B33» is answered too, and its reason is now demonstrable.** The folder asked: *"Wenn es
      Absicht ist, gehört die Begründung aufgeschrieben — sie wäre ein starkes Argument."*
      **It is:** a register access lowers to `volatile`, and `volatile` IS the statement *"this
      place may change between two reads"*. Narrowing it after a comparison would be **wrong**,
      not merely absent. The reason belongs in `SPRACHE.md` beside V1–V3.

### From the emitter (2026-08-17) — the cost pass carries the typical case

- [ ] **`mappings of`: the cost pass under-counts by seven orders of magnitude.**
      [`dokumente/SPRACHE.md`](dokumente/SPRACHE.md):786 says it quantifies over **ALL
      reachable leaf entries** of a `walk`; the pass bounds it at `levels × node length`
      (`kosten.rs`:362, `walkschranken`) — **2 048** for four levels of 512, where the leaves
      number **512^4 = 68 719 476 736**. *The pass counts one descent PATH and calls it the
      domain.*
      **This is the class the folder has paid for twice** — `revoke` promised 200 ops and costs
      16 452 480, A4 promised 4 096 and costs 831 488. **Both times a HUMAN wrote the typical
      case instead of the bound and the pass caught it. Here it is the pass itself.**
      Either the domain means a path (then `SPRACHE.md`:786 is wrong and the name misleads) or
      it means the set (then no `walk` traversal can carry a cost promise). *The emitter
      refuses rather than pick the smaller reading.*

### From the reassignment (2026-08-17) — three judgements the measurement forces

- [ ] **Frame and Publication are refuted as carried, each at ONE named site.** «B39» — the MMU
      writes `A`/`D` itself, so *"only what stands there changes"* is **false** there, and the
      limit the rebooking of 2026-08-16 wrote down (*"an unknown name falls in the name pass"*)
      does **not** cover a writer that is not a program. «B19» — see the item under BUILDING.
      **The tipping rule is unambiguous** (*a construct that carries a class only partly leaves
      it hanging*); what is open is whether the folder applies it, which would put `N_neu` at
      **5** again. *The evidence is there; the booking is a judgement.*
- [ ] **Does a NAMED residue tip a class?** *Overflow* has five hanging obligations, and three of
      them are `narrow … else` — a **named, checked, bounded** discharge with its own bar (≤ 24),
      not an unnamed gap. **If a named residue tips, `N_neu` rises again; if it does not, the
      tipping rule needs the word "unnamed" in it.** Either way the rule gets sharper, and today
      it is silent on the difference.
- [ ] **Thirteen of the 36 hanging plumbing obligations belong to NO class of the eleven** —
      device notation, `format`, the missing struct literal, the missing return-value binding.
      **The taxonomy was built for what a kernel gets wrong; a third of the measured gaps are
      about what the language cannot SAY.** *Does the folder count on a second axis, or does it
      say why it does not?*
- [ ] **`narrow` sites are not equal, and neither measurement sees it.** `FRAGMENTE.md`:1660 —
      else branch **reachable** (a hostile DTB takes it). `:1100` — else branch **cannot be
      taken** and must stand there anyway. **The bar of 24 counts them the same.** A yardstick
      that cannot tell a check from a ritual measures the wrong thing.

### From the escalation of 2026-08-14 — one number never reconciled

- [ ] **54 or 102 relational preconditions?** Part 1 of the design review says 54,
      [`dokumente/SPRACHE.md`](dokumente/SPRACHE.md):662 and :1222 say 102. **Two numbers for the
      same population, neither with a search path** — W7. Resolving it means a count against
      `../caprock-messbasis`, not a decision.

### The group: three forms stand — what is open is PRESERVATION

- [ ] **All three S17 obligations stand as FORM. What is missing is the preservation.**
      Built: (a) locks in rank order (`U003`/`U005`), (c) no intermediate exit (`U006`),
      (b) the statement connects (`U007`).
      **Pulled up 2026-08-16:** the clause stands, and with it `U007` — a
      group invariant must name **at least two** carriers, otherwise it belongs at the
      table. With that (b) is built as a **form**. **What stays open is (b) as PRESERVATION:** that the
      statement holds under an operation is the prover's business and falls to S16/S17 — the checker
      establishes the three conditions under which the question can be put at all.
      **The next step is therefore the group operation** (`ops` over the group), and it
      is no longer a preliminary but the recipient of the proof obligation.

### «B41» — three domains are demanded as measured. Build them or not?

- [ ] **The need is on the table, with `file:line` — the decision is not.** B3 found
      **584 non-traversable lines**, and **226 of them (38,7 %) stand in DMAR/PCIe**,
      that is, in none of the three suspected areas. Three named gaps:
      * **`ancestors of`** — the device topology is walked **upwards** (`cur =
        topo[cur].parent`, four bodies). Downwards it is a domain, upwards it is not.
      * **Union-find** — `dmar.rs:519` `find` **writes the chain it is walking**
        (`parent[x] = parent[parent[x]]`). Traversal and surgery in one statement;
        none of the eight domains covers that.
      * **Chain over an edge function** — `redirect.rs:577`/`625` walk the handler edge
        over a parameter `kante: impl Fn(u16) -> Option<u16>`; the chain arises only
        through the call and is not declarable.

      **The three are NOT of equal rank, and the ordering is half the decision:**
      * ~~**`ancestors of`**~~ — **built 2026-08-17** (`beispiele/18`, poison 69). And the
        build uncovered a gap that `descendants of` already had: over an
        `index into T` the cost pass did not find the bound, because the table name came
        unqualified out of the index type. **No example had ever triggered the
        site** — the corpus carries `descendants of` only in predicates, where no
        cost pass runs.
      * **Edge function — the line question has had its CRITERION since 2026-08-16.** It is the
        general case of `chain(a,b)`, and the precedent already stands in the language:
        **the `update` body of `exchange` — pure, M1-typed, over a value, without a
        quantifier.** An edge function of the same class (*one value in, one `option` value
        out, no world*) is **not a quantifier stock but a declared step.**
        > **The cut:** quantifier stock begins where the function appears in **statements**
        > instead of in **domain generation**. As long as it only supplies witnesses and stands in
        > no `requires`/`invariant`, the line does not move.
        **With this cut the chain swallows `ancestors of`**, and «B41» goes from three
        gaps back to **one design line**. *And the measurement from the same day shows that
        it is the same subject as the closure item:* `impl Fn(u16) -> Option<u16>`
        stands three times in `sched/redirect.rs` and is both at once.
      * **Union-find — will probably get NO traversal form at all.** `find` with
        path compression mutates the structure it runs over: **the interlocking from
        P0.1 attempt 1, disguised as a read operation.** Prediction in the folder: it stays a
        5 : 1 item or becomes **group-`ops` material** (compression as a generated operation
        with preservation of the representative invariant). *The prediction stands there so that a
        proposal for a `union_find` domain has to beat it first.*

      **W3 is satisfied (measured need), and W3 does not demand that one follow it.** The price
      stands in column 2 of the convergence metric: **every further domain is one more domain that
      every reader has to believe.**

### The question that decides the core

- [ ] **Real linearity is the only mechanism no existing tool supplies** —
      measured: Verus' `tracked` is **affine**, Rust is affine, SPARK's leak check hangs on an
      **allocation**. The boot phase, `Parked` and the linear checking obligation hang on it.
      **Open: is one mechanism enough to justify a language?** The cheaper answer
      would be a contribution to Verus (linear instead of affine). That is the most expensive open question in the folder.
- [ ] **ATS is the nearest relative for the core and is unexamined** — linear types plus proofs,
      compiled to C. The same logic as the Verus gate: *the nearest relative is built, the
      folder is not.* **Should have been run before P2; P2 ran first.** That does not make the comparison
      void, only more expensive: it now measures against something built instead of against
      a design.
- [ ] **For every further mechanism, run the counter-calculation.** M2 at the lock evidence and M1 came out
      against the folder on 2026-08-13. **M3 is to be measured against the right baseline:
      not Verus, but `tock-registers`/`svd2rust`** — typed register accesses are a
      Rust library. The question is what it lacks: transitions over bits, conditions over
      register boundaries, barrier domain in the type.

---
### Syntax — open decisions (details in [`dokumente/SYNTAX.md`](dokumente/SYNTAX.md))

- [ ] **Variable lengths in `format`** — the hard 20 % of every parser generator, no
      notation available.
- [ ] **Version evolution:** does an `@version 3` reader also read v2 — **refusal or migration**?
      Both defensible, neither decided.
- [ ] **Genericity** — without it every table needs its own `traverse`; with it the question
      of how contracts are parameterised.
- [ ] **The stock of quantifiers in `spec fn` is undecided — and that is exactly where the line moves**,
      if nobody watches.
- [ ] **Error propagation:** without `?` every call becomes three lines, with `?` there is hidden
      control flow. Both contradict a design rule.
- [ ] **The keyword language** is in English, because that is what the existing code is. Price: a break with the
      German running text. Reversible (one table in the lexer).
### Design — open decisions

- [ ] **Roundtrip** `lesen(schreiben(x)) == x` belongs in the differential test.
- [ ] **Cost figure per invariant** and at `by unbesucht`: which structure, who resets it,
      what the reset costs, whether it may live under the lock.
- [ ] **Quantify the axiom layer — the x86 half is runnable, the aarch64 half is NOT.**
      **As long as the number is missing, "memory-safe under A1…An" is a form without content.**
      * **x86:** runnable against `../caprock-messbasis` (= `SEL4Lake/SEL4Lake` @ `arch/x86_64`,
        `a1bf707`). Open.
      * **~~aarch64~~ — BLOCKED, and not for reasons of time (2026-08-15).** The
        only aarch64 tree in the folder (`SEL4Lake/ARMTest/stm32mp25-kernel`) is **not a
        second kernel but an older snapshot of THE SAME lineage** — evidenced
        with `git log --follow`: `R099`, a rename with 99 % similarity from
        `sel4lake-cap` to `caprock-cap` (see [`dokumente/HISTORIE.md`](dokumente/HISTORIE.md), *Zwei Fundstellen
        aus einer Vererbung*). It lies outside git.
        **A counter-table from it would not be a second architecture but the same line
        counted twice** — exactly the error class this folder booked on 2026-08-15.
        *The number would not be imprecise but wrong, and in the flattering
        direction: it would evidence transferability where only a copy stands.*
      * **What it would take:** an aarch64 kernel with a lineage **of its own**, or the
        honest version of the sentence — *"measured for x86; for aarch64 no number stands,
        and the available tree cannot supply one."*

- [ ] **The line shares of the GABBRO side — that is what still closes the metric.**
      B3 has been run and did **not** supply them; it measures the code form, the formula
      weights proof obligations (`dokumente/MESSUNGEN.md`, *EINSETZUNG*). What is missing: what a
      proof **in Gabbro** costs for the same 73 obligations. **That is no longer a measurement on
      Caprock** — for it the obligations have to be written in Gabbro. Until then
      ~~the metric stands at `≥ 1,90`~~ **die Kennzahl lautet seit dem 2026-08-19 `unbekannt,
      > 0,5`**, und **jede kleinere Zahl im Umlauf verwechselt die zwei Seiten**. *Und der
      Posten hat seither einen genaueren Namen: nicht „ein Beweis in Gabbro", sondern **P6** --
      die ERZEUGTE Verfeinerungspflicht. Vorher gibt es nichts zu beweisen, das nicht erfunden
      waere.*

---
### From the inversion of the question ([`dokumente/SPRACHE.md`](dokumente/SPRACHE.md))

- [ ] **The eighteen conversions are claims about lowerability, not evidence.** Each needs
      its C lowering written down — before the canonisation in [`dokumente/SYNTAX.md`](dokumente/SYNTAX.md).
- [ ] **`retry` with `bounded`/`progress`/`on_exceeded` is the replacement for "unbounded waiting".**
      Open: is one number enough, or does it need two bounds (attempts **and** ticks)?
- [ ] **No. 14 demands a `publishes` clause at 2 231 sites.** Whether that carries is decided by no
      paper exercise — that is the largest single item of the whole conversion.
- [ ] **`breaking I { … }` legalises an invariant violation.** The price is visibility
      instead of hiding; whether that is enough is undecided.
### Paper steps — not a line of code. Every item can kill the thesis

> **Renamed 2026-08-14.** This heading was called "P0", the next one "P1" — and
> [`dokumente/SPRACHE.md`](dokumente/SPRACHE.md) §6 assigns P0…P7 to the **checker plan**, where P1 is the
> grammar unification and not `check`. **Two label systems with the same names
> in the same file**; the same error class as the G collision further up.

- [ ] **`touches` is too coarse** — it needs a form for "changes the set only through
      consumption". Without it the ordering hangs on a promise instead of on a condition.
### Performance — two items, both before the first benchmark

- [ ] **Amortise the bound check:** `bounded N ops` does not have to be checked per
      iteration. `progress` carries the termination, the bound is a **watchdog** — a check
      **every 2^k iterations** lowers the cost to ~1/2^k, the promise becomes "breaks after at most
      N + 2^k". **Decide before the first benchmark**, otherwise it measures a construct nobody
      would build that way.
- [ ] **The tension lowering-flat against fast is unpriced.** The folder has paid it only on the
      correctness side; on the performance side the lowering is a **bet on the
      C compiler**, and it hangs on the unwritten form table.

---

# MEASUREMENTS — need a run

- [ ] **Acceptance of the third addition** (§6): catalogue against count — **every counted instruction
      has an axiom or a construct, every line an instruction**; the mode ladder as a speech test
      (a swapped `write_cr0(PG)` **must** break); the precomputed boot tables byte-identical
      against what today's trampoline builds at run time.
- [ ] **P5–P7** from [`dokumente/SPRACHE.md`](dokumente/SPRACHE.md) §6 — **the form table with
      witness pairs, the C emission, one Caprock module end-to-end.**
      **Every stage consumes the result of the previous one, like a `Duty`.**
      *(P4 has fallen: M2 stands as `L101`–`L105`, the pairing pass as `V001`–`V004`.
      What stays open at P4 is the **template** for M2 — it stands in the template list,
      not here.)*
### From the criterion ([`dokumente/BEWEIS.md`](dokumente/BEWEIS.md))



- [ ] **Argue the dividing line at a borderline case.** "Names only the machine" is sharp enough for
      today's cases — the first disputed case belongs in `dokumente/BEWEIS.md`, not in a footnote.
### Induction — entered, and the one number is missing


- [ ] **The generated scheme has to go into Isabelle once** — it is a template in the sense of L3 and
      thereby the item that **shrinks** the trust base.
- [ ] **Well-foundedness hangs on an invariant one wants to prove.** The declaration has to
      name which — and the measure (number of descendants) is a premise, not a result.
### To be re-checked, because quoted from memory

- [ ] **The freedom of the name "Gabbro"** across package registries, GitHub and language lists — together with what
      was found. "I found nothing" is a null finding without a size.

---
### `check` without a language

- [ ] **`check` as a Rust macro library**, retroactively against the 33 measurement-discipline traps, each with a
      mutation. Gate: **≥ 5 caught**. Useful even if Gabbro never comes into being.

---

---

# BUILDING — needs code

### «NL» — der Weg zu „nur noch eigene Logik" ([`dokumente/PLAN.md`](dokumente/PLAN.md)) — **PUNKT 1**

- [ ] **NL.1 -- `ops` braucht eine WORTMENGE, und das ist der groesste Posten** *(2026-08-19)*.
      `table.ops.erhaltung` traegt die K-Spalte -- **28 von 73 Pflichten** -- und ist
      `entworfen`, weil `opdecl` beliebige Bezeichner nimmt. **Der zweite Ausweg (der Nutzer
      schreibt die Wirkung) ist keiner: dann faellt Schnitt (c).** *Welche Operationen die
      Menge fuehrt, ist eine Messung am ZWEITEN Korpus -- der erste hat null `ops`-Stellen.*
      **Gemessen 2026-08-19** (`kernel/` + `mm/`, 659 Dateien): entfernen 479 · einfuegen 448
      · anlegen 408 · umhaengen 127 · ersetzen 11. **Einfuegen und Entfernen tragen 63 % --
      und `umhaengen` steht an 127 Stellen, also genau die Operation, fuer die
      `Table_Ops_Erhaltung.thy` das GEGENBEISPIEL fuehrt.** *Der Korpus braucht die Operation,
      von der der Beweis sagt, dass sie bricht.* Die Entscheidung steht damit mit Zahlen da.
- [ ] **NL.2 -- ZEHN Zusagen ohne Leser** *(13 am 2026-08-19, drei gefallen: `M116` fuer
      `mut`, `E011` fuer `touches`, `S005` fuer `abstieg`)*. Als naechste `ghost` (ein
      Geisttyp darf im erzeugten C nicht vorkommen), `pro_kern` (`per cpu N` gegen NCORES),
      `offset_into` (die Schranke wird nicht geprueft). Dann `obermenge`, `bedingung`,
      `embeds`, `mirrors`, `verlaesst`, `gates`, `counterprobe`. *Jede einzeln, jede mit
      Giftprobe, jede mit Korpusmessung VORHER.*
- [ ] **`S005` prueft die NOTWENDIGE Bedingung des Abstiegs, nicht die hinreichende**
      *(2026-08-19)*. Dass das Mass sich bewegen KANN, haelt der Pass; DASS es faellt, bleibt
      `consuming.ordnung`. **Der Schritt dazwischen waere die Richtung:** bei `by decreasing
      (lenof(s.worte) - i)` muesste `i` WACHSEN, damit das Mass faellt -- heute genuegt, dass
      der Rumpf `i` ueberhaupt schreibt. *Ein `i -= 1` kaeme durch.*
- [ ] **NL.3 -- `ensures` ueber WELTZUSTAND, die haeufigere Form** *(2026-08-19)*. Numerisch
      und relational tragen seit heute; `ensures mmu_an_zahl == 1` steht siebenmal in
      `beispiele/22` und traegt nicht. **Sie kollidiert mit U4/U5** -- ein Aufruf toetet jeden
      nichtlokalen Fakt -- und waere die erste Ausnahme davon. *Aufschreiben, bevor gebaut
      wird, wie bei «H2.1».*

### «H2» — AUSGEFUEHRT 2026-08-19, `H = 17 -> 15`

**H2.1** (Zaehlerregel, `domaene.rs`, `elems of <Feld>`, Gift 114/115) und **H2.2** (die alte
Begruendung beschrieb den falschen Zweig) sind gebaut; beide `narrow` sind fort, beide
`PFLICHTEN.md`-Zeilen zu. **Alle acht verbleibenden verankerten Pflichten sind
NOTATIONSLUECKEN -- nicht eine ist ein Handbeweis.** Was daraus offen bleibt:

- [ ] **Der zweite Korpus hat keine `H`-Messung, und ohne sie ist `H = 15` Falle 80**
      *(2026-08-19)*. Ueber den zehn Fragmenten beweist kein Mensch mehr Klempnerei von Hand
      -- **aber die zehn sind selbst gewaehlt.** Fuenf Linux-Fragmente stehen daneben, und
      ueber ihnen ist nichts gezaehlt. *Das ist der eine Posten, der zwischen „Boden der
      Messung" und „Boden der Sprache" steht.*
- [ ] **`FRAGMENTE.md` benutzte `Stack`, ohne ihn je zu deklarieren** *(gefunden 2026-08-19)*.
      Nachgetragen wie `STACK_MAX` am 2026-08-15, mit abgeleiteter Wortzahl. **Wie viele
      weitere Traeger benutzt der Ausschnitt, ohne sie zu nennen?** Jeder davon macht eine
      Pflicht unsichtbar -- die zweite fiel hier sofort auf (`s.len - frei`, geschlossen mit
      der relationalen Nachbedingung). *Eine Zaehlung, und sie ist klein.*

- [ ] **Die Axiomschicht schuldet einen Satz ueber den SPERRABDRUCK** *(benannt 2026-08-19
      von `Gruppe_Erhaltung.thy`)*. Das Locale `zug` nimmt `voll i` als *„der Abdruck ist
      gehalten"* und schliesst daraus, dass niemand hinsieht. **Dass ein gehaltener Abdruck
      einen fremden Kern wirklich fernhaelt, ist eine Aussage ueber das SPEICHERMODELL** und
      faellt nicht in diesen Satz -- dieselbe Stelle, an der `paarung` ihre
      `release`/`acquire`-Sichtbarkeit schuldet. *Vorher war die Praemisse unsichtbar; jetzt
      steht sie in der Zahl.*
- [ ] **`group` steht an EINER Korpusstelle** *(2026-08-19)*. `beispiele/17` ist die einzige;
      die vier Verbindungsinvarianten des Sweeps vom 2026-08-16 (V1-V4) sind gemessen, aber
      nicht geschrieben. **Zwei bewiesene Schablonen ueber einem Konstrukt mit einer
      Fundstelle** -- das ist der Grund, warum die Amortisationszahl heute zweimal gestiegen
      ist. *Solange V1-V4 nicht als `group` dastehen, misst die Zahl den Beweisvorlauf und
      nicht die Amortisation.*

- [ ] **Die HAEUFIGERE Haelfte von Punkt 4 fehlt: `ensures` ueber WELTZUSTAND**
      *(gemessen 2026-08-19)*. Von 28 fremden Deklarationen liefern nur **4** eine Ganzzahl;
      die Mehrheit spricht ueber Plaetze (`ensures mmu_an_zahl == 1`, siebenmal in
      `beispiele/22`). **Die Wiederherstellung einer Tatsache ueber einen globalen Platz nach
      einem Ruf kollidiert mit U4/U5** -- *ein Aufruf toetet jeden nichtlokalen Fakt*, und
      `mutiere-pruefer.py` fuehrt dafuer eine eigene Mutation. *Sie waere die erste Ausnahme
      von dieser Regel und gehoert gemessen, bevor sie gebaut wird.*
- [ ] **Die STARKE Fassung von `M115` braucht eine Entscheidungsprozedur** *(2026-08-19)*.
      Heute faellt nur, was der Bereich des Arguments AUSSCHLIESST; dass der Rufer die
      Vorbedingung HERSTELLT, prueft niemand. **M1 stellt Fakten her und entscheidet keine
      Praedikate** -- die starke Fassung ist ein eigenes Stueck Maschinerie und zerlegte
      ausserdem den Korpus. *Vorher zaehlen, an wie vielen Rufstellen eine Vorbedingung heute
      unbewiesen bleibt.*
- [ ] **Gabbro unterdrueckt FOLGEFEHLER nicht, und niemand hat das je aufgeschrieben**
      *(gefunden 2026-08-19 an `M112`)*. Der Ausschnitt `SYNTAX.md`:533 scheitert am Parser
      («B8»: ein Ruf in einem `place`), damit wird seine `spec fn` nie erklaert, und
      `maintains` meldet einen Namen, den es sehr wohl gibt. **Nach einem `P001` laufen alle
      Paesse weiter, und was sie melden, kann Rauschen sein.** *Entweder die Paesse
      anhalten, oder die Entscheidung aufschreiben -- heute steht sie nur in einer
      Testliste.*

- [ ] **Drei der sieben haengenden Praemissen brauchen keine Pruefarbeit, sondern eine
      SPRACHFORM** *(gemessen 2026-08-19 beim Fuellen von `braeuchte`)*. `ops` braucht eine
      Wortmenge, `by consuming` einen genannten Zeitpunkt fuer die Leerheit,
      `accumulates.monoid` die Ausfuehrungskontexte. **Die haengenden Praemissen sind
      mehrheitlich keine vergessene Pruefarbeit, sondern nicht getroffene Entscheidungen** --
      und das aendert, wer sie schliessen kann.
- [ ] **`N009` sieht nur ZAHLLITERALE** *(2026-08-19)*. Ein berechneter Registerversatz
      (`CAP.FRO * 16`) bleibt stumm, und `bank`-Register werden nicht gegen die Hauptebene
      gehalten -- die Basis waere zu raten. **W10: der Bericht verpflichtet, er spricht
      nicht frei.** *Was fehlt, ist die Zaehlung, an wie vielen Korpusstellen ein Versatz
      NICHT literal ist.*
- [ ] **Der Beweis, dass `bitlage::lies` die Lagen trennt, hat kein Register**
      *(2026-08-19)*. Die Praemisse `trennt f g` von `format.roundtrip` ist durch die
      KONSTRUKTION erfuellt -- sequentielle Byte-Lagen, monoton wachsender Versatz. **Das ist
      eine Aussage ueber den PRUEFER, und fuer die gibt es kein Register**; dieselbe Lage wie
      `Intervall_Aussen.thy`. *Heute steht der Grund in `durch:` als Prosa.*

- [ ] **`ops` hat keine WORTMENGE, und das ist der Rest von Punkt 2** *(gemessen 2026-08-19)*.
      `opdecl = "ops" identlist ";"` nimmt beliebige Bezeichner; `insert, remove, relabel,
      delete_leaf` sind in `SPRACHE.md` 10.2 ein BEISPIEL, keine Menge. **Ein Erzeuger kann
      aus einem Namen keine Wirkung ableiten.** Zwei Auswege: eine geschlossene Wortmenge mit
      je definierter Wirkung (wie `merge add|max|min`), oder der Nutzer schreibt die Wirkung
      und der Erzeuger prueft sie -- *dann ist es aber keine ERZEUGTE Mutation mehr, und
      Zuschnitt (c) faellt.* **Vorher zaehlen, welche Operationen der zweite Korpus
      braucht** -- der erste hat null.
- [ ] **`einfuegen` braucht ZWEI Bedingungen, und keine hat einen Pass** *(2026-08-19,
      `Table_Ops_Erhaltung.thy`)*. Der Platz ist FRISCH, der Elter ERREICHBAR. Beim Loeschen
      traegt das `requires ist_blatt(c, s)` des Rufers die Bedingung -- beim Einfuegen gibt
      es keine solche Zeile. *Ein Erzeuger, der `einfuegen` ausliefert, muesste sie
      herstellen oder verlangen.*

- [ ] **P6 ist EROEFFNET, nicht erledigt** *(2026-08-19)*. `maintains` hat einen Leser
      (`M112`-`M114`), und `gabbro pflichten` zaehlt die erzeugten Pflichten: **17 ueber 31
      Beispiele, davon 7 fremd.** *Was fehlt, ist die zweite Haelfte:* die Pflicht muss in
      einer Form dastehen, die ein Beweiser lesen kann -- heute ist sie eine Zeile im
      Bericht. **Und die K/A/W-Einordnung bleibt Handarbeit**, ausdruecklich: ein Werkzeug,
      das sie raet, waere die stille Antwort, gegen die dieser Ordner sonst schreibt.
- [ ] **`maintains` nennt UNQUALIFIZIERT** *(2026-08-19)*. `M112` sammelt `spec fn` und
      Invarianten ueber alle Module flach ein, weil der Korpus unqualifiziert schreibt.
      **Zwei gleichnamige Invarianten in zwei Modulen sind damit ununterscheidbar** --
      dieselbe Bauart wie `typ_von_ort` vor dem 2026-08-17, nur noch nicht ausgeloest.
      *Eine Regel, die mehr verlangt als der Korpus schreibt, zerlegt ihn; die Verschaerfung
      braucht also zuerst eine Messung, wie viele Stellen qualifizieren muessten.*

- [ ] **P6 ist die Grundlage der Kennzahl, nicht ihr Zubehoer** *(geschaerft 2026-08-19)*.
      Die Zahl ist zurueckgezogen (`unbekannt, > 0,5`), weil `w` an VERUS-Zeilen gemessen war.
      Ein Isabelle-verankertes `w` braucht **eine W-Pflicht, die ENTSTANDEN ist** -- und
      erzeugt wird sie von P6, der Verfeinerungspflicht aus `spec fn`/`impl fn`. **Keine
      Sprachsemantik noetig:** die Absenkung nach C ist die Bedeutung, und beide Seiten stehen
      in einer Sprache. *Solange P6 fehlt, muesste man die Pflicht erfinden, die man dann
      misst -- genau die Bewegung, gegen die R7 und W3 stehen.*
- [ ] **Die Zeilenanteile der eigenen zehn Theorien sind gezaehlt, aber nicht KLASSIFIZIERT**
      *(2026-08-19)*. 1 639 Zeilen, 48 Saetze, 86 Beweisschritte -- was davon ist Prosa, was
      Modell, was Beweis? **Fuer die Amortisationszahl 10,4 ist es gleich, fuer jeden Vergleich
      mit einer Verus- oder seL4-Zahl nicht.** *Eine Isar-Datei dieses Ordners ist zu einem
      grossen Teil Fliesstext, und wer sie gegen eine Verus-Zeilenzahl haelt, vergleicht zwei
      verschiedene Dinge -- dieselbe Verwechslung eine Ebene tiefer.*

- [ ] **`C001` sagt „keine Absenkung" und wird fuer FALSCHES mitbenutzt** *(gefunden
      2026-08-19 an «B24»)*. Eine Bitlage jenseits der Wortbreite ist kein *„das koennen wir
      noch nicht"*, sondern ein *„das ist falsch"* -- bis heute trug beides dieselbe Kennung.
      Zwei der drei Faelle sind mit `N007`/`N008` in den Pruefer gezogen; **die Luecke im Wort
      bleibt bewusst `C001`**, weil erst die Absenkung eine bestimmte Wortgrenze braucht.
      *Was offen bleibt: wie viele der uebrigen `C001`-Stellen dieselbe Verwechslung tragen.*
- [ ] **`bool @N` in einem `format` ist ungeprueft, und zwar benannt** *(2026-08-19)*.
      `bitlage.rs` bucht es als `Unklar`: die Wortbreite steht ohne ganzzahligen Traeger nicht
      fest -- die 63 in `nx : bool @63` kommt aus dem Wort der Gruppe, nicht aus `bool`.
      **W10: eine untere Schranke weist weder zurueck noch bestaetigt sie.** *`format Pte`
      lebt genau davon, und ein Fehlalarm dort waere teurer als das Schweigen.*
- [ ] **Die Kachelungsluecke (`N009`) ist NICHT gebaut, und der Grund ist der Korpus**
      *(gemessen 2026-08-19)*. `format Elf64Ph` laesst mit `p_flags : u32 @[2:0]`
      neunundzwanzig Bits unbenannt; die Regel im Pruefer haette den eigenen Korpus zerlegt.
      **Der Erzeuger sagt sie ab, und dort ist sie richtig** -- eine Luecke macht das Wort
      unentscheidbar, sobald jemand Bytes anfassen will. *Offen ist, ob `Elf64Ph` seine
      uebrigen 29 Bits `reserved` nennen sollte -- dann faellt die Ausnahme mit.*

- [ ] **Ein Waechter, der jeden Pass-Walker gegen die blockfuehrenden Anweisungsarten haelt**
      *(fuenfte Instanz am 2026-08-19)*. Vier blinde Walker an einem Tag (`H007` in
      `observes`, der RCU-Walker in Schleifen, `typ_von_ort` gegen `index_pruefen`, und der
      `retry`-Rumpf), und jetzt die fuenfte: **`sammle_namen_pred` betrat den `Ort`, aber
      nicht seinen Index** -- `ensures … W.slots[tippfehler]` ging mit 0 Fehlern durch.
      *Jedes Mal wurde der Rumpf betreten und ein Zweig davon nicht.* **Fuenf Funde derselben
      Bauart sind kein Zufall, sondern ein fehlendes Werkzeug** -- dasselbe Argument wie bei
      `pruefe-klauseln.py` und `pruefe-widerruf.py`, und beide haben beim ersten Lauf
      geliefert.
- [ ] **`pruefe-widerruf.py` ist ein GEDAECHTNIS und kein URTEIL** *(gebaut 2026-08-19)*.
      Sieben Widerrufe gebucht, acht Fundstellen geschlossen. **Er findet nur, was jemand als
      widerrufen aufgeschrieben hat** -- und dass zwei der acht in der SPEZIFIKATION standen
      (`SYNTAX.md`:165, `SPRACHE.md`:614) und von Hand nicht gefunden wurden, sagt, dass es
      weitere gibt. *Was fehlt, ist die andere Richtung: eine Liste dessen, was gebaut wurde,
      gegen die Dokumente gehalten -- statt eine Liste dessen, was widerrufen wurde.*
- [ ] **`Self` in einem `ensures` ist ungemessen** *(2026-08-19)*. `sammle_namen_pred` bindet
      seit heute Quantorbinder und steigt in Indizes ab; **`Self` kennt es nicht.** Im Korpus
      steht `Self` nur in `invariant`, wo dieser Pass nicht laeuft -- *also ist es heute kein
      Fehlalarm und morgen vielleicht einer.* Eine Zeile, sobald ein `ensures` es benutzt.

- [ ] **`atomic` ist ein ITEM, kein Slotfeld** *(gemessen 2026-08-18 an K2-F2)*. Das Original
      benutzt `atomic_long_inc_not_zero` -- **ein atomares RMW ist seine eigene
      Wechselseitigkeit**, und ein RCU-Leser darf damit einen Zaehler erhoehen, ohne die
      Schreibersperre zu nehmen. In Gabbro ist ein Zaehler IM Objekt nicht atomar
      deklarierbar, also verlangt `H010` dort eine Sperre, die das Original nicht braucht.
      *Die Nachbildung ist damit strenger als das Vorbild -- und das ist ein Befund ueber die
      Sprache, nicht ueber den Prueferlauf.*
- [ ] **Die GNADENFRIST ist eine ANNAHME, keine Pruefung -- und hat noch keinen Ort**
      *(2026-08-18)*. `H011`/`H012` halten die zwei pruefbaren Haelften (nicht im eigenen
      Lesebereich, nicht ohne Schreibersperre). Dass kein Leser das alte Objekt mehr sieht,
      stellt kein statischer Pass her. **Sie gehoert dorthin, wo `progress` steht** -- und der
      Pruefer verlangt sie noch nicht: ein `rcu … reclaims` ohne eine benannte
      Gnadenfristannahme geht heute durch. *Dieselbe Regel wie `S003`, an einem anderen
      Konstrukt.*
- [ ] **`observes` senkt nicht ab** *(2026-08-18)*. Der Erzeuger weigert sich benannt. Die
      Absenkung waere zwei fremde Ruempfe wie bei `lock` (`_beobachten`/`_freigeben`), und die
      Zeugniszeile muesste sagen, dass diese Einheit eine RCU-Domaene liest -- **eine Aussage
      ueber die Rueckgewinnung, nicht ueber Zahlen.**
- [ ] **«K2» ist abgeschlossen -- und fuenf Fragmente sind keine Aussage ueber 64 000
      Dateien** *(2026-08-18)*. Vier von fuenf tragen ohne Rest; die Nachbildungen sind keine
      Uebersetzungen, denn die Strukturen sind erfunden, wo sie nicht mitgeschnitten waren.
      **Gemessen ist die FORM, nicht der Rumpf.** Wer die Zahl als Deckung liest, liest sie
      falsch -- *dieselbe Warnung, die schon bei den elf Uebersetzungseinheiten steht.*
- [ ] **Die Zaehlerueberlaufklasse gehoert in die Messungen, nicht nur in ein Fragment**
      *(2026-08-18)*. `M101` fand in K2-F2 einen Ueberlauf, den das Original nicht prueft --
      `atomic_long_inc_not_zero` schuetzt gegen NULL, nicht gegen die obere Schranke. **Wie
      viele der 637 `atomic_*()`-Stellen des zweiten Korpus sind Zaehler ohne obere
      Schranke?** Das ist eine Zaehlung, und sie waere die erste Zahl dieses Ordners, die
      einen FREMDEN Fehler misst statt eine eigene Deckung.

- [ ] **`D004` hat auf diesem Korpus NULL Biss** *(gemessen 2026-08-18)*. Alle zwoelf
      `opaque`-Deklarationen der Beispiele erklaeren und benutzen im **selben Modul**, also
      greift die Modulgrenze zu Recht nicht. **Dieselbe Lage wie `E010`**, und derselbe
      Beleg: die Regel ist an Giftproben gemessen, nicht am Korpus. *Eine Eigenschaft des
      Korpus, nicht der Regel -- und ein weiteres Argument fuer den zweiten.*

- [ ] **Die zwei Gleitkommasonden gibt es als NAMEN, nicht als Programm**
      *(2026-08-18)*. `sonde_mxcsr_rne` und `sonde_keine_ueberbreite` stehen im Manifest, und
      damit ist die Annahme falsifizierbar ERKLAERT. **Geschrieben ist keine von beiden.**
      *Das Manifest sagt selbst, dass es nur die Sonde nennt und nicht ihren Lauf* -- aber ein
      Name ohne Programm ist die schwaechste Form von falsifizierbar, die es gibt.
- [ ] **`F003` (Rundungsmodus im Typ) ist heute UNERREICHBAR, und das ist die Antwort**
      *(2026-08-18)*. Die Absage soll einen anderen Modus als RNE treffen -- **es gibt keine
      Form, einen zu schreiben.** Sie jetzt zu bauen hiesse, drei oder vier Woerter in den
      Wortschatz zu nehmen, deren einziger Zweck es waere, abgelehnt zu werden: eine
      Spracherweiterung ohne gemessenen Bedarf (W3). *Die Entscheidung `f64<RNE>` bleibt
      gebucht; die Absage entsteht mit ihr, nicht davor.*
- [ ] **`F003` (Rundungsmodus im Typ) und `F006` (`long double`/`f16`)** *(2026-08-18)*. Die
      beiden letzten Absagen der Familie. `f64<RNE>` waere die vierte Instanz eines
      vorhandenen Musters (`ptr<…>`, `atomic … seq`, `format … endian`); `long double` wird
      benannt abgelehnt, und der Korpus begruendet es (FF2: eine Sprosse von sieben).

- [ ] **Der PRUEFER hat kein Register** *(2026-08-18)*. `Intervall_Aussen.thy` ist die erste
      Theorie dieses Ordners, die von M1 handelt statt vom Erzeuger -- und sie steht in
      **keinem** Schablonenregister, weil das Register Erzeugerpflichten fuehrt
      (*„eine Beweispflicht, die der Erzeuger schuldet"*). **Damit gibt es jetzt zwei
      Vertrauensflaechen und nur eine Buchung.** Die zweite wird bisher nur von
      `mutiere-pruefer.py` gemessen -- Mutationen, nicht Saetze. *Ein zweites Register waere
      die naheliegende Antwort; ob es eines sein soll, ist eine Entscheidung.*
- [ ] **Produkt, Quotient und die Null haben ihren Satz noch nicht**
      *(2026-08-18)*. `Intervall_Aussen.thy` deckt die SUMME. Fuer Produkt und Quotient
      rechnet der Pruefer ueber die vier Ecken; dass das Minimum der vier die untere Schranke
      ist, braucht Monotonie in beiden Argumenten und eine Fallunterscheidung nach Vorzeichen.
      Die Null ist ein eigener Satz: `-0.0` liegt in `0.0 .. 1.0`, und `1.0 / x` gibt `-inf`.

### «F» — f32 und f64, geplant 2026-08-18 (`PLAN.md`, „«F» — f32 und f64, vollstaendig")

**Der Beschluss weicht von W3 ab und sagt es:** der Bedarf ist gemessen null, die Entscheidung
zu bauen ist die des Ordners. **Ersatz fuer die Bedarfszaehlung ist der Korpus, und er kommt
zuerst** -- sonst entwirft man fuer eine vorgestellte Verwendung.

- [ ] **F0: drei bis fuenf echte Gleitkommafragmente**, jedes mit seinem Befund. *Der Bedarf
      darf entschieden werden; er darf nicht erfunden werden.*
- [ ] **F1: sieben Entscheidungen vor der Grammatik.** Die tragende ist die dritte: **die
      Negation liefert ihre Tatsache GENAU DANN, wenn beide Operanden als Nicht-NaN bekannt
      sind.** Damit ist die Verengungsmaschinerie bedingt statt abgeschaltet -- *ohne diese
      Entscheidung ist Gleitkomma in Gabbro unbrauchbar, mit ihr gewoehnlich.*
- [ ] **F3: die sechzehn gemessenen Stellen** (`umgebung` 6, `m1` 6, `typen` 4) entscheiden je,
      was sie mit `Typ::Gleitkomma` tun. **Keine darf stillschweigend durchfallen.**
- [ ] **F5/F6: die Einheit rechnet mit Gleitkomma -- das gehoert ins ZEUGNIS.** Es aendert
      Aufrufkonvention und Kontextwechsel; fuer einen Kernel ist es eine Aussage ueber
      Preemption, nicht ueber Zahlen. Dazu SSE2 als Annahme mit Falsifikator.
- [ ] **P-F1 ist das wichtigste Tor: der GANZZAHLPFAD bleibt bitgleich**, nachgewiesen von
      einer Differenzeinheit statt von einem Eindruck. *Wer dort etwas verschiebt, beschaedigt
      eine Sprache mit gemessenem Bedarf zugunsten einer mit entschiedenem.*

- [ ] **`backed` steht im Pruefer und noch nicht im ZEUGNIS** *(2026-08-18)*. Eine Einheit,
      die Adressraum von Speicher trennt, sagt damit etwas ueber ihren Speicherbedarf --
      **und das Zeugnis nennt es nicht.** Dieselbe Klasse wie die Gleitkommazeile: der Leser
      muss es sehen, ohne den Quelltext zu lesen. *Dazu die Frage, ob der Erzeuger die
      Reserve als Feld anlegen soll oder ob sie eine Aussage an den Binder ist.*
- [ ] **Wer die Hinterlegung ERHOEHT, verspricht die Seiten** *(2026-08-18)*. `M108` haelt
      jeden Zugriff unter `backed`; dass die Seiten dahinter wirklich eingehaengt sind, ist
      eine Aussage ueber den Verwalter und steht in keiner Annahme. **Der Kernel ist selbst
      die Instanz, die sie einhaengt** -- die Zusage gehoert damit in die Axiomschicht, mit
      Sonde, oder an eine `ensures`-Klausel der einhaengenden Funktion.
- [ ] **`i < N` ist nicht `i ist hinterlegt`** *(2026-08-18)*. Eine `table count 1000000000`
      geht sauber durch und senkt zu einem Feld von knapp 30 GiB ab. Was Gabbro NICHT sagen
      kann: dass nur die ersten `k` Plaetze hinterlegt sind. Ein Zugriff auf einen nicht
      hinterlegten Platz ist typkorrekt und trotzdem ein Fehlzugriff -- **und in einem Kernel
      ist das besonders scharf, weil er selbst die Instanz ist, die Seiten hinterlegt.** Das
      ist der Bedarfsbeleg fuer die wertgetragene Schranke.

- [ ] **`entrust` senkt nicht ab** *(2026-08-18)*. Wort, Item, Zeugniszeile und drei Absagen
      stehen (`N004`/`N005`/`N006`); der Erzeuger weigert sich benannt (`C001`). Die
      Uebergabe ist ein Registervertrag plus Sprung -- **dieselbe Baustelle wie `entry`**, und
      die ist gemessen leer. *Wer `entrust` absenkt, senkt den Eintrittsvertrag zum ersten
      Mal ab.*
- [ ] **Bindet `stack` an eine Deklaration?** *(offen seit 2026-08-18)*. `entrust … at NAME`
      wird gehalten (`N006`), der Stapel nicht. Ein Gaststapel ist womoeglich ein
      Bindersymbol und keine Gabbro-Deklaration -- **die Frage ist eine Entscheidung, keine
      Bauarbeit**, und bis sie faellt, steht `stapel` als FREMD gebucht.

### Deklariert, exportiert, nie gelesen — die Klasse hat einen Namen und einen Waechter

**Gemessen 2026-08-18** mit `./pruefe-klauseln.py`: 131 Feldnamen aus `ast.rs` gegen 23
Leserdateien. **48 Felder gebucht** -- 21 nur getragen (nur `emit.rs`/`zeugnis.rs`/`cli`),
27 ungelesen. Nach Urteil: **17 ZUSAGE**, 6 ABSENKUNG, 25 TOT. *Die Stufe ist gemessen, die
Klasse ist ein Urteil, und das Werkzeug sagt beides getrennt an.*

Der Waechter klemmt in beide Richtungen und weist seine Messfaehigkeit nach (R14: `span` muss
als gelesen herauskommen, `section` nicht). **Die Liste unten ist eine UNTERE Schranke** --
gemessen wird je Name, nicht je Struktur (W10).

- [ ] **`leaves` und der Abstieg des `traverse` haben weiter keinen Leser**
      *(gemessen 2026-08-18)*. `progress` hat seit heute einen (`S003`/`S004`); die beiden
      anderen Schleifenzusagen nicht. **`leaves` nennt, was den Ausgang verlaesst** -- das ist
      eine Linearitaetsaussage, und M2 liest sie nicht. **Der Abstieg traegt die Terminierung
      des `traverse`**, und `schleifen.rs` steigt in den Rumpf, ohne ihn anzusehen.
- [ ] **Zahn 3: acht Praemissen ohne Hersteller** *(gemessen 2026-08-18,
      `gabbro schablonen`)*. Neun bewiesene Schablonen, siebzehn Praemissen, **acht davon
      stellt niemand her**. Die schaerfste: `device.konstruktor` ist bewiesen, und sein
      Hauptsatz setzt `getrennt r s` voraus -- *wer das Zeugnis liest, schliesst aus
      „bewiesen" auf Ueberlappungsfreiheit.* **Das ist die Umkehrung der Klausel-Klasse und
      teurer als sie:** bei einer ungelesenen Klausel weiss niemand etwas, hier weiss man
      etwas Falsches. Die Marke steht auf 8 und geht nach unten.
- [ ] **`by consuming` liest kein Pass** *(gemessen 2026-08-18)*. Beide Praemissen von
      `consuming.ordnung` -- *die Mutation ist ein ENTFERNEN* und *die Auswahl ist MINIMAL* --
      sind damit nicht bloss unhergestellt, sondern unherstellbar, solange niemand das
      Konstrukt ansieht. **`Consuming.thy` K-2 fuehrt fuer die erste ein Gegenbeispiel**: EIN
      Umhaengen macht aus einem wohlfundierten Zustand eine Schlinge.
- [ ] **`versatz`: der bewiesene Satz hat keine Prueferzeile** *(gemessen 2026-08-18)*. Dass
      zwei `reg` einander nicht ueberlappen, ist der HAUPTSATZ von `Device_Konstruktor.thy`;
      gelesen wird das Feld nur von `emit.rs`. Gleich daneben: `schritt` -- **`stride 0` macht
      die Bank leer**, und die Theorie nennt das selbst eine Fundstelle. *Ein bewiesener Satz
      ohne Pass ist eine Zusage ueber ein Programm, das so nicht geprueft wird.*
- [ ] **`entry` gibt es nicht** *(gemessen 2026-08-18)*. Zwoelf Felder -- `regs_in`,
      `regs_out`, `preserves`, `clobbers`, `stack`, `vektor`, `via`, `ist`, `verschachtelt`,
      `dispatch`, `pro_kern` -- und **keine Datei ausserhalb des Lesers nennt `EntryDecl`**.
      Der Eintrittsvertrag ist geschriebene Grammatik und sonst nichts. *Das ist der Vertrag,
      den `entrust` erben soll* -- wer `entrust` baut, baut ihn zum ersten Mal.
- [ ] **`pub` ist wirkungslos** *(gemessen 2026-08-18)*. Kein Pass, kein Erzeuger liest
      `oeffentlich`. Sichtbarkeit wird weder geprueft noch abgesenkt -- **und eine
      Bibliotheks-ABI beginnt bei genau diesem Wort.**
- [ ] **`ensures`/`maintains` werden GEZAEHLT, nicht gelesen** *(gemessen 2026-08-18)*.
      `zeugnis.rs:370,391` ruft `.len()` und `.is_empty()`; kein Pass haelt sie gegen den
      Rumpf oder auch nur gegen die Wohlgeformtheit. **Die Bibliotheks-ABI soll sie tragen.**
- [ ] **`walk`, `check`, `invariant`: gelesen und sonst nirgends** *(gemessen 2026-08-18)*.
      der Abstieg eines `walk` (`from`/`down`/`leaf`), `floor`/`measures`/`gates`/
      `counterprobe`, `cost`/`runs` an der `invariant` -- dazu `by` (der Induktionshinweis
      verfaellt), `masked` an einer Sperre, `exhaustive`, der Ergebnistyp eines `axiom`,
      `scale`, die Formatversion und der Fehlername im `let … else`. *Kein Fehler, aber auch
      keine Sprache.*


### The emitter: every remaining fragment is blocked by a DECISION, not by work

**Measured 2026-08-17** by running `gabbro emit` over all ten blocks of
[`dokumente/FRAGMENTE.md`](dokumente/FRAGMENTE.md). Three units go through
(`beispiele/16`, F7, F8); the other seven are blocked by **seven constructs**, and **none of
the seven is a translation** — each needs a representation the folder has not chosen:

| Construct | blocks | the open question |
|---|---|---|
| **`traverse`** | F1 · F3 · F6 · F9 | each domain iterates differently: `descendants of` is a tree walk with removal, `queue`, `elems of`, `mappings of` from a `walk`. **`slots of … by unvisited` would be mechanical — none of the four uses it** |
| **`format`** | F2 · F9 · F10 | byte layout, declared endianness, the `where` validator, `offset_into Self`. *Not a C struct — padding and bitfield order are implementation-defined.* Accessors over a byte pointer is the candidate; the register already carries `format.roundtrip` |
| **`device`** | F2 · F4 · F9 | register accessors per `class r`/`w`/`w1c`, `mirrors`, `transition`, `bank … at expr` |
| **`retry`** | F4 · F10 | **`bounded N ops` is an OPERATION budget, not an iteration count.** The conversion is `N / cost-per-pass`, which the cost pass knows and the emitter does not — *and whether that conversion is the right reading is a decision, not arithmetic* |
| **`forever`** | F5 | the same, plus «B11»: it has no exit at all |
| **`walk`** | F9 | the four-level descent as an iteration |
| **`atomic` / `check`** | F6 | memory ordering; and `check` is a test harness, not a program |

- [ ] **Decide `retry`'s ops→iterations reading.** It is the cheapest of the seven and it
      unblocks two fragments. **The emitter refuses today rather than guess.**
- [ ] **Decide the `format` lowering.** It unblocks three, and the template obligation
      (`format.roundtrip`) is already entered — *no new ratchet slot needed.*

- [ ] **`cc -Wextra` finds a dead parameter and NO Gabbro pass does.** `FRAGMENTE.md` F8 takes
      `toeten(l, t, k)` and never reads `k` — the function resolves `t` instead. The C emitter
      silences it with `(void)k;` because *the user did not write the generated line*, and the
      finding belongs on the Gabbro level. **Today the checker has no diagnostic for an unread
      parameter**, and a C compiler found something ten passes did not. *That is a small pass
      and a real one.*

- [ ] **`publishes` at a DEVICE REGISTER — the one unbuilt item of the escalation of 2026-08-14.**
      Six of the seven are built, this one is not: `publishes` sits at `atomicdecl`, and the
      store the class *Publication* exists for is not an atomic at all — the virtio `avail`
      index is a **volatile store into a DMA region, to a device** («B19»,
      [`PFLICHTEN.md`](dokumente/PFLICHTEN.md) F4:796). **The class is carried for atomics and
      not for device registers**, and that is the second half of the same gap.
### The write-right line `by ops` — and the group proof sentence that precedes it

- [ ] **`by ops` is built — what stays open is ONE breakthrough: `breaking` on a
      `by ops` field.** The checker answers the question today *implicitly*: `kbedingung.rs`
      keeps the `breaking` sites per carrier, and `ist_geschlossen` demands that there be none
      — a `breaking` therefore **opens the carrier again**, instead of being a compile error.
      **That is a defensible answer and it stands stated nowhere.**
      *A property whose back door stands only in the code is a promise with a back door.*
      (Breakthrough 2 — the `dma` edge — is closed: `R001`, placement rule.)

- [ ] **The group proof sentence: the quantifier is open, the walkthrough is no longer.**
      *"B13 falls exactly when **every** connection invariant occurring in the tree has a
      group whose `ops` close it."* **What fell on 2026-08-16:** the
      paper walkthrough at the CapSpace/CDT pair (three answers), the sweep for the *other*
      invariants (**four found: V1–V4**), the grammar line (`group … over { … }`) and
      three of the four form obligations (`U003`/`U005`/`U006`/`U007`).
      **What is open is exactly two things:**
      * **The quantifier itself.** Four found means four found — W12. The sweep was a
        candidate list with search paths, not a mechanical walkthrough. What it systematically
        misses stands beside it: invariants without a common index field, say a
        sum condition over two tables.
      * **The `ops` over the group** — the recipient of the proof obligation from S16/S17.
        The checker today establishes the three conditions under which the question *"does the
        invariant hold?"* can be put at all; **it does not answer it.**

      *And a side finding of the sweep changes the expectation: **there is in the existing code NO
      double acquisition of the same lock class** (`system.rs`:15). The expected first test case for
      `locks ordered` thereby drops out; the one that was found is a different one — two classes with
      an ordering over two crates (V4).*

### Group `ops` + `by ops` — the design, BEFORE the first grammar line

Three commitments from the paper test, each re-checked. **They stand here because they change the
design, not because they decorate it.**

### E1 — The group's lock imprint is TWO-LEVEL, and that decides the grammar

Mutations take exclusive, the generated read operation (`lookup` class) takes **shared** —
that is measured in the tree: `33 CAPS.read()` against `44 CAPS.write()`. **The
construct therefore declares both modes PER `op`, not one per group.**

```
group Kappen over { Slots, Objekte } locks KAPPEN {
    op einfuegen  exclusive;
    op entfernen  exclusive;
    op nachschlagen shared;      -- der heisse Pfad
}
```

**Without this line `locks shared` would be built and the group could not use it** —
every generated operation would take exclusive, and the most-travelled path of the kernel would be
the slowest again. *A construct that makes another one unusable is a
design error, not a feature backlog.*

### E2 — The speech test has an obligatory direction, and it is a FILE

`refcount -= 1` with the null check **afterwards** must be unwritable under `by ops`. That
belongs as a **poison fragment in the test, not as a sentence in the text** — the folder's
rule that a promise needs a place at which it falls.

**CORRECTED.** I had written that the cut stands in two **independently
written** cores. That is wrong, and it is mechanically refuted:

```
$ git log --follow --name-status -- crates/caprock-cap/src/space.rs
R099   crates/sel4lake-cap/src/space.rs -> crates/caprock-cap/src/space.rs
```

**`R099` — a rename with 99 % similarity.** The same authorship line, the same file;
the copy under `ARMTest/` is an older snapshot of the same lineage, not a second
core. *Two sites from one inheritance are one site.*

The load-bearing justification is a different one — and it is measured, not inferred:

```
$ git log -L 1060,1075:crates/caprock-cap/src/space.rs --oneline
b026c83  A-3.3: Finalized leiht seinen Speicher …          2026-07-29
083a698  DMA: Teardown-Token (ext-37) -- Freigabe nur gegen Nachweis
0f246f9  ext-23 D0: DmaCap + DmaEnforcer …
9085cc0  ext-22 P4: generische Device-MMIO-Infrastruktur …
2d50d42  feat(cap/ipc): first-class Reply-Cap mit Revocation
2111f30  initial                                            2026-06-23
```

The line sequence has stood **since the original commit** (`2111f30`, there at line 341/342, literally
the same order) and has survived **five rebuilds of exactly this region** — among them
two that rewrote the release semantics themselves (`Reply-Cap mit Revocation`,
`DMA-Teardown-Token`). Over five weeks, over a package rename, over the
duplication of the file.

> **B29 is not a slip but an attractor.** Whoever writes the delete path writes
> it that way — even at the fifth rebuild, even after the trap had been paid for once. **That carries
> the speech-test obligation just as well as the refuted independence claim, and it
> is the true justification.**

The existing probe `beispiele/gift/37-b29-unter-ops.gab` covers `ops` on the **table**
(`D001`). The new one covers `by ops` on the **field** — `field : u16 by ops` — and must hit exactly
this line sequence.

### E3 — The Verus template: take over the clause structure, NOT the types

**Re-checked, and the mechanism is a different one than assumed — the warning becomes
stronger thereby, not weaker.**

`cap_space.rs:17` carries `pub refcount: nat`. At the delete path stands:

```
:791   let oldrc = cs.objects[o as int].refcount;
:792   assert(oldrc >= 1);                        // <- WIRD BEWIESEN, aus der Invariante
:793   let newrc: nat = (oldrc - 1) as nat;
```

**The model proves the precondition.** So it is not that the template answers the question
wrongly — it answers it rightly, **from the invariant**. What `nat`
takes away is something else: the type carries **no width**, so over the
*representation* no obligation ever arises. There is exactly **one** net, and it hangs on the invariant.

In Gabbro the same field carries `u32 in 0 ..= NSLOTS`. With that `-= 1` at 0 is an
**M1 error out of the TYPE** — without any reference to the invariant. **Two independent nets
instead of one**, and the second is exactly what fell in the speech test as `M104` next to `D001`.

> **The template takes over the CLAUSE STRUCTURE of the model (one `spec fn` over all
> clauses, preservation per operation), not its TYPES.**
>
> If it inherits `nat` along with it, the generated obligation list looks complete while the second
> net is missing — and worse: a generated C emission could
> omit the range check, *because the proof says it cannot go negative*. That is literally the
> booked error class: **releasing a claim about the model into the machine**
> (`dokumente/HISTORIE.md`, commit `5904cae`). Then the model would be a trojan gift.

**The checking line against it, mechanically:** no field generated by a template may carry a
type without a width. That is checkable at the template itself, not only at the artefact.
### From wave 4 (2026-08-16) — two conditions and one candidate

- [ ] **«B38» — the side condition on the named carrier.** *"The continuation re-checks
      **or** names what it carries instead"* is the right form — **but a carrier
      `masks IRQ` holds only if the entry context carries `nested masked`.** Without this
      coupling *"the masking carries me"* is the assurance from **R15**, which is satisfied
      as soon as the checker is silent. **Mechanically checkable** via `entrydecl`; to be built.
- [ ] **«B39» — the exception rule to the hardware axiom, and it is a CANDIDATE for a new
      word.** `A`/`D` are written by the MMU itself — the GDT lesson at the page machinery. **As soon as
      group `ops` reach the page machinery, the axiom collides with the
      write-right promise**: the K condition demands that ALL write sites be generated.
      Which fields of a `walk` declaration are **hardware-writable** belongs at the
      declaration (candidate line `hardware A, D;`), the way `reserved` belongs at a
      `format` field. *`R001` does not see the MMU today — it writes past every grammar,
      only in the `normal` space instead of in the `dma` space.*
      **It burdens the convergence bet: it would be column 1, not only column 2.**
### From the paper test of 2026-08-14 — one dead and two live candidates

> **One candidate died on 2026-08-14 and therefore stands here NO LONGER:**
> `locks ordered` — zero test cases in the tree. The obituary stands in
> [HISTORIE.md](dokumente/HISTORIE.md), the measurement in [MESSUNGEN.md](dokumente/MESSUNGEN.md).
> *This file carries exclusively what is open; a construct that has died is not a done
> item but a break with our own intention — and that belongs in the history.*



### The four items to the goal — plan with gates in [`dokumente/PLAN.md`](dokumente/PLAN.md) §A

**The goal is: Gabbro proves everything except functional correctness.** Read against this goal
the greater part of the 31 fragment findings falls away (`dokumente/PLAN.md` §A, resorting) —
what remains is four, and **one of them is not solved but grazed**.



- [ ] **A2 — RUN: dynamic calls are forbidden, `fnptr` needs no contract.**
      The two dynamically used traits have ONE implementation each. **New and
      undecided: 64 closures** (`dyn FnMut`/`Fn`) — Gabbro has none, and what becomes of them
      (embedding, pointer plus context, prohibition) stands nowhere.
- [ ] **A4 — `costs` at a RECURSIVE function stays an assumption.** A call counts
      the *declared* costs of the callee; at a cycle nobody recomputes. That is
      the intention of §7 — but it means that the termination hangs there on a promise.




- [ ] **A5 — acceptance:** fragments through the compiler afresh, the count over
      **Gabbro source text** instead of over Rust (**only then is the mark ≤ 24 really
      decidable** — see the report of the invalid measurement further below), and the four never
      written-out areas.
### From the counter-check (2026-08-14) — what is still open

- [ ] **THE CHEAP CLOSURE, and it belongs BEFORE the big sentences about "nothing else":
      `effects` checks writes and `locks`, but not reads and not calls.**
      Frame completeness holds today only for the **write half**; "only the entered
      logic is active" is thereby half a statement. The same checking mechanics, the other direction.
      The body reconciliation stands (E005/E006); two halves are missing:
      * **Reading** — `dokumente/FRAGMENTE.md` reads in every function places that no `reads` line
        names. Whether that is a finding about the fragments or the intended meaning of
        `effects`, **the folder decides, not the pass**. As long as that is open, it
        may not check what it does not know.
      * ~~**Call effects**~~ — **BUILT 2026-08-15 (`E008`).** An effect list
        includes those of the callees; `effects { pure }` means transitively pure. *What
        is NOT built and stands beside it: the mapping onto the ARGUMENTS — a
        `writes p.slots` of the callee is seen with ITS parameter name. Coarse in the
        safe direction (W9), and the mapping needs an alias analysis that does not
        exist.*
- [ ] **The mutation probe covers the checker today, not the emission.**
      `./mutiere-pruefer.py` damages one rule of the checker at a time and looks whether a
      probe falls — **24 of 24 caught** (2026-08-14). What is still missing is the same probe
      on the **annotation emission** (see *Checker and generator*): that is where the
      wished-for-form proof arises, and there is still nothing there to damage, because nothing
      is emitted yet.
      * **~~The mutations are written by hand~~ — RUN 2026-08-15, gate
        PASSED.** `erzeuge-mutationen.py` twists systematically: **7 of 39 caught
        (18 %)** against 38 of 38 of the hand mutations. The suspicion was right, and the
        actual finding is **where**: 6 of the 15 real gaps in `typen.rs`, 5 in
        `umgebung.rs`. *The checker is tight where it PRODUCES REFUSALS, and thin where it
        COMPUTES.* What stays open from it: **value tables for the range arithmetic** —
        example files hit classes, not boundaries.




- [ ] **The parser is laxer than the EBNF at THREE places** *(was: six; corrected and
      checked 2026-08-16 — one `.gab` probe run per place)*:
      * Vocabulary words as names after `::`, in `reaches … via` and in `chain(a,b)` — three
        places that the file's own header does **not** exempt.
      **Closed are:** `pub` at 13 item kinds (`P034`), `pub const` in the `table` body (was
      too strict), `type T = { };` as an empty sum type (`P035`, poison 61), and
      the comma rule — `entrydecl`, `slotdecl` and `reg … fields` carried **three different
      rules for the same thing**; now one: separating comma obligatory, trailing comma
      optional.

### From P2 — what the parser found and what is now to be decided

- [ ] **THE DECISION that P2 forces: the closed vocabulary collides with
      ordinary naming** — nine words at eleven places, `slots` `ops` `next` `slot`
      `from` `boot` `stack` `check` `u64`. **The hardest case is `slots`, because the language
      generates the name itself** (`slots of c`, `c.slots[s]`) and at the same time forbids it as a place.
      Two ways out, both with a price: contextual words (then the table does not hold what it
      claims) or renaming (then every user carries the list in their head).
      **The compiler today admits words as names only after `.`/`->` and before `:`.**

- [ ] **Per template at least one mutation that falls ONLY if the once-obligation is really
      checked.** Today: **0 of 19** — most templates are designed, and what
      is not code catches no mutation. **The coupling of the two new registers is the
      condition for the template register being more than a list.**
- [ ] **The annotation emission needs template entries of its own and mutations of its own.**
      `65 von 65` measures the checker today; about the **wished-for-form channel** it says nothing —
      and that is exactly where a coherently weakened generator is caught **by no proof**.
- [ ] **Every new generated form needs its template entry BEFORE it becomes grammar.**
      `gabbro schablonen` carries today **20, of which 15 unproved**. The list is the ratchet
      over the surface into which the third way out shifts its burden of proof —
      **if it grows, the trust base grows, even if the metric shines.**
### Checker and generator

- [ ] **Mutation probe on the ANNOTATION EMISSION**, not only on the code emission. The coherently
      weakened case (code **and** contract) is caught by **no** proof — only by the
      differential test against the handwriting. That is its named task.
- [ ] **Emit the assumption set into the artefact** ("proved under A1…An"), as a **set of names**
      with a class, not as a number. A ratchet over a cardinal number does not bite against exchange.
- [ ] **Every falsifier needs its own speech test:** *can it fail at all?*
- [ ] **The scope in [`dokumente/SPRACHE.md`](dokumente/SPRACHE.md) is new — run a counter-probe:** look for a construct
      whose line is too strong. The table has the same prehistory as the two
      overreaches in `dokumente/HISTORIE.md`.

---
### Later

- [ ] **Binary verification** — the only route that takes the lowering out of the trust base.
      A project of its own.
- [ ] **Reusable specification theories** — they help the **second** project. May be counted in
      no cost calculation as long as there is one kernel.


---

---

# BOOKKEEPING
### The order, cheapest first — three documents converge on ONE missing number

1. ~~**The five scratchpad classes into the repo.**~~ **RUN 2026-08-15** as
   *a fresh collection of all eleven* — `N_neu = 5`, today 4. The 19 are **replaced, not
   continued**; their subject was no longer nameable (W7).
2. ~~**Split the 17 measured logic obligations**~~ **RUN 2026-08-16** over
   `N_L = 81`: K = 28, A = 13, W = 40 — and **booked as MISSED** over the
   corrected population (`N_L = 73`, W = 38), because eight seq lemmas
   are tool artefacts. **What is missing is B3** — without line shares no
   substitution into the weighting formula. *(originally:)* split into *by construction · descent statement
   (generated scheme bites) · value statement (does not bite)*. **Half a day of paper, and the
   greatest leverage in the folder:** the gap calculation ends at "k unknown", the hard
   promises end at the same split, and the ceiling of the step promises hangs on it.
   **Three documents, one number.**
3. ~~**The four missing domain fragments**~~ **WRITTEN 2026-08-16** (F7–F10). The
   convergence bet has its data points: **four fragments, zero new constructs** — and in
   the second column **three changed meanings** («B37», «B38», «B39»).

> **~~No checker line before the result of 2.~~ — VIOLATED on 2026-08-14, on announcement.**
> The compiler was begun before the result of 2. The rule stays standing here,
> struck through instead of deleted: what it was meant to prevent has happened — P2 and P3
> can no longer kill the thesis *before* the compiler is built. What the build brought in
> stands in [`dokumente/MESSUNGEN.md`](dokumente/MESSUNGEN.md); what it cost stands here.
### Reconciliation — what 2026-08-14 found in this file

**The question was whether this list is still sensible at all.** Answer: the **content** yes,
the **bookkeeping** no. Eight classes of finding, all mechanically demonstrable:

| | Finding | done |
|---|---|---|
| **1** | **Eight `[x]` entries** in a file whose closing sentence reads "exclusively what is open" | taken out; each is recorded elsewhere (see below) |
| **2** | **"there is no compiler (P2–P7)"** — there is one up to P3 | corrected |
| **3** | **Two ordering rules stood there as being in force although they are violated** ("no checker line before 2", "not a line of Rust") | struck through with a date, not deleted |
| **4** | **"Six of the nine passes are missing"** — it is five whole and two half | corrected |
| **5** | **Stale numbers from P1**: 117 rules, 187 terminals (today 139 / 206) | taken out along with the entry |
| **6** | **Three topics twice** — `narrow` three times, *variable lengths* and *version evolution* twice each | drawn together |
| **7** | **Two label systems with the same names**: the headings "P0"/"P1" against the checker plan P0…P7, where P1 is the grammar unification | renamed |
| **8** | **Four done items carried as open**: `by consuming` (has stood in the grammar since `dokumente/SYNTAX.md`:416), `vtd.rs` and `space.rs` (both run, see `dokumente/MESSUNGEN.md` P0.2/P0.3), P0.4 (run, `dokumente/MESSUNGEN.md`) | taken out |

**And one that is mine:** the correction *"the mark ≤ 24 is missed, not open"*
I reported as done on the same day — in `dokumente/MESSUNGEN.md` it was, **here it was not**.
The replacement missed the quotation mark and ran silently into nothing. *A correction
one reports without looking it up is the same movement as a number one claims
without measuring it.*

### What that says about the form of this file

It has **grown chronologically** — every day appended at the bottom, and nobody went back.
Exactly the prehistory out of which the folder drew its 24 files together to 9 on 2026-08-14.
**The next question is therefore not a tidying question but a question of role:**

- [ ] **Does this file need a cut by ROLE instead of by date?** Today it mixes four
      kinds: *design questions* (undecided, need a judgement), *measurements* (need
      a run), *checker defects* (need code) and *things to be re-checked* (need a
      source). A list in which half a day of paper stands next to a subproject no longer
      sorts — and a list that does not sort does not get read.

### Where the removed items are recorded

| Item | Source |
|---|---|
| P1 — grammar unification | [`dokumente/SPRACHE.md`](dokumente/SPRACHE.md) §6 (checker plan), guardian `pruefe-syntax.sh` |
| P2 — lexer and parser | [`dokumente/MESSUNGEN.md`](dokumente/MESSUNGEN.md), section *P2* |
| P3 — M1 + V1–V3 | [`dokumente/MESSUNGEN.md`](dokumente/MESSUNGEN.md), section *P3* |
| `revoke` on paper | [`dokumente/MESSUNGEN.md`](dokumente/MESSUNGEN.md), *P0.1* |
| P0.1b — witness ordering | [`dokumente/SPRACHE.md`](dokumente/SPRACHE.md) §9.2 |
| `by induction over` | [`dokumente/SYNTAX.md`](dokumente/SYNTAX.md) §5, [`dokumente/SPRACHE.md`](dokumente/SPRACHE.md) part V |
| seL4 split, SPARK ladder | [`dokumente/PLAN.md`](dokumente/PLAN.md) |
| `vtd.rs`, `space.rs`, P0.4 | [`dokumente/MESSUNGEN.md`](dokumente/MESSUNGEN.md), *P0.2/P0.3* and *P0.4* |
| **G1–G11** (2026-08-15) | [`dokumente/SYNTAX.md`](dokumente/SYNTAX.md) (EBNF pulled up), `beispiele/11-grammatikbefunde.gab`, poison `43`–`45` |
| **Counter rule** (2026-08-15) | [`dokumente/SPRACHE.md`](dokumente/SPRACHE.md) §1, *„Die Zaehlerregel"* |
| **F4/F6 outdated** (2026-08-15) | [`dokumente/FRAGMENTE.md`](dokumente/FRAGMENTE.md); **gate P2 stands at 10 of 10** (2026-08-16) |
| **Mutation generator** (2026-08-15) | `erzeuge-mutationen.py`, advance protocol + result in [`dokumente/MESSUNGEN.md`](dokumente/MESSUNGEN.md) |
| **TODO guardian** (2026-08-15) | `pruefe-todo.py`, seven classes with a speech test |
