# Gabbro — offene Punkte

> **Aufgeraeumt 2026-08-16.** Die acht Entwurfs- und Messdokumente liegen jetzt in
> [`dokumente/`](dokumente/); im Wurzelverzeichnis stehen nur noch **README, TODO und DONE**.
> **Zwanzig Punkte sind gegen den CODE geprueft und nach [`DONE.md`](DONE.md) gewandert** —
> nicht gegen die Erinnerung: je Punkt eine Kennung, eine Datei oder eine Befehlszeile.
>
> **Caprock-Punkte herausgenommen 2026-08-16.** Diese Liste fuehrt **Gabbro**. Was ihren
> Gegenstand in Caprocks Code oder Buchfuehrung hat, gehoert dorthin — auch wenn es hier
> entstanden ist. *Eine Aufgabenliste, die zwei Projekte fuehrt, sortiert fuer keines.*
> Herausgenommen: Eager-FP, K1–K3, N2, die zwei offenen Klempnerei-Pflichten,
> Fortschritt/Aushungern (D8). **Nicht geloescht, sondern nach
> [`dokumente/AN-CAPROCK.md`](dokumente/AN-CAPROCK.md) gewandert** — sie sind Befunde, nur
> nicht unsere.
>
> **Abgeglichen 2026-08-14.** Diese Datei fuehrt **ausschliesslich Offenes**; Erledigtes steht
> in den Entwurfsdateien, Widerlegtes in [`dokumente/HISTORIE.md`](dokumente/HISTORIE.md), Gemessenes in
> [`dokumente/MESSUNGEN.md`](dokumente/MESSUNGEN.md). Der Abgleich am 2026-08-14 fand die Datei **in acht Punkten
> unwahr ueber sich selbst** — acht erledigte Eintraege, sechs Aussagen, die der Ordner
> ueberholt hatte, drei doppelt gefuehrte Themen, zwei kollidierende Etikettensysteme und
> stehengebliebene Zahlen aus P1. **Eine Liste, die nicht stimmt, kostet mehr als keine:**
> sie sagt an jeder Stelle „das ist noch offen", und der Leser glaubt es.
> Was der Abgleich einzeln gefunden hat, steht am Ende unter *Abgleich*.

## Leistung — zwei Posten, beide vor dem ersten Benchmark

- [ ] **Die Schrankenpruefung amortisieren:** `bounded N ops` muss nicht je Durchgang geprueft
      werden. `progress` traegt die Terminierung, die Schranke ist ein **Watchdog** — eine Pruefung
      **alle 2^k Durchgaenge** senkt die Kosten auf ~1/2^k, die Zusage wird „bricht nach hoechstens
      N + 2^k". **Vor dem ersten Benchmark entscheiden**, sonst misst er ein Konstrukt, das niemand
      so bauen wuerde.
- [ ] **Die Spannung flach-absenken gegen schnell ist ungepreist.** Der Ordner hat sie nur auf der
      Korrektheitsseite bezahlt; auf der Leistungsseite ist die Absenkung eine **Wette auf den
      C-Uebersetzer**, und sie haengt an der ungeschriebenen Formentabelle.

## Die Reihenfolge, billig zuerst — drei Dokumente laufen auf EINE fehlende Zahl zu

1. **Die fuenf Scratchpad-Klassen ins Repo.** Sie entsperren das 19→0-Tor, das sonst
   unentscheidbar bleibt.
2. **Die 17 gemessenen Logik-Pflichten aufteilen** in *durch Konstruktion · Abstiegsaussage
   (erzeugtes Schema greift) · Wertaussage (greift nicht)*. **Ein halber Tag Papier, und die
   groesste Hebelwirkung im Ordner:** die Lueckenrechnung endet bei „k unbekannt", die harten
   Zusagen enden bei derselben Aufteilung, und die Decke der Schrittzusagen haengt daran.
   **Drei Dokumente, eine Zahl.**
3. **Die vier fehlenden Bereichsfragmente** (Scheduler, MMU, Lader, Parser) — und sie sind
   **zugleich das Messgeraet fuer die Konvergenzwette**: neue Konstrukte je Fragment muessen fallen.

> **~~Keine Prueferzeile vor dem Ergebnis von 2.~~ — VERLETZT am 2026-08-14, auf Ansage.**
> Der Uebersetzer wurde vor dem Ergebnis von 2 angefangen. Die Regel bleibt hier stehen,
> durchgestrichen statt geloescht: was sie verhindern sollte, ist eingetreten — P2 und P3
> koennen die These nicht mehr *vor* dem Uebersetzerbau toeten. Was der Bau eingebracht hat,
> steht in [`dokumente/MESSUNGEN.md`](dokumente/MESSUNGEN.md); was er gekostet hat, steht hier.

## Was fehlt, um Caprock VOLLSTAENDIG in Gabbro zu schreiben (Stand 2026-08-14)

**Bekannte Blocker: keiner mehr.** Die zwei gemessenen „passt nicht" aus `dokumente/FRAGMENTE.md` sind zu —
`forever` hat mit `leaves`/`leave` einen Ausgang, `transition` schreibt mit `transset` **mehrere
Orte in einem Zug** (`caller` und `reply_owner` nie halb gesetzt).

**Was fehlt, ist deshalb keine Konstruktliste, sondern MESSUNG:**


**Und getrennt davon, weil es nicht die Ausdruckskraft betrifft:** der Uebersetzer steht bis
**P3** (Lexer, Parser, vier von neun Paessen — zwei davon nur teilweise, s. `gabbro paesse`);
**P4–P7 fehlen**, die **C-Formentabelle** (40–60 Eintraege) ist ungeschrieben, und die
**Beweisschablonen** sind benannt, nicht entworfen.

> **Seit [`dokumente/SPRACHE.md`](dokumente/SPRACHE.md) (2026-08-14) sind die neun Entwurfsfragen entschieden.**
> Was hier steht, ist ueberwiegend **Messung**, nicht Entwurf.




- [ ] **Abnahme der dritten Ergaenzung** (§6): Katalog gegen Zaehlung — **jeder gezaehlte Befehl
      hat ein Axiom oder ein Konstrukt, jede Zeile einen Befehl**; die Mode-Leiter als Sprechprobe
      (vertauschtes `write_cr0(PG)` **muss** brechen); die vorberechneten Boot-Tabellen byteidentisch
      gegen das, was das heutige Trampolin zur Laufzeit baut.
- [ ] **P4–P7** aus [`dokumente/SPRACHE.md`](dokumente/SPRACHE.md) §6 — M2 samt Schablone, C-Emission,
      Paarungs-Pass mit Litmus-Sonden, ein Caprock-Modul end-to-end.
      **Jede Stufe verbraucht das Ergebnis der vorigen, wie eine `Duty`.**

## Die Schreibrechtszeile `by ops` — und der Gruppen-Pruefsatz, der ihr vorausgeht

- [ ] **`field : u16 by ops` — zwei vorhandene Woerter, null Wortschatzzuwachs.** Ein Feld, das
      **nur** die erzeugten Operationen seiner Tabelle schreiben. Damit wird die K-Bedingung des
      Messprotokolls (*„gilt nur, wenn ALLE Mutationen des Traegers erzeugte Operationen sind"*)
      von einer **Pruefvorschrift zu einer Grammatikeigenschaft** — und `refcount -= 1` von Hand
      ist schlicht nicht schreibbar. **Vor die Zaehlung eingetragen ist konsistent: sie macht
      Messung 2 schaerfer, nicht weicher. Protokollarbeit, keine Zaehlung.**
      * **Durchstich 1 — `breaking`.** Ein `breaking` auf einem `by ops`-Feld ist **entweder
        Uebersetzungsfehler oder steht unter der F8-Regel** (Schluss nur durch erzeugte
        Operation). Die Wechselwirkung muss ausgesprochen werden, sonst ist die Eigenschaft
        eine Zusage mit Hintertuer.
      * **Durchstich 2 — der Rand.** Ein `extern fn` mit Schreibwirkung auf den Traeger, oder
        ein `dma`-Raum, der ihn erreicht, umgeht jede Grammatik. **Ehrliche Fassung: „innerhalb
        von Gabbro unschreibbar; die Ausnahmen stehen im Manifest."** Und M3 schliesst den
        DMA-Fall **strukturell** aus: ein `by ops`-Traeger liegt in keinem `dma`-erreichbaren
        Bereich — eine Platzierungsregel wie bei der GDT.
- [ ] **DER GRUPPEN-PRUEFSATZ, und er geht der Schreibrechtszeile VORAUS.** `refcount_matches`
      ist eine **Verbindungs**-Invariante: der Zaehler in Tabelle A muss der Zahl der Verweise
      in B entsprechen. **Werden `ops` je Tabelle erzeugt, erhaelt keine einzelne Operation
      sie** — Verweis-Einfuegen in B *plus* Inkrement in A ist **eine** logische Operation ueber
      beiden, und wer die Koordination als Handleim dazwischenschreibt, hat die Invariante
      wieder als Aussage ueber die Zusammensetzung, also **L**.
      **Ein `refcount`, den nur die `ops` von A schreiben, waehrend die Wahrheit ueber ihn in B
      liegt, ist geschuetzt und trotzdem falsch.**
      * **Was es braucht:** Operationen ueber einer **Tabellengruppe** — die Verbindungs-
        Invariante an der Gruppe deklariert, die Operation (retype, CDT-insert, revoke-Schritt)
        ueber CapSpace *und* CDT *und* Zaehler **in einem Zug**, der Erzeuger prueft die
        Erhaltung gegen die Gruppendeklaration.
      * **DER PRUEFSATZ, auf Papier, vor der Grammatik:** *B13 faellt genau dann, wenn jede im
        Baum vorkommende Verbindungs-Invariante eine Gruppe hat, deren `ops` sie schliessen.*
      * **UND ER IST DIESELBE UNTERSUCHUNG WIE `locks ordered` — nicht zwei.** Mehrkern in
        Zeile 1 verschmilzt sie: auf **einem** Kern heisst *„jede Operation fuer sich
        erhaltend"* ein sequenzielles Argument; auf **mehreren** heisst es **erhaltend unter
        dem Sperrprotokoll**. Eine `ops`-Operation muss deklarieren, **unter welcher Sperre**
        sie laeuft, und die Schablone beweist die Erhaltung **relativ dazu**. Fuer die Gruppe
        folgt sofort: Gruppen-`ops` ueber CapSpace *und* CDT halten die Sperren **beider**
        Traeger — **und ob das eine gemeinsame Sperre ist oder zwei mit Ordnung, IST die
        `locks ordered`-Frage.**
      * **Ein Durchgang, drei Antworten** — am CapSpace/CDT-Paar, auf Papier:
        1. welche Verbindungs-Invarianten existieren,
        2. welche Gruppen schliessen sie,
        3. **welchen Sperrabdruck haben die Gruppenoperationen.**
        **Tauchen dort zwei Sperren derselben Klasse auf, ist das zugleich der erste echte
        Prueffall fuer `locks ordered` — billiger als das ganze Scheduler-Fragment**, und der
        Scheduler tritt danach mit einem **getesteten** statt einem vermuteten Sperrkonstrukt an.

## Aus Welle 4 (2026-08-16) — zwei Bedingungen und ein Kandidat

- [ ] **«B38» — die Randbedingung an den benannten Traeger.** *„Die Fortsetzung prueft neu
      **oder** nennt, was sie stattdessen traegt"* ist die richtige Form — **aber ein Traeger
      `masks IRQ` gilt nur, wenn der Eintrittskontext `nested masked` fuehrt.** Ohne diese
      Kopplung ist *„mich traegt die Maskierung"* die Zusicherung aus **R15**, die erfuellt
      ist, sobald der Pruefer schweigt. **Mechanisch pruefbar** ueber `entrydecl`; zu bauen.
- [ ] **«B39» — die Ausnahmeregel zum Hardware-Axiom, und sie ist ein KANDIDAT auf ein neues
      Wort.** `A`/`D` schreibt die MMU selbst — die GDT-Lektion am Seitenwerk. **Sobald
      Gruppen-`ops` das Seitenwerk erreichen, kollidiert das Axiom mit der
      Schreibrechtszusage**: die K-Bedingung verlangt, dass ALLE Schreibstellen erzeugt sind.
      Welche Felder einer `walk`-Deklaration **hardwarebeschreibbar** sind, gehoert an die
      Deklaration (Kandidatenzeile `hardware A, D;`), so wie `reserved` an einem
      `format`-Feld. *`R001` sieht die MMU heute nicht — sie schreibt an jeder Grammatik
      vorbei, nur im `normal`-Raum statt im `dma`-Raum.*
      **Belastet die Konvergenzwette: es waere Spalte 1, nicht nur Spalte 2.**

## Aus dem Papiertest vom 2026-08-14 — ein toter und zwei lebendige Kandidaten

> **Ein Kandidat ist am 2026-08-14 gestorben und steht deshalb NICHT mehr hier:**
> `locks ordered` — null Prueffaelle im Baum. Der Nachruf steht in
> [HISTORIE.md](dokumente/HISTORIE.md), die Messung in [MESSUNGEN.md](dokumente/MESSUNGEN.md).
> *Diese Datei fuehrt ausschliesslich Offenes; ein gestorbenes Konstrukt ist kein erledigter
> Punkt, sondern ein Bruch mit der eigenen Absicht — und der gehoert in die Historie.*



- [ ] **N3 — `held` braucht einen Zweig fuer Leser-Schreiber-Sperren.** `held <= K ops` ist
      fuer **exklusive** Halter gedacht; auf der geteilten Seite ist die Rechengroesse die
      **Writer-Wartezeit unter Leserdruck**, nicht die Haltezeit eines Lesers. **Der Kostenpass
      rechnet heute nur den exklusiven Fall** — und die Latenzformel aus §9.3 mit ihm.

## Gruppen-`ops` + `by ops` — der Entwurf, VOR der ersten Grammatikzeile

Drei Festlegungen aus dem Papiertest, jede nachgeprueft. **Sie stehen hier, weil sie den
Entwurf aendern, nicht weil sie ihn schmuecken.**

### E1 — Der Sperrabdruck der Gruppe ist ZWEISTUFIG, und das entscheidet die Grammatik

Mutationen nehmen exklusiv, die erzeugte Leseoperation (`lookup`-Klasse) nimmt **geteilt** —
das ist im Baum gemessen: `33 CAPS.read()` gegen `44 CAPS.write()`. **Also deklariert das
Konstrukt beide Modi JE `op`, nicht einen je Gruppe.**

```
group Kappen over { Slots, Objekte } locks KAPPEN {
    op einfuegen  exclusive;
    op entfernen  exclusive;
    op nachschlagen shared;      -- der heisse Pfad
}
```

**Ohne diese Zeile waere `locks shared` gebaut und die Gruppe koennte es nicht nutzen** —
jede erzeugte Operation naehme exklusiv, und der meistgelaufene Pfad des Kernels waere
wieder der langsamste. *Ein Konstrukt, das ein anderes unbrauchbar macht, ist ein
Entwurfsfehler, kein Feature-Rueckstand.*

### E2 — Die Sprechprobe hat eine Pflichtrichtung, und sie ist eine DATEI

`refcount -= 1` mit der Null-Pruefung **danach** muss unter `by ops` unschreibbar sein. Das
gehoert als **Gift-Fragment in den Test, nicht als Satz in den Text** — die Regel des
Ordners, dass eine Zusage eine Stelle braucht, an der sie faellt.

**BERICHTIGT.** Ich hatte geschrieben, der Schnitt stehe in zwei **unabhaengig
geschriebenen** Kernen. Das ist falsch, und es ist mechanisch widerlegt:

```
$ git log --follow --name-status -- crates/caprock-cap/src/space.rs
R099   crates/sel4lake-cap/src/space.rs -> crates/caprock-cap/src/space.rs
```

**`R099` — eine Umbenennung mit 99 % Aehnlichkeit.** Dieselbe Autorenlinie, dieselbe Datei;
die Kopie unter `ARMTest/` ist ein aelterer Schnappschuss derselben Abstammung, kein zweiter
Kern. *Zwei Fundstellen aus einer Vererbung sind eine Fundstelle.*

Die tragfaehige Begruendung ist eine andere — und sie ist gemessen, nicht erschlossen:

```
$ git log -L 1060,1075:crates/caprock-cap/src/space.rs --oneline
b026c83  A-3.3: Finalized leiht seinen Speicher …          2026-07-29
083a698  DMA: Teardown-Token (ext-37) -- Freigabe nur gegen Nachweis
0f246f9  ext-23 D0: DmaCap + DmaEnforcer …
9085cc0  ext-22 P4: generische Device-MMIO-Infrastruktur …
2d50d42  feat(cap/ipc): first-class Reply-Cap mit Revocation
2111f30  initial                                            2026-06-23
```

Die Zeilenfolge steht **seit dem Ursprungscommit** (`2111f30`, dort Zeile 341/342, woertlich
dieselbe Reihenfolge) und hat **fuenf Umbauten genau dieser Region** ueberlebt — darunter
zwei, die die Freigabesemantik selbst umgeschrieben haben (`Reply-Cap mit Revocation`,
`DMA-Teardown-Token`). Ueber fuenf Wochen, ueber eine Paketumbenennung, ueber die
Verdopplung der Datei.

> **B29 ist kein Ausrutscher, sondern ein Attraktor.** Wer den Loeschpfad schreibt, schreibt
> ihn so — auch beim fuenften Umbau, auch nachdem die Falle einmal bezahlt war. **Das traegt
> die Sprechproben-Pflicht genauso gut wie die widerlegte Unabhaengigkeitsbehauptung, und es
> ist die wahre Begruendung.**

Die vorhandene Probe `beispiele/gift/37-b29-unter-ops.gab` deckt `ops` auf der **Tabelle**
(`D001`). Die neue deckt `by ops` auf dem **Feld** — `field : u16 by ops` — und muss genau
diese Zeilenfolge treffen.

### E3 — Die Verus-Vorlage: Klauselstruktur uebernehmen, Typen NICHT

**Nachgeprueft, und der Mechanismus ist ein anderer als vermutet — die Warnung wird dadurch
staerker, nicht schwaecher.**

`cap_space.rs:17` fuehrt `pub refcount: nat`. Am Loeschpfad steht:

```
:791   let oldrc = cs.objects[o as int].refcount;
:792   assert(oldrc >= 1);                        // <- WIRD BEWIESEN, aus der Invariante
:793   let newrc: nat = (oldrc - 1) as nat;
```

**Das Modell beweist die Vorbedingung.** Es ist also nicht so, dass die Vorlage die Frage
falsch beantwortet — sie beantwortet sie richtig, **aus der Invariante**. Was `nat`
wegnimmt, ist etwas anderes: der Typ traegt **keine Breite**, also entsteht ueber die
*Darstellung* nie eine Pflicht. Es gibt genau **ein** Netz, und es haengt an der Invariante.

In Gabbro traegt dasselbe Feld `u32 in 0 ..= NSLOTS`. Damit ist `-= 1` bei 0 ein
**M1-Fehler aus dem TYP** — ohne jeden Bezug auf die Invariante. **Zwei unabhaengige Netze
statt einem**, und das zweite ist genau das, was in der Sprechprobe als `M104` neben `D001`
fiel.

> **Die Schablone uebernimmt die KLAUSELSTRUKTUR der Vorlage (eine `spec fn` ueber allen
> Klauseln, Erhaltung je Operation), nicht ihre TYPEN.**
>
> Erbt sie `nat` mit, sieht die erzeugte Pflichtliste vollstaendig aus, waehrend das zweite
> Netz fehlt — und schlimmer: eine erzeugte C-Emission koennte die Bereichspruefung
> weglassen, *weil der Beweis sagt, es koenne nicht negativ werden*. Das ist woertlich die
> gebuchte Fehlerklasse: **eine Behauptung ueber das Modell in die Maschine entlassen**
> (`dokumente/HISTORIE.md`, Commit `5904cae`). Dann waere die Vorlage ein trojanisches Geschenk.

**Die Pruefzeile dagegen, mechanisch:** kein von einer Schablone erzeugtes Feld darf einen
Typ ohne Breite tragen. Das ist an der Schablone selbst pruefbar, nicht erst am Erzeugnis.

## Die vier Posten zum Ziel — Plan mit Toren in [`dokumente/PLAN.md`](dokumente/PLAN.md) §A

**Das Ziel ist: Gabbro beweist alles ausser funktionaler Korrektheit.** Gegen dieses Ziel
gelesen faellt der Grossteil der 31 Fragmentbefunde heraus (`dokumente/PLAN.md` §A, Neusortierung) —
uebrig bleiben vier, und **einer davon ist nicht geloest, sondern gestreift**.



- [ ] **A2 — GEFAHREN: dynamische Aufrufe werden verboten, `fnptr` braucht keinen Vertrag.**
      Die zwei dynamisch benutzten Traits haben je EINE Implementierung. **Neu und
      unentschieden: 89 Verschluesse** (`dyn FnMut`/`Fn`) — Gabbro hat keine, und was daraus
      wird (einbetten, Zeiger plus Kontext, Verbot), steht nirgends.
- [ ] **A4 — `costs` an einer REKURSIVEN Funktion bleibt eine Annahme.** Ein Aufruf zaehlt
      die *deklarierten* Kosten des Gerufenen; bei einem Zyklus rechnet niemand nach. Das ist
      die Absicht von §7 — es heisst aber, dass die Terminierung dort an einer Zusage haengt.




- [ ] **A5 — Abnahme:** Fragmente mit dem Uebersetzer neu, die Zaehlung ueber
      **Gabbro-Quelltext** statt ueber Rust (**erst dann ist die Latte ≤ 24 echt
      entscheidbar** — s. den Bericht der ungueltigen Messung weiter unten), und die vier nie
      ausgeschriebenen Bereiche.

## Aus der Gegenpruefung (2026-08-14) — was noch offen ist

- [ ] **DER BILLIGE ABSCHLUSS, und er gehoert VOR die grossen Saetze ueber „sonst nichts":
      `effects` prueft Schreiben und `locks`, aber nicht Lesen und nicht Aufrufe.**
      Rahmenvollstaendigkeit gilt heute nur fuer die **Schreibhaelfte**; „nur die eingetragene
      Logik ist aktiv" ist damit eine halbe Aussage. Dieselbe Pruefmechanik, andere Richtung.
      Der Rumpfabgleich steht (E005/E006); zwei Haelften fehlen:
      * **Lesen** — `dokumente/FRAGMENTE.md` liest in jeder Funktion Stellen, die keine `reads`-Zeile
        nennt. Ob das ein Befund ueber die Fragmente ist oder die gemeinte Bedeutung von
        `effects`, **entscheidet der Ordner, nicht der Pass**. Solange das offen ist, darf
        er nicht pruefen, was er nicht weiss.
      * **Aufrufwirkungen** — die Wirkungen des Gerufenen muessten auf die Argumente des
        Aufrufers abgebildet werden. **Das ist der Posten, der `effects` erst kompositional
        macht**, und ohne ihn deckt eine Wirkungsliste nur die erste Ebene.
- [ ] **Die Mutationsprobe deckt heute den Pruefer, nicht die Emission.**
      `./mutiere-pruefer.py` beschaedigt je eine Regel des Pruefers und sieht nach, ob eine
      Probe faellt — **24 von 24 gefangen** (2026-08-14). Was noch fehlt, ist dieselbe Probe
      auf der **Annotationsemission** (s. *Pruefer und Erzeuger*): dort entsteht der
      Wunschform-Beweis, und dort gibt es noch nichts zu beschaedigen, weil noch nichts
      emittiert wird.
      * **~~Die Mutationen sind von Hand geschrieben~~ — GEFAHREN 2026-08-15, Tor
        BESTANDEN.** `erzeuge-mutationen.py` verdreht systematisch: **7 von 39 gefangen
        (18 %)** gegen 38 von 38 der Handmutationen. Der Verdacht war richtig, und der
        eigentliche Befund ist **wo**: 6 der 15 echten Luecken in `typen.rs`, 5 in
        `umgebung.rs`. *Der Pruefer ist dicht, wo er ABSAGEN ERZEUGT, und duenn, wo er
        RECHNET.* Offen bleibt daraus: **Wertetabellen fuer die Bereichsarithmetik** —
        Beispieldateien treffen Klassen, nicht Grenzen.



- [ ] **Die Etiketten G1–G8 kollidieren** mit einer aelteren Messung in
      [`dokumente/MESSUNGEN.md`](dokumente/MESSUNGEN.md), die G1/G2/G3/G5 fuer etwas anderes vergibt.
- [ ] **Der Parser ist an sechs Stellen laxer als die EBNF**: `pub` an 13 Item-Arten, die es
      nicht fuehren · Wortschatzwoerter als Namen nach `::`, in `reaches … via` und in
      `chain(a,b)` (drei Stellen, die der eigene Dateikopf **nicht** freistellt) · `mut` und
      Typannotation an `let … else` · `exhaustive` und `mirrors` an beliebiger Stelle ·
      `reg … fields` ohne Schlusskomma, waehrend `slotdecl` es erzwingt · `type T = { };`
      wird zum leeren **Summen**typ statt zum leeren Verbund.
      **Und an einer Stelle strenger:** `pub const` im `table`-Rumpf faellt, obwohl es
      ableitbar ist.

## Aus P2 — was der Parser gefunden hat und was jetzt zu entscheiden ist

- [ ] **DIE ENTSCHEIDUNG, die P2 erzwingt: der geschlossene Wortschatz kollidiert mit
      gewoehnlicher Benennung** — neun Woerter an elf Stellen, `slots` `ops` `next` `slot`
      `from` `boot` `stack` `check` `u64`. **Der schwerste Fall ist `slots`, weil die Sprache
      den Namen selbst erzeugt** (`slots of c`, `c.slots[s]`) und ihn als Ort zugleich verbietet.
      Zwei Auswege, beide mit Preis: kontextuelle Woerter (dann haelt die Tabelle nicht, was sie
      behauptet) oder Umbenennen (dann traegt jeder Anwender die Liste im Kopf).
      **Der Uebersetzer laesst Woerter heute nur nach `.`/`->` und vor `:` als Namen zu.**

- [ ] **Je Schablone mindestens eine Mutation, die NUR faellt, wenn die Einmal-Pflicht real
      geprueft wird.** Heute: **0 von 16** — die meisten Schablonen sind entworfen, und was
      kein Code ist, faengt keine Mutation. **Die Kopplung der zwei neuen Register ist die
      Bedingung dafuer, dass das Schablonenregister mehr ist als eine Liste.**
- [ ] **Die Annotationsemission braucht eigene Schablonen-Eintraege und eigene Mutationen.**
      `32 von 32` misst heute den Pruefer; ueber den **Wunschform-Kanal** sagt es nichts —
      und genau dort wird ein stimmig abgeschwaechter Erzeuger **von keinem Beweis** gefangen.
- [ ] **Jede neue erzeugte Form braucht ihren Schablonen-Eintrag, BEVOR sie Grammatik wird.**
      `gabbro schablonen` fuehrt heute **16, davon 16 unbewiesen**. Die Liste ist die Ratsche
      ueber der Flaeche, in die der dritte Ausgang seine Beweislast verschiebt —
      **waechst sie, waechst die Vertrauensbasis, auch wenn die Kennzahl glaenzt.**










## Papierschritte — keine Zeile Code. Jeder Punkt kann die These töten

> **Umbenannt 2026-08-14.** Diese Ueberschrift hiess „P0", die naechste „P1" — und
> [`dokumente/SPRACHE.md`](dokumente/SPRACHE.md) §6 vergibt P0…P7 an den **Prueferplan**, wo P1 die
> Grammatikvereinigung ist und nicht `check`. **Zwei Etikettensysteme mit denselben Namen
> in derselben Datei**; dieselbe Fehlerklasse wie die G-Kollision weiter oben.

- [ ] **`touches` ist zu grob** — es braucht eine Form für „verändert die Menge nur durch
      Verbrauch". Ohne sie hängt die Ordnung an einer Zusage statt an einer Bedingung.

## `check` ohne Sprache

- [ ] **`check` als Rust-Makrobibliothek**, rückwirkend gegen die 33 Messdisziplin-Fallen, jede mit
      Mutation. Tor: **≥ 5 gefangen**. Nützlich auch dann, wenn Gabbro nie entsteht.

---

## Die Frage, die über den Kern entscheidet

- [ ] **Echte Linearität ist der einzige Mechanismus, den kein vorhandenes Werkzeug liefert** —
      gemessen: Verus' `tracked` ist **affin**, Rust ist affin, SPARKs Leckprüfung hängt an einer
      **Allokation**. An ihr hängen die Bootphase, `Parked` und die lineare Prüfpflicht.
      **Offen: reicht ein Mechanismus, um eine Sprache zu rechtfertigen?** Die billigere Antwort
      wäre ein Beitrag an Verus (linear statt affin). Das ist die teuerste offene Frage des Ordners.
- [ ] **ATS ist der nächste Verwandte für den Kern und ungeprüft** — lineare Typen plus Beweise,
      kompiliert nach C. Dieselbe Logik wie das Verus-Tor: *der nächste Verwandte ist gebaut, der
      Ordner nicht.* **Sollte vor P2 gefahren werden; P2 lief zuerst.** Damit ist der Vergleich
      nicht hinfaellig, sondern nur teurer: er misst jetzt gegen etwas Gebautes statt gegen
      einen Entwurf.
- [ ] **Für jeden weiteren Mechanismus die Gegenrechnung führen.** M2 am Sperrbeleg und M1 sind am
      2026-08-13 gegen den Ordner ausgegangen. **M3 ist gegen die richtige Grundlinie zu messen:
      nicht Verus, sondern `tock-registers`/`svd2rust`** — typisierte Registerzugriffe sind eine
      Rust-Bibliothek. Die Frage ist, was ihr fehlt: Übergänge über Bits, Bedingungen über
      Registergrenzen, Barrierendomäne im Typ.

---

## Induktion — eingetragen, und die eine Zahl fehlt


- [ ] **Das erzeugte Schema muss einmal nach Isabelle** — es ist eine Schablone im Sinne von L3 und
      damit der Posten, der die Vertrauensbasis **verkleinert**.
- [ ] **Wohlfundiertheit hängt an einer Invariante, die man beweisen will.** Die Deklaration muss
      nennen, welche — und das Mass (Zahl der Abkömmlinge) ist Voraussetzung, nicht Ergebnis.

## Aus dem Kriterium ([`dokumente/BEWEIS.md`](dokumente/BEWEIS.md))



- [ ] **Die Trennlinie an einem Grenzfall streiten.** „Nennt nur die Maschine" ist scharf genug für
      die heutigen Fälle — der erste Streitfall gehört in `dokumente/BEWEIS.md`, nicht in eine Fussnote.

## Aus der Umkehrung der Frage ([`dokumente/SPRACHE.md`](dokumente/SPRACHE.md))

- [ ] **Die achtzehn Umwandlungen sind Behauptungen über Absenkbarkeit, keine Belege.** Jede braucht
      ihre C-Absenkung hingeschrieben — vor der Kanonisierung in [`dokumente/SYNTAX.md`](dokumente/SYNTAX.md).
- [ ] **`retry` mit `bounded`/`progress`/`on_exceeded` ist der Ersatz für „unbegrenztes Warten".**
      Offen: reicht eine Zahl, oder braucht es zwei Schranken (Versuche **und** Ticks)?
- [ ] **Nr. 14 verlangt eine `publishes`-Klausel an 2 231 Stellen.** Ob das trägt, entscheidet keine
      Papierübung — das ist der grösste Einzelposten der ganzen Umstellung.
- [ ] **`breaking I { … }` legalisiert eine Invariantenverletzung.** Der Preis ist Sichtbarkeit
      statt Verstecken; ob das reicht, ist unentschieden.

## Syntax — offene Entscheidungen (Einzelheiten in [`dokumente/SYNTAX.md`](dokumente/SYNTAX.md))

- [ ] **Variable Längen in `format`** — die harten 20 % jedes Parser-Erzeugers, keine
      Schreibweise vorhanden.
- [ ] **Versionsevolution:** liest ein `@version 3`-Leser auch v2 — **Absage oder Migration**?
      Beides vertretbar, keins entschieden.
- [ ] **Generizität** — ohne sie braucht jede Tabelle ihren eigenen `traverse`; mit ihr die Frage,
      wie Verträge parametrisiert werden.
- [ ] **Die Sperrordnung fehlt in der Syntax.** `locks CAPS` nennt die Sperre, nicht die **Stufe**.
- [ ] **Der Vorrat an Quantoren in `spec fn` ist unentschieden — und genau dort wandert die Linie**,
      wenn niemand aufpasst.
- [ ] **Fehlerfortpflanzung:** ohne `?` wird jeder Aufruf drei Zeilen, mit `?` gibt es verborgenen
      Kontrollfluss. Beides widerspricht einer Entwurfsregel.
- [ ] **Schlüsselwortsprache** steht auf Englisch, weil das der Bestand ist. Preis: Bruch mit dem
      deutschen Fliesstext. Reversibel (eine Tabelle im Lexer).

## Entwurf — offene Entscheidungen

- [ ] **Roundtrip** `lesen(schreiben(x)) == x` gehört in den Differenztest.
- [ ] **Kostenangabe je Invariante** und an `by unbesucht`: welche Struktur, wer setzt sie zurück,
      was kostet der Reset, darf sie unter dem Lock leben.
- [ ] **Die Axiomschicht beziffern — die x86-Haelfte ist fahrbar, die aarch64-Haelfte NICHT.**
      **Solange die Zahl fehlt, ist „speichersicher unter A1…An" eine Form ohne Inhalt.**
      * **x86:** fahrbar gegen `../caprock-messbasis` (= `SEL4Lake/SEL4Lake` @ `arch/x86_64`,
        `a1bf707`). Offen.
      * **~~aarch64~~ — BLOCKIERT, und zwar nicht aus Zeitgruenden (2026-08-15).** Der
        einzige aarch64-Baum im Ordner (`SEL4Lake/ARMTest/stm32mp25-kernel`) ist **kein
        zweiter Kernel, sondern ein aelterer Schnappschuss DERSELBEN Abstammung** — belegt
        mit `git log --follow`: `R099`, eine Umbenennung mit 99 % Aehnlichkeit von
        `sel4lake-cap` nach `caprock-cap` (s. [`dokumente/HISTORIE.md`](dokumente/HISTORIE.md), *Zwei Fundstellen
        aus einer Vererbung*). Er liegt ausserhalb von git.
        **Eine Gegentabelle daraus waere keine zweite Architektur, sondern dieselbe Linie
        zweimal gezaehlt** — genau die Fehlerklasse, die dieser Ordner am 2026-08-15 gebucht
        hat. *Die Zahl waere nicht ungenau, sondern falsch, und zwar in die schmeichelhafte
        Richtung: sie wuerde Uebertragbarkeit belegen, wo nur Kopie steht.*
      * **Was es braeuchte:** ein aarch64-Kernel mit **eigener** Abstammung, oder die
        ehrliche Fassung des Satzes — *„gemessen fuer x86; fuer aarch64 steht keine Zahl,
        und der vorhandene Baum kann sie nicht liefern."*

- [ ] **B3 beziffern: welche Rümpfe lassen sich NICHT als Traversierung schreiben?** IPC-Fastpath,
      `revoke`, Warteschlangenchirurgie des Schedulers sind die Kandidaten. **Jeder von ihnen kostet
      5 : 1 auf seinem Anteil** — 5 % des Kernels sind +0,25 auf die Kennzahl, 10 % sind +0,5.
      Das ist die Zahl, die früh gebraucht wird und die niemand hat: sie sagt, **wie weit vom Boden
      entfernt** der Entwurf landet.

---

## Prüfer und Erzeuger

- [ ] **Mutationsprobe auf der ANNOTATIONSEMISSION**, nicht nur auf der Codeemission. Der stimmig
      abgeschwächte Fall (Code **und** Vertrag) wird von **keinem** Beweis gefangen — nur vom
      Differenztest gegen die Handschrift. Das ist dessen benannte Aufgabe.
- [ ] **Annahmenmenge ins Erzeugnis emittieren** („bewiesen unter A1…An"), als **Menge von Namen**
      mit Klasse, nicht als Zahl. Eine Ratsche über einer Kardinalzahl greift nicht gegen Austausch.
- [ ] **Jeder Falsifikator braucht seine eigene Sprechprobe:** *kann er überhaupt fehlschlagen?*
- [ ] **Der Geltungsbereich in [`dokumente/SPRACHE.md`](dokumente/SPRACHE.md) ist neu — Gegenprobe fahren:** ein Konstrukt suchen,
      dessen Zeile zu stark ist. Die Tabelle hat dieselbe Vorgeschichte wie die zwei
      Überschreibungen in `dokumente/HISTORIE.md`.

---

## Nachzuprüfen, weil aus dem Gedächtnis zitiert

- [ ] **Die Namensfreiheit „Gabbro"** über Paketregister, GitHub und Sprachlisten — mitsamt dem,
      was gefunden wurde. „Ich habe nichts gefunden" ist ein Nullbefund ohne Grösse.

---

## Später

- [ ] **Binärverifikation** — der einzige Weg, der die Absenkung aus der Vertrauensbasis nimmt.
      Eigenes Projekt.
- [ ] **Wiederverwendbare Spezifikationstheorien** — helfen dem **zweiten** Projekt. Dürfen in
      keiner Kostenrechnung mitgezählt werden, solange es einen Kernel gibt.


---

## Abgleich — was der 2026-08-14 an dieser Datei fand

**Die Frage war, ob diese Liste ueberhaupt noch sinnvoll ist.** Antwort: der **Inhalt** ja,
die **Buchfuehrung** nein. Acht Klassen von Befunden, alle mechanisch nachweisbar:

| | Befund | erledigt |
|---|---|---|
| **1** | **Acht `[x]`-Eintraege** in einer Datei, deren Schlusssatz „ausschliesslich Offenes" lautet | herausgenommen; jeder ist anderswo verzeichnet (s. u.) |
| **2** | **„es gibt keinen Uebersetzer (P2–P7)"** — es gibt einen bis P3 | berichtigt |
| **3** | **Zwei Reihenfolgeregeln standen als geltend da, obwohl sie verletzt sind** („keine Prueferzeile vor 2", „keine Zeile Rust") | durchgestrichen mit Datum, nicht geloescht |
| **4** | **„Sechs der neun Paesse fehlen"** — es sind fuenf ganz und zwei halb | berichtigt |
| **5** | **Stehengebliebene Zahlen aus P1**: 117 Regeln, 187 Terminale (heute 121 / 189) | mit dem Eintrag herausgenommen |
| **6** | **Drei Themen doppelt** — `narrow` dreimal, *Variable Laengen* und *Versionsevolution* je zweimal | zusammengezogen |
| **7** | **Zwei Etikettensysteme mit denselben Namen**: die Ueberschriften „P0"/„P1" gegen den Prueferplan P0…P7, wo P1 die Grammatikvereinigung ist | umbenannt |
| **8** | **Vier erledigte Posten als offen gefuehrt**: `by consuming` (steht seit `dokumente/SYNTAX.md`:416 in der Grammatik), `vtd.rs` und `space.rs` (beide gefahren, s. `dokumente/MESSUNGEN.md` P0.2/P0.3), P0.4 (gefahren, `dokumente/MESSUNGEN.md`) | herausgenommen |

**Und einer, der mir gehoert:** die Berichtigung *„die Latte ≤ 24 ist verfehlt, nicht offen"*
habe ich am selben Tag als erledigt gemeldet — in `dokumente/MESSUNGEN.md` war sie es, **hier nicht**.
Die Ersetzung traf das Anfuehrungszeichen nicht und lief still ins Leere. *Eine Berichtigung,
die man meldet, ohne sie nachzusehen, ist dieselbe Bewegung wie eine Zahl, die man behauptet,
ohne sie zu messen.*

### Was das ueber die Form dieser Datei sagt

Sie ist **chronologisch gewachsen** — jeder Tag haengte unten an, und niemand ging zurueck.
Genau die Vorgeschichte, aus der der Ordner am 2026-08-14 seine 24 Dateien auf 9 zusammenzog.
**Die naechste Frage ist deshalb keine Aufraeumfrage, sondern eine Rollenfrage:**

- [ ] **Braucht diese Datei einen Schnitt nach ROLLE statt nach Datum?** Heute mischt sie vier
      Sorten: *Entwurfsfragen* (unentschieden, brauchen ein Urteil), *Messungen* (brauchen
      einen Lauf), *Pruefermaengel* (brauchen Code) und *Nachzupruefendes* (brauchen eine
      Quelle). Eine Liste, in der ein halber Tag Papier neben einem Teilprojekt steht, sortiert
      nicht mehr — und eine Liste, die nicht sortiert, wird nicht gelesen.

### Wo die herausgenommenen Punkte verzeichnet sind

| Punkt | Fundstelle |
|---|---|
| P1 — Grammatikvereinigung | [`dokumente/SPRACHE.md`](dokumente/SPRACHE.md) §6 (Prueferplan), Waechter `pruefe-syntax.sh` |
| P2 — Lexer und Parser | [`dokumente/MESSUNGEN.md`](dokumente/MESSUNGEN.md), Abschnitt *P2* |
| P3 — M1 + V1–V3 | [`dokumente/MESSUNGEN.md`](dokumente/MESSUNGEN.md), Abschnitt *P3* |
| `revoke` auf Papier | [`dokumente/MESSUNGEN.md`](dokumente/MESSUNGEN.md), *P0.1* |
| P0.1b — Zeugenordnung | [`dokumente/SPRACHE.md`](dokumente/SPRACHE.md) §9.2 |
| `by induction over` | [`dokumente/SYNTAX.md`](dokumente/SYNTAX.md) §5, [`dokumente/SPRACHE.md`](dokumente/SPRACHE.md) Teil V |
| seL4-Aufteilung, SPARK-Leiter | [`dokumente/PLAN.md`](dokumente/PLAN.md) |
| `vtd.rs`, `space.rs`, P0.4 | [`dokumente/MESSUNGEN.md`](dokumente/MESSUNGEN.md), *P0.2/P0.3* und *P0.4* |
| **G1–G11** (2026-08-15) | [`dokumente/SYNTAX.md`](dokumente/SYNTAX.md) (EBNF nachgezogen), `beispiele/11-grammatikbefunde.gab`, Gift `43`–`45` |
| **Zaehlerregel** (2026-08-15) | [`dokumente/SPRACHE.md`](dokumente/SPRACHE.md) §1, *„Die Zaehlerregel"* |
| **F4/F6 veraltet** (2026-08-15) | [`dokumente/FRAGMENTE.md`](dokumente/FRAGMENTE.md); Tor P2 steht weiter bei 1 von 6, s. u. |
| **Mutationsgenerator** (2026-08-15) | `erzeuge-mutationen.py`, Vorab + Ergebnis in [`dokumente/MESSUNGEN.md`](dokumente/MESSUNGEN.md) |
| **TODO-Waechter** (2026-08-15) | `pruefe-todo.py`, sieben Klassen mit Sprechprobe |
