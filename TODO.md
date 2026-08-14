# Gabbro — offene Punkte

> **Abgeglichen 2026-08-14.** Diese Datei fuehrt **ausschliesslich Offenes**; Erledigtes steht
> in den Entwurfsdateien, Widerlegtes in [`HISTORIE.md`](HISTORIE.md), Gemessenes in
> [`MESSUNGEN.md`](MESSUNGEN.md). Der Abgleich am 2026-08-14 fand die Datei **in acht Punkten
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
> steht in [`MESSUNGEN.md`](MESSUNGEN.md); was er gekostet hat, steht hier.

## Was fehlt, um Caprock VOLLSTAENDIG in Gabbro zu schreiben (Stand 2026-08-14)

**Bekannte Blocker: keiner mehr.** Die zwei gemessenen „passt nicht" aus `FRAGMENTE.md` sind zu —
`forever` hat mit `leaves`/`leave` einen Ausgang, `transition` schreibt mit `transset` **mehrere
Orte in einem Zug** (`caller` und `reply_owner` nie halb gesetzt).

**Was fehlt, ist deshalb keine Konstruktliste, sondern MESSUNG:**

- [ ] **Vier von zehn Bereichen sind nie ausgeschrieben worden:** **Scheduler**, **MMU/
      Seitentabellen**, **Lader/`SYS_LOAD`**, **Parser/Checkpoint**. Kein Urteil, kein Fragment —
      und ein Bereich ohne Fragment ist eine Vermutung.
- [ ] **Die sechs vorhandenen Fragmente sind gegen die ZWEITE Fassung geschrieben**, die Grammatik
      ist bei der vierten. Sie muessen nachgezogen und neu beurteilt werden.
- [ ] **Fuenf der elf Klempnerei-Klassen liegen nur im Scratchpad** — rund 6 der 19 haengenden
      Pflichten sind damit **nicht gegen die Sprache pruefbar**.
- [ ] **`programs/` brach 4 von 4** — aber die Messung ist **aelter als die Konstrukte**, die es
      betreffen (`leaves`, `transition publishes`). Ungeprueft, ob es heute traegt.

**Und getrennt davon, weil es nicht die Ausdruckskraft betrifft:** der Uebersetzer steht bis
**P3** (Lexer, Parser, vier von neun Paessen — zwei davon nur teilweise, s. `gabbro paesse`);
**P4–P7 fehlen**, die **C-Formentabelle** (40–60 Eintraege) ist ungeschrieben, und die
**Beweisschablonen** sind benannt, nicht entworfen.

> **Seit [`SPRACHE.md`](SPRACHE.md) (2026-08-14) sind die neun Entwurfsfragen entschieden.**
> Was hier steht, ist ueberwiegend **Messung**, nicht Entwurf.

- [ ] **P0 IST TEILWEISE GEFAHREN** ([`MESSUNGEN.md`](MESSUNGEN.md), 2026-08-14). Ergebnis:
      **Ordering-Stichprobe bestanden, 36/36, kein vierter Ausgang.** `19 → 0` ist
      **nicht entscheidbar**, weil **fuenf der elf Klassen nur im Scratchpad liegen** — das ist ein
      Befund ueber das **Protokoll**, nicht ueber die Sprache, und woertlich Falle 80.
      `narrow` ≤ 24 ist offen, nur die Formpruefung war fahrbar.
- [ ] **Die fuenf Scratchpad-Klassen mit Fundstellen ins Repo**, dann Teil 1 wiederholen.
      Vorher bleibt das `19 → 0`-Tor unentscheidbar. *(Der Satz hiess bis zum 2026-08-14
      „DER NAECHSTE SCHRITT IST KEINE ZEILE RUST" — er ist ueberholt, nicht erfuellt: die
      Rustzeilen kamen zuerst. Der Posten selbst ist unveraendert offen.)*
- [ ] **Eager-FP je Architektur oder global entscheiden.** Berichtigt: auf **x86 ist es eager**
      (`system.rs:1215`, mit genau der CVE-Begruendung der Ergaenzung); **lazy ist der
      aarch64-Pfad**. Das Dekret trifft also die andere Architektur, wo das Argument nicht in
      derselben Form greift.
- [ ] **Protokoll der Ordering-Klassifikation um K1–K3 ergaenzen** — sie sind **Wegfaelle**, keine
      Widerlegungen: unter Sperre entfaellt das Atomic (K1, ein Teil der 2 231 verschwindet),
      Konstruktinneres zaehlt in die Schablonenflaeche statt in die Stichprobe (K2), und
      `accumulates` mit Verbund ist an `sync:572-592` **strikt besser als das Original** (K3).
- [ ] **~~P0 — DIE MESSUNG~~** (urspruengliche Fassung): Die 74-Pflichten-Messung gegen
      Festlegung + beide Ergaenzungen wiederholen: **haengende Klempnerei 19 → 0**; dazu eine
      **Ordering-Stichprobe** (≥ 30 der 2 231 Fundstellen, geschichtet nach Datei) — jede ist
      Paarung, Zaehler oder benannter `seq`-Fall, **ein vierter Ausgang widerlegt die Paarung**;
      dazu die **`narrow`-Zaehlung ≤ 24**. Abnahme ist nicht Zustimmung.
- [ ] **Abnahme der dritten Ergaenzung** (§6): Katalog gegen Zaehlung — **jeder gezaehlte Befehl
      hat ein Axiom oder ein Konstrukt, jede Zeile einen Befehl**; die Mode-Leiter als Sprechprobe
      (vertauschtes `write_cr0(PG)` **muss** brechen); die vorberechneten Boot-Tabellen byteidentisch
      gegen das, was das heutige Trampolin zur Laufzeit baut.
- [ ] **P4–P7** aus [`SPRACHE.md`](SPRACHE.md) §6 — M2 samt Schablone, C-Emission,
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

## Aus dem Papiertest vom 2026-08-14 — ein toter und zwei lebendige Kandidaten

> **Ein Kandidat ist am 2026-08-14 gestorben und steht deshalb NICHT mehr hier:**
> `locks ordered` — null Prueffaelle im Baum. Der Nachruf steht in
> [HISTORIE.md](HISTORIE.md), die Messung in [MESSUNGEN.md](MESSUNGEN.md).
> *Diese Datei fuehrt ausschliesslich Offenes; ein gestorbenes Konstrukt ist kein erledigter
> Punkt, sondern ein Bruch mit der eigenen Absicht — und der gehoert in die Historie.*

- [ ] **L-A — `locks shared`: GEBAUT bis auf den Zeugen am Aufrufrand.**
      Grammatik, Pass und Kostenzweig stehen (`SPRACHE.md` §11.2.1): `S001` (Schreiben unter
      geteilter Nahme), `S002` (geteilt ohne `shared held`), `S003` (Hochstufung), `S004`
      (Zusage ohne Messstelle), `E007` (geteilt erklaert, exklusiv genommen), `K003` (die
      geteilte Haltezeit gegen ihre eigene Zahl). Fuenf neue Mutationen, alle gefangen;
      Beispiel `10-geteilte-sperre.gab`, Giftproben 38–41.
      * **Der Zeuge am Aufrufrand steht als Zwischenregel** (`S005`): ein geteilter Block
        ruft **keine** Funktion mit `requires Held(…)`. Punkt. Zu streng — auch der Aufruf
        ueber eine andere Sperre faellt, der harmlos waere — aber in die sichere Richtung
        irrend, und der Preis steht in der Absage.
      * **Was offen bleibt, ist die ECHTE Pruefung**, und der Mechanismus ist derselbe wie
        bei den Aufrufwirkungen in Pass 8: der **Aufrufgraph**. *Ein Mechanismus, zwei
        Fehlerrichtungen* — und nur eine davon war gefaehrlich, naemlich diese: bis `S005`
        stand, war die Grenze nicht ungeprueft, sondern **durchlaessig** (der Zeuge
        existierte, seine Staerke wurde nicht geprueft). Mit Pass 8 wird `S005` **ersetzt**,
        nicht gelockert: ein geteilter Zeuge deckt dann genau `requires Held-shared`.
- [ ] **L-B — `ghost Stale(T)`: Uebergabe mit Neuvalidierung. Kandidat, kein Beschluss.**
      Das Muster, das Doppelnahme **ersetzt**: unter Sperre A waehlen, freigeben, unter B
      fortsetzen, Befund neu pruefen. Die ehrliche Fassung ist **kein Atomizitaetsversprechen,
      sondern ein Zwang**: ein Wert ueber einer Sperrgrenze verliert seine Fakten (*das tut die
      Sprache schon*) **und** die Fortsetzung muss die tragende Bedingung erneut pruefen.
      **Hinter das Scheduler-Fragment — dort liegt seine Messstrecke.**
- [ ] **N2 — die Ordering-Vollzaehlung braucht eine Spalte „Ordnungsteilnehmer".** `FP_OWNER`
      ist ein Atomic, das **ausdruecklich Teil der Deadlock-Herleitung** ist. Welche Atomics
      das sind, entscheidet, ob sie in die Paarung oder in die Sperrordnung gehoeren.
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

**Nachgetragen, und es verschaerft den Auftrag:** der Schnitt steht **zweimal**, in zwei
unabhaengig geschriebenen Kernen desselben Baums.

| Baum | Stelle | Form |
|---|---|---|
| `SEL4Lake/SEL4Lake` (Caprock) | `crates/caprock-cap/src/space.rs:1067–1068` | `refcount -= 1;` dann `if … == 0` |
| `SEL4Lake/ARMTest/stm32mp25-kernel` | `crates/sel4lake-cap/src/space.rs:617–618` | **dieselbe Form, dieselbe Reihenfolge** |

*Damit ist der Bedarf nach W3 nicht bloss gezaehlt, sondern doppelt gezaehlt — und die
Wiederholung in einem zweiten Kern sagt mehr als die Haeufigkeit im ersten: die Form kommt
nicht aus einer Gewohnheit eines Autors.*

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
> (`HISTORIE.md`, Commit `5904cae`). Dann waere die Vorlage ein trojanisches Geschenk.

**Die Pruefzeile dagegen, mechanisch:** kein von einer Schablone erzeugtes Feld darf einen
Typ ohne Breite tragen. Das ist an der Schablone selbst pruefbar, nicht erst am Erzeugnis.

## An CAPROCK, nicht an Gabbro

- [ ] **N1 — die zwei dokumentierten Sperrordnungen in `system.rs` widersprechen sich.**
      Kopf (`:11–13`): `… → SCHEDS[*] (R2) → Heap.inner (R3) → MEM (R4, innerster)`, dazu
      *„`MEM` haelt nie einen weiteren Lock"*. Gegen `:723`: *„`CAPS` < {`EPS[i]`, `NTFNS[i]`,
      `MEM`} < `SCHEDS[*]` < `FP_STATES`"*. **Entweder ist MEM Blatt oder es hat SCHEDS unter
      sich — beides zugleich geht nicht.** Entscheiden kann es nur der Code.
      *Und genau diese Fehlerklasse — zwei Prosaordnungen, die niemand gegeneinander prueft —
      macht eine deklarierte `rank`-Zeile strukturell unmoeglich.*

## Die vier Posten zum Ziel — Plan mit Toren in [`PLAN.md`](PLAN.md) §A

**Das Ziel ist: Gabbro beweist alles ausser funktionaler Korrektheit.** Gegen dieses Ziel
gelesen faellt der Grossteil der 31 Fragmentbefunde heraus (`PLAN.md` §A, Neusortierung) —
uebrig bleiben vier, und **einer davon ist nicht geloest, sondern gestreift**.

- [ ] **~~A1 und der Ursprung~~ — BEIDE ZU (2026-08-14).** Die Frage war kleiner als
      gedacht: **Kernzustand braucht gar keinen Zeiger.** Eine `table` ist Speicher, ihr Name
      ist ihr Ort; ein `device` hat seine Parameterliste als Konstruktor. Beides gebaut,
      beides in `beispiele/09-ohne-zeiger.gab` ausgeschrieben. Uebrig bleiben Zeiger fuer
      DMA, belegte Regionen und fremden Speicher — **und nur dort ist Trennung ueberhaupt
      eine Frage.** Dort gibt eine Funktion Besitz her, und `own` macht ihn linear.
      **Was jetzt fehlt, ist nur noch der Pass**, s. naechster Punkt.
- [ ] **M2 (Pass 5) bauen — jetzt ohne Entwurfsfrage davor.** Linearitaet durchsetzen:
      ein linearer Wert wird auf jedem Weg **genau einmal** verbraucht, nicht verdoppelt,
      nicht fallengelassen; ein Parameter ist **verbraucht, wenn `effects` ihn unter
      `consumes` nennt, sonst geliehen**. Daran haengen `Held`, `BootPhase`, `Parked`,
      `Duty(check)` und die `own`-Zeiger. **Der Mechanismus, den kein vorhandenes Werkzeug
      liefert — und der einzige, der die Sprache traegt.**
- [ ] **A2 — GEFAHREN: dynamische Aufrufe werden verboten, `fnptr` braucht keinen Vertrag.**
      Die zwei dynamisch benutzten Traits haben je EINE Implementierung. **Neu und
      unentschieden: 89 Verschluesse** (`dyn FnMut`/`Fn`) — Gabbro hat keine, und was daraus
      wird (einbetten, Zeiger plus Kontext, Verbot), steht nirgends.
- [ ] **A4 — `costs` an einer REKURSIVEN Funktion bleibt eine Annahme.** Ein Aufruf zaehlt
      die *deklarierten* Kosten des Gerufenen; bei einem Zyklus rechnet niemand nach. Das ist
      die Absicht von §7 — es heisst aber, dass die Terminierung dort an einer Zusage haengt.
- [ ] **~~A1 (urspruenglich)~~ — der Aliasposten.** `SYNTAX.md`:10 zaehlt „Alias" unter dem, was durch Konstruktion faellt;
      **der Mechanismus dafuer ist nicht auffindbar.** Nichts verbietet zwei
      `ptr<normal,rw>`-Parameter auf dasselbe Objekt, und `restrict` wird aus `effects`
      *erzeugt* — die Rahmenaussage ruht auf einer Zusage statt auf einer Bedingung.
      **Vorschlag aus dem Ordner selbst** (`SPRACHE.md` §3b: *„ein linearer Block ist seine
      Region"*): **ein Zeiger mit `own` ist ein linearer Wert**, geliehen ueber `requires` wie
      die Bootphase. **Papiertest an F1 und F3, keine Zeile Code davor** — und die Stelle, an
      der er scheitert, wenn er scheitert, ist `revoke`s `traverse`-Rumpf: ein linearer Wert
      ist nach dem ersten Durchgang verbraucht.
- [ ] **~~A2 (urspruenglich)~~ — dynamische Aufrufe zaehlen.** `fnptr` traegt keinen Vertrag («B9»),
      also ist die Rahmenaussage an jedem Aufruf durch einen Zeiger leer. **≤ 10 und alle durch
      `match` ersetzbar → verbieten** (kein neues Konstrukt); sonst braucht `fnptr` einen
      Vertrag. **Eine Stunde, und sie kann ein Konstrukt einsparen.**
- [ ] **~~A3~~ — GEFAHREN und GEBAUT.** `index into T` erbt die Schranke; der Indextyp wird
      erzeugt statt geschrieben. Nebenbefund: `index into` war nur `slottype`, nicht
      `typeexpr` — die halbe Aenderung waere nichts wert gewesen. Auch zu.
      *(urspruenglich:)* `table … count N`. Eine Tabelle nennt ihre Slotzahl nicht; `index into T` hat
      keine Obergrenze aus der Deklaration, und M4 ruht dort auf einer Konvention. Eine Zeile
      Grammatik, der Indextyp wird erzeugt statt geschrieben. **Vor A4** — Traversierungskosten
      brauchen eine Domaenenschranke.
- [ ] **~~A4~~ — GEBAUT (Pass 9).** Das Tor fiel zweimal in beide Richtungen: erst rechnete
      der Pass zu viel (vier Primitiven, nicht sechs), dann waren drei deklarierte Zahlen
      geraten — darunter eine Traversierung, die statt 4 096 ops **831 488** kostet.
      *(urspruenglich:)* das Kostenmodell (Pass 9). `costs`, `held`, `per_pass`, `bounded` sind heute
      Deklarationen, die niemand nachrechnet: **`retry` behauptet Terminierung, es prueft sie
      nicht.** Modell steht (`SPRACHE.md` §7), Tor ist zweiseitig gegen die deklarierten Zahlen
      der Fragmente — passt es nicht, ist zu sagen, **welche Seite falsch ist.**
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
      * **Lesen** — `FRAGMENTE.md` liest in jeder Funktion Stellen, die keine `reads`-Zeile
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
      * **Die Mutationen sind von Hand geschrieben** — 24 Stueck, je eine Regel. Ein
        Erzeuger, der alle Operatoren und Bedingungen des Pruefers systematisch verdreht,
        faende mehr. **Die 100 % sind eine Aussage ueber diese 24, nicht ueber den Pruefer.**
- [ ] **`cast` ist aus der Grammatik nie eindeutig ableitbar** (`cast = path "(" expr ")"`
      ist echte Teilmenge von `call`), und der Erreichbarkeitswaechter sieht das nicht, weil
      er auf Nichtterminalebene arbeitet. **G9.**
- [ ] **Das `forever`-Beispiel in [`SYNTAX.md`](SYNTAX.md) §8 parst nicht** — es schreibt
      `bounded 4096 cycles` statt `ops` und laesst das pflichtige `on_exceeded` weg. **G10.**
- [ ] **`SYNTAX.md` §5 sagt „Sieben Domaenen, geschlossen"** und zaehlt acht auf. **G11.**
- [ ] **Die Etiketten G1–G8 kollidieren** mit einer aelteren Messung in
      [`MESSUNGEN.md`](MESSUNGEN.md), die G1/G2/G3/G5 fuer etwas anderes vergibt.
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
- [ ] **G1 — `atomicdecl` braucht `publishes`.** Die Regel kennt es nicht, das Beispiel darunter
      benutzt es, [`SPRACHE.md`](SPRACHE.md) §11.3 verlangt es, F6 schreibt es achtmal.
      Der Uebersetzer nimmt es an und meldet `P031` — bis die EBNF nachgezogen ist.
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
- [ ] **G2 — `axiom` braucht `-> typeexpr` und `requires`.** `axiom rdtscp() -> u64 requires
      Has(RDTSCP) …` ist heute nicht schreibbar. **Betrifft die Axiomschicht**, also den groessten
      unbewiesenen Posten der Sprache.
- [ ] **G3 — `placeshift` gegen `placesuffix`: `->` ist mehrdeutig.** In
      `transition drv { ST: ACK -> ACK | DRIVER }` ist `ACK -> ACK` beides. Der Parser
      entscheidet zugunsten des Uebergangs; **die Entscheidung gehoert in die Grammatik.**
- [ ] **G4 — `entrydecl` verlangt ein Schlusskomma, das kein Beispiel schreibt.**
- [ ] **G5 — `u64::max` ist kein `path`.** Beide Segmente sind Woerter; `path = ident
      { "::" ident }` deckt es nicht, `SYNTAX.md` §2 schreibt es.
- [ ] **G6 — zwei Terminale ausserhalb der Tabelle: `O` (`costexpr`) und `version`
      (`@version`).** `pruefe-wortschatz.py` sieht beide nicht — Grossbuchstabe bzw. fuehrendes
      `@`. **Ein Befund ueber den Waechter**, dieselbe blinde Stelle wie zweimal zuvor.
- [ ] **G7 — `clobbers { }` ist nicht schreibbar.** `identlist` verlangt mindestens einen Namen;
      ein Eintritt, der nichts zerstoert, kann das nicht sagen.
- [ ] **G8 — eine `table` nennt ihre Slotzahl nicht, und das trifft M4.** `index into T` hat
      keine Obergrenze aus der Deklaration; die Schranke haengt an einem von Hand passend
      gewaehlten Indextyp (`type SlotIdx = u32 in 0 ..< NSLOTS`), und **nichts bindet die
      beiden aneinander**. „Kein ungeprueftes Indizieren" ruht an dieser Stelle auf einer
      Konvention statt auf der Sprache. Der Uebersetzer prueft Indizes deshalb nur gegen
      `[T; N]`. **Vorschlag: `table T count N { … }`, und `index into T` erbt die Schranke.**
- [ ] **Die Zaehlerregel gehoert in [`SPRACHE.md`](SPRACHE.md), sie stand in keinem Dokument:**
      *jeder Zaehler braucht eine Schranke in der Deklaration **und** eine Pruefung vor der
      Rechnung.* `u64` ohne Obergrenze ist nicht erhoehbar, und `in 0 .. GRENZE` allein reicht
      nicht — `+ 1` reicht bis `GRENZE + 1`. Dreimal am eigenen Beispielkorpus aufgeschlagen.
- [ ] **~~Die `narrow`-Vollzaehlung~~ — GEFAHREN 2026-08-14 und UNGUELTIG**
      ([`MESSUNGEN.md`](MESSUNGEN.md)). `zaehle-narrow.py` findet 513 Bereichspflichten im
      Baum und klassiert 168 nach N — **die Zahl wird nicht berichtet**, weil eine
      Handstichprobe in 3 von 5 Faellen einen Fehler des Zaehlers zeigt, alle in dieselbe
      **Die Latte „≤ 24" ist nach jeder von vier gefahrenen Lesarten VERFEHLT** (N = 150,
      168, 177, 317 gegen eine Latte von 24) — die Zahl ist ungenau, das Urteil nicht.
      * **Der methodische Befund trifft das eigene Protokoll:** seine Sprechprobe verlangte
        Trefferquote an **drei** bekannten Stellen und konnte damit die **Genauigkeit an 513**
        nicht abnehmen. *Eine Handstichprobe mit Umfang und Fehlerschranke gehoert ins
        Protokoll, vorab.*
      * **Was die Zaehlung fahrbar macht, ist der Uebersetzer selbst** — die drei fehlenden
        Reparaturen sind zusammen M1+V1–V3 auf Rust, also der Pass, der schon steht, nur fuer
        die falsche Sprache. **Erst muessen die Fragmente parsen (heute 1 von 6, Tor P2);
        dann zaehlt Gabbro seine eigenen `narrow` mit derselben Regelmenge, die es prueft.**
      * Der Zaehler bleibt im Ordner — als **Finder von Kandidaten**, nicht als Messgeraet.
- [ ] **Zwei Fragmente sind veraltet, nicht falsch:** F4 schreibt `QueueSetup(q : Virtq)`
      (`typedecl` verlangt `typelist`, nicht `params` — der Kommentar «B3» ist gegen die zweite
      Fassung geschrieben), F6 setzt ein Semikolon hinter `let … else { … }`.
- [ ] **Fuenf der neun Paesse fehlen ganz** (D1/D2, M3, M2, Paarung, costs), **zwei sind nur
      teilweise gebaut** (M1 ohne Modulaufloesung, `effects` ohne Rumpfabgleich).
      `gabbro paesse` fuehrt beide Klassen samt dem, was mit jeder durchkommt.
      **Der naechste ganze ist M3 oder D1/D2 — vorher aber die zwei Teilstuecke**, weil ein
      halb gebauter Pass eine Zusage macht, die er nicht haelt.

**Ausschliesslich Offenes** — und seit dem 2026-08-14 stimmt das wieder. Die Reihenfolge folgt
[`PLAN.md`](PLAN.md); die Etiketten P0…P7 gehoeren dem Prueferplan in
[`SPRACHE.md`](SPRACHE.md) §6 und werden hier nicht zweitvergeben.

---

## Papierschritte — keine Zeile Code. Jeder Punkt kann die These töten

> **Umbenannt 2026-08-14.** Diese Ueberschrift hiess „P0", die naechste „P1" — und
> [`SPRACHE.md`](SPRACHE.md) §6 vergibt P0…P7 an den **Prueferplan**, wo P1 die
> Grammatikvereinigung ist und nicht `check`. **Zwei Etikettensysteme mit denselben Namen
> in derselben Datei**; dieselbe Fehlerklasse wie die G-Kollision weiter oben.

- [ ] **`touches` ist zu grob** — es braucht eine Form für „verändert die Menge nur durch
      Verbrauch". Ohne sie hängt die Ordnung an einer Zusage statt an einer Bedingung.
- [ ] **Die Basisrate zählen.** Wie viele Formate hat Caprock wirklich, wie oft ändern sie sich,
      wie viele Fehler dieser Klasse pro Jahr (aus `done.md` auszählbar)? Fällt sie klein aus, ist
      das ehrlichste Ergebnis „die Falle ist zu selten für eine Sprache".

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

- [ ] **Die Zahl, die alles entscheidet:** wieviele der **17 gemessenen Logik-Pflichten** brauchen
      `by induction over`, wieviele kommen ohne aus, **wieviele brauchen rekursive `spec fn` oder
      Lemmata**? Ein einziger Fall in der letzten Spalte setzt die Decke tiefer. **Dieselbe Messung
      ist der Falsifikator der L3-Entscheidung, die auf n = 1 ruht.**
- [ ] **Das erzeugte Schema muss einmal nach Isabelle** — es ist eine Schablone im Sinne von L3 und
      damit der Posten, der die Vertrauensbasis **verkleinert**.
- [ ] **Wohlfundiertheit hängt an einer Invariante, die man beweisen will.** Die Deklaration muss
      nennen, welche — und das Mass (Zahl der Abkömmlinge) ist Voraussetzung, nicht Ergebnis.

## Aus dem Kriterium ([`BEWEIS.md`](BEWEIS.md))

- [ ] **Beide Messungen nach Logik/Klempnerei aufschlüsseln** — `delete_leaf` (3,6–6 : 1) und
      `Endpoint::call` (1,8–2,3 : 1). **Ohne diese Aufteilung ist eine Zahl kein Messwert.**
      Das ist der nächste Papierschritt.
- [ ] **Zwei Klempnerei-Pflichten stehen heute schon offen** und sind je eine Widerlegung des
      Kriteriums an ihrer Stelle: `self.queues[p]` nach `31 - leading_zeros()`
      (`caprock-sched/src/lib.rs:1996`) braucht die Datenstruktur-Invariante; und **jedes
      Verfeinerungslemma**, falls die Absenkung nicht flach genug ist.
- [ ] **Die Trennlinie an einem Grenzfall streiten.** „Nennt nur die Maschine" ist scharf genug für
      die heutigen Fälle — der erste Streitfall gehört in `BEWEIS.md`, nicht in eine Fussnote.

## Aus der Umkehrung der Frage ([`SPRACHE.md`](SPRACHE.md))

- [ ] **Die achtzehn Umwandlungen sind Behauptungen über Absenkbarkeit, keine Belege.** Jede braucht
      ihre C-Absenkung hingeschrieben — vor der Kanonisierung in [`SYNTAX.md`](SYNTAX.md).
- [ ] **`retry` mit `bounded`/`progress`/`on_exceeded` ist der Ersatz für „unbegrenztes Warten".**
      Offen: reicht eine Zahl, oder braucht es zwei Schranken (Versuche **und** Ticks)?
- [ ] **Nr. 14 verlangt eine `publishes`-Klausel an 2 231 Stellen.** Ob das trägt, entscheidet keine
      Papierübung — das ist der grösste Einzelposten der ganzen Umstellung.
- [ ] **`breaking I { … }` legalisiert eine Invariantenverletzung.** Der Preis ist Sichtbarkeit
      statt Verstecken; ob das reicht, ist unentschieden.

## Syntax — offene Entscheidungen (Einzelheiten in [`SYNTAX.md`](SYNTAX.md))

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
- [ ] **Die Axiomschicht beziffern.** Wie viele Axiome braucht ein x86- und ein aarch64-Kernel?
      **Solange die Zahl fehlt, ist „speichersicher unter A1…An" eine Form ohne Inhalt.**
- [ ] **Fortschritt/Aushungern** (Caprocks D8) fällt unter **keinen** Mechanismus. Offen, ob das
      so bleibt oder ob es einen sechsten braucht.
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
- [ ] **Der Geltungsbereich in [`SPRACHE.md`](SPRACHE.md) ist neu — Gegenprobe fahren:** ein Konstrukt suchen,
      dessen Zeile zu stark ist. Die Tabelle hat dieselbe Vorgeschichte wie die zwei
      Überschreibungen in `HISTORIE.md`.

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
| **8** | **Vier erledigte Posten als offen gefuehrt**: `by consuming` (steht seit `SYNTAX.md`:416 in der Grammatik), `vtd.rs` und `space.rs` (beide gefahren, s. `MESSUNGEN.md` P0.2/P0.3), P0.4 (gefahren, `MESSUNGEN.md`) | herausgenommen |

**Und einer, der mir gehoert:** die Berichtigung *„die Latte ≤ 24 ist verfehlt, nicht offen"*
habe ich am selben Tag als erledigt gemeldet — in `MESSUNGEN.md` war sie es, **hier nicht**.
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
- [ ] **Und die Buchfuehrung braucht einen Waechter.** Die acht Befunde oben sind **saemtlich
      maschinell pruefbar**: `[x]` in einer Datei, die „ausschliesslich Offenes" behauptet ·
      Zahlen gegen `pruefe-syntax.sh` · doppelte Themen · Etiketten gegen den Prueferplan.
      **Dieser Ordner haelt seine Grammatik mit zwei Waechtern und seinen Pruefer mit einer
      Mutationsprobe — seine Aufgabenliste mit gar nichts.**

### Wo die herausgenommenen Punkte verzeichnet sind

| Punkt | Fundstelle |
|---|---|
| P1 — Grammatikvereinigung | [`SPRACHE.md`](SPRACHE.md) §6 (Prueferplan), Waechter `pruefe-syntax.sh` |
| P2 — Lexer und Parser | [`MESSUNGEN.md`](MESSUNGEN.md), Abschnitt *P2* |
| P3 — M1 + V1–V3 | [`MESSUNGEN.md`](MESSUNGEN.md), Abschnitt *P3* |
| `revoke` auf Papier | [`MESSUNGEN.md`](MESSUNGEN.md), *P0.1* |
| P0.1b — Zeugenordnung | [`SPRACHE.md`](SPRACHE.md) §9.2 |
| `by induction over` | [`SYNTAX.md`](SYNTAX.md) §5, [`SPRACHE.md`](SPRACHE.md) Teil V |
| seL4-Aufteilung, SPARK-Leiter | [`PLAN.md`](PLAN.md) |
| `vtd.rs`, `space.rs`, P0.4 | [`MESSUNGEN.md`](MESSUNGEN.md), *P0.2/P0.3* und *P0.4* |
