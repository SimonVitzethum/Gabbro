# Gabbro — die Messungen

**Alles, was gefahren wurde, an einem Ort.** Zusammengezogen am 2026-08-14; Text unveraendert.
**Was hier nicht steht, ist nicht gemessen.**


---

# MESSPROTOKOLL fuer Messung 2 — VORAB, vor der ersten angesehenen Pflicht

**Diese Regeln stehen hier, bevor eine einzige der 17 Logik-Pflichten angesehen wurde.** Der Grund
ist die dokumentierte Schwaeche dieses Ordners: **sechs von neun Berichtigungen in
[`HISTORIE.md`](HISTORIE.md) waren Umdeutungen an einer Grenze.** Und diese Zaehlung hat ein
eingebautes **Anreizgefaelle** — Abstiegsaussagen sind billig (automatische Induktion),
Wertaussagen teuer. Wer das Kriterium waehrend der Zaehlung schaerft, schaerft es in die bequeme
Richtung.

*(Der Commit dieses Abschnitts steht im Verlauf **vor** dem Commit der Zaehlung. Das ist der
einzige Beleg dafuer, dass „vorab" mehr ist als eine Behauptung ueber die Reihenfolge.)*

## Die drei Spalten — je ein Satz, und mehr nicht

| Spalte | Entscheidungsregel |
|---|---|
| **K — durch Konstruktion** | Die Aussage der Pflicht **erwaehnt nur die Maschine**, ODER sie ist eine **deklarierte Invariante**, deren Erhaltung der Erzeuger einmal ueber der Deklaration zeigt. **Ein Mensch schreibt nichts.** — **Bedingung, mechanisch zu pruefen (s. u.).** |
| **A — Abstiegsaussage** | Die Pflicht laesst sich schreiben als *„fuer alle x in ⟨**deklarierter** Domaene⟩: P(x)"*, und P(x) folgt aus P auf den **echt kleineren** Elementen **plus genau einer deklarierten Schrittzusage**. |
| **W — Wertaussage** | Alles Uebrige: das Argument betrifft **Werte, die ein Rumpf rechnet** und die keine Deklaration festlegt. |

### Die Bedingung an K, und sie ist mechanisch statt kippbar

**„Der Erzeuger zeigt es einmal" gilt nur, wenn ALLE Mutationen des Traegers erzeugte Operationen
sind.** Eine einzige Handmutation — ein `breaking`-Block, ein Schreibpfad ausserhalb der
`ops`-Liste — und die Erhaltung ist **Menschenarbeit**, also **A oder W**.

**Je Pflicht ist das eine mechanische Frage: sind alle Schreibstellen des Traegers erzeugt?**
Die Kippregel wuerde den Fall im Zweifel fangen; **mechanisch pruefbar schlaegt kippbar**, weil es
nicht von der Sorgfalt beim Zaehlen abhaengt.

> **Nebenertrag, gratis:** dieselbe Pruefung liefert die **Liste der `breaking`-Stellen** — genau
> den Posten L3 aus der Restliste (*„`breaking`-Wiederherstellungen ohne erzeugte
> Schlussoperation"*).

## Die Kippregel — sie kippt IMMER nach W

1. **Passt eine Pflicht auf zwei Spalten, gilt die teurere.**
2. **Muesste die Abstiegsstruktur fuer den Beweis erst eingefuehrt werden** (sie ist nicht
   deklariert), ist es **W**.
3. **Braucht die Induktion eine verstaerkte Hypothese**, ist es **W** — Verstaerkung ist
   Menschenarbeit und genau der Schritt, den ein Loeser raten muesste.
3b. **„Genau eine deklarierte Schrittzusage" heisst JE ABSTIEG, nicht je Eigenschaft.** Eine
   Pflicht, deren Beweis **zwei Abstiege mit je einer Zusage komponiert**, bleibt **A**. Eine, deren
   **einzelner Induktionsschritt zwei Zusagen gleichzeitig** braucht, faellt nach **W**.
   *Diese Lesart steht hier, weil an genau dieser Stelle der erste Streitfall entstehen wird.*
4. **Nicht geteilt, nicht gerundet.** Eine Pflicht zaehlt ganz, in einer Spalte.

## Aufzeichnung, je Pflicht

`Datei:Zeile` · Spalte · **ein** Satz Begruendung. Mehr nicht — eine lange Begruendung ist ein
Kippfall, der sich verteidigt.

**Und die Regeln muessen falsifizierbar bleiben:** laesst sich eine Pflicht mit diesen drei Saetzen
**gar nicht** beurteilen, wird das als **Befund ueber die Regeln** aufgezeichnet und nicht still
nach W gedrueckt. Ein Regelwerk, das jeden Fall entscheidet, hat keine Kante.

## Die zwei Ausgaenge, ebenfalls vorab — damit gemessen und nicht gedeutet wird

| Ausgang | was er heisst |
|---|---|
| **W ≥ 9 von 17** | Die Decke der Schrittzusagen deckt eine **Minderheit**. Der 5 : 1-Handbeweispreis gilt fuer **mehr** als die angenommenen 5 %, der 0,8 : 1-Ueberschlag wandert nach oben. **Das ist kein Stimmungsdaempfer, sondern die Zahl, die `k` beziffert** — und erst sie macht den seL4-Vergleich ehrlich |
| **W ≤ 8 von 17** | Die Decke **traegt**, und die harten Schrittzusagen sind das **staerkste Stueck der Sprache** |

**Beide Ausgaenge sind gute Ergebnisse — genau weil sie hier stehen, bevor gezaehlt wird.**

## Die GEWICHTE — vorab, sonst wandert der Ueberschlag nach Belieben

**„Der 0,8 : 1-Ueberschlag wandert" ist ohne Gewichte keine Aussage.** Wohin er wandert, haengt am
**Zeilenanteil**, den die W-Pflichten tragen — und der **IPC-Fastpath wiegt anders als eine
Randpruefung**. Werden die Anteile erst **nach** der Zaehlung bestimmt, ist die Versuchung
strukturell, W-Pflichten klein zu wiegen.

**Reihenfolge, verbindlich:**

1. die 17 Pflichten mit `Datei:Zeile` auffinden (sonst ungueltig, s. u.);
2. **je Pflicht den Zeilenumfang des betroffenen Rumpfs messen** — **vor** dem ersten Blick auf die
   Spalten;
3. **dann** klassifizieren.

**Die Formel, festgeschrieben:**

```
F        = Zeilen der zehn Fragmentruempfe (Rust-Original, ohne Leerzeilen)
W_zeilen = Zeilen der Ruempfe, deren Pflicht als W gebucht ist
w        = W_zeilen / F                     -- Anteil IN DER STICHPROBE
Ueberschlag = w * 5,0  +  (1 - w) * 0,3
```

> **Der Vorbehalt gehoert in dieselbe Zeile, nicht in eine Fussnote:** die zehn Fragmente sind
> **keine Zufallsstichprobe** — sie wurden nach **Breite** gewaehlt. Die Hochrechnung von `w` auf
> den ganzen Kernel traegt diese Verzerrung, und ihre **Richtung ist unbekannt**. Der Ueberschlag
> ist damit eine **Einsetzung mit benannter Unsicherheit**, keine Messung des Kernels.

## Was die Messung UNGUELTIG macht (nicht bloss unguenstig)

Lassen sich weniger als 17 Pflichten mit `Datei:Zeile` wiederfinden, ist die **Quelle** nicht
reproduzierbar — dieselbe Protokollklasse wie die fuenf Scratchpad-Klassen, und dann wird nicht
gezaehlt, sondern erst die Grundlage hergestellt.

---


---

# P0 — die Abnahmemessung, soweit der Ordner es zuliess

## P0 GEFAHREN — soweit der Ordner es zulässt

> **EINGETRAGEN 2026-08-14.** Drei Zahlen nachgeprueft: `virtio-blk` hat **0** `Ordering::`
> (bestaetigt), `FINE_BLOCKS = 8` steht in `mmu.rs:186` (bestaetigt), und **Nebenbefund (a) ist
> berichtigt** — auf x86 ist FP **eager**, s. u.

**Gefahren am 2026-08-14** gegen den Zweig `arch/x86_64` von Caprock (frischer Clone) und den
Gabbro-Ordner (Stand `d910e18`). Drei Messungen nach Plan (ERGAENZUNG-2 §6, Stufe P0), plus
Nebenbefunde. **Vorab das Urteil, damit es niemand aus dem Text zusammensuchen muss:**

| Tor | Ergebnis |
|---|---|
| Ordering-Stichprobe (kein vierter Ausgang) | **bestanden, 36/36** — mit drei Protokollergänzungen, die keine vierten Ausgänge sind |
| Hängende Klempnerei 19 → 0 | **nicht entscheidbar**: 6 der 11 Klassen sind im Ordner dokumentiert und fallen; **5 Klassen liegen im Scratchpad, nicht im Repo** — die Messgrundlage ist nicht reproduzierbar |
| `narrow` ≤ 24 | **offen**: nur Formprüfung möglich, Vollzählung steht aus |

Nach der eigenen Reihenfolgeregel folgt daraus: **kein Prüfercode.** Der nächste Schritt ist
keine Zeile Rust, sondern die Scratchpad-Klassen ins Repo — eine Messung, die nicht im Ordner
liegt, ist nach Falle 80 eine Zahl, die jemand parallel zur Wahrheit führt.

---

### Teil 1 — die 19 hängenden Pflichten gegen die Konstrukte

Dokumentiert in `MESSUNGEN.md` sind sechs Klassen mit Fundstellen. Abgleich:

| Klasse (dokumentiert) | Konstrukt | Urteil |
|---|---|---|
| `forever`/`per_pass`-Ritual (8 Schleifen, Ticket-Spinlock ohne `try_lock`, Ed25519 über Manifest) | `on_exceeded`-Pflicht, `held <= K ops` an der Sperre (ohne sie in Dienstschleifen nicht nehmbar), eingabeabhängige Schranke | **fällt** — der Spinlock `caprock-sync:821` wird unschreibbar statt falsch beschrieben |
| `per_pass` in Zyklen (D10) | Einheit `ops`, definiert in FESTLEGUNG §7 | **fällt** |
| `publishes` an der Deklaration (671 Stellen; `FP_OWNER[core]` selbstbezüglich; Aussage-Nutzlast; virtio-`avail` volatil ans Gerät; Zähler ohne Schreibweise) | `publishstmt` am Store, `ghost static`-Reifizierung, `transition publishes`, `publishes nothing` | **fällt** — alle vier benannten Unterfälle haben eine Schreibweise |
| PTE = Zeiger UND Bitfeld → fehlende achte Domäne (`mmu.rs:1283`) | `embeds` + `walk` + `mappings of` | **fällt, mit einer Konstrukterweiterung** (s. Teil 4b) |
| 54 relationale Vorbedingungen | V2 | **fällt der Form nach** (s. Teil 3) |
| `break`/`continue` unerwähnt | `leave`/`next` mit Zielname, Verbotsliste ergänzt | **fällt** |

**Die übrigen fünf Klassen** („die übrigen fünf Klassen aus dem Bericht im Scratchpad",
`MESSUNGEN.md`) **existieren im Repo nicht.** Damit sind schätzungsweise 6 der 19
Pflichten nicht gegen die Festlegung prüfbar — nicht, weil ein Konstrukt fehlt, sondern weil die
Messung fehlt. **Das Tor „19 → 0" ist so formuliert nicht entscheidbar, und das ist ein Befund
über das Protokoll, nicht über die Sprache.** Auftrag: die fünf Klassen mit Fundstellen ins Repo,
dann diesen Teil wiederholen.

---

### Teil 2 — Ordering-Stichprobe: 36 Stellen, sechs Schichten, kein vierter Ausgang

Grundgesamtheit im Zweig: `threads/mod.rs` 872, `bringup.rs` 390, `system.rs` 184, `fuzz.rs` 112,
`caprock-sync` 53, `vtd.rs` 41, weitere darunter. Stichprobe systematisch (jede n-te Fundstelle
je Schicht), 36 Stellen gelesen und klassifiziert:

| Klasse | # | Beispiele (Datei:Zeile) |
|---|---|---|
| **Paarung: `publishes`** (Release-Store mit Nutzlast/Flagge) | 8 | `threads:2918` (CTRL_DONE), `threads:4154`, `threads:4397`, `bringup:3040` (DRV_STEP), `bringup:3211`, `system:5148` (IRQ_PENDING), `system:6505`, `sync:472` (Zeiger-Nutzlast) |
| **Paarung: `awaits`** (Acquire-Load, Nutzlast danach) | 11 | `threads:1508` (MIG_PROGRESS-Schwelle), `threads:3405`, `threads:3652`, `bringup:807`, `bringup:1435` (Bitmenge), `vtd:104/876/989/1543` (Kernel-Spiegel des Geräts), `system:5561`, `sync:488` |
| **dritte Form: `exchange`** | 6 | `colors:103` (CAS-or-Schleife → beschränkter `retry`), `system:5189` (Slot-Claim), `system:4502` (Init-Riegel), `sync:979`*, `konsole:387`, `vtd:550` (`fetch_or`-melde-einmal: Zweig auf Alt-Bit) |
| **Zähler: `publishes nothing`** | 8 | `threads:705`, `bringup:61/2634`, `system:55/2720/8790`, `sync:510/563` |
| Nutzlast-Lesen **unter erworbenem `Vis`** (relaxed nach Flaggen-Acquire) | 3 | `threads:3898` (RCAP_CLIENT_PD nach RCAP_DONE-awaits), `sync:660–675` (Berichts-Schnappschuss), `sync:641` |

**Kein vierter Ausgang.** Aber drei Klassen, die das Protokoll der Ergänzung nicht vorsah und
die dort eingetragen gehören — keine Widerlegungen, sondern **Wegfälle**:

* **K1 — „unter Sperre: das Atomic entfällt."** `system:1361` (`FP_OWNER`-Reset in
  `fp_reset_slot`, dokumentiert „unter gehaltenem SCHED") ist in Rust nur atomar, weil
  `static mut` unsicher wäre. In Gabbro ist es ein Platz unter `lock … protects` — kein Atomic,
  keine Paarung, eine Klasse weniger. Ein Teil der 2 231 Fundstellen verschwindet so.
* **K2 — Konstruktimplementierung.** `sync:979` (RW-Writer-CAS) und die Konsolen-CAS sind das
  Innere von Sperre/Konsole — in Gabbro **erzeugte** Konstrukte, kein Benutzercode. Sie zählen in
  die Schablonen-Vertrauensfläche, nicht in die Stichprobe.
* **K3 — `accumulates` mit Verbund.** `sync:572–592` ist die dokumentierte gutartige Rennstelle:
  `fetch_max` hält die Zahl korrekt, der `STELLE`-Zeiger kann vom falschen Ereignis stammen —
  im Code als hingenommen kommentiert. Per-Kern-**Paare** `(max, stelle)` mit Merge beim Lesen
  halten beides konsistent: **das Konstrukt ist an dieser Stelle strikt besser als das Original.**
  `accumulates` braucht dafür Verbundwerte in der Merge-Menge (kleine Erweiterung, benannt).

---

### Teil 3 — `narrow`: nur die Formprüfung war fahrbar

Die 255/102/54-Zählung stammt aus dem Ordner; meine Stichprobenziehung war zu dünn für eine
eigene Proportion (der reguläre Ausdruck fing eine Handvoll Stellen, z. B. `alloc.rs:133`
`if start >= r.base && end <= zone_end` — lehrbuchhaft V2). **Der Form nach** deckt V2 alle 54
relationalen Fälle: geprüfter Vergleich zweier Stellen, Differenz im Zweig. **Ungetestet und als
Risiko benannt:** der Fall, in dem Prüfung und Verwendung **in verschiedenen Funktionen** liegen
— V-Fakten sterben an der Funktionsgrenze, und ob dieser Schnitt im Baum vorkommt (Prüfung im
Rufer, Subtraktion im Gerufenen), entscheidet, ob `requires a >= b` als Vertrag reicht oder ob
die 24er-Messlatte reißt. **Die Vollzählung ist der offene Rest von P0** und gehört mit einem
besseren Muster gefahren (die Ordner-Lektion: „die Korpusgröße hängt am regulären Ausdruck").

---

### Teil 4 — Nebenbefunde, zwei davon mit Entscheidungsbedarf

**(a) BERICHTIGT beim Eintragen — auf x86 ist es EAGER, und der Konflikt liegt auf der anderen
Architektur.**

`kernel/src/system.rs:1215` sagt woertlich: **`x86_64: EAGER. Der Ausloeser des Wechsels ist der
WECHSEL, nicht der erste Zugriff.`** Die Begruendung darunter ist **exakt die der Ergaenzung**:
*„Lazy-FP ueber eine PD-Grenze ist auf x86 CVE-2018-3665 … fuer ein Cap-System, dessen
Verkaufsargument Isolation ist, waere das ein Widerspruch im Kern des Anspruchs."* `CR0.TS` bleibt
dauerhaft aus, ein `#NM` ist per Definition ein Kernelfehler.

**Die Namen haben in die Irre gefuehrt:** `FP_OWNER`, `fp_switch_count` („Lazy-FP-Owner-Wechsel")
und der Doc-Kommentar bei `:1204` beschreiben den **aarch64**-Pfad — `CPACR_EL1` ist ein
ARM-Register. Das ist dieselbe Klasse, die dieser Ordner fuehrt: **einen Namen gelesen statt die
Sache.**

**Der Konflikt bleibt, aber verschoben und kleiner:** Caprock ist **eager auf x86, lazy auf
aarch64**. Das Dekret „eager only" trifft damit die **aarch64**-Seite, wo das
CVE-2018-3665-Argument in dieser Form nicht greift. Zu entscheiden ist also nicht „Dekret gegen
Baum", sondern: **gilt die Eager-Pflicht je Architektur oder global?**

*Die urspruengliche Fassung des Befundes:*
**(a-alt) ERGAENZUNG-2 §3.4 kollidiert mit dem gemessenen Code: Caprock x86 fährt Lazy-FP.**
`system.rs` führt `FP_OWNER` je Kern und zählt „abgeschlossene **Lazy**-FP-Owner-Wechsel"
(`fp_switch_count`). Die Ergänzung dekretierte eager-only („lazy ist die CVE-Falle und wird
nicht angeboten"). Zwei Ausgänge, beide mit Preis: eager erzwingen (512-Byte-`fxsave` je
Kontextwechsel, Umbau des gemessenen Schemas) **oder** Lazy als Konstrukt mit Besitzzeugen
(`FpOwner(core)`-Übergabe als Paarung — die Stichprobe zeigt, dass die Zugriffe heute teils
unter Sperre laufen, K1) plus einer Sonde gegen die Leckklasse. **Nicht hier zu entscheiden;
als Konflikt eingetragen.** Ein Dekret, das dem gemessenen Bestand widerspricht, ohne ihn zu
nennen, wäre die Überschreibungsform auf Architekturebene.

**(b) W^X ist formulierbar, aber das `mappings`-Tupel braucht Ebenenindizes.** Der echte Audit
(`vspace_wx_ok`) schließt die geteilten Kernel-PTs aus (`i >= FINE_BLOCKS`). Die Invariante
heißt also `forall m in mappings of vspace: m.index[2] >= FINE_BLOCKS => !(m.user && m.writable
&& !m.nx)` — das Tupel muss je Ebene den Slot-Index tragen. Eine Zeile in der
`walk`-Domänendefinition, hier eingetragen statt still ergänzt.

**(c) Die `programs/`-Klasse (4/4 hängend) bestätigt die Deckung von der anderen Seite:**
`virtio-blk/main.rs` enthält **null** Atomics — die Dienstschleife hängt an volatilen
DMA-Stores und der `forever`-Form, also genau an `transition publishes` (F5) und §9.3. Die
Klassifikation der Ergänzung trifft die Realität des Programms.

---

### Was jetzt zu tun ist, in Reihenfolge

1. **Die fünf Scratchpad-Klassen ins Repo** (mit Fundstellen), dann Teil 1 wiederholen — vorher
   ist das 19→0-Tor unentscheidbar und bleibt es.
2. **Die `narrow`-Vollzählung** mit robusterem Muster, samt gezielter Suche nach dem
   Funktionsgrenzen-Schnitt.
3. **Lazy-FP entscheiden** (4a) — es ist die einzige Stelle, an der ein Ergänzungsdekret dem
   gemessenen Baum widerspricht.
4. Protokoll der Ordering-Klassifikation um K1–K3 ergänzen; `accumulates` um Verbundwerte,
   `mappings` um Ebenenindizes.
5. ~~**Erst danach P1**~~ — **P1 ist bereits gefahren** (2026-08-14, nach dem Stand, gegen den
   dieser Bericht geschrieben wurde): Festlegung und alle drei Ergaenzungen sind in der EBNF,
   **119 Regeln, 0 offen, 189 Terminale gegen 189 Wortschatzwoerter**, beide Waechter gruen.
   **Die Regel „keine Prueferzeile vor Tor P1" gilt unveraendert weiter** — und sie ist nicht
   gebrochen worden.


---

# Der Logik/Klempnerei-Split

## Der Logik/Klempnerei-Split — erstmals gemessen, und er faellt gegen den Entwurf

> **W7-KEHRAUS 2026-08-15: UNBELEGT — ZU ERSETZEN.** Die Aufteilung der **74** ist **nicht im
> Ordner**; was dasteht, ist das Aggregat (74 / 17 / 57 / 19 / 1) und eine Bereichstabelle
> ohne Fundstellen. Der ganze Abschnitt fuehrt **eine** `Datei:Zeile`, und die gehoert zur
> Eager-FP-Frage. **Die 17er-Zaehlung ist daran am 2026-08-15 ungueltig geworden** (s. dort),
> und `delete_leaf` ist beim Nachzaehlen von **3,6–6 : 1** auf **1,75 : 1** gekippt.
> *Nicht geloescht: die Markierung ist der Befund.*

**2026-08-14.** Zehn handuebersetzte Fragmente aus acht Bereichen, **74 Beweispflichten** einzeln
zugeordnet. Das Kriterium aus [`BEWEIS.md`](BEWEIS.md) hatte bis dahin **nie** eine Messung
gesehen.

---

### Das Aggregat

| | |
|---|---|
| Beweispflichten gesamt | **74** |
| **Logik** (erwaehnt die Sache) | 17 |
| **Klempnerei** (erwaehnt nur die Maschine) | 57 |
| **davon bleibt beim Programmierer haengen** | **19 — also 33 %** |
| Logik-Pflichten, die **gar nicht formulierbar** sind | **1** |

**Nach Bereich:** Parser 1/9 haengend, IPC 1/8 — **die halten**. Scheduler + SMP 5, MMU 2 plus ein
Ausdrucksloch. **`programs/` bricht vollstaendig: 4 von 4**, alle an der Dienstschleife von
`virtio-blk`.

> **Damit ist die Zusage „alles ausser dem Logikbeweis faellt durch Konstruktion" an 19 benannten
> Stellen widerlegt.** Nach der Entscheidung vom 2026-08-14 ist das **kein Abbruch, sondern
> Eskalation**: fuer jede der elf Klassen ist das Konstrukt zu entwerfen, das sie abnimmt.

---

### Die drei Verdachtsstellen — alle drei bestaetigt

#### `per_pass bounded n cycles` ist ein Ritual

96 Endlosschleifen im Baum. **Fuer acht ist die Zusage nachweislich falsch:** ihr Durchgang enthaelt
einen Ticket-Spinlock ohne Schranke (`crates/caprock-sync/src/lib.rs:821` — **nachgeprueft: der
Crate hat kein `try_lock`, null Fundstellen**) oder Ed25519 ueber ein Manifest beliebiger Laenge.

**Drei Fehler in einem Konstrukt, und alle drei stehen im eigenen Register:**

1. **Gabbro sagt nirgends, ob Sperrwartezeit in `per_pass` zaehlt.** Zaehlt sie, ist die Klausel
   fuer **jede** sperrende Schleife unerfuellbar; zaehlt sie nicht, sagt sie **nichts ueber
   Latenz** — also nichts.
2. **`retry` hat `on_exceeded` als Pflicht, `forever` hat es nicht.** Eine Schranke ohne benannten
   Ueberlauf — **D11 woertlich**: „wer eine Kapazitaet einfuehrt, muss den Ueberlauf BENENNEN".
3. **Das einzige `forever`-Beispiel steht auf `cycles`** — der Groesse, die Caprock bei **D10** als
   unbrauchbar gemessen hat („eine Iterationszahl ist eine Eigenschaft des Programms, eine
   Zeitmessung nicht").

#### `publishes` steht an der falschen Stelle

671 Deklarationen. **Die Klausel sitzt an der Deklaration, die Nutzlast entsteht am Store.**

* `FP_OWNER[core]` veroeffentlicht `FP_STATES[<die tid, die es selbst traegt>]` — **selbstbezueglich**,
  und der Kernindex **existiert an der Deklaration nicht**.
* `STALE_STEP.store(2)` veroeffentlicht „in der `senders`-Queue steht ein toter Eintrag" — **kein
  `place`**, sondern eine Aussage.
* **Die sicherheitskritischste Veroeffentlichung im Baum ist gar kein Atomic:** `Queue::publish`
  (virtio-`avail`-Index) ist ein volatiler Store in eine DMA-Region **an ein Geraet**.
* Fuer reine Zaehler gibt es **keine korrekte Schreibweise**: die Prosa sagt „Pflicht", die EBNF
  sagt optional, und `placelist` hat **kein leeres Wort**.

#### Eine echte Eigenschaft faellt aus allen sieben Domaenen

**W^X ueber eine zweistufige Seitentabelle** (`crates/caprock-hal/src/x86_64/mmu.rs:1283`, **im
Kernel gefahren**). Die innere Quantifizierung braeuchte eine Domaene ueber einem **dereferenzierten,
gerechneten Zeiger**; `descendants of` folgt der Parent-Relation *einer* Tabelle, und
`reaches … via` ist ein Praedikat, kein Domaenenkonstruktor.

> **Die Ursache liegt eine Ebene tiefer: ein PTE ist zugleich Zeiger UND Bitfeld**, und dafuer hat
> Gabbro kein Konstrukt. Das ist die Wurzel, nicht die fehlende achte Domaene.

---

### Und die Subtraktionsmessung kippt mein `narrow`-Ergebnis

**[`MESSUNGEN.md`](MESSUNGEN.md) ist damit ueberholt, und der Fehler ist meiner.**

| | meine Messung | die Gegenmessung |
|---|---|---|
| Korpus | 94 (25 `-=`, 69 `a - b`) | **255** (27 `-=`, 228 `a - b`) |
| flusssensitiv | 4 (`leading_zeros`) | **102** |
| **davon relational** (`if a >= b { a - b }`) | **0** | **54** |

**Entscheidend ist nicht die Zahl, sondern die Form.** Ein `if a >= b { a - b }` ist eine
**Beziehung zwischen zwei Variablen**, und die kann ein Intervalltyp **nicht tragen** — er sagt
etwas ueber *einen* Wert. Die vier `leading_zeros`-Stellen, aus denen ich *„M1 braucht genau eine
Flussregel, keine allgemeine Inferenz"* abgeleitet habe, sind **alle vier einstellig**: meine
Stichprobe enthielt **null** relationale Faelle.

> **Das ist das Hausmuster, angewandt auf mich:** ein Satz, der wahr waere, haette ich den
> Geltungsbereich nicht stillschweigend erweitert. Ich habe aus einer Stichprobe, die die harte
> Form **strukturell ausschloss**, auf alle Faelle geschlossen. **Offener Punkt 1 in `SYNTAX.md`
> geht von `[x]` zurueck auf `[ ]`.**

*Nachgezaehlt: mein engeres Muster ergibt weiterhin 25 und 65. Die Korpusgroesse haengt am
regulaeren Ausdruck; beide Zahlen sind Untergrenzen verschiedener Muster. **An der Form aendert das
nichts** — 54 relationale Faelle sind 54, wie immer man den Nenner zaehlt.*

---

### Zwei Funde, die nicht im Auftrag standen

**`keeping` toetet Falle 4 nicht — es BENENNT sie.** In meinem eigenen `device`-Beispiel ist die
Bitliste falsch: **GCMD-Bit 30 ist `SRTP`** (nachgeprueft: `const GCMD_SRTP: u32 = 1 << 30;`,
`vtd.rs:58`) — ein **Ein-Schritt-Kommando**, kein Zustandsbit. Jedes Kommando haette „Set Root Table
Pointer" neu ausgeloest. Und `IRE`/`QIE`, die Caprock mitfuehren **muss**, fehlen.

> **Der Beleg gegen das Konstrukt ist, dass sein Erfinder es im eigenen Beispiel falsch gefuehrt
> hat.** Die Liste richtig zu bekommen **ist** das urspruengliche Problem; `keeping` verschiebt es
> von der Schreibstelle in die Deklaration. Das ist besser — **einmal statt je Aufruf** —, aber es
> ist Verschiebung, nicht Beseitigung, und genau so gehoert es dazustehen.

**Es gibt kein `break` und kein `continue`.** `breaking` ist das Invariantenkonstrukt; die Liste
„Was es absichtlich nicht gibt" nennt `while`, `for`, `goto` — **`break` nicht**. Vermutlich
versehentlich, und es trifft genau den Fall, den §8 als `forever`-Beispiel fuehrt: **die
Hauptschleife eines Servers**.

---

### Der Streitfall, den die Trennlinie nicht entscheidet

`depleted_count -= 1` ist **Klempnerei** (ein Unterlauf) — aber sie faellt **nur** ueber die
Invariante *„der Zaehler ist die Zahl der erschoepften Konten"*, und die ist **Logik**.

**Hier wird eine Invariante nicht ERHALTEN, sondern BENUTZT**, um eine Bereichspflicht zu erledigen.
[`BEWEIS.md`](BEWEIS.md) kennt diesen Fall nicht.

- [ ] **Eine dritte Spalte, oder „faellt durch Konstruktion" wird zur bequemen Buchung.** Vorschlag:
      **Klempnerei, getragen von Logik** — sie faellt, aber **nur so weit, wie die Invariante
      bewiesen ist**. Damit ist sie kein Freibetrag mehr, sondern haengt sichtbar an einem
      Logikposten. *Das ist der erste Streitfall der Trennlinie, und er gehoert hierher statt in
      eine Fussnote.*

---

### Was jetzt zu entwerfen ist — elf Klassen, Eskalation statt Abbruch

- [ ] **`forever` braucht `on_exceeded`** wie `retry`, und eine Aussage darueber, **ob Sperrzeit in
      `per_pass` zaehlt.** Ohne beides ist die Klausel ein Ritual.
- [ ] **`per_pass` in einer anderen Groesse als `cycles`** — D10 hat Zeit als Mass verworfen.
- [ ] **`publishes` an den STORE**, nicht an die Deklaration; eine Form fuer „nichts" und eine fuer
      **volatile Stores an ein Geraet**, die keine Atomics sind.
- [ ] **Ein Konstrukt fuer „Zeiger UND Bitfeld"** (PTE). Daraus folgt die achte Domaene von selbst.
- [ ] **Eine Form fuer relationale Vorbedingungen** (`a >= b`), die ein Intervalltyp nicht tragen
      kann. **Das ist der grosse Posten** — 54 Fundstellen.
- [ ] **`break`/`continue`** entscheiden: aufnehmen oder ausdruecklich verbieten.
- [ ] Die uebrigen fuenf Klassen aus dem Bericht im Scratchpad.

---

### Der Gegenentwurf, zweite Runde — 15 Regeln, und drei Selbstwiderlegungen

Parallel hat der Vervollstaendiger die Grammatik gegen den ganzen Baum gehalten (1 896 Zeilen).
**Was davon SOFORT eingearbeitet ist**, weil es einen Fund beantwortet:

| Regel | ersetzt | Grund |
|---|---|---|
| `mirrors GCMD from GSTS` **je Geraet** | `keeping` **je Uebergang** | 18 handgefuehrte Eintraege, wo `vtd.rs` **eine** Konstante hat — das Konstrukt war die Falle, gegen die es gebaut war |
| `publishes nothing`, `relaxed` | `publishes` als Prosa-Pflicht und EBNF-Kuer | 41 % der Atomics waren unschreibbar; `relaxed` fehlte bei **779** Vorkommen, `seq` stand im Wortschatz bei **0** |
| `old`, `offset_into`, `never` als **Produktionen** | Woerter ohne Grammatik | **`offset_into` stand in der Wortschatztabelle und in keiner Produktion** — die ELF-Absenkung war damit nicht ungeprueft, sondern **unaufschreibbar** |

**Drei Befunde, die der Vervollstaendiger gegen sich selbst gefunden hat:**

1. **„Barrieren gehoeren zum Adressraum" ist zur Haelfte falsch.** In `Queue::publish` liegen beide
   Stores im **selben** Raum (`dma`) und brauchen trotzdem eine Barriere. Berichtigt: **der Raum
   bestimmt die STAERKE, `publishes` den ORT.**
2. **`accumulates max` (Wasserstandsmarke, 213 RMW-Stellen) senkt sich auf eine unbegrenzte
   CAS-Schleife ab** — **der Uebersetzer emittiert, was die Sprache verbietet.** Unentschieden, und
   es ist der erste Kandidat fuer „zwei geforderte Eigenschaften widersprechen einander".
3. **Sein staerkstes Fragment und seine schwaechste Annahme sind dasselbe Konstrukt:** die
   Phasenverfolgung am `device` traegt nur bei *einem* Besitzer — und traegt damit genau dort
   **nicht**, wo Falle 4 sitzt (VT-d, geteilt ueber alle Kerne).

**Drei offene Punkte hat er geschlossen, mit Zahlen:** Generizitaet (**16 von 62** echt, alles auf
`Slab`/`SpinLock` — beide Konstrukte existieren; **0 von 6** Traits polymorph) · Versionsevolution
(**0 von 11** Migrationen ⇒ **Absage**) · `costs` (Zyklen entfallen, **Operationen** werden
hergeleitet — D10 woertlich).

**Sein schwaechster Teil, selbst benannt:** `abi { … }` — **5 von 25 neuen Woertern fuer eine Regel,
die null bezahlte Fallen toetet**, und **3 von 168** `asm!`-Stellen angesehen. Eine Skizze, keine
Regel.


---

# P0.1 — revoke auf Papier

## P0.1 — `revoke` auf Papier. Ergebnis: BEDINGT, und die Bedingung ist ein fehlendes Konstrukt

**Gefahren am 2026-08-13**, gegen `crates/caprock-cap/src/space.rs:619` (echter Code, nicht
Skizze). Der Ausgang war weder das vorbereitete Ja noch das vorbereitete Nein.

---

### Was zu zeigen war

`revoke(s)` löscht den ganzen Teilbaum unter `s`. Drei Pflichten:

| | Pflicht |
|---|---|
| **T** | **Terminierung** |
| **N** | **Nachbedingung:** danach hat `s` keine Abkömmlinge |
| **I** | **Invariantenerhaltung:** `cdt_wellformed` und Kettenendlichkeit gelten weiter |

Der echte Code ist eine äussere Schleife („solange `s` ein Kind hat: zum Blatt absteigen, Blatt
löschen") mit **zwei** Schrittgrenzen und einem gezählten Abbruch, wenn der Teilbaum nicht
baumförmig ist.

---

### Erster Versuch: als `traverse`. **Scheitert, und zwar sauber**

```gabbro
traverse victims over subtree(s) by unvisited touches writes slots { delete(it); }
```

**Geht nicht.** `by unvisited` setzt eine **stabile** Menge voraus — der Fortschritt ist „noch nicht
besucht", und die besuchte Menge wächst gegen eine feste Grundmenge. `revoke` **verkleinert die
Menge, über die es läuft**. Eine Traversierung, die ihre eigene Grundmenge mutiert, ist mit
`over`/`by` nicht beschreibbar.

**Damit ist die Vorhersage aus `PLAN.md` bestätigt: `revoke` passt nicht in die vorhandenen
Konstrukte.**

### Zweiter Versuch: als `loop … variant`. **Geht, kostet aber einen HANDBEWEIS**

```gabbro
loop { let leaf = descend_to_leaf(s); delete_leaf(leaf); } variant descendants(s)
```

`variant descendants(s)` ist schreibbar. Dass er **streng fällt**, ist es nicht: dafür braucht es
*„`delete_leaf(l)` mit `l ∈ descendants(s)` verkleinert `descendants(s)` um genau 1"* — ein Lemma,
das jemand hinschreibt. **Das ist genau der Ausgang, der 0,5 : 1 ausser Reichweite bringt.**

---

### Dritter Versuch: ein Konstrukt, das FEHLT — und dann fällt alles heraus

```gabbro
traverse victims over subtree(s) by consuming touches writes slots
{ delete_leaf(it); }        -- `it : linear Member(subtree(s))`
```

**`by consuming`**: die Laufvariable ist ein **linearer Zugehörigkeitszeuge**, und der Rumpf **muss**
ihn verbrauchen. Wer ihn nicht verbraucht, übersetzt nicht — M2, ohne Sonderregel.

| Pflicht | wie sie fällt |
|---|---|
| **T** | die Menge ist durch `NSLOTS` beschränkt (M1) und schrumpft je Runde um mindestens eins, weil ein linearer Zeuge verbraucht wird. **Kein Variant je Programm — das Lemma fällt EINMAL im Erzeuger an** |
| **N** | die Schleife endet, wenn die Menge leer ist. **Aber**: „Zeugenmenge leer ⇒ keine Abkömmlinge" ist eine Entsprechung, die unter **jeder** Mutation halten muss — **das IST die Schleifeninvariante**, verschoben in die erzeugte Geistertheorie |
| **I** | `delete_leaf` ist eine **erzeugte** Operation des `table`-Konstrukts (Zuschnitt (c)). Der Erzeuger zeigt **einmal**, dass das Aushängen eines Blattes `child_points_back` und Kettenendlichkeit erhält — über der Deklaration, nicht je Aufrufstelle |

> **BERICHTIGUNG, und sie betrifft die Formulierung aller drei Zeilen.** Die erste Fassung schrieb
> bei **T** „kein Variant, kein Lemma" und bei **I** korrekt „der Erzeuger zeigt einmal" —
> **dieselbe Aussage, eine Formulierung ehrlich, die andere nicht.** Es ist **Amortisierung, keine
> Beseitigung**: je Programm null, **je Konstrukt nicht null**. Als absolute Aussage wäre „kein
> Lemma" Überschreibung Nr. 4 gewesen, in genau der Form, die `HISTORIE.md` führt.
>
> **Die Folge ist architektonisch:** die **Geistertheorie-Schablone wird die vertrauenskritischste
> Komponente der Sprache** — dort lebt die strukturelle Induktion, und geprüft wird sie vom
> **unverifizierten** Gabbro-Kern. Sie steht damit neben der Axiomschicht, nicht darunter.

**Und ein vierter Posten fällt weg, der im echten Code Zeilen kostet:** der Zweig „Teilbaum ist
nicht baumförmig" wird **unerreichbar**. `subtree(s)` ist nur definiert, wenn die Invariante gilt;
gilt sie, gibt es den Zyklus nicht. Die zwei Schrittgrenzen, der `note_overrun`, der `break` —
alles Folgen davon, dass die Invariante im Rust-Code **nicht** getragen wird.

---

### Das Loch in Versuch 3: der Zeuge trägt ZUGEHÖRIGKEIT, `delete_leaf` braucht BLATTHEIT

`it : linear Member(subtree(s))` sagt **„war im Teilbaum"**. Löschen darf man einen Slot aber nur,
wenn er **jetzt** ein Blatt ist — sonst verwaisen seine Kinder. Und Blattheit **ändert sich mit
jeder Löschung**.

**Ein linearer Zeuge, der beim Aufbau der Geistertheorie entsteht, kann eine mutierende Eigenschaft
nicht in die Zukunft tragen.** Der Rust-Code hat sein `descend_to_leaf` **in** der Schleife aus
genau diesem Grund; die Skizze oben hat es stillschweigend fallen lassen. `{ delete_leaf(it); }`
typisiert so **nicht**.

---

### P0.1b — der vierte Versuch: woher kommt die Ordnung, und wer erhält sie?

**Zwei Auswege, und nur einer trägt.**

#### (B) `delete_leaf` bekommt eine Blattheits-Vorbedingung — VERWORFEN

Dann braucht es einen **zweiten** Zeugen, und ihn herzustellen ist der Abstieg — also eine
Traversierung **im Rumpf**, über dieselbe mutierende Struktur. **Das Verschränkungsproblem aus
Versuch 1 kehrt eine Ebene tiefer wieder.**

#### (A) Die Zeugen kommen in POST-ORDER — trägt, mit einer scharfen Bedingung

In der Nachordnung eines Waldes gilt: **wenn der `k`-te Zeuge an der Reihe ist, sind alle seine
Abkömmlinge die `k-1` vorherigen — also schon verbraucht.** Er *ist* in diesem Augenblick ein Blatt.

| | |
|---|---|
| **Bedingung** | der Rumpf darf die Menge **ausschliesslich durch Verbrauch** verändern. Jede andere Schreibung auf `slots` zerstört die Ordnung. `touches` muss das ausdrücken können — heute kann es nur „schreibt `slots`", was zu grob ist |
| **Kosten zur Laufzeit** | **keine zusätzlichen.** Die Nachordnung ist Geist; das Erzeugnis steigt weiterhin je Runde zum linken Blatt ab — **exakt der vorhandene Rust-Code.** `by consuming` senkt sich also auf `descend_to_leaf` + `delete_leaf` ab |
| **Kosten im Beweis** | das Lemma *„in Nachordnung ist das `k`-te Element ein Blatt, nachdem die ersten `k-1` entfernt wurden"* — **strukturelle Induktion über den Baum** |

> **Damit steht die ursprüngliche Vorhersage wieder da, nur an einer anderen Stelle.** `PLAN.md`
> sagte: die Korrektheitsbedingung von `revoke` ist strukturell, also Induktion. **Sie ist nicht
> verschwunden — sie ist in die Geistertheorie-Schablone gewandert**, wo sie einmal statt je
> Programm anfällt. Das ist der (c)-Handel, und er ist real; er ist nur kein Zauber.

- [ ] **`touches` ist zu grob.** Es braucht eine Form für „verändert die Menge **nur** durch
      Verbrauch" — sonst hängt die Ordnung an einer Zusage statt an einer Bedingung. **Das ist ein
      Syntaxposten, der aus diesem Test stammt und vor der Kanonisierung entschieden sein muss.**

---

### Das Ergebnis, in drei Sätzen

1. **`revoke` ist ausdrückbar — aber nicht in den Konstrukten, die `SYNTAX.md` heute nennt.**
   Es fehlt genau eines: **die verbrauchende Traversierung**, und sie braucht **Post-Ordnung** plus
   eine `touches`-Form, die es noch nicht gibt.
2. **Mit ihr fallen T, N und I je PROGRAMM auf null** — nicht auf null überhaupt. Sie fallen
   **einmal im Erzeuger** an, als strukturelle Induktion in der Geistertheorie-Schablone.
3. **Der Preis ist Vertrauen, nicht Laufzeit:** zur Laufzeit senkt sich das Konstrukt auf den
   vorhandenen Rust-Algorithmus ab. Aber die **Schablone wird die vertrauenskritischste Komponente
   der Sprache**, geprüft vom unverifizierten Kern.

---

### Der Nebenbefund ist wichtiger als das Ergebnis: die ZÄHLREGEL ist kaputt

Die Geistertheorie hat **keine Laufzeitwirkung**. Nach der Zählregel aus `PLAN.md` — *Spezifikation
ist, was der Übersetzer vor der Codeerzeugung löscht* — zählt sie damit **in den Zähler**.

> **Dann verschlechtert der Gold-Mechanismus die Kennzahl, je besser er wirkt.** Zuschnitt (c)
> erzeugt mehr Geistercode, also mehr „Spezifikation", also ein schlechteres Verhältnis — während
> die Arbeit, die ein Mensch leistet, sinkt.

Das ist dieselbe Klasse wie „ein Zähler, der VERSUCHE zählt, beantwortet die Frage nach der WIRKUNG
nicht". Die Regel muss lauten:

> **Spezifikation ist, was ein MENSCH schreibt und was der Übersetzer vor der Codeerzeugung löscht.**
> Erzeugter Geistercode ist weder Spezifikation noch Code — er ist **Ausgabe**.

**Gefunden hat das der Papiertest, nicht das Gegenlesen** — und er hat einen halben Tag gekostet
statt der Wochen, die eine Messung am Übersetzer gekostet hätte.

---

### Was das NICHT zeigt

* **Ein Rumpf ist kein Kernel.** `revoke` fällt heraus, weil seine Nachbedingung *„die Menge ist
  leer"* ist — eine Aussage über **Zugehörigkeit**, und Zugehörigkeit ist genau das, was ein
  linearer Zeuge trägt. Der IPC-Fastpath hat eine Nachbedingung über **Werten** (die Nachricht kam
  an, die Antwortpflicht liegt beim richtigen Thread). **Nichts hier zeigt, dass die auch fällt.**
* **Die 10 %-Annahme bleibt unbelegt.** Sie trägt die ganze bedingte Ja-Antwort und ist die am
  wenigsten gestützte Zahl des Ordners — gemessen sind **68,8 % algorithmischer Rest**.
* **Zuschnitt (c) ist damit erstmals empirisch gestützt**, nicht nur vom Ziel gefordert: ohne
  erzeugtes `delete_leaf` fällt Pflicht **I** auf einen Handbeweis zurück.

---

### Was daraus folgt

- [ ] **`by consuming` in `SYNTAX.md` aufnehmen** — mit der Geistertheorie, die es verlangt, und
      der offenen Frage, welche `over`-Mengen Zeugen liefern können.
- [ ] **Die Zählregel in `PLAN.md` berichtigen** (Mensch-geschrieben, nicht bloss gelöscht).
- [ ] **P0.4 (neu): denselben Test am IPC-Fastpath.** Er ist der Fall, für den `revoke` nichts
      aussagt — und er entscheidet die 10 %-Annahme, nicht dieser hier.


---

# P0.2 und P0.3 — device und space.rs

## P0.2 und P0.3 — beide Tore GEFALLEN

**Gefahren am 2026-08-13** von einem unabhaengigen Pruefer, gegen echten Caprock-Code, nur auf
Papier. Bericht und Artefakte im Sitzungs-Scratchpad (`vtd.gabbro`, `delete_leaf.gabbro`,
`delete_leaf.beweis`). Die Zahlen unten habe ich nachgezaehlt, wo sie tragen.

---

### P0.2 — `vtd.rs` als `device`-Block. **Gefallen, und der Grund ist der Nenner**

Der Block: **96 Deklarationszeilen** (15 Register, 5 `transition`, 2 `reason`, 3 `format`,
3 `assume`). `vtd.rs`: **1 448 Zeilen** ohne Leerzeilen, davon **577 Prosa** (nachgezaehlt).

| Faktor gegen … | Wert | Tor ≥ 5 | beantwortet die Frage … |
|---|---|---|---|
| die **ganze Datei** (1 448) | **15,1** | bestanden | „wie viel kleiner ist eine Deklaration als eine Datei, die groesstenteils etwas anderes ist" — **fuer die These bedeutungslos** |
| das, was er **deckt** (306) | **3,2** | **GEFALLEN** | die eigentliche Frage |
| gedeckten **Code** ohne Prosa (191) | **2,0** | **GEFALLEN** | dieselbe, schaerfer |

> **Der Faktor 15 ist genau das Artefakt, gegen das das Tor gebaut war.** Wer ihn meldet, misst die
> Groesse des ungedeckten Restes und nennt sie Knappheit.

**Ungedeckt: 1 141 von 1 448 Zeilen = 78,9 %** (beim Code 78,1 %). Der Pruefer hat die Datei in
66 Bloecke zerlegt und lueckenlos klassifiziert, **zugunsten von Gabbro gerechnet**: ~185 Zeilen
Mehrinstanz-Logik, ~150 Queued Invalidation, ~168 Second-Level-Seitentabellen, ~151 IRTE-Vergabe,
~145 Fehlerbuchhaltung, ~330 Hochlauf.

**Eine ehrliche Gabbro-Fassung der ganzen Datei: ≈ 1 353 Zeilen — Faktor 1,07.**

**Damit ist die Knappheitsthese in der Form widerlegt, in der sie im Plan stand.** `device` ist auf
seinem Gebiet doppelt so knapp wie Rust, nicht fuenffach — und sein Gebiet ist ein Fuenftel der
Datei. Registerlayout ist das Leichte; Warteschlangen, Invalidierung und Fehlerbuchhaltung sind Code.

---

### P0.3 — `delete_leaf` zweimal. **Ueber der Abbruchmarke**

| | Zeilen |
|---|---|
| Gabbro-Code | 63 |
| Spezifikation (nach der Regel: steht in der Quelle, wird vor der Codeerzeugung geloescht) | 71 |
| **Verhaeltnis** | **1,13 : 1** (enger Nenner: 1,69 : 1) |

**Aber die Zahl ist eine Untergrenze, und das ist der eigentliche Befund:** sechs Beweisposten sind
Stuempfe (`{ ... }`). Ausgeschrieben liegt das Verhaeltnis bei **3,6–6 : 1** — **ueber der
Abbruchmarke von 3 : 1**. Dazu: **31 von 134 Zeilen (23 %) sind heute gar nicht schreibbar.**

---

### Das Aggregat — und es erledigt die 10 %-Annahme

Ueber **67,3 % des Baums (44 832 Zeilen)**, drei Toepfe:

| | Anteil |
|---|---|
| **(a)** ausdrueckbar, Beweispflicht faellt durch Konstruktion | **15,1 %** |
| **(b)** ausdrueckbar, braucht handgeschriebene Spezifikation | **65,1 %** |
| **(c)** heute nicht ausdrueckbar | **19,8 %** |

`PLAN.md` rechnete mit **10 %**, die handgeschriebene funktionale Beweise brauchen. Gemessen sind
es **65,1 %** — und die Zahl landet neben den **68,8 %** algorithmischem Rest, die derselbe Plan
selbst fuehrt. **Die Annahme, die die ganze bedingte Ja-Antwort trug, ist nicht haltbar.**

Bei 65 % zu 5 : 1 liegt das Mittel nicht bei 0,8 : 1, sondern **jenseits von 3 : 1** — also an der
Abbruchmarke.

---

### Was das heisst, ohne Beschoenigung

1. **Zwei der drei billigen Papiertore sind gefahren, beide gingen gegen den Ordner.**
2. **Die 0,5 : 1-These ist in ihrer bisherigen Begruendung tot.** Sie ruhte auf „10 % brauchen
   Handbeweis"; gemessen sind 65 %.
3. **Was ueberlebt, ist kleiner und benennbar:** auf den 15,1 %, wo die Beweispflicht durch
   Konstruktion faellt, tut sie es. Das ist ein echter Gewinn — aber es ist ein Fuenftel des
   Kernels, nicht der Kernel.

- [ ] **Die Abbruchbedingung ist beruehrt, nicht ausgeloest** — sie verlangt eine Messung an zwei
      Modulen in Phase P6, nicht eine Hochrechnung. **Aber die Hochrechnung steht jetzt da**, und
      wer sie ignoriert, hat die Marke nachtraeglich gewaehlt.
- [ ] **P0.4 (IPC-Fastpath) ist damit nicht mehr die Entscheidung, sondern die Bestaetigung.**


---

# P0.4 — die Gegenprobe

## P0.4 — die Gegenprobe: ein Entwurf, ein Pruefer, und ein Loch in der MESSVORSCHRIFT

**Gefahren am 2026-08-13.** Ein Agent entwarf eine vollstaendige Grammatik (1 882 Zeilen), ein
zweiter prueft sie gegen echten Caprock-Code. Beide nur auf Papier. Die tragenden Zahlen habe ich
nachgeprueft.

---

### Der wichtigste Fund betrifft nicht die Sprache, sondern die Kennzahl

> **Eine Kennzahl aus ungeprueften Zusagen belohnt falsche Zusagen — sie sind kurz.**

Drei Belege, alle im Fragment, das die Zahl des Entwerfers traegt:

| | Fund | Fundstelle |
|---|---|---|
> **Umbenannt 2026-08-16: `G1`–`G3` heissen hier jetzt `GP1`–`GP3`.** Die Kennungen
> kollidierten mit den Grammatikbefunden `G1`–`G11` aus P2 (`SYNTAX.md`), die etwas voellig
> anderes bezeichnen — dort eine fehlende EBNF-Zeile, hier ein falsches `ensures`.
> **Zwei Etikettensysteme mit denselben Namen sind dieselbe Fehlerklasse wie zwei
> Prosaordnungen, die niemand gegeneinander prueft** — `GP` fuer *Gegenpruefung*, `G` bleibt
> bei der Grammatik.

| **GP1** | ein `ensures` ist **falsch**, nicht bloss unbewiesen: `e.caller is Some(cl) => cl == current_id(...)`. Bei offenem Rendezvous A und Aufrufer B behauptet es `A == B` — **nachgeprueft**: der zweite Aufrufer geht in `senders`, ohne `caller` anzufassen. **Und es ist im Zaehler mitgezaehlt** | `crates/caprock-ipc/src/lib.rs:652` |
| **GP2** | `msg_copied` — die **einzige** funktionale Eigenschaft eines Fastpaths — steht in **keinem** `ensures`. Gezaehlt und an nichts gebunden; `transfer()` hat gar keine Nachbedingung | — |
| **GP3** | `effects` vergisst `locks SCHEDS[owner_core(...)]` auf dem Cross-Core-Pfad — **vom Autor der Regel** | — |

**GP3 und der Fund F12 („`effects` ist fail-open") sind dasselbe Loch von zwei Seiten:** eine
weggelassene Wirkung ist **zugleich die staerkste Zusage und die kuerzeste Spezifikation**. Wer
misst, wird belohnt; wer vollstaendig ist, bestraft.

#### Was daraus fuer das Messprotokoll folgt

- [ ] **Eine Kennzahl ohne Gueltigkeitspruefung ihrer Zusagen ist eine Untergrenze mit BENANNTER
      Fehlerrichtung** — falsche und unvollstaendige Zusagen sind kuerzer als richtige. Das gehoert
      neben jede Zahl, sonst liest sie sich wie ein Messwert.
- [ ] **Drei Regeln, ohne die nicht gemessen wird:** (1) jedes gezaehlte `ensures` wird gegen den
      echten Code gehalten; (2) eine benannte, aber an keine Nachbedingung gebundene Eigenschaft
      zaehlt **nicht** — sie ist Zierat; (3) `effects` wird gegen die tatsaechlichen Zugriffe
      geprueft, nicht gelesen.

---

### Die Zahlen

#### Der Anti-Katalog-Prueftein: **3 neue Woerter, nicht zwoelf — bestanden**

Der Entwerfer setzte ihn sich selbst: *„kommen bei `vtd.rs` wieder zwoelf, ist es ein Katalog."*
Gegen die 14 benannten Luecken des `vtd`-Blocks braucht seine Grammatik **drei** zusaetzliche
Woerter: RMW-Zustandsbits, Registerbank an laufzeitberechneter Basis, bedingte Uebersetzung
(**335 `cfg(feature)`-Fundstellen** im Baum, nachgezaehlt). Alles Uebrige faellt auf `tagged`,
`atomic`, `iasm`, `Queue(T,N)` oder Parametrisierung.

> **Der Vorbehalt ist groesser als die Zahl.** Vier der „0-Wort"-Zeilen sind Aenderungen an
> `device` — dem Konstrukt, das er **unveraendert laesst**. Gemessen: `vtd|iommu|smmu` kommt in
> seinen 1 882 Zeilen **zweimal** vor, `device` als Konstrukt in **null** von 14 Codebloecken.
> **Fuenf Wortschatzwoerter und fuenf getoetete Fallen, ohne eine Zeile Erprobung** — die Funde
> F5 (nur Einzelbits), F6 (keine Laufzeitoffsets) und F8 (`device` toetet Falle 4 nicht) ueberleben
> unberuehrt.

#### Das Verhaeltnis, ausgeschrieben statt behauptet

| Beispiel | als Untergrenze | **ausgeschrieben** |
|---|---|---|
| `delete_leaf` (Pruefer) | 1,13 : 1 | **3,6–6 : 1** |
| `Endpoint::call` (Entwerfer) | 1,15 : 1 | **1,8–2,3 : 1** |

**Die Untergrenzen sind fast gleich, die ausgeschriebenen nicht — und der Grund ist der Befund:**
`call`s Nachbedingungen sind **Wertaussagen ueber einer FIFO**, `delete_leaf`s sind **strukturelle
Eigenschaften eines mutierenden Baumes**.

> **Der (b)-Topf (65,1 %) ist ZWEIGIPFLIG, und der teure Gipfel heisst *Induktion ueber eine
> Struktur, die sich unter dem Beweis aendert*.** Genau darauf zielt `by consuming` — das ist der
> erste unabhaengige Beleg dafuer, dass das Konstrukt die richtige Stelle trifft.

**Gewichtet ueber den ausdrueckbaren Teil: ≈ 2 : 1.** Unter der Abbruchmarke (3 : 1), **viermal
ueber dem Ziel** (0,5 : 1).

---

### Die drei Nachpruefungen

1. **„M1 ist ein Loeser" — BESTAETIGT**, und schlimmer als gemeldet. `crates/caprock-sched/src/lib.rs:1996`:
   `let p = (31 - self.bitmap.leading_zeros()) as usize;` braucht eine flusssensitive Folgerung —
   und die Zeile **darunter**, `self.queues[p]`, braucht zusaetzlich die **Datenstruktur-Invariante**.
   **P2s Tor „S1a/S1b unformulierbar mit 0 Zeilen Annotation" ist damit von einer
   Entscheidbarkeits- zu einer Heuristikfrage geworden.**
2. **Quantorengrenze:** sechs Ausdruecke geprueft, **eine** Ueberschreitung — die selbstgemeldete.
   Daneben eine **ungemeldete derselben Klasse**: `no_orphan_object` traegt `runs online` und ist
   ein Praedikat **ueber** einem Aggregat, was seine eigene Regel nicht zulaesst.
3. **Sperrschachtelungen: Zahl UND Richtung falsch.** Es sind **4 von 10** (`docs/invariants.md:36`),
   nicht 5 von 14 — und alle vier nehmen danach einen **groesseren** Rang, sind also nach seiner
   eigenen Regel schachtelbar. **Der echte Befund ist besser als der behauptete:** sein
   `locks L { }`-Block macht Schachteln billig und das gewollte Kopieren-und-Freigeben teuer —
   **ein Anreizgefaelle gegen Caprocks ausdrueckliche Faustregel**, keine Ausdruckslueke.

**G5:** die CAS-Zahl misst die falsche Groesse. Drei Schleifen statt zwei, zwei davon in
`konsole.rs` statt in `caprock-sync` — und die Klasse ist **unbegrenztes Warten**, nicht CAS: allein
`caprock-sync` hat **vier** solche Schleifen, darunter der Ticket-Lock selbst, und nur eine enthaelt
ein `compare_exchange`. **Sein Urteil wird dadurch staerker, nicht schwaecher.**

**Selbstkorrektur des Pruefers:** `ObjectKind` hat **13** Varianten, nicht 11 — die Zahl des
Entwerfers war richtig, die eigene zu klein. **Nachgezaehlt: 13.**

---

### Wo der Entwurf an echtem Code scheitert — vom Entwerfer selbst gemeldet

**CAS-/Warteschleifen: keine Loesung.** `move_cap` ist eine Knotenumbenennung ohne Baumkonstrukt
(**neuer B3-Kandidat, stand auf keiner Liste**). `install` braucht **Transaktionen**, sonst
existiert zwischen `alloc_object` und `alloc_slot` ein Zustand, den kein Konstrukt beschreibt.
`Finalized<'a>` braucht Lebenszeiten, die es nicht gibt. **Und die zentrale Fastpath-Eigenschaft
(„darf dieser Thread in diesen Rahmen schreiben?") ist eine AUTORITAETS-, keine Adressraumfrage —
M1–M4 sagen dazu nichts.**

**Ein Positivbefund:** virtio-`used`/`avail`-Eigentum ist phasenabhaengig und faellt aus **demselben**
Mechanismus wie die Bootphase — **zweite unabhaengige Fundstelle** fuer den linearen Geisterzeugen.


---

# narrow — gemessen und zurueckgenommen

## `narrow` gemessen — der gefaehrlichste offene Punkt geht gut aus

**2026-08-14.** Offener Punkt 1 in [`SYNTAX.md`](SYNTAX.md) lautete: *`narrow` verwandelt eine
Beweispflicht in eine Laufzeitpruefung. Kommt er haeufig vor, ist das Kriterium verletzt — Klempnerei
bliebe beim Programmierer, nur in anderer Form.* **Gemessen an 65 001 Zeilen Caprock.**

*(Die drei Agenten, die das breiter pruefen sollten, sind am Sitzungslimit gescheitert. Das hier ist
die Messung von Hand — schmaler, aber gefahren.)*

---

### Woher Indizes ihre Schranke nehmen — drei Dateien, 268 Fundstellen

| Datei | Fundstellen | **Schranke aus dem Typ moeglich** (`index into …`) | Feld | fremd/sonstiges |
|---|---|---|---|---|
| `caprock-cap/src/space.rs` (Tabelle) | 86 | **75,6 %** | 2,3 % | 22,1 % |
| `caprock-sched/src/lib.rs` (algorithmisch) | 156 | **94,9 %** | 2,6 % | 2,6 % |
| `kernel/src/threads/mod.rs` | 25 | 0 % | — | 100 % (konstante Felder wie `FP_PATTERN[id]`) |

> **Die Auswahlverzerrung, gegen die ich geprueft habe, ist nicht eingetreten.** Ich erwartete, dass
> `index into` nur in Tabellendateien traegt und im **algorithmischen** Code versagt. Gemessen ist
> es umgekehrt: der Scheduler liegt bei **94,9 %**, hoeher als der Cap-Space.

---

### Die harte Klasse: **4 Fundstellen in 65 001 Zeilen**

Flusssensitiv — der Bereich folgt aus einer **vorher geprueften Bedingung**, nicht aus dem Typ:

| | |
|---|---|
| `caprock-sched/src/lib.rs:1996` | `(31 - self.bitmap.leading_zeros())` |
| `crates/caprock-hal/src/cache_decode.rs:68` | `63 - n.leading_zeros()` |
| `kernel/src/colors.rs:864` | `u64::BITS - (n - 1).leading_zeros()` |
| `kernel/src/colors.rs:1052` | `n_lines.trailing_zeros()` |

**Alle vier sind dieselbe Redewendung: eine Bitposition aus einem Wort.** Und alle vier stehen
hinter einer Nullpruefung — `dequeue_highest` hat zwei Zeilen darueber
`if self.bitmap == 0 { return None; }`.

---

### Damit wird die Aussage ueber M1 praeziser — und schwaecher als befuerchtet

Der Entwerfer meldete: *„M1 heisst Bereichstyp und ist ein Loeser."* Das stimmt, **aber nicht in der
Allgemeinheit, in der es klingt.** Was M1 wirklich braucht:

> **Genau eine Flussregel: eine geprueste Bedingung verengt den Bereich der geprueften Groesse im
> Zweig danach.** Nach `if x == 0 { return }` ist `x : u64 in 1..`.

Das ist die billigste Form von Flusssensitivitaet und in jedem Bereichspruefer Stand der Technik.
**Was M1 NICHT braucht, ist allgemeine Inferenz.** Und mit dieser einen Regel plus einem
eingebauten `highest_bit(x: u64 in 1..) -> u32 in 0..63` traegt die Signatur den Bereich —
**alle vier Stellen sind damit ohne `narrow` schreibbar.**

- [ ] **Aus dem gefaehrlichsten offenen Punkt wird eine Entwurfsentscheidung:** M1 bekommt die
      Verengung an geprueften Bedingungen, und die Bitzaehl-Intrinsics kommen mit Vertrag statt roh.
      **`narrow` bleibt im Entwurf, aber als Notausgang fuer den Einzelfall — nicht als
      Regelfall.**

---

### Was diese Messung NICHT zeigt — sonst ist es Ueberschreibung Nr. 15

* **Der Klassierer ist eine Heuristik ueber `x[y]`-Mustern.** Er sieht **keine** Indizes, die aus
  Arithmetik oder aus einem Schleifenzaehler stammen. Die 1 398 variablen Indizierungen im ganzen
  Baum sind damit **nicht** klassifiziert, nur 268 davon.
* **„Schranke aus dem Typ moeglich" ist eine Aussage ueber die DEKLARATION, kein Beweis.** Sie
  setzt voraus, dass die Tabelle ihre Felder als `option index into slot` fuehrt. Dass das geht, ist
  Entwurf; dass es traegt, ist ungeprueft.
* **Die zweite Kandidatenklasse ist ungemessen:** 25 `-=` und 69 `a - b` auf potenziell
  vorzeichenlosen Groessen. Ein Unterlauf nach einer Pruefung ist dieselbe Form wie die vier oben —
  **wieviele davon flusssensitiv sind, weiss ich nicht.**
* **Drei Dateien sind keine Erhebung.** `programs/` ist praktisch ungemessen (eine einzige
  Fundstelle im geprueften Userspace-Modul).

- [ ] **Die 69 Subtraktionen klassifizieren.** Das ist die naechste billige Messung und die
      einzige, die das Ergebnis noch kippen kann.

---

# P2 — Lexer und Parser, erstmals gefahren

## P2 GEFAHREN (Teil 1): der Uebersetzer liest, und das Tor faellt — **1 von 6 Fragmenten**

**2026-08-14.** Erste Zeile Rust in diesem Ordner. Gebaut ist P2 aus dem Prueferplan
([`SPRACHE.md`](SPRACHE.md) Teil III §6): **Lexer, Wortschatz, Parser ueber die vollstaendige
EBNF**, dazu drei der neun Pruefpaesse. Der Baum liegt in `crates/`, der Befehl heisst `gabbro`.

> **Die Reihenfolgeregel ist verletzt, und das steht hier statt in einer Fussnote.**
> `TODO.md` sagt: *„DER NAECHSTE SCHRITT IST KEINE ZEILE RUST"* — zuerst die fuenf
> Scratchpad-Klassen, dann `19 → 0`. Der Uebersetzer wurde trotzdem angefangen, auf Ansage.
> **Was das kostet, ist benannt:** P2 kann die These nicht mehr *vor* dem Uebersetzerbau toeten,
> weil der Uebersetzerbau schon laeuft. Was es einbringt, steht unten — die Messung war ohne
> Uebersetzer nicht fahrbar, und sie faellt gegen die Grammatik.

### Das Tor, vorab und unveraendert

> **P2** | Lexer+Parser ueber alle Fragmente des Ordners | *100 % der Fragmente parsen; drei
> Gift-Fragmente scheitern mit benannter Absage*

**Ergebnis: 1 von 6.** Die Gift-Seite steht: 26 Sprechproben, jede in beide Richtungen; die
Verbotsliste (`while`, `for`, `goto`, `break`, `continue`, `switch`, `unsafe`, `_ =>`) faellt mit
**benannter** Absage statt mit einem Folgefehler drei Token weiter.

| Fragment | Zeilen | Fehler | Klasse |
|---|---|---|---|
| **F1** Cap-Space | 212 | 1 | Wortschatz (`slots`) |
| **F2** VT-d als `device` | 134 | **0** | — |
| **F3** IPC-Fastpath | 126 | 1 | Wortschatz (`ops`) |
| **F4** virtio-Transport | 117 | 5 | Wortschatz (`next`, `slot`×2, `from`), veraltete Fassung |
| **F5** Userspace-Dienstschleife | 92 | 1 | Wortschatz (`boot`) |
| **F6** Pruefgeruest | 110 | 2 (+10 Hinweise) | Semikolon, `atomic … publishes` |

Ueber den ganzen Ordner (`FRAGMENTE.md` + die Beispiele in `SYNTAX.md` und `SPRACHE.md`):
**8 von 32 Uebersetzungseinheiten ohne Fehler, 1 030 Zeilen Gabbro.** Acht weitere Bloecke sind
**Ausschnitte** — sie fangen mitten in einer Form an und zaehlen nicht gegen das Tor; der
Uebersetzer trennt beide Klassen selbst, sonst waere die Prozentzahl ohne Nenner.

### Der Befund, und er ist NICHT „die Fragmente sind alt"

**Sieben von zehn Fehlern in `FRAGMENTE.md` sind eine einzige Klasse: der geschlossene Wortschatz
kollidiert mit gewoehnlicher Kernel-Benennung.** Ueber den ganzen Ordner sind es **neun Woerter an
elf Stellen**:

| Wort | wo es kollidiert | Rolle im Wortschatz |
|---|---|---|
| **`slots`** | `lock CAPS protects { slots, cdt }` (F1, und dasselbe Beispiel in `SYNTAX.md` §11) | Quantorendomaene |
| `ops` | Parametername (F3) | Kosteneinheit, `table ops` |
| `next` | Registername im virtio-Deskriptor (F4) | `next <marke>;` |
| `slot` | `let slot = q.AVAIL_IDX % q.n;` (F4, zweimal) | `slotdecl` |
| `from` | Parametername (F4); `mirrors … from …` (`SYNTAX.md` §14) | `mirrors` |
| `boot` | Parametername (F5) | Adressraum, `bootdecl` |
| `stack` | `step stack = boot_stack_top;` (`SPRACHE.md` §5, Bootpfad) | `entryextra` |
| `check` | `linear ghost type Duty(check);` (`SYNTAX.md` §2, eigenes Beispiel) | `check`-Block |
| `u64` | `u64::max` (`SYNTAX.md` §2, `SPRACHE.md` §M1) | Ganzzahltyp |

**`slots` ist der schwerste, weil die Sprache den Namen selbst erzeugt.** `slots of c` ist eine
der acht Domaenen, `c.slots[s]` steht in jedem Fragment — und dieselbe Zeichenfolge ist als
**Ort** nicht schreibbar. Der Parser laesst sie nach `.` und `->` zu (dort kann kein
Schluesselwort stehen, also nichts verwechselt werden) und weist sie ueberall sonst ab. **Das ist
eine Entscheidung, die die Grammatik nicht trifft, und sie steht als Entscheidung im Quelltext.**

**Zwei Auswege, beide kosten etwas, keiner ist hier gewaehlt:** die kollidierenden Woerter
kontextuell machen (dann ist der Wortschatz nicht mehr geschlossen, und die Tabelle in
`SYNTAX.md` behauptet mehr, als sie haelt) — oder die Fragmente umbenennen (dann traegt jeder
Anwender die Liste im Kopf, und `slots` bleibt trotzdem erzeugt **und** verboten).

### Sechs Loecher in der Grammatik, gefunden vom Parser, nicht vom Lesen

Jedes davon ist ein Fall, in dem **ein Beispiel der Spezifikation gegen die EBNF derselben
Spezifikation faellt.** Dieselbe Familie wie die drei Fehler, die `pruefe-syntax.sh` 2026-08-13
gefunden hat — und der Grund, warum ein Parser mehr sieht als ein Waechter ueber Regelnamen.

| | Fundstelle | was fehlt |
|---|---|---|
| **G1** | `atomicdecl` (`SYNTAX.md` §11) | **kein `publishes`** — das Beispiel zwei Zeilen darunter benutzt es, `SPRACHE.md` §11.3 verlangt es, F6 schreibt es **achtmal**. Der Parser nimmt es an und meldet `P031` je Fundstelle |
| **G2** | `axiom` (`SYNTAX.md` §12) | **kein `-> typeexpr`, kein `requires`** — `axiom rdtscp() -> u64 requires Has(RDTSCP) …` (`SPRACHE.md` Teil IV) ist nicht schreibbar. Betrifft die Axiomschicht, den *„groessten unbewiesenen Posten der ganzen Sprache"* |
| **G3** | `placeshift` gegen `placesuffix` | **mehrdeutig**: in `transition drv { ST: ACK -> ACK \| DRIVER }` ist `ACK -> ACK` zugleich Uebergang und Feldzugriff. Der Parser loest es zugunsten des Uebergangs auf — **eine Entscheidung, die in die Grammatik gehoert** |
| **G4** | `entrydecl` (`SYNTAX.md` §1) | `{ ident ":" ident "," }` verlangt das Schlusskomma **nach jedem** Eintrag; `regs in { nr: rax, …, a3: r10 }` (`SPRACHE.md` Teil II) hat keins |
| **G5** | `path` (`SYNTAX.md`, Lexik) | `path = ident { "::" ident }` — **`u64::max` ist kein `path`**, weil `u64` und `max` Woerter sind. Steht in `SYNTAX.md` §2 und `SPRACHE.md` §M1 |
| **G6** | `costexpr`, `format` | **`O` und `version` sind Terminale, die kein Waechter sieht**: `pruefe-wortschatz.py` liest nur `"[a-z_]…"`, also nicht `"O"` (gross) und nicht `"@version"` (fuehrendes `@`). Zwei Woerter ausserhalb der geschlossenen Tabelle |

**G6 ist ein Befund ueber den Waechter, nicht ueber die Grammatik** — dieselbe blinde Stelle, die
`SYNTAX.md` oben schon zweimal protokolliert. Der Uebersetzer haelt seine Wortliste jetzt
mechanisch gegen die Tabelle (`tests/wortschatz.rs`, in **beide** Richtungen, 189/189).

### Was an den Fragmenten selbst veraltet ist — und das ist kein Grammatikbefund

* **F4**: `linear ghost type QueueSetup(q : Virtq);` schreibt `params` in die Klammern; `typedecl`
  verlangt dort `typelist`. Der Kommentar «B3» im Fragment behauptet das Gegenteil — er ist gegen
  die **zweite** Fassung geschrieben, die Grammatik ist bei der vierten. `Held(Lock)` ist heute
  richtig.
* **F6**: `let g = f() else (e) { return false; };` — die Grammatik gibt den Formen mit Block
  **kein** abschliessendes Semikolon. Zwei Stellen.

### Was dieser Lauf ausdruecklich NICHT sagt

* **Sechs von neun Paessen sind nicht gebaut** — D1/D2, M1+V1–V3, M3, M2, Paarung, costs. `gabbro
  paesse` druckt die Liste samt dem, was mit jedem offenen Pass ungeprueft bleibt, und jeder Lauf
  wiederholt sie unter dem Ergebnis. **Ein gruener Lauf ist die Abwesenheit der Befunde, die drei
  Paesse sehen koennen — mehr nicht.**
* **Kein erzeugtes C.** Die Absenkung ist nicht angefangen; die Formentabelle (40–60 Eintraege)
  ist weiter ungeschrieben.
* **Der Parser prueft die FORM.** Dass `effects { pure }` dasteht, heisst nicht, dass es stimmt —
  das entscheidet der Wirkungspass, den es noch nicht gibt.

### Was gegen den Uebersetzer selbst geprueft wird

`forbid(unsafe_code)` steht im Arbeitsbereich **und** wird von `tests/verfassung.rs` gehalten:
jede Kiste muss `[lints] workspace = true` fuehren, jede Abhaengigkeit auf der benannten Liste
stehen (heute: **keine ausser den eigenen Kisten**), und kein `.gab` im Uebersetzerbaum —
Selbst-Hosting steht auf der Verbotsliste. **Sprechprobe gefahren:** ein `unsafe {}` in
`span.rs` bricht die Uebersetzung mit `usage of an unsafe block`, dann zurueckgenommen.

**31 Tests, alle gruen; `pruefe-syntax.sh` und `pruefe-wortschatz.py` unveraendert gruen.**

---

# P3 — M1 und die drei Flussregeln, gebaut und gefahren

## P3 GEFAHREN: **der Pass reproduziert einen Befund, den der Ordner von Hand gefunden hatte**

**2026-08-14, gleicher Tag wie P2.** Gebaut ist Pass 3 der Passliste: **Bereichstypen (M1)
samt Konstantenauswertung, V1, V2, V3**, dazu ein Beispielkorpus von **8 sauberen Dateien
(871 Zeilen)** und **15 Giftdateien (128 Zeilen)**, jede mit dem Code, mit dem sie fallen muss.

### Was der Pass am eigenen Fragment findet — und was das wert ist

`FRAGMENTE.md` Zeile 248 (Fragment F1; das Rust-Original steht in
`crates/caprock-cap/src/space.rs:1067`): `o.slots[obj].refcount -= 1;`

```
Fehler: [M104] `o.slots[…].refcount` -= verlaesst den Bereich: `u32 in 0 .. 80255`
               gegen `u8 in 1 .. 1`
Fehler: [M101] die Zuweisung verlangt `u32 in 0 .. 80255`, der Wert hat `u32 in -1 .. 80254`
```

Das ist Befund **«B29»**, drei Zeilen darueber von Hand eingetragen, mit der Begruendung
*„M1 verlangt, dass das Ergebnis im Bereich bleibt; `refcount == 0` faellt aber nur ueber die
Buchfuehrungs-Invariante aus, und die ist nach «B13» gar nicht aufschreibbar."*

> **BERICHTIGT 2026-08-14, noch am selben Tag.** Die erste Fassung dieses Abschnitts nannte
> das eine **„unabhaengige Wiederentdeckung … ohne dass ihm jemand gesagt haette, wo er
> suchen soll"** und gab als Fundstelle `space.rs:248` an. **Beides war falsch:**
>
> * `space.rs:248` ist ein Strukturfeld; die 248 ist eine **`FRAGMENTE.md`-Zeile**, die
>   echte Rust-Stelle liegt auf `:1067`. Eine Zeilennummer mit dem falschen Dateinamen
>   davor ist keine Fundstelle.
> * **„Unabhaengig" traegt nicht.** Genau dieser Fall ist die erklaerte Motivation des
>   Passes und steht zweimal als eingebauter Pruefstein: `beispiele/gift/01-unterlauf.gab`
>   nennt ihn in seiner Kopfzeile, und `typen.rs` fuehrt ihn als Einheitstest
>   `subtraktion_faellt_unter_null`. Die **Zeile** wurde dem Pass nicht genannt, die
>   **Form** schon. Das ist ein **bestandener Regressionstest**, und der ist etwas wert —
>   aber er ist nicht der Beleg, als den ich ihn ausgegeben habe.
>
> Gefunden hat das die Gegenpruefung (s. u.), nicht ich. Der Ausgabeblock oben stand
> zudem **redigiert** da (`gegen \`1\`` statt `gegen \`u8 in 1 .. 1\``) — weggefallen war
> genau der Teil, der zeigt, dass das Literal `1` als **u8** modelliert wird, und das ist
> die Wurzel eines eigenen Befunds.

Ueber den ganzen Ordner: **8 M1-Befunde unter zwei Codes** (4 × `M101`, 4 × `M104`), alle in
`FRAGMENTE.md`, keiner in den Beispielen.

### Zwei Befunde, die man nicht zusammenwerfen darf

| Code | Aussage |
|---|---|
| **`M104`** | der Wert ist auf der **Maschine nicht darstellbar** — die Breite ist weg (`u32 * u32`, `0 - 1` auf `u32`) |
| **`M101`** | der Wert passt nicht in den **deklarierten Bereich seines Ziels** (`a + 1` verlaesst `0 .. GRENZE`) |
| **`M102`** | der Nenner schliesst die Null nicht aus |
| **`M103`** | der Index passt nicht in die Laenge seines Feldes |

Wer die ersten beiden zusammenwirft, verliert genau die Aussage, die M1 macht: **der Bereich
ist eine Zusage der Deklaration, die Breite eine Eigenschaft der Maschine.**

### Die Lektion, die der Korpus erzwungen hat — und sie stand in keinem Dokument

**Ein `u64`-Zaehler ohne Obergrenze ist nicht erhoehbar.** `wert + 1` verlaesst `u64`, wenn
`wert` bis `2^64-1` reichen darf; M1 sagt das an der Zeile. Die Folge ist eine Regel, die
jede Kernel-Zeile betrifft:

> **Jeder Zaehler braucht zwei Dinge: eine Schranke in der Deklaration und eine Pruefung vor
> der Rechnung.** `type Zaehlerwert = u64 in 0 .. GRENZE;` allein reicht nicht — `+ 1` reicht
> dann bis `GRENZE + 1`. Erst `if w < GRENZE { w = w + 1; }` traegt, und V1 macht daraus
> Code ohne Laufzeitkosten.

Das ist an drei Stellen des eigenen Beispielkorpus aufgeschlagen, bevor es dastand.

### Eine Regel, die dazukam — benannt, nicht eingeschmuggelt

**V1 gilt auch fuer den Weg NACH einem Zweig, der immer verlaesst.**

```gabbro
if a < b { return 0; }
return a - b;                    -- hier gilt a >= b, ohne dass es dasteht
```

Der Zweig endet mit `return`; was danach kommt, ist genau der Fall `a >= b` — **syntaktisch
entscheidbar, ohne Fixpunkt** (letzte Anweisung ist `return`/`leave`/`next` oder ein Aufruf
nach `never`). Ohne diese Regel braucht **jeder fruehe Rueckstieg** ein `narrow`, und die
Messlatte *„`narrow` ≤ 24 Fundstellen"* faellt an einer Redewendung statt an der Sprache.
**Sie steht als Entscheidung im Quelltext und hier, nicht als stilles Regelwachstum.**

### Die Deckung — die Zahl, ohne die ein gruener Lauf nichts sagt

`gabbro pruefe` druckt je Datei, **wieviele Ausdruecke M1 typisieren konnte**:

```
beispiele/08-bereiche.gab: 23 Items, 0 Fehler, 0 Hinweise
  M1 sah 54 Ausdruecke, 0 davon ohne Typ (100 % Deckung)
```

Ueber den Beispielkorpus: **150 Ausdruecke, 13 ohne Typ, 91 % Deckung** — und **Deckung
heisst „hat einen Typ", nicht „wurde geprueft"** (s. die Gegenpruefung weiter unten; sie
fand sechzehn Dateien mit echten Ueberlaeufen, vierzehn davon mit 100 % Deckung). Die 13 sind
`sizeof`/`lenof` (brauchen das Layout, also die Absenkung), `old(…)` (Geisterausdruck) und
Aufrufe fremder Funktionen. **Ohne diese Zahl sehen „nichts gefunden" und „nichts angesehen"
gleich aus** — und das ist die Falle, an der ein Pruefer wertlos wird.

### Was P3 NICHT prueft

* **Praedikate.** `requires`, `ensures`, `invariant` sind Geisterausdruecke; M1 sieht Ruempfe.
* **Aufrufwirkungen auf Nichtlokales.** Jeder Aufruf toetet jeden Fakt ueber eine Stelle mit
  Feld- oder Indexzugriff. Lokale Groessen bleiben — Gabbro hat **keinen Adressoperator**,
  also kann ein Gerufener sie nicht aendern. Das ist der einzige Ort, an dem der Pass eine
  Aussage ueber Alias macht, und er macht die **konservative**.
* **`index into T` hat keine Obergrenze** — s. Befund G8 unten.

### Zwei weitere Grammatikbefunde, gefunden beim Schreiben der Beispiele

| | Fundstelle | was fehlt |
|---|---|---|
| **G7** | `entrydecl` | `clobbers { }` ist nicht schreibbar: `identlist` verlangt mindestens einen Namen. **Ein Eintritt, der nichts zerstoert, kann das nicht sagen.** |
| **G8** | `table` | **eine Tabelle nennt ihre Slotzahl nicht.** `index into T` hat damit keine Obergrenze aus der Deklaration; die Schranke haengt an einem *von Hand* passend gewaehlten Indextyp (`type SlotIdx = u32 in 0 ..< NSLOTS`). **M4 — „kein ungeprueftes Indizieren" — ruht an dieser Stelle auf einer Konvention, nicht auf der Sprache.** Der Uebersetzer prueft Indizes deshalb nur gegen `[T; N]`, nicht gegen Tabellen |

**48 Tests, alle gruen** (P2: 25, P3: +23), `pruefe-syntax.sh` und `pruefe-wortschatz.py`
unveraendert gruen.

---

# MESSPROTOKOLL fuer die `narrow`-Vollzaehlung — VORAB, vor der ersten gezaehlten Stelle

**Diese Regeln stehen hier, bevor eine einzige Fundstelle angesehen wurde, und in einem
eigenen Commit VOR dem Commit der Zaehlung.** Der Grund ist die dokumentierte Schwaeche
dieses Ordners: **sechs von neun Berichtigungen in [`HISTORIE.md`](HISTORIE.md) waren
Umdeutungen an einer Grenze**, und diese Zaehlung hat ein eingebautes Anreizgefaelle — jede
Stelle, die man einer V-Regel zuschlaegt, macht das Ergebnis besser. Wer die Regeln waehrend
der Zaehlung schaerft, schaerft sie in die bequeme Richtung.

## Die Latte, unveraendert seit [`SYNTAX.md`](SYNTAX.md)

> **`narrow`-Zaehlung am Baum: ≤ 24 Fundstellen.** Wachsen sie darueber, ist die Regelmenge
> V1–V3 zu klein — **und *das* ist die Widerlegung, nicht ein weiteres Regelwachstum in Stille.**

## Was gezaehlt wird — und was ausdruecklich nicht

**Gezaehlt werden die Stellen, an denen M1 eine Bereichspflicht erzeugt und sie NICHT aus den
Operandentypen faellt:**

| | Klasse | Grund |
|---|---|---|
| **ja** | Subtraktion auf vorzeichenloser Groesse | Unterlauf; die gemessene Klasse (255 Fundstellen, 102 flusssensitiv) |
| **ja** | Division und Rest | der Nenner muss die Null ausschliessen |
| **nein** | Addition und Multiplikation | in Rust ohne Bereichstypen nicht von „passt ohnehin" zu trennen; **eine Zahl daraus waere geraten** |
| **nein** | Indizierung | die Schranke haengt an `index into T`, und **`table` nennt seine Slotzahl nicht** (Befund G8). Eine Zaehlung waere eine Aussage ueber eine Konvention, nicht ueber die Sprache |

**Die Auslassungen sind Teil des Ergebnisses**, nicht sein Kleingedrucktes: die gemessene Zahl
deckt zwei von vier Pflichtklassen.

## Die sechs Spalten — je ein Satz, und mehr nicht

| Spalte | Entscheidungsregel |
|---|---|
| **K — durch Konstruktion** | Beide Operanden sind Literale oder `const`, ODER die Operation ist ausdruecklich behandelt (`checked_sub`, `saturating_sub`, `wrapping_sub`, `checked_div`). **Keine Pflicht, kein Mensch.** |
| **V1** | Im selben Rumpf steht **vor** der Stelle eine Pruefung der **geprueften Groesse gegen eine Konstante** (`if n > 0`, `if n == 0 { return }`, `assert!(n >= 1)`, `while n > 0`), und zwischen Pruefung und Gebrauch liegt **kein Schreiben** auf die Groesse. |
| **V2** | Dasselbe, aber die Pruefung stellt **die beiden Stellen der Subtraktion gegeneinander** (`if a >= b`, `if a < b { return }`, `assert!(a >= b)`). |
| **V3** | Die Stelle steht in einem `match`-Zweig, und der beteiligte Wert ist die **Bindung dieses Zweiges**. |
| **F — Funktionsgrenze** | Keine Pruefung im Rumpf, und **mindestens ein Operand ist ein Parameter**. Die Pruefung liegt also — wenn es sie gibt — beim Aufrufer. **Das ist die Klasse, die entscheidet, ob `requires a >= b` als Vertrag reicht**, und sie zaehlt NICHT gegen die Latte. |
| **N — `narrow`** | Alles Uebrige: keine Pruefung, und die Operanden entstehen im Rumpf. **Nur diese Spalte zaehlt gegen die 24.** |

## Die Kippregel — sie kippt IMMER nach N

1. **Passt eine Stelle auf zwei Spalten, gilt die teurere** (N vor F vor V3 vor V2 vor V1 vor K).
2. **Ist unklar, ob zwischen Pruefung und Gebrauch geschrieben wird, ist es N.** Ein Fakt, der
   vielleicht gestorben ist, ist kein Fakt.
3. **Liegt eine SCHLEIFENGRENZE zwischen Pruefung und Stelle, ist es N** — die Pruefung steht
   vor der Schleife, die Stelle in ihrem Rumpf. Schleifen tragen keine Fakten hinein, und das
   ist eine Regel der Sprache, keine Schwaeche des Zaehlers. **Stehen beide im selben
   Schleifenrumpf, gilt die Pruefung normal.**
   > **Berichtigt 2026-08-14, VOR der ersten gezaehlten Stelle und in eigenem Commit.** Die
   > erste Fassung las *„liegt die Pruefung in einer Schleife, die die Stelle umschliesst"* —
   > das haette jede Pruefung INNERHALB eines Schleifenrumpfs nach N gekippt und damit eine
   > Regel der Sprache falsch wiedergegeben. Der Fehler ist beim Bauen des Klassierers
   > aufgefallen, nicht beim Zaehlen; **er steht hier, weil eine stille Berichtigung genau
   > die Bewegung waere, gegen die dieses Protokoll geschrieben ist.**
4. **Steht die Pruefung NACH der Stelle, zaehlt sie nicht.**

## Der Klassierer ist eine Heuristik — und er hat eine Sprechprobe

Der Zaehler liest Rust **zeilenweise**, nicht als Baum. Er kann Makrorümpfe, Verschluesse und
mehrzeilige Bedingungen falsch schneiden. **Deshalb gilt er nur als Messgeraet, wenn er die
Stellen findet, die dieser Ordner schon kennt:**

* `crates/caprock-sched/src/lib.rs:1996` — `31 - self.bitmap.leading_zeros()`, in
  [`TODO.md`](../TODO.md) als offene Klempnerei-Pflicht gefuehrt;
* `kernel/src/colors.rs:864` und `crates/caprock-hal/src/cache_decode.rs:68` — dieselbe
  Redewendung, die die frueherre Messung als „vier Fundstellen, alle dieselbe Form" fand.

**Findet er sie nicht, ist die Zahl ungueltig** — nicht ungenau, ungueltig.

## Was die Messung UNGUELTIG macht (nicht bloss unguenstig)

1. **Der Klassierer findet die drei Sprechproben oben nicht.**
2. **Eine Regel wird waehrend der Zaehlung geaendert.** Aendert sie sich, wird von vorn gezaehlt,
   und das Protokoll bekommt einen neuen Abschnitt mit Datum.
3. **Eine Stelle wird von Hand umklassifiziert, ohne dass die Regel dafuer hier steht.**
4. **Die Zahl wird ohne die Spaltenverteilung berichtet.** Eine Gesamtzahl ohne K/V1/V2/V3/F/N
   ist kein Messwert — sie sagt nicht, ob die Sprache traegt oder ob der Zaehler blind ist.

## Die zwei Ausgaenge, ebenfalls vorab

| | |
|---|---|
| **N ≤ 24** | Die Regelmenge V1–V3 traegt. `narrow` bleibt eine benannte Ausnahme statt eines Rituals. |
| **N > 24** | **Widerlegung an dieser Stelle.** Die Regelmenge ist zu klein gewaehlt — und die Antwort ist dann NICHT eine vierte Regel, sondern der Eintrag in [`HISTORIE.md`](HISTORIE.md). |

Und getrennt davon, ohne Latte, weil niemand sie vorab setzen konnte:

| | |
|---|---|
| **F = 0** | V-Fakten sterben nie an der Funktionsgrenze; `requires` als Vertrag ist unnoetig. |
| **F > 0** | **Jede dieser Stellen braucht `requires a >= b` am Gerufenen** — und damit ist die Frage aus [`TODO.md`](../TODO.md) beantwortet, nicht vermutet. |

---

# Die `narrow`-Vollzaehlung — GEFAHREN und **UNGUELTIG**, mit Grund

**2026-08-14.** Das Protokoll steht oben, in zwei Commits vor dieser Zeile. Der Klassierer
`zaehle-narrow.py` ist gebaut, geeicht und gefahren. **Sein Ergebnis darf nicht benutzt
werden**, und der Grund ist wichtiger als jede Zahl, die er ausgibt.

## Was der Zaehler ausgibt — und warum es keine Messung ist

Ueber 114 Dateien und 71 061 Zeilen (`kernel/`, `crates/`, `programs/`) findet er
**513 Bereichspflichten** (Subtraktion, Division, Rest) und klassiert sie:

| K | V1 | V2 | V3 | F | **N** |
|---|---|---|---|---|---|
| 269 | 20 | 16 | 0 | 40 | **168** |

**168 gegen eine Latte von 24 waere eine Widerlegung.** Sie wird hier **nicht** berichtet,
weil eine Handstichprobe zeigt, dass die Zahl die Blindheit des Zaehlers misst, nicht die
Sprache.

## Die Eichung — vier benannte Defekte, alle VOR der Zaehlung repariert

| | Defekt | Wirkung |
|---|---|---|
| **1** | `pd as usize - 1` — der Cast zerschnitt den Operanden zu `usize` | jede Pruefung auf `pd` unauffindbar |
| **2** | Verschlussparameter (`\|a: u64, b: u64\|`) galten nicht als Parameter | jede Stelle in einem Verschluss faelschlich N statt F |
| **3** | saettigende Redewendungen (`len - frei.min(len)`) | durch Konstruktion sicher, gezaehlt als N |
| **4** | **`if c < 2 { return None; }` etabliert danach `c >= 2`** | die haeufigste Form im Baum; **derselbe Regelzusatz, den der Uebersetzer als `endet_immer` fuehrt** — ein Zaehler, der sie nicht kennt, misst eine ANDERE SPRACHE als der Pruefer |

Nach allen vieren fiel N von 208 auf 168. **Jede Reparatur bewegte die Zahl in die bequeme
Richtung** — und genau deshalb steht hier jede einzeln.

## Die Handstichprobe, die das Verfahren toetet

Fuenf N-Stellen ausserhalb des Bringup-Codes, von Hand nachgesehen:

| Fundstelle | Zaehler | von Hand | |
|---|---|---|---|
| `caprock-hal/src/x86_64/acpi.rs:101` | N | **N** | `(root.len() - 36) / entry_size` ohne Pruefung — ein echter Befund |
| `kernel/src/system.rs:446` | N | **N** | `base - PAGE` ohne Pruefung |
| `caprock-mem/src/color.rs:131` | N | **K** | `(1u64 << per) - 1` kann nicht unterlaufen; der Zaehler rechnet den Bereich von `1 << per` nicht aus |
| `kernel/src/loader.rs:685` | N | **V1** | `(v != 0).then(\|\| … v - 1)` — die Pruefung steht in einer Booleschen Kette, nicht in einem `if` |
| `kernel/src/system.rs:4088` | N | **F** | `n - aus_datei` mit dokumentierter Vorbedingung; in Gabbro ein `requires`, kein `narrow` |

**Drei von fuenf falsch, alle in dieselbe Richtung: zu viel N.** Eine Fehlerrate dieser
Groesse macht 168 zu einer Zahl ueber den Zaehler.

## Der Befund ist METHODISCH, und er trifft mein eigenes Protokoll

> **Die Sprechprobe des Protokolls war zu schwach.** Sie verlangte, dass der Klassierer
> **drei bekannte Fundstellen findet** — das ist eine Aussage ueber **Trefferquote an drei
> Stellen**, nicht ueber **Genauigkeit an 513**. Der Zaehler bestand sie und lag trotzdem
> in 60 % der Stichprobe falsch.
>
> **Eine Sprechprobe ueber drei Faellen kann keinen Klassierer ueber 513 abnehmen.** Das ist
> derselbe Fehler wie die zweimal bezahlte blinde Stelle in `pruefe-syntax.sh`: ein Pruefer,
> der eine Richtung prueft und ueber die andere schweigt. **Wer das naechste Mal ein
> Messgeraet baut, setzt die Handstichprobe INS PROTOKOLL — mit Umfang und Fehlerschranke,
> vorab.**

## Was die Zaehlung fahrbar machen wuerde

Die drei Reparaturen, die noch fehlen, sind keine Regexe mehr: **Bereichsrechnung ueber
`1 << x`**, **Boolesche Ketten statt `if`**, **dokumentierte Vorbedingungen als `F`**. Das
ist zusammen genau **M1 mit V1–V3, angewandt auf Rust** — also der Pass, der in
`crates/gabbro-check/src/m1.rs` schon steht, nur fuer die falsche Sprache.

**Daraus folgt die Reihenfolge, und sie verbindet die beiden Messungen dieses Tages:**

> **Die `narrow`-Zaehlung ist erst genau fahrbar, wenn Caprock-Bereiche in Gabbro vorliegen —
> dann zaehlt der Uebersetzer selbst, mit derselben Regelmenge, die er prueft.** Und dafuer
> muessen zuerst die Fragmente parsen (heute **1 von 6**, Tor P2).

## BERICHTIGUNG 2026-08-14 — **die Latte ist nicht offen, sie ist verfehlt**

Die erste Fassung dieses Abschnitts schloss mit *„Die Latte ≤ 24 bleibt also offen"*.
**Das ist die eine Stelle, an der dieser Bericht sich selbst geschont hat**, und die
Gegenpruefung hat sie gefunden.

Sie hat den Klassierer unter **vier** Lesarten gefahren, darunter die fuer die Sprache
guenstigste, die sich bauen liess:

| Lesart | N |
|---|---|
| guenstigste (grosszuegige K-Regel **plus** erweiterte Konstantenerkennung) | **150** |
| wie oben berichtet | **168** |
| ohne die undeklarierte Ordnerbeschraenkung | **177** |
| K-Regel **woertlich nach Protokoll** (der Nenner allein genuegt dort nicht) | **317** |

**Die Latte ist 24. Jede Lesart verfehlt sie um Faktor 6 bis 13.** Die Fehlerrate des
Zaehlers — von drei unabhaengigen Stichproben auf 40–60 % beziffert, alle einseitig zu viel
N — reicht nicht annaehernd, um diesen Abstand zu erklaeren. Und die Gegenrichtung entlastet:
**0 von 19 gezogenen K/V1/V2/F-Stellen waren in Wahrheit N**, 168 ist also eine harte
**Obergrenze**, keine Schaetzung um einen Mittelwert.

> **Damit steht es so:** die Zahl ist ungenau, das **Urteil** ist es nicht. *„Die Latte
> bleibt offen"* war falsch — richtig ist: **die Latte ist nach jeder belegbaren Lesart
> verfehlt, und wie weit genau, ist unbekannt.** Eine unbequeme Zahl mit einem
> Methodenargument wegzuraeumen ist dieselbe Bewegung, gegen die das Messprotokoll oben
> geschrieben ist — sie kam nur eine Ebene hoeher wieder herein.

**Was das fuer die Sprache heisst, steht noch nicht fest** und gehoert nicht in diese
Messung: ob V1–V3 zu klein sind, ob `narrow` zu eng gedacht ist, oder ob Rust-Code
systematisch anders prueft als Gabbro-Code es koennte — das entscheidet erst der Lauf des
Uebersetzers ueber Gabbro-Quelltext. **Was feststeht: die Latte haelt heute nicht.**

**Was ausdruecklich NICHT gemessen ist:** die genaue Zahl der `narrow`-Stellen. Wer sie
zitiert, zitiert einen ungeeichten Zaehler — **aber wer sagt, die Latte sei offen, zitiert
gar nichts.**

### Zwei weitere Protokollbrueche, von der Gegenpruefung gefunden

* **Die groesste Klassierregel des Skripts steht nicht im Protokoll.** Das Protokoll sagt
  K = *„**beide** Operanden sind Literale oder `const`"*; das Skript laesst bei `div`/`rem`
  den **Nenner** genuegen. **149 der 513 Pflichten haengen daran**, und die Liste der vier
  benannten Eichungsdefekte fuehrt ihn nicht auf — die Liste, die fuer Transparenz da ist,
  laesst den groessten Posten aus.
* **`V3 = 0` ist ein Artefakt.** Die V3-Regel des Skripts feuert ueber 513 Stellen kein
  einziges Mal; `entkerne` frisst Byte-Literale (`b'0'`) und hinterlaesst Phantom-Operanden.
  **Die Latte ist gegen V1–V3 gesetzt, gemessen wurde V1–V2.** Das allein macht die Zahl
  ungueltig, unabhaengig von jeder Stichprobe.

---

# Die Gegenpruefung — **16 Dateien, die durchkamen und fallen mussten**

**2026-08-14.** Ein zweiter Opus-5-Lauf hat den Uebersetzer, die Beispiele, die Messungen
und dieses Dokument gegengelesen, mit dem ausdruecklichen Auftrag, **Fehler zu finden statt
zu bestaetigen**. Er hat drei Unteragenten angesetzt, 111 Werkzeugaufrufe gefahren und
**keine Datei in beiden Baeumen angefasst**. Was er gefunden hat, ist der wertvollste
Einzelposten dieses Tages.

## Der Satz, der falsch war — und er steht in der Spezifikation, nicht nur im Quelltext

> [`SPRACHE.md`](SPRACHE.md) §3.2: *„eine **Faktenmenge**, die nur an den drei benannten
> Stellen waechst und bei **jedem Schreiben auf eine beteiligte Stelle stirbt**"*

**Er war auf fuenf unabhaengigen Wegen falsch.** Der Pass meldete `0 Fehler` — und in
vierzehn der sechzehn Faelle dazu **„100 % Deckung"**.

| | Was durchkam | zu |
|---|---|---|
| **U1** | ein Schreiben **im Unterblock** toetete den Fakt des umgebenden Blocks nicht — jedes `if`, `match`, `locks`, jeder Schleifenrumpf | **ja** |
| **U2** | `let x = …` erbte den Fakt seines verdeckten Vorgaengers | **ja** |
| **U3** | der Fakt ueber `buf[i]` ueberlebte `i = 0` — der Ort blieb, sein Index bewegte sich darunter weg | **ja** |
| **U4** | `ist_lokal` hielt `static mut g` fuer lokal; sein Fakt starb bei keinem Aufruf | **ja** |
| **U5** | ein Aufruf **in einem Ausdruck** (`let t = nuller(z);`) toetete gar nichts — nur die Anweisungsform tat es | **ja** |
| **U6** | `narrow … else { }` installierte seinen Bereich, ohne dass der Zweig verlaesst | **ja** |
| **U7** | `let … else { }` ohne Divergenz — die Regel aus `SYNTAX.md` §7 prueft**e** kein Pass | **ja** |
| **U8** | `schiebe_links` gab bei moeglicherweise negativem Operanden den **vollen** Bereich zurueck und loeschte damit den Ueberlauf | **ja** |
| **U9** | **M4 prueft**e den Index nur beim **Lesen**, nie beim **Schreiben** — die gefaehrlichere Richtung | **ja** |
| **U10** | eine deklarierte `u8 in 200 .. 200` nahm die Breite der Gegenseite an; ob eine Deklaration zufaellig ein Punkt ist, entschied, ob M1 rechnet oder schweigt | **ja** |
| **U11/U12** | Signaturen und Typen sind nach **blankem Namen** verschluesselt: ein gleichnamiges `fn` oder `type` in einem anderen Modul loescht die Bereichspruefung | **nein — s. u.** |
| **Q** | der `effects`-Pass sieht **nie einen Rumpf**: `effects { pure }` ueber einer schreibenden Funktion kommt durch | **nein — s. u.** |

**Zehn davon sind zu, mit je einer Giftdatei**, die sie festhaelt
(`beispiele/gift/16-…` bis `25-…`). Zwei bleiben offen und stehen jetzt in der Passliste,
wo `gabbro paesse` sie ausdruckt:

* **Pass 3 (M1) ist `TEIL`** — Namen ohne Modulaufloesung.
* **Pass 8 (`effects`) ist `TEIL`** — geprueft wird die Deklaration, nie der Rumpf.

> **Der Zustand `Teilgebaut` ist neu, und er ist der eigentliche Ertrag dieses Befunds.**
> Bis heute kannte die Passliste nur *gebaut* und *offen* — und ein Pass, der zur Haelfte
> prueft, meldete sich als gebaut. **Das war ein falsches Gruen an genau der Stelle, an der
> dieser Ordner keins haben will.**

## Zwei Parserfehler, beide gefahren

* **`pfeil_ist_suffix` leckte**: ein `?` sprang vor die Wiederherstellung, und ein Tippfehler
  in **einem** `transition` machte `->` im **ganzen Rest der Datei** zum Nichtsuffix — drei
  Absagen, zwei davon Phantome auf gueltigen Zeilen. Genau der Folgefehlerregen, den die
  Anweisungserholung verhindern soll. **Zu.**
* **`publishes`**: der Parser nahm `publishes { … }` (steht **nicht** in der EBNF) und wies
  `publishes place` ab (**steht** dort, §11). Doppelt falsch, und bei `atomic … publishes`
  meldete er den Riss sogar selbst. **Zu**, beide Formen gehen, die Klammerform sagt `P032`.

## Was die Testsuite nicht konnte — und was daraus folgt

> *„Es gibt keinen Test, dessen Fehlschlag ‚ein echter Ueberlauf wurde uebersehen' bedeutet."*

48 Tests, beide Richtungen, alle gruen — und sechzehn Ueberlaeufe kamen durch. Die Proben
pruefen **Anwesenheit einer erwarteten Absage** und **Abwesenheit von Absagen bei geglaubtem
Wohlverhalten**; keine prueft, ob ein Loch existiert, das niemand vermutet hat. Der
Giftkorpus ist jetzt von 15 auf **25** gewachsen, und die zehn neuen sind genau die Dateien,
die einmal durchkamen. **Das ersetzt die fehlende Testart nicht — es sammelt nur, was eine
Gegenpruefung findet, und die naechste findet anderes.**

## Und die Deckungszahl, an der es am meisten haengt

91 % Deckung ueber dem Beispielkorpus heisst **„hat einen Typ"**, nicht **„wurde geprueft"**.
Vierzehn der sechzehn Gegenbeispiele meldeten **100 %**. Die Zahl steht im Bericht dafuer ein,
dass *„nichts gefunden" und „nichts angesehen" nicht gleich aussehen* — **genau dort sahen
sie gleich aus.** Sie bleibt stehen, weil sie etwas misst; **aber sie misst weniger, als ihr
Name verspricht**, und das steht ab jetzt daneben.


---

# Mutationsprobe auf den Pruefer — **24 von 24**

**2026-08-14.** Die Gegenpruefung hatte einen Satz hinterlassen, der die eigentliche Luecke
benannte: *„Es gibt keinen Test, dessen Fehlschlag ‚ein echter Ueberlauf wurde uebersehen'
bedeutet."* 48 Proben in beide Richtungen waren gruen, waehrend sechzehn Ueberlaeufe
durchkamen — weil eine Probe **die Anwesenheit einer erwarteten Absage** prueft und nicht,
**ob eine Regel ueberhaupt noch greift**.

`./mutiere-pruefer.py` stellt genau diese Frage: es beschaedigt **je eine Regel** des
Pruefers, faehrt die Testsuite und sieht nach, ob etwas faellt.

| | |
|---|---|
| **ueberlebt** | **Befund.** Diese Regel koennte ausfallen, ohne dass eine Probe faellt — sie ist heute unbewacht |
| **gefangen** | die Regel steht unter Beobachtung |
| **ungueltig** | die Mutation uebersetzt nicht; sie zaehlt nicht mit |

Die Quelle wird nur waehrend eines Laufs veraendert und danach **byteweise gegen Hash
wiederhergestellt**, auch bei Abbruch. Das Geruest hat seine eigene Sprechprobe: eine
**Nullmutation muss ueberleben** (sonst misst es die Datei statt die Regel) und eine tote
Bereichspruefung **muss fallen**.

## Erster Lauf: 21 von 24 — und die drei, die durchkamen, sind die interessanten

| Mutation | Regel |
|---|---|
| `literal-immer` | **U10** — ein Punktbereich nimmt wieder fremde Breite an |
| `schieben-ohne-vorzeichen` | **U8** — `schiebe_links` vergisst den negativen Operanden |
| `v3-tot` | **V3** — der `match`-Binder traegt seine Nutzlast nicht mehr |

**Alle drei waren Regeln, die am selben Tag repariert worden waren** — und keine hatte
einen Test, der sie festhaelt. Die Reparaturen standen im Quelltext, die Zusicherung nirgends.
Besonders deutlich bei U8: `beispiele/gift/24-schieben-mit-vorzeichen.gab` faellt schon an der
**oberen** Ecke, also konnte der Korpus „halbe Regel" nicht von „ganzer Regel" unterscheiden.

Drei neue Proben (`gift/26`, `gift/27`, zwei Einheitstests in `typen.rs`) schliessen das —
und die letzte davon brauchte zwei Anlaeufe: die Regel steht **symmetrisch** im Quelltext,
und ein Test, der nur eine Seite anfasst, laesst eine Mutation der anderen ueberleben.

**Zweiter Lauf: 24 von 24.**

## Was die Zahl NICHT sagt

**Die 24 Mutationen sind von Hand geschrieben**, je eine je Regel. Ein Erzeuger, der alle
Operatoren und Bedingungen des Pruefers systematisch verdreht, faende mehr. **100 % ist eine
Aussage ueber diese 24, nicht ueber den Pruefer** — genau wie eine Sprechprobe ueber drei
Fundstellen keinen Klassierer ueber 513 abnimmt. *Dieselbe Lehre, zweimal am selben Tag.*

Und die Probe deckt den **Pruefer**, nicht die **Emission**. Der Posten, den `README.md`
fuehrt — *Mutationsprobe auf der Annotationsemission* — bleibt offen, weil noch nichts
emittiert wird.


---

# Die zwei Teilpaesse geschlossen — und was die Mutationsprobe dabei fand

**2026-08-14.** Nach der Gegenpruefung standen zwei Paesse als `Teilgebaut` in der Liste.
Beide sind jetzt zu, und beide Reparaturen faengt die Mutationsprobe.

## Pass 3 — Modulaufloesung

Signaturen, Typen und Konstanten waren nach **blankem Namen** verschluesselt. Die
Aufloesung geht jetzt vom eigenen Modul nach aussen, dann ueber die `use`-Zeilen.

**Sie faengt beide Richtungen, und das ist der Beleg, dass sie stimmt:**

| Fall | vorher | nachher |
|---|---|---|
| `zwei::nimm(x)` mit `x + 1000` auf vollem `u32`, daneben ein fremdes `eins::Eng = u32 in 0..10` | **0 Fehler** — der fremde enge Typ gewann, M1 schwieg zu einem echten Ueberlauf | 2 Fehler |
| `eins::nimm(x)` mit `x + 1000` auf `0 .. 10`, daneben ein fremdes `zwei::Eng = u32` | **2 Fehler** — falscher Befund, der Pfad lief am letzten Abschnitt in ein fremdes Modul | 0 Fehler |

Ein stilles Loch **und** ein falscher Befund, beide aus derselben Zeile.

## Pass 8 — `effects` gegen den Rumpf

Bis hierher pruefte der Pass nur die **Deklaration**: Anwesenheit, `pure` allein,
`diverges`. Damit erzwang die Zusage *„`effects` ist nicht fail-open"* eine **Liste, nicht
ihre Wahrheit** — `effects { pure }` ueber einer schreibenden Funktion kam durch.

Jetzt muss **jedes Schreiben** und **jedes `locks`** von einer erklaerten Wirkung gedeckt
sein (`E005`, `E006`); gedeckt heisst: die erklaerte Stelle ist ein Praefix der
geschriebenen, `writes c.slots` deckt `c.slots[s].benutzt`.

**Der Pass bleibt `Teilgebaut`, und zwar mit Grund** — nicht aus Unfertigkeit:

* **Lesen wird nicht geprueft.** `FRAGMENTE.md` liest in jeder Funktion Stellen, die keine
  `reads`-Zeile nennt. Ob das ein Befund ueber die Fragmente ist oder die gemeinte Bedeutung
  von `effects`, **entscheidet der Ordner und nicht der Pass**. Ein Pruefer, der eine
  ungeklaerte Frage in seine Absagen einbaut, entscheidet sie stillschweigend.
* **Aufrufwirkungen ebenso nicht.** Dafuer muessten die Wirkungen des Gerufenen auf die
  Argumente des Aufrufers abgebildet werden. **Das ist der Posten, der `effects` erst
  kompositional macht.**

## Was die Mutationsprobe dazu sagte

Drei neue Mutationen (`rumpf-egal`, `sperre-egal`, `modul-egal`). Die dritte **ueberlebte** —
die Gegenbeispiele zur Modulkollision lagen im Scratchpad, nicht im Giftkorpus. Zwei
Dateien spaeter: **27 von 27.**

*Dasselbe Muster wie beim ersten Lauf: die Reparatur stand im Quelltext, die Zusicherung
nirgends. Ohne die Mutationsprobe waere es beide Male unbemerkt geblieben.*

**Stand danach: 3 von 9 Paessen ganz gebaut, 1 teilweise, 5 offen.** 50 Tests, 32
Giftdateien, fuenf Waechter gruen.


---

# A1 bis A4 gefahren — vier Tore, und drei fielen anders aus als geplant

**2026-08-14.** Der Plan (`PLAN.md` §A) setzte vier Posten mit zweiseitigen Toren. Alle vier
sind gefahren.

## A1 — `own` linear: **GRUEN auf die Mechanismusfrage**

Papiertest an F1, wie das Tor es verlangte, **ohne eine Zeile Pruefercode davor**.

**Die Stelle, an der es scheitern musste, traegt:** `revoke`s `traverse`-Rumpf ruft
`blatt_loeschen` mit zwei `own`-Zeigern. Ein linearer Wert waere nach dem ersten Durchgang
verbraucht — **er wird geliehen**, weil die Wirkungsliste ihn nicht unter `consumes` nennt.
Und diese Unterscheidung braucht **kein neues Wort**: `eff` fuehrt `consumes` bereits, und
`boot_end(t) effects { consumes t }` gegen `raw fn … requires BootPhase` macht sie schon.

> **Kein fuenfter Mechanismus.** Trennung faellt aus M2, wie die Ableitungstabelle in §3b es
> immer behauptet hat — die Grammatik muss es nur sagen.

**Aber die zweite Haelfte deckt Schaerferes auf, als das Tor gefragt hat.** Die Leihe traegt
die *Kette*; sie hat keinen **Ursprung**. `lock KAPPEN protects { eintraege }` nennt
**Plaetze**, keinen linearen Wert; `lockstmt = "locks" place block` hat **keinen Binder**;
`static mut` ist nicht linear; und **Gabbro hat keinen Adressoperator**, also kann niemand
einen Zeiger auf globalen Zustand bilden. Ein `device` hat eine Erzeugungsform
(`device Vtd(basis : Pa) at mmio`), eine `table` **hat keine**.

> **Damit steht die Kette auf einem Parameter, der aus dem Nichts kommt** — und das ist ein
> Befund, den keiner der 31 nennt. Er gehoert vor jede Zeile M2-Pass.

## A2 — Dynamische Aufrufe: **das Tor faellt auf „verbieten"**

67 `dyn`-Stellen im Kern. Aber die Aufschluesselung entscheidet:

| Trait | dynamische Stellen | **Implementierungen** |
|---|---|---|
| `SchedOps` | 10 | **1** (`KernelSched`) |
| `Park` | 9 | **1** (`Sicht<'_>`) |
| `DmaEnforcer` | 0 | 2 (benutzt schon statische Dispatch) |
| `FnMut`/`Fn` | ~~89~~ **64** | — (**Verschluesse**, s. u.) · *die 89 hat keinen Suchweg, berichtigt 2026-08-16, s. ERGEBNIS* |

**Die beiden Traits, die dynamisch benutzt werden, haben je EINE Implementierung.** Das ist
keine Polymorphie, sondern eine Schichtgrenze — der Aufruf ist statisch bekannt, und in
Gabbro verschwindet das Trait-Objekt.

> **`fnptr` braucht keinen Vertrag.** Der Posten aus «B9» faellt weg, und die Verbotsliste
> waechst statt der Grammatik.

**Der Rest ist eine Frage, die der Plan nicht vorgesehen hat: 64 Verschluesse** (*hier stand 89; die Zahl hatte keinen Suchweg*)**.** Gabbro hat
gar keine — weder `dyn FnMut` noch `impl FnMut`. Was daraus wird (einbetten, Zeiger plus
Kontext, oder Verbot), ist **unentschieden und neu**.

## A3 — `table … count N`: **gebaut, und ein Befund aus sich selbst**

Der Indextyp wird jetzt **erzeugt**: `index into T` erbt die Schranke aus `T`s `count`, und
M4 bekommt seine Zahl zum ersten Mal aus der Sprache statt aus der Konvention, dass jemand
`type SlotIdx = u32 in 0 ..< NSLOTS` passend danebenschreibt.

**Beim Bauen fiel auf, dass die halbe Aenderung nichts wert gewesen waere:** `index into` war
nur `slottype`, nicht `typeexpr` — der erzeugte Typ liess sich **in keiner Signatur nennen**,
also haette daneben doch wieder ein handgeschriebener Typ gestanden. Auch das ist zu
(`indexty` als `typeexpr`; `slottype` wird dadurch kuerzer statt laenger).

## A4 — Das Kostenmodell: **das Tor fiel ZWEIMAL, in beide Richtungen**

**Erst war die Implementierung falsch.** Sie berechnete `if`, `return` und das Laden von
Konstanten mit — §7 nennt aber genau **vier** Primitiven. Nach der Berichtigung hielten die
deklarierten Zahlen von `08-bereiche.gab` (4, 8, 8) **exakt**. *Die Deklarationen waren
richtig, der Rechner nicht.*

**Dann waren die Deklarationen falsch**, an drei anderen Stellen:

| | deklariert | gerechnet | warum |
|---|---|---|---|
| `einsammeln` | 4 096 | **831 488** | Traversierung ueber die ganze Tabelle: NSLOTS × (200 + 3) |
| `scharfschalten` | 64 | **1 032** | enthaelt einen `retry … bounded 1024 ops` |
| `faellige_wecken` | 4 096 | **5 120** | NFAEDEN × 5 |

Alle drei hatte ich geraten. **Das ist die Sorte Zahl, gegen die dieser Ordner sein
Messprotokoll geschrieben hat** — sie sah plausibel aus und war nie gerechnet.

**Der wertvollste Befund ist `K002`:** `04-schleifen.gab` hielt `PLANER` ueber einer vollen
Traversierung — **3 072 ops gegen `held <= 300`**. Und die Antwort ist *nicht*, `held` zu
erhoehen: **die Sperre gehoert IN den Durchgang.** An dieser Zahl haengt die Latenzaussage
jeder Wartestelle (§9.3), und ohne Pass 9 war sie eine Behauptung.

## Was A1–A4 zusammen bewegt haben

| | vorher | nachher |
|---|---|---|
| Paesse ganz gebaut | 3 von 9 | **4 von 9** (+ costs), 1 teilweise |
| Giftdateien | 32 | **36** |
| Mutationen gefangen | 27 von 27 | **32 von 32** |
| Waechter | 5 | 5 |

**Und drei Befunde, die es vor A1–A4 nicht gab:** der fehlende **Ursprung** der Eigentumskette
(A1), die **64 Verschluesse** ohne Form in der Sprache (A2) — *hier stand 89, eine Zahl ohne Suchweg* —, und `costs` an einer **rekursiven**
Funktion, das eine Annahme bleibt statt einer Rechnung (A4, im Passkopf benannt).


---

# Der Ursprung — und er loeste sich auf, statt geschlossen zu werden

**2026-08-14.** A1 hatte einen Befund hinterlassen, der vor jeder Zeile M2-Pass stand: die
Eigentumskette hat keinen Anfang. `lock L protects { … }` nennt Plaetze statt eines linearen
Werts, `locks` hat keinen Binder, `static mut` ist nicht linear, und **Gabbro hat keinen
Adressoperator** — niemand kann einen Zeiger auf globalen Zustand bilden.

**Die Antwort ist nicht ein neues Konstrukt, sondern eine Frage, die vorher niemand gestellt
hat: braucht Kernzustand ueberhaupt einen Zeiger?**

## Nachgesehen, nicht vermutet

`kernel/src/system.rs` schreibt `CAPS.write().cspace` — **eine** CapSpace-Instanz, hinter
einer Sperre. Das `&mut CapSpace`, das durch alle Caprock-Signaturen laeuft, ist **Rusts
Leihform**, nicht die Struktur der Sache. F1 hat sie mituebersetzt, weil die Vorlage sie hatte.

## Zwei Aussagen, und beide kosten kein Wort

| | |
|---|---|
| **Eine `table` IST Speicher.** Ihr Name ist ihr Ort: `Kappenraum.slots[s]` ist ein `place`, `Held(KAPPEN)` der Beleg | **eine** Instanz, also kein Zeigerpaar, also **keine Aliasfrage** |
| **Die Parameterliste eines `device` IST sein Konstruktor.** `device Vtd(basis : Pa)` sagt, woraus ein Vtd entsteht | die Adresse kommt aus Daten (ACPI-DMAR), nicht aus dem Nichts |

**F1 und F2 sind beide ohne einen einzigen Zeiger ausgeschrieben** und gehen durch alle fuenf
gebauten Paesse (`beispiele/09-ohne-zeiger.gab`, 19 Items, 0 Fehler).

## Was uebrig bleibt — und nur dort war Trennung je eine Frage

**DMA-Puffer, belegte Regionen, fremder Speicher.** Dort gibt eine Funktion Besitz her:

```gabbro
extern fn belegen(bytes : u64) -> ptr<normal, rw+own> Region effects { allocs halde };
extern fn freigeben(r : ptr<normal, rw+own> Region)          effects { consumes r };
```

`own` macht den Zeiger linear; **verbraucht, wenn `effects` ihn unter `consumes` nennt,
sonst geliehen.** Kein fuenfter Mechanismus, kein neues Wort, keine Grammatikaenderung.

> **Die Lehre ist nicht die Antwort, sondern die Frage.** Der Befund lautete *„der Kette
> fehlt der Anfang"* — und die Kette war das Problem. Sie stand nur da, weil ein
> Rust-Original sie hatte. **Ein Fragment, das seine Vorlage mituebersetzt, bringt deren
> Zwaenge mit, und die sehen dann wie Anforderungen der neuen Sprache aus.** Das trifft die
> anderen fuenf Fragmente genauso, und es ist ein Grund mehr, sie nachzuziehen.

**Damit ist der letzte Entwurfsposten vor dem M2-Pass weg.** Was fehlt, ist nur noch der Pass.


---

# Die 200 000 ausgezaehlt — die Zahl, auf der Gabbros ganze These ruht

**2026-08-14, gemessen statt geschaetzt.** `l4v` bei `f4940273` (2026-08-08), flacher Klon,
Zeilen in `*.thy`. **Eine Architektur (ARM)**, damit die Zahlen vergleichbar sind: der Baum
traegt heute fuenf, und ein Gesamtzaehler ueber `proof/` (861 309) misst die Architekturzahl
mit statt den Beweisaufwand.

| Posten | Verzeichnis | Zeilen | Anteil |
|---|---|---|---|
| **Invariantenerhaltung** ueber dem abstrakten Modell | `proof/invariant-abstract` (neutral + ARM) | **76 873** | **32,1 %** |
| **Verfeinerung** abstrakt → ausfuehrbar | `proof/refine` | **95 915** | **40,1 %** |
| **Verfeinerung** ausfuehrbar → C | `proof/crefine` | **66 670** | **27,8 %** |
| **funktionale Korrektheit, ARM** | | **239 458** | 100 % |

Dazu, **oben drauf und getrennt**:

| | | |
|---|---|---|
| Sicherheitssaetze (Posten 5) | `proof/infoflow` + `proof/access-control` | **56 323** = **+23,5 %** |
| C-Semantik (Posten 2) | `tools/c-parser` | 86 891 |
| Binaerverifikation (Posten 4) | `tools/asmrefine` | 10 651 |
| abstrakte Spezifikation | `spec/abstract` (neutral + ARM) | 10 280 |
| ausfuehrbare Spezifikation | `spec/design` | 7 695 |

> **Die bestaetigte Zahl haelt.** `TODO.md` fuehrt „Beweise im `l4v`-Repo ~200 000" als
> nachgeprueft; gemessen sind es **239 458 fuer die funktionale Korrektheit einer
> Architektur**. Groessenordnung und Zuschnitt stimmen — die Zahl war richtig, sie war nur
> **unaufgeschluesselt**, und die Aufschluesselung ist das, woran Gabbros These haengt.

## Was die Aufteilung fuer Gabbro sagt — und sie sagt drei verschiedene Dinge

**Gabbros Argument lautet: die Verfeinerung faellt weg, weil Spezifikation und Implementierung
dieselbe Sprache sind.** Das sind **67,9 %**. Aber die drei Drittel verhalten sich verschieden:

| | Anteil | was Gabbro damit macht |
|---|---|---|
| **abstrakt → ausfuehrbar** | **40,1 %** | **faellt strukturell weg.** Eine Schicht statt zwei — das ist die Low\*-Anordnung und der belastbarste Teil der These |
| **ausfuehrbar → C** | **27,8 %** | **wird nicht wegbewiesen, sondern wegvertraut.** Die flache Absenkung ist eine Zusage; `BEWEIS.md` bucht `restrict` und `volatile` als Vertrauen. Zurueckholbar nur ueber Posten 4 — und **das Werkzeug dafuer ist klein** (10 651 Zeilen), der Beweis nicht |
| **Invariantenerhaltung** | **32,1 %** | **faellt NICHT mit den Schichten.** Amortisierbar ueber `table … ops`, aber **nur wo alle Mutationen erzeugt sind** — die K-Bedingung des Messprotokolls. Wieviele Traeger das erfuellen, ist **nie gezaehlt worden** |
| **Sicherheitssaetze** | **+23,5 %** | **gar nicht adressiert** (Posten 5) |

> **Damit ist „die 19,5 : 1 nimmt Gabbro weg" auf eine pruefbare Form gebracht:**
> **40 % strukturell, 28 % ins Vertrauen verschoben, 32 % bleiben als Invariantenarbeit** —
> und die 32 % sind genau der Posten, dessen Amortisation an einer Bedingung haengt, die
> niemand gemessen hat.

**Die Kennzahl-Vorhersage aendert sich damit nicht, ihre Begruendung schon:** wer 0,5 : 1
erwartet, erwartet, dass die 32 % vollstaendig amortisieren **und** die 28 % vertrauenswuerdig
sind. Beides ist heute unbelegt.


---

# Die Suche nach weiteren B13-artigen Fehlurteilen — vier gefunden, drei Klassen

**2026-08-14.** Die B13-Lehre lautet: *ein Urteil „nicht formulierbar" kann falsch sein, weil es
die **handgeschriebene** Form voraussetzt — die erzeugte braucht die Aussage gar nicht.* Alle
absoluten Urteile des Ordners sind daraufhin durchgesehen und, wo moeglich, **gegen den
Uebersetzer gefahren** statt beurteilt.

## Klasse 1 — B13-artig: das Urteil setzt die Handschrift voraus

| | Urteil | der dritte Ausgang |
|---|---|---|
| **«B7»** | *„`return Completion { id: …, len: … }` ist nicht schreibbar"* — kein Verbundliteral in `expr` | **Die Parameterliste einer Deklaration IST ihr Konstruktor.** Genau das ist am 2026-08-14 fuer `device` gebaut worden (`Vtd(basis)`); ein `type Completion = { id, len }` bekaeme `Completion(id, len)` aus **demselben Mechanismus**. Das Urteil setzte voraus, dass ein Literal eine **syntaktische Form** sein muss |
| **«B10»** | *„`traverse` liefert keinen Wert, es gibt kein `break`; die Suche nach dem ERSTEN Treffer wird zum Leeren der ganzen Menge, ein Operationszaehler ist nicht erhebbar"* | **Zwei Drittel loesen sich auf.** Eine **erzeugte** Suchoperation (`ops finde`) gibt den ersten Treffer ohne `break`; der Zaehler ist `accumulates` — **und `accumulates` war selbst der dritte Ausgang fuer «B21»**. Uebrig bleibt nur, dass ein handgeschriebener Suchrumpf weiter nicht geht |
| **«B26»** | *„`transition reset { DEVICE_STATUS: any -> 0 }` ist nicht schreibbar: es gibt keinen Platzhalter fuer den Vorzustand"* | Eine **erzeugte** `reset`-Operation ueber der `state`-Deklaration braucht kein `any` — sie ist der Uebergang in den Anfangszustand, und den nennt die Deklaration bereits |

## Klasse 2 — schlicht falsch: gegen den Uebersetzer gefahren

| | Urteil | gefahren |
|---|---|---|
| **«B12»** | *„`forall i in 0 ..< MSG_WORDS` ist nicht schreibbar: die sieben Domaenen decken es nicht"* | **`elems of` IST eine der acht Domaenen.** `forall w in elems of msg : w == 0` **parst und geht durch alle Paesse.** Eine Zahlenbereichs-Domaene fehlt weiter — die Aussage ueber die Nachrichtenworte ist aber schreibbar, und genau die war der Anlass |
| **«B14»** (halb) | *„`option` gibt es nur als `slottype`, nicht als `typeexpr`"* | **Mit A3 mitgekommen**, ohne dass ich es gemerkt habe: `impl fn f(o : option index into T)` geht. *Die zweite Haelfte — `let … else` verlangt rechts einen `call` — steht weiter offen* |

## Klasse 3 — echt, und ausdruecklich NICHT in den dritten Ausgang geschoben

* **«B15» Generizitaet.** `Queue(T, const N)` braucht **Monomorphisierung**, und die ist
  [`PLAN.md`](PLAN.md)s eigener Kandidat fuer *„zwei geforderte Eigenschaften widersprechen
  einander"* — sie ist die erste nicht-flache Absenkung und greift M-Gold-2 an. **Hier gibt es
  keinen dritten Ausgang, und ihn zu behaupten waere derselbe Fehler wie B13, nur andersherum.**
* **«B23»/«B20» Granularitaet.** Eine Klasse je *Register* statt je *Feld*; `wrapping` am
  Slottyp statt am Registertyp. Das ist **fehlende Feinheit der Notation**, keine erzeugbare
  Form. Ehrlich offen.
* **«B27»** `prim fn` ohne `abi`-Block: ein fehlendes Konstrukt, kein Fehlurteil.

## Und zwei stehengebliebene Urteile

* [`FRAGMENTE.md`](FRAGMENTE.md):62 sagt weiter *„`forever` hat keinen Ausgang"* — `leaves`
  gibt es seit der dritten Fassung.
* [`BEWEIS.md`](BEWEIS.md):376 sagt *„W^X bleibt unformulierbar"* — `walk` + `mappings of` +
  `embeds` gibt es seit der Festlegung.

**Beide bleiben stehen**, weil der Ordner seine widerlegten Fassungen behaelt; die Widerlegung
steht hier, nicht dort.

## Die Lehre, in der Form, in der sie beim naechsten Mal greift

> **Ein Urteil „nicht formulierbar" ist erst vollstaendig, wenn es sagt, WELCHE FORM es
> voraussetzt.** B13, B7, B10 und B26 setzten alle die Handschrift voraus und nannten es nicht.
> Die Pruefzeile dazu ist billig und mechanisch: *waere die Aussage noetig, wenn die Operation
> erzeugt waere?* — **und sie gehoert in die Fragmentvorschrift**, neben die vier
> Pruefschritte, die dort schon stehen.
>
> **Und sie hat einen zweiten Halbsatz, ohne den sie Schlagseite hat:**
> *…**und was kostet die erzeugte Form die Schablonenflaeche?***
>
> **Der dritte Ausgang ist nicht kostenlos — er verschiebt Beweislast an EINEN Empfaenger.**
> `by consuming`, `table ops`, `transset`, `exchange`, `accumulates`, und jetzt die vier
> Kandidaten dieser Nachpruefung: alles faellt *„einmal in der Schablone"*, und die Schablone
> ist die vertrauenskritischste unbewiesene Flaeche. **Ohne Zaehlung waechst sie monoton und
> unbeziffert — genau wie die Axiomschicht vor ihrer Auszaehlung.**
>
> **Deshalb gibt es seit dem 2026-08-14 die dritte Zaehlspalte:** `gabbro schablonen`,
> **16 Schablonen, 16 davon unbewiesen**, jede mit dem Satz, was genau einmal gezeigt werden
> muss. Ein Eintrag ohne diesen Satz ist ein Name und keine Buchung, und ein Test setzt das
> durch. **Der eine Isabelle-Posten ist damit keine Zahl 1, sondern eine Liste mit Laenge.**

### Die Grenze dieser Nachpruefung — und sie gehoert an die Messstelle, nicht in eine Fussnote

**Bei «B12» und «B14» steht als Beleg „parst und geht durch alle Paesse".** Das ist ein
legitimes Orakel fuer **schreibbar** — der Uebersetzer entscheidet genau das. **Es ist kein
Orakel fuer „traegt".** Die gebauten Paesse pruefen Grammatik, Namen, Bereiche, Schleifenmarken,
Wirkungen und Kosten; sie pruefen **nicht die Semantik dahinter** — ob `elems of msg` wirklich
ueber die Nachrichtenworte quantifiziert, entscheidet kein Pass, sondern die Bedeutung der
Domaene.

> **Beide Aussagen sauber getrennt:** «B12» behauptete, die Aussage sei **nicht schreibbar** —
> das ist widerlegt. Ob sie **traegt**, ist damit nicht gezeigt, und **wer diese Zeile spaeter
> als Beleg fuer das Zweite liest, erbt einen Zirkel:** ein junger Pruefer wuerde dann seine
> eigene Unvollstaendigkeit als Bestaetigung ausgeben.


---

# Der Pruefer als Messgeraet fuer die Messungen, die vor ihm stehen sollten

**2026-08-14.** Die [`HISTORIE.md`](HISTORIE.md) fuehrt den Bruch der Reihenfolgeregel. **Ein
aufgezeichneter Bruch ist kein Freibrief dafuer, dass die Schere weiter aufgeht** — und je
mehr Pruefer vor der 17er-Zaehlung entsteht, desto teurer wird deren unguenstiger Ausgang und
desto groesser der Druck, ihn umzudeuten.

**Der Ausweg ist nicht, das Werkzeug anzuhalten, sondern es der Warteschlange dienstbar zu
machen.** Die K-Bedingung des Messprotokolls ist mit der vorhandenen Passinfrastruktur
mechanisch pruefbar:

> *„Je Pflicht ist das eine mechanische Frage: **sind alle Schreibstellen des Traegers
> erzeugt?**"*

`gabbro k-bedingung <datei>` beantwortet sie je Traeger — und **liefert nebenbei die
`breaking`-Liste, also Posten L3 der Restliste**, genau wie das Protokoll es vorhersagt.
Dieselbe Regel gibt es jetzt auch als Absage: **`D001`**, denn `SPRACHE.md` §10.2 sagt
ohnehin *„handgeschriebene Mutation an einer `table` mit `ops` ist ein Uebersetzungsfehler"*.

## Der erste Lauf, am eigenen Beispielkorpus

```
Traeger      ops    Handschrift  breaking  K
Kappenraum   NEIN   9            0         FAELLT
Objekte      NEIN   2            0         FAELLT
-- 2 Traeger: 0 mal haelt K, 2 mal faellt sie.
```

**Null von zwei.** Beide Tabellen nennen kein `ops`, beide werden von Hand mutiert — **genau
die Lage, in der `FRAGMENTE.md` F1 steht**, und genau der Grund, warum «B29» und «B13» dort
toedlich aussahen. *Die Zahl ist damit kein Befund gegen die Sprache, sondern der erste
mechanische Eingang in Messung 2* — die Spalte K/A/W je Pflicht faengt hier an.

**Damit schliesst die Schere von der anderen Seite**, und der Eintrag in `HISTORIE.md`
bekommt nachtraeglich einen Ertrag statt nur eines Preises.

---

## Zwei Praezisierungen an den neuen Registern

**1. Die Fallrichtung der Schablonen-Ratsche steht jetzt da, und ein Test haelt sie:**

> **Ein Eintrag verlaesst die Liste nur BEWIESEN oder MITSAMT SEINEM KONSTRUKT** — nicht
> durch Umformulierung, nicht durch Zusammenfassen zweier Eintraege zu einem, nicht dadurch,
> dass die Pflicht „eigentlich schon in einer anderen steckt". **Eine Flaeche, die man durch
> Umschreiben verkleinert, ist nicht kleiner geworden.**

**2. `32 von 32` hatte die falsche Bezugsgroesse.** Die ehrliche ist **Mutationen je
Emissionsflaeche**:

| Flaeche | Mutationen | |
|---|---|---|
| **Pruefer** (Absagen) | **32** | gebaut, mutierbar |
| **Annotationsemission** — der Wunschform-Kanal | **0** | **nicht gebaut, also nicht beschaedigbar** |
| **C-Emission** | **0** | nicht gebaut |
| **Erzeuger-Schablonen** | **0** | 16 Eintraege, ueberwiegend entworfen — was kein Code ist, faengt keine Mutation |

> **Eine Flaeche mit 0 Mutationen ist nicht gedeckt, sondern unbeschaedigbar.** `32 von 32`
> misst die **Codehaelfte des Pruefers**; ueber Annotation und Emission sagt es nichts — und
> `README.md` fuehrt die Annotationsemission ausdruecklich als die Stelle, an der ein
> stimmig abgeschwaechter Erzeuger **von keinem Beweis** gefangen wird.


---

# PAPIERTEST — Gruppe und Sperren am CapSpace/CDT-Paar

**Gefahren 2026-08-14** gegen `arch/x86_64`. Drei Fragen nach Protokoll, drei Antworten, ein
Urteil ueber ein Kandidatenkonstrukt — und zwei Luecken, die nicht im Auftrag standen.

> **Nachgeprueft, nicht uebernommen.** Jede Fundstelle dieses Protokolls ist gegen den Baum
> gehalten worden; was dabei dazukam, steht als *nachgetragen* markiert.

## Antwort 1 — die Verbindungs-Invarianten: drei echte, vier strukturelle, und sie sind **schon formalisiert**

`audit_cdt` fuehrt die Liste als Anomalie-Codes 1–7. **K1** (belegter Slot → belegtes Objekt),
**K2** (`refcount(o)` == Zahl der zeigenden Slots — *das ist «B13» woertlich*) und **K3**
(belegt ⟺ `refcount > 0`) sind **Verbindungs**-Invarianten; K4–K7 sind strukturell.

**Der Fund, der die Schablonenfrage veraendert:**
`Verification/capability-system/proofs/cap_space.rs` (**832 Zeilen, nachgeprueft**) fuehrt genau
diese Liste als **eine** `spec fn cap_inv` (Zeile 56, Konjunktion der Klauseln 1–7, in Verus).
Der Kopf der Datei sagt die Sache selbst:

> *„Jede Capability-Operation wird bewiesen, `cap_inv` zu ERHALTEN — d. h. eine Operation
> erhaelt ALLE Invarianten zugleich (anders als die getrennten Pilot-Modelle)."*

**Das ist die Gruppen-Schablone, und sie existiert bereits von Hand.** Damit hat der Eintrag
`gruppe.ops` eine **Vorlage statt eines leeren Blatts**: die „einmal je Operation"-Beweise
waeren von der Schablone zu **erzeugen** statt zu erfinden. Und die Uebertragungsrichtung ist
im Baum belegt — an zwei Stellen war das Audit-Oracle **schwaecher** als die Verus-Invariante
und wurde nachgezogen. *Die formale Fassung ist die Quelle, das Audit die Projektion.*

## Antwort 2 — die Gruppe existiert schon als Struktur; `by ops` verschaerft eine vorhandene Grenze

**Der CDT ist keine zweite Tabelle:** `Mdb` (parent/first_child/next_sibling/prev_sibling)
liegt **im Slot**. Das Paar ist `{slots, objects}` — beide Slabs in **einem** `CapSpace`, alle
Mutationen Methoden ueber `&mut self`, also ueber beiden Traegern zugleich. **Gabbros
Gruppen-`ops` gibt einer vorhandenen Architektur eine Grammatik, keine neue.**

**Die Schreibstellen des kritischen Felds, einzeln nachgeprueft:**

| Stelle | was | bestaetigt |
|---|---|---|
| `space.rs:1018` | `refcount: 1` im Verbundliteral (install) | ja |
| `space.rs:543` | `+= 1` (copy, von mint mitbenutzt) | ja |
| `space.rs:1067` | `-= 1`, **Null-Pruefung in :1068 danach** | ja — *das ist «B29»* |
| *nachgetragen* | `object.rs:191` `refcount: 0` im `EMPTY`-Vorgabewert | keine Mutation eines lebenden Objekts |

`object.rs:182` fuehrt das Feld als `pub(crate)`. **Rusts Sichtbarkeit ist damit das heutige
`by ops` auf Crate-Ebene — die Grammatikzeile verengt Crate auf Konstrukt, sie erfindet die
Grenze nicht.**

> **B13-Urteil am Papier bestaetigt:** mit Gruppen-`ops` faellt K2 je Operation; mit `ops` je
> Einzeltabelle faellt sie nicht. **Der Gruppen-Pruefsatz haelt.**

## Antwort 3 — der Sperrabdruck: EINE Sperre, und von einer Art, die die Sprache nicht kennt

`static CAPS: RwSpinLock<Caps>` (`system.rs:732`, Rang R0, aeusserster). Mutationen nehmen
`write()` exklusiv, **die heisse Cap-Aufloesung nimmt nur `read()`**. Der Sperrabdruck der
Gruppenoperationen ist einheitlich; die Frage *„eine gemeinsame oder zwei mit Ordnung"* ist
beantwortet: **eine, per Architektur.**

*Nachgetragen, weil es L-A beziffert:* **33 `CAPS.read()`-Stellen gegen 44 `CAPS.write()`.**

### Das Urteil: **`locks ordered` stirbt**

Die Pruefzeile war, ob jede Mehrfachnahme derselben Klasse lexikalisch gemeinsam steht. **Die
Antwort ist staerker: es gibt keine einzige Mehrfachnahme derselben Klasse.** `system.rs:15`
fuehrt es als Invariante — *„kein Pfad nimmt zwei verschiedene `SCHEDS[*]` gleichzeitig"* — und
die Migration, der erwartete Prueffall, arbeitet anders: `SCHEDS[src].lock().migration_candidate()`
(`system.rs:2804`) — **nehmen, waehlen, freigeben**, dann die Zielseite mit Neuvalidierung.

> **Null Prueffaelle — das Wort kommt nicht in die Grammatik.** Kein Konstrukt ohne gemessenen
> Bedarf; dieselbe Regel, die `abi { … }` gestoppt hat. **Und der Papiertest hat damit genau
> das getan, wofuer er gebaut war: er hat seinen eigenen Kandidaten getoetet, statt ihn zu
> bestaetigen.**

## Zwei echte Luecken, die der Test stattdessen fand

**L-A — die Sprache kennt keine geteilte Sperrnahme.** `lock`/`locks` und der `Held`-Zeuge sind
**exklusiv** gedacht. Die heisseste Sperre des Baums ist ein **Reader-Writer**-Lock, und der
heisse Pfad ist die geteilte Seite: **33 Fundstellen**. Ohne `locks shared` — *Held geteilt:
liest die geschuetzten Plaetze, schreibt sie nicht, **mechanisch pruefbar gegen die Effektmenge
des Blocks*** — ist die Cap-Aufloesung, **der meistgelaufene Pfad des Kernels, nicht
schreibbar.** Konstruktluecke erster Ordnung, auf keiner Liste.

**L-B — Uebergabe mit Neuvalidierung.** Das Muster, das Doppelnahme **ersetzt**: unter Sperre A
waehlen, freigeben, unter B fortsetzen, **Befund neu pruefen**. Die ehrliche Fassung ist kein
Atomizitaetsversprechen, sondern ein **Zwang**: ein Wert, der eine Sperrgrenze ueberquert,
verliert seine Fakten (*das tut die Sprache schon* — V-Regeln sterben) **und** die Fortsetzung
muss die tragende Bedingung erneut pruefen. Skizze: die Auswahl liefert `ghost Stale(T)`, das
erst eine erneute Pruefung unter der neuen Sperre in ein nutzbares `T` wandelt.
**Kandidat, kein Beschluss.**

## Nebenbefunde — und N1 geht an Caprock, nicht an Gabbro

**N1 — die zwei dokumentierten Sperrordnungen widersprechen sich, und zwar schaerfer als
beschrieben.** Nachgeprueft:

* `system.rs:11–13`: *„`CAPS` (R0) → `EPS`/… (R1) → `SCHEDS[*]` (R2) → `Heap.inner` (R3) →
  `MEM` (R4, **innerster**)"* — und dazu **„`MEM` haelt nie einen weiteren Lock"**.
* `system.rs:723`: *„aussen→innen: `CAPS` < {`EPS[i]`, `NTFNS[i]`, **`MEM`**} < `SCHEDS[*]` <
  `FP_STATES`"* — **MEM in der Mitte einer Kette, die weitergeht**.

Beides zugleich geht nicht: entweder ist MEM Blatt (Kopf) oder es hat SCHEDS unter sich (:723).
**Genau diese Fehlerklasse — zwei Prosaordnungen, die niemand gegeneinander prueft — macht eine
deklarierte `rank`-Zeile strukturell unmoeglich.** *An Caprock zu klaeren.*

**N2 — `FP_OWNER` als „atomares Beiboot" der Sperrordnung.** Der Reschedule-Pfad haelt
`SCHEDS[core]` „+ atomares `FP_OWNER`" — ein Atomic, das **ausdruecklich Teil der
Deadlock-Herleitung** ist. Die Grenzziehung *„welche Atomics sind Ordnungsteilnehmer"* gehoert
in die Ordering-Vollzaehlung als **eigene Spalte**.

**N3 — die RwSpinLock-Beobachtung schaerft die `held`-Rechnung.** `held <= K ops` war fuer
**exklusive** Halter gedacht; auf der geteilten Seite ist die Rechengroesse nicht die Haltezeit
eines Lesers, sondern die **Writer-Wartezeit unter Leserdruck**. **Die Latenzformel aus §9.3
braucht fuer Leser-Schreiber-Sperren einen eigenen Zweig** — und der Kostenpass rechnet heute
nur den exklusiven Fall.

## Die Sprechprobe, die der Test verlangt hat — gefahren

`beispiele/gift/37-b29-unter-ops.gab` schreibt `zaehler -= 1` von Hand an einer `table` mit
`ops`. **Dieselbe Zeile faellt zweimal:**

```
Fehler: [D001] `von_hand_senken` schreibt `Objekte` von Hand, obwohl die Tabelle `ops` nennt
Fehler: [M104] `o.slots[…].zaehler` -= verlaesst den Bereich: `u32 in 0 .. 65535` gegen `1`
```

**Die Sprachform und die Messform an derselben Stelle** — `D001` sagt „die K-Bedingung faellt",
`M104` ist der Unterlauf, der «B13» toedlich aussehen liess. Der K-Bedingungsbericht dazu:
*1 Traeger, 0 mal haelt K.*

## Was aus dem Papiertest geworden ist — noch am selben Tag

`locks ordered` ist **gestrichen** (Nachruf in [HISTORIE.md](HISTORIE.md)). **L-A ist
gebaut**, weil die Zusage genau eine ist und mechanisch faellt: *geteilt halten heisst, die
geschuetzten Plaetze zu lesen und nicht zu schreiben* — `protects` nennt sie, der Rumpf nennt
seine Ziele, der Abgleich ist derselbe wie bei `E006`.

| | |
|---|---|
| Grammatik | `locks [shared] place block`, `lock … [shared held <= K ops]`, `effects { locks shared N }` |
| Absagen | `H001` `H002` `H003` `H004` `E007` `K004` |
| Proben | Beispiel `10-geteilte-sperre.gab`; Gift `38`–`41` |
| Mutationen | **+5, alle gefangen** — 37 von 37 auf der Flaeche *pruefer* |

**Zwei Zahlen statt einer** (Nebenbefund N3 ist damit zu): `held` galt fuer **exklusive**
Halter, und der Kostenpass rechnete nur den. `shared held` ist eine eigene Zusage mit eigener
Pruefung, weil die tragende Groesse auf der geteilten Seite eine andere ist — die
**Schreiberwartezeit unter Leserdruck**.

**Die gefaehrliche Richtung hat einen eigenen Code bekommen.** `E007` faellt, wenn ein Rumpf
exklusiv nimmt und `locks shared` erklaert; die Umkehrung ist zulaessig. Wer mehr haelt, als
er zusagt, irrt in die sichere Seite — wer weniger haelt, laesst den Aufrufer eine
Latenzrechnung auf Nebenlaeufigkeit bauen, die es nicht gibt.

> **Offen bleibt der Zeuge am Aufrufrand** — `requires Held(N)` aus einem geteilten Block
> heraus. Das ist dieselbe Asymmetrie eine Ebene hoeher und braucht den **Aufrufgraphen**:
> genau das Loch, an dem in Pass 8 schon die Aufrufwirkungen haengen. *Ein Loch, nicht zwei.*

## Berichtigung zur Sprechproben-Begründung — 2026-08-15

Ich hatte den B29-Schnitt als in **zwei unabhängig geschriebenen Kernen** stehend gemeldet.
**Falsch.** `git log --follow` zeigt `R099` — eine Umbenennung mit 99 % Ähnlichkeit von
`crates/sel4lake-cap/src/space.rs` nach `crates/caprock-cap/src/space.rs`, dieselbe
Autorenlinie. Die zweite Kopie lag ausserhalb von git, ein älterer Schnappschuss derselben
Abstammung. **Zwei Pfade sind kein Beleg für zwei Herkünfte** (`HISTORIE.md`).

**Die tragfähige Begründung ist gemessen statt erschlossen.** `git log -L 1060,1075` über die
Löschpfad-Region:

| | |
|---|---|
| Ursprung | `2111f30`, **2026-06-23** — dort Zeile 341/342, wörtlich dieselbe Reihenfolge |
| Umbauten der Region seither | **5**, bis `b026c83` (2026-07-29) |
| davon an der Freigabesemantik selbst | **2** — `Reply-Cap mit Revocation`, `DMA-Teardown-Token` |

Die Zeilenfolge — `-= 1`, Null-Prüfung **danach** — hat alle fünf überlebt, dazu eine
Paketumbenennung und die Verdopplung der Datei.

> **B29 ist kein Ausrutscher, sondern ein Attraktor.** Wer den Löschpfad schreibt, schreibt
> ihn so — auch beim fünften Umbau, auch nachdem die Falle einmal bezahlt war. Das trägt die
> Sprechproben-Pflicht besser als die widerlegte Unabhängigkeitsbehauptung, denn es sagt
> etwas über die **Wiederkehr**, nicht über die Verbreitung.

---

# VORAB — Messprotokoll: systematisch erzeugte Mutationen gegen den Pruefer

**Eigener Commit, VOR dem Lauf.** Nach dem Lauf wird an diesem Abschnitt nichts geaendert;
das Ergebnis kommt darunter.

> **Anmerkung zur Form:** Der Auftrag verlangt das Vorab-Protokoll in einem eigenen Commit
> *und* einen gitignorierten Werkstattordner. Beides zugleich geht nicht — ein Commit ueber
> eine ignorierte Datei ist leer. Das Vorab steht deshalb **hier**, wo die Vorab-Protokolle
> dieses Ordners immer standen (so schon bei Messung 2), und die Werkstattfassung verweist
> darauf. *Die Regel ist die Unveraenderlichkeit nach dem Lauf, nicht der Ordner.*

## Was gemessen wird

Ein Generator verdreht **systematisch** je eine Stelle in `crates/gabbro-check/src/*.rs` —
im Unterschied zu den 38 **von Hand** gewaehlten Mutationen, die je eine Regel treffen, die
ich beim Schreiben im Kopf hatte. *Genau das ist der Verdacht: `38 von 38` ist eine Aussage
ueber die 38 Stellen, die mir eingefallen sind.*

| Klasse | Verdrehung |
|---|---|
| `VERGL` | Vergleichsoperator kippen (`>` ↔ `>=`, `<` ↔ `<=`, `==` ↔ `!=`) |
| `BOOL` | `&&` ↔ `\|\|` |
| `NEG` | Bedingung negieren |
| `KONST` | Ganzzahlliteral um 1 verschieben |
| `LEER` | Schleifenrumpf uebergehen |

## Zaehlregel

* **Ein Mutant zaehlt nur, wenn er UEBERSETZT.** Bricht `cargo build`, ist er **ungueltig**
  und faellt aus Zaehler **und** Nenner. *Eine Deckungszahl zaehlt Belege, nicht Versuche*
  (`WERKZEUGKASTEN.md` W1).
* **Gefangen** = `cargo test` faellt **oder** eine Giftprobe verliert ihren Code **oder** ein
  sauberes Beispiel bekommt eine Absage.
* **Entkommen** = alle Proben bleiben gruen.
* Die 38 Handmutationen werden **getrennt** gefuehrt und nicht dazugezaehlt.

## Kippregel

Haengt oder bricht die Probe (Zeitschranke 120 s), zaehlt der Mutant als **ungueltig**, nicht
als gefangen. **Grenzfaelle kippen in die teurere Spalte, werden nie geteilt.**

## Das zweiseitige Tor

| | |
|---|---|
| **bestanden** | **mindestens ein entkommener Mutant**, den die 38 Handmutationen nicht finden — dann ist `38 von 38` als Aussage ueber 38 Stellen entlarvt |
| **gefallen** | **kein einziger entkommt** — dann ist der Pruefer an den erzeugten Stellen so dicht wie an den gewaehlten. **Das ist ein Ergebnis, kein Misserfolg.** |
| **ungueltig** | **weniger als 30 Mutanten uebersetzen** — dann misst der Lauf den Generator, nicht den Pruefer |

## Was der Lauf ausdruecklich NICHT sagt

Nichts ueber die Emissionsflaechen. Annotation, Code und Schablone haben weiterhin **0
Mutationen** — und was 0 Mutationen hat, ist nicht gedeckt, sondern **unbeschaedigbar**.

## ERGEBNIS des Laufs — 2026-08-15, Stichprobe 40 von 377 Stellen

**Das Tor ist BESTANDEN, und deutlich.** Die vorab festgelegte Zahl:

| | |
|---|---|
| mutierbare Stellen gefunden | **377** in 13 Dateien |
| gezogen (deterministisch, fester Keim) | **40** |
| **gefangen** | **7** |
| **entkommen** | **32** |
| ungueltig (uebersetzt nicht) | **1** — aus Zaehler **und** Nenner |
| **Quote** | **7 von 39 = 18 %** |

Gegen `38 von 38 = 100 %` der Handmutationen. **`38 von 38` war eine Aussage ueber 38
Stellen, die mir beim Schreiben eingefallen sind — nicht ueber den Pruefer.** Genau das stand
als Verdacht im TODO, und es ist jetzt beziffert.

### Die Aufteilung der 32 — NACHTRAEGLICH, und darum getrennt gefuehrt

**Die 18 % oben stehen und werden nicht angefasst** (R2). Was hier folgt, ist eine
*Klassifikation danach*, keine Neurechnung — sie sagt, **was** entkommen ist, nicht wie viele.

| | Klasse | was es bedeutet |
|---:|---|---|
| **15** | **REGEL** | echte Luecke: die Stelle koennte ausfallen, ohne dass eine Probe faellt |
| 4 | Meldungstext / Dokumentation | eine verdrehte Fundstellenangabe ist keine Regelverletzung |
| 3 | Testkoerper | misst die Probe, nicht die Regel — **Filterluecke des Generators** |

**Die drei Testkoerper und die vier Meldungstexte sind ein Befund ueber den Generator**, nicht
ueber den Pruefer: sein `BLIND`-Filter erkennt Kommentare und lange Zeichenketten, aber nicht
`#[cfg(test)]`-Bereiche und nicht mehrzeilige Meldungen. *Auch das gehoert berichtet — ein
Messgeraet, dessen Ausschuss man nicht kennt, liefert keine Zahl, sondern einen Eindruck.*

### Die fuenfzehn echten Luecken

```
typen.rs:277  [VERGL]  if a.min >= 0 && b.min > 0 {
typen.rs:317  [BOOL]   if a.min < 0 || b.min < 0 {
typen.rs:343  [KONST]  if bits >= 127 {
typen.rs:346  [KONST]  (1i128 << bits) - 1
typen.rs:352  [VERGL]  if b.min < 0 || b.max >= a.breite as i128 {
typen.rs:257  [KONST]  let min = ecken.iter().copied().min().unwrap_or(0);
umgebung.rs:121 [VERGL] if z.rsplit("::").next() == Some(kurz) {
umgebung.rs:438 [BOOL]  BinOp::Und => i128::from(x != 0 && y != 0),
umgebung.rs:439 [BOOL]  BinOp::Oder => i128::from(x != 0 || y != 0),
umgebung.rs:439 [KONST] (dieselbe Zeile, andere Verdrehung)
umgebung.rs:543 [KONST] .unwrap_or_else(|| IntBereich::voll(32, false));
kosten.rs:244 [KONST]   XForm::Update { rumpf, .. } => Kosten::Zahl(1).plus(…)
kosten.rs:248 [KONST]   Kosten::Zahl(1).plus(self.ruf(&l.ruf)).plus(self.block(&l.sonst))
kbedingung.rs:194 [KONST] let (mut haelt, mut faellt) = (0, 0);
schablonen.rs:270 [KONST] n + 1,
```

**Das Muster ist lesbar, und es ist nicht zufaellig:** die Luecken haeufen sich in
`typen.rs` (**6**) und `umgebung.rs` (**5**) — der **Bereichsarithmetik** und der
**Konstantenauswertung**. Beides sind Schichten, die kein Beispiel direkt anspricht: die
Beispiele pruefen, ob eine Absage faellt, nicht ob eine Grenze **genau** stimmt. Ein Beispiel
mit `u8 in 0 .. 200` faellt bei jeder falschen Obergrenze zwischen 200 und 255 gleich aus.

> **Der eigentliche Befund ist damit nicht „82 % entkommen", sondern WO sie entkommen:** Der
> Pruefer ist dicht an den Stellen, an denen er **Absagen erzeugt**, und duenn an denen, an
> denen er **rechnet**. Die Handmutationen zielten auf die Absagen, weil Absagen das sind,
> was man beim Schreiben im Kopf hat.

**Was daraus folgt und was NICHT.** Es folgt: die Bereichsarithmetik braucht Proben, die
**Grenzen** treffen statt Klassen — Wertetabellen, nicht Beispieldateien. Es folgt **nicht**,
dass der Pruefer an den 38 gemessenen Regeln schlechter ist als gemeldet; diese Zahl steht
unveraendert und misst weiterhin, was sie misst.

---

# TOR P2 IST ERREICHT — 6 von 6, am 2026-08-15

**Zum ersten Mal parst der gesamte Fragmentkorpus gegen die Grammatik von heute** — 791 Zeilen
Gabbro in sechs Uebersetzungseinheiten, null Absagen.

| Stand | Einheiten sauber |
|---|---|
| 2026-08-14 (Lauf 1, vor allen Reparaturen) | **1 von 6** (17 %) |
| nach Welle 0/1 | 1 von 6 |
| nach `M-woerter` (provisorisch, R12) | 2 von 6 |
| nach den semantischen Nachzuegen | **6 von 6 (100 %)** |

## Was das Tor gekostet hat — und wer die Fehler hatte

**Vier davon waren Fehler im PRUEFER, nicht im Korpus.** Das ist der eigentliche Ertrag:

| | Befund | Klasse |
|---|---|---|
| `E005` | hielt **lokale Namen** fuer Wirkungen — eine Funktion, die nur zaehlt, konnte nicht `pure` sein | zu streng |
| `S002` | `endet_immer` kannte **keine Aufrufe** — ein Block, der auf `exit();` endet, galt als durchfallend, obwohl `exit` divergiert | zu streng |
| `queue`-Domaene | hatte **keine Schranke**, obwohl sie eindeutig ableitbar ist: der Verbund einer Warteschlange traegt **genau ein** Feldarray | Luecke |
| `Some`/`None` | `option index into T` hatte **keinen Konstruktor**. Der Bestand schreibt `Some(x)` seit jeher — in `match`-Mustern, in Ausdruecken, **und in `SPRACHE.md`:381 selbst**; die Grammatik kannte es an keiner der drei Stellen | Luecke |

Dazu zwei tote Woerter derselben Klasse: **`Self` stand in der Wortschatztabelle und in keiner
Produktion** — der Waechter sah es nie, weil seine Terminalregex nur Kleinbuchstaben las.
*Dritter Fund dieser Art an einem Tag.*

## Und zwei Befunde ueber den KORPUS, die eine Groessenordnung tragen

**«B34» — `revoke` sagte `<= 200 ops` zu; der Rumpf kostet 16 452 480.** Fuenf
Groessenordnungen. Die 200 waren kein Tippfehler, sondern der **typische** Fall; `costs` ist
aber eine **Schranke**. Sichtbar wurde es erst, als `CapSpace` seine Slotzahl nannte
(`count NSLOTS`) — vorher konnte der Pass die Domaene nicht schranken und sagte das
(`K003`), statt zu schaetzen. **Zweites Auftreten derselben Verwechslung** (A4: 4 096
zugesagt, 831 488 gerechnet).

> **Was der Kernel wirklich tut, steht damit nicht in der Zeile:** Caprock begrenzt `revoke`
> ueber die **CDT-Tiefe**, nicht ueber die Tabellengroesse. Diese Schranke ist in Gabbro heute
> **nicht ausdrueckbar** — `descendants of` erbt die Tabelle. *Das ist der Befund, nicht die
> Zahl.*

**«B32» — `wrapping` steht am Slot, nicht am Register.** virtios `AVAIL_IDX` laeuft **per
Entwurf** um; `slottype = intty "wrapping"` (SYNTAX.md:500) kann das aussprechen, `regdecl`
nicht. **Der haeufigste Fall in einem Geraetetreiber kann seine Absicht nicht sagen.**

**«B33»** — die V-Regeln verengen den Typ eines **Registerortes** nach `if … == N { return; }`
nicht; nur `narrow` traegt die Tatsache. Ob das Absicht ist (ein Register kann sich zwischen
Pruefung und Rechnung aendern!) oder eine Luecke, entscheidet der Ordner. **Wenn es Absicht
ist, gehoert die Begruendung aufgeschrieben — sie waere ein starkes Argument.**

## «B29» ist aufgeloest, und zwar an der Sprache

Die Vorlage schrieb `refcount -= 1;` und prueefte **danach** auf Null, mit dem Argument, die
Buchfuehrungs-Invariante sei nach «B13» nicht aufschreibbar. **Beides stimmt und beides half
nicht** — denn `narrow … else` verlangt keine Invariante, sondern eine **Pruefung**:

```gabbro
narrow o.slots[obj].refcount to 1 .. 80255 else {
    return Fehler::Buchfuehrung;
}
o.slots[obj].refcount -= 1;
```

**Das ist der Unterschied zwischen einem Netz und zweien:** die Invariante bleibt der Grund,
warum der `else`-Zweig nie genommen wird; der Typ bleibt der Grund, warum er **dastehen muss**.

## Die methodische Lehre, und sie ist teuer bezahlt

> **Eine Absageliste hinter einem Parserfehler ist keine Messung, sondern eine UNTERE
> SCHRANKE.**

Die Wortschatzkollisionen waren erst 6, dann 7, nach der Umbenennung **14** — jede geschlossene
Stelle laesst den Parser weiterlaufen und mehr finden. `memos/M-woerter.md` nannte 6; die Zahl
stand hinter zwei Desynchronisationen. **Und ich bin in dieselbe Falle getappt, nachdem ich sie
notiert hatte:** Zeile 873 war keine Kollision, sondern ein Folgefehler — ich habe ein echtes
Schluesselwort umbenannt und musste es zuruecknehmen.

---

# VORAB — Messprotokoll: die `narrow`-Zaehlung ueber GABBRO-Quelltext

**Eigener Commit, VOR der Zaehlung.** Nach dem Lauf wird an diesem Abschnitt nichts geaendert.

## Vorgeschichte, in einem Satz
Die Zaehlung ueber **Rust** war am 2026-08-14 **ungueltig** (Klassifikatorfehler 40–60 %), und
das Urteil lautete: *die Zahl ist ungenau, das Urteil nicht* — N = 150…317 gegen eine Latte
von 24. Fahrbar wurde die Zaehlung erst mit Tor P2 (6 von 6, 2026-08-15).

## Was gezaehlt wird

**Die Bereichspflichten, die eine EXPLIZITE Abtragung brauchen** — also genau die Stellen, an
denen der Schreiber `narrow … to … else { … }` hinschreiben muss, weil weder der Typ noch die
V-Regeln den Nachweis tragen.

**Mechanisch, ohne Klassifikator:**

1. Aus dem Fragmentkorpus alle `narrow`-Anweisungen **entfernen**.
2. `gabbro pruefe` fahren und die Absagen `M101`/`M104` zaehlen.
3. **Diese Zahl ist N** — jede solche Absage ist eine Stelle, die ohne `narrow` nicht
   uebersetzt.

*Der Klassifikator, an dem die erste Zaehlung starb, faellt damit ersatzlos weg: nicht ein
Skript entscheidet, was eine Bereichspflicht ist, sondern der Pass, der sie prueft.*

## Zaehlregel

* Gezaehlt werden **Fundstellen**, nicht Absagen: `M101` und `M104` an derselben Zeile sind
  **eine** Pflicht (der Pass meldet Bereich und Breite getrennt).
* Eine Stelle in einem **Kommentar** oder in einer entfernten `narrow`-Zeile selbst zaehlt
  nicht.
* **R16:** bricht der Parser irgendwo ab, ist die Zahl eine **untere Schranke** und wird als
  „≥ n, Abbruch bei X" gefuehrt, nicht als n. Tor P2 steht bei 6 von 6 — es darf beim
  Entfernen der `narrow` **nicht** fallen; faellt es, ist der Lauf ungueltig.

## Handstichprobe — Umfang und Fehlerschranke VORAB

* **n = 20** Fundstellen, geschichtet ueber die sechs Einheiten (je Einheit mindestens eine,
  Rest proportional zur Zeilenzahl). Sind es weniger als 20 Fundstellen, wird **jede** geprueft
  und der Umfang berichtet.
* Von Hand entschieden: *ist an dieser Stelle wirklich ein Nachweis noetig, oder liegt der
  Wert nachweislich im Bereich?*
* **Fehlerschranke: hoechstens 1 Fehler in der Stichprobe.** Bei 2 oder mehr ist die Zaehlung
  **ungueltig** — getrennt von „verfehlt" gefuehrt.

## Hochrechnung, und ihre Grenze

Der Korpus ist **791 Zeilen Gabbro** gegen **75 294 Zeilen Rust** im Kern (`a1bf707`,
139 Dateien). Eine Hochrechnung ueber diesen Faktor **wird berichtet, aber nicht als Messwert
gefuehrt** — die sechs Fragmente sind nach ihrer Schwierigkeit gewaehlt, nicht zufaellig, und
sind damit **kein reprasentativer Schnitt**. Die Dichte steht als Dichte da.

## Das zweiseitige Tor

| | |
|---|---|
| **bestanden** | die gemessene Dichte traegt eine Hochrechnung **≤ 24** fuer den ganzen Kern |
| **verfehlt** | sie traegt eine Hochrechnung **> 24** |
| **ungueltig** | ≥ 2 Fehler in der Handstichprobe · **oder** Tor P2 faellt beim Entfernen der `narrow` · **oder** der Parser bricht ab (dann: untere Schranke, R16) |

**Die Latte wird nicht verschoben.** Sie stand bei 24 und steht bei 24.

## R14 — das Geschirr beweist zuerst, dass es messen kann

Vor der ersten Zahl:
1. **Der Bauabbruch unterscheidet sich vom Treffer.** Das Zaehlwerkzeug bricht sichtbar ab,
   wenn `gabbro pruefe` gar nicht laeuft — es zaehlt dann **nicht** null.
2. **Die Zahl haengt nachweislich am Prueflingt.** Probe: **ein** `narrow` wieder einsetzen;
   N muss **um genau eins fallen**. Tut es das nicht, misst der Lauf etwas anderes.

## ERGEBNIS der `narrow`-Zaehlung — 2026-08-15

**N = 2** Bereichspflichten in 791 Zeilen Gabbro, sechs Uebersetzungseinheiten.

| | |
|---|---|
| entfernte `narrow`-Anweisungen | 2 |
| Tor P2 ohne sie | **4 von 6** — es faellt, also misst der Lauf etwas |
| **N (Fundstellen)** | **2** |
| Dichte | **2,5 je 1000 Zeilen** |
| R14-Selbstprobe | **bestanden** — 2 entfernte `narrow` → genau 2 zusaetzliche Pflichten |

## Handpruefung — n = 2, also JEDE (Vorab: „weniger als 20 ⇒ jede, Umfang berichten")

| Stelle | Urteil |
|---|---|
| `space.rs`-Fragment, `refcount -= 1` | **echte Pflicht.** `u32 in 0 .. 80255`, und der Unterlauf ist «B29» selbst |
| `kstackmark`-Fragment, `i += 1` | **KEINE echte Pflicht** — die Traversierung laeuft ueber `s.worte` und begrenzt `i`; **M1 sieht das nicht.** Eine Pruefer-Grenze, keine Sprachpflicht |

**1 Fehler in der Stichprobe.** Die vorab festgelegte Schranke war „hoechstens 1" — die
Zaehlung ist damit **gueltig**, und zwar **knapp**.

> **Der Befund hinter dem Befund:** die Haelfte der gemessenen Pflichten ist eine
> **Prueferbeschraenkung**, nicht eine Sprachpflicht. Bei n = 2 ist das keine Quote, sondern
> ein Hinweis — aber es ist **derselbe Hinweis, den die ungueltige Rust-Zaehlung gab**
> (Klassifikatorfehler 40–60 %, alle in dieselbe Richtung). *Zweimal in Folge zeigt die
> Handprobe in dieselbe Richtung: die Rohzahl ist zu HOCH.*

## Das Tor — **verfehlt nach dem Wortlaut, und das Protokoll war widersprüchlich**

Hochgerechnet auf 75 294 Zeilen Kern: **2 / 791 × 75 294 ≈ 190**. Gegen eine Latte von 24
ist das um den Faktor **acht** verfehlt; zieht man die Prueferbeschraenkung ab, bleibt
**≈ 95**, also Faktor **vier**.

**Und hier faellt ein Befund ueber mein eigenes Vorab-Protokoll an.** Es sagt beides:

> *„bestanden: die gemessene Dichte traegt eine Hochrechnung ≤ 24"*
>
> *„Die Hochrechnung wird berichtet, aber **nicht als Messwert gefuehrt** — die sechs
> Fragmente sind nach ihrer Schwierigkeit gewaehlt, nicht zufaellig."*

**Ich habe das Tor an eine Groesse gehaengt, die dasselbe Protokoll als nicht-messend
erklaert.** Nach **R2** wird ein Tor nach dem Lauf nicht angepasst — also steht: **verfehlt**,
mitsamt der Feststellung, dass die Entscheidungsgrundlage nach dem eigenen Protokoll keine
ist. *Ein Tor, das auf einer erklaerten Nicht-Messung ruht, ist ein Konstruktionsfehler des
Protokolls, und er gehoert berichtet statt repariert.*

**Was trotzdem feststeht und mehr wert ist als das Tor:**

* Die Zaehlung ist **zum ersten Mal ohne Klassifikator gefahren** — nicht ein Skript
  entscheidet, was eine Bereichspflicht ist, sondern der Pass, der sie prueft. *Genau daran
  war die erste Zaehlung gestorben.*
* **N = 2 ueber 791 Zeilen ist etwas voellig anderes als die 150…317 der Rust-Zaehlung** —
  und der Unterschied ist kein Messfehler, sondern die **Sache**: die Rust-Zaehlung zaehlte
  *alle* Bereichspflichten, Gabbros Typen und V-Regeln tragen davon den Grossteil **ohne**
  eine `narrow`-Zeile. Gezaehlt wird hier nur, was den **Notausgang** braucht.
* **Die naechste Zaehlung braucht n, nicht Sorgfalt.** Bei zwei Fundstellen entscheidet jede
  einzelne Handprobe ueber 50 % des Ergebnisses. Die vier fehlenden Bereichsfragmente
  (Scheduler, MMU, Lader, Parser) sind die Messgrundlage, nicht ein Nebenpunkt.

---

# BASISRATE — „Wie viele Formate hat Caprock wirklich, wie oft aendern sie sich, wie viele Fehler dieser Klasse pro Jahr?" (TODO.md:480)

**Gefahren 2026-08-15** gegen `../caprock-messbasis` @ `a1bf707`.
Der TODO-Eintrag nennt das ehrlichste moegliche Ergebnis selbst mit: *„Faellt sie klein aus,
ist das ehrlichste Ergebnis ‚die Falle ist zu selten fuer eine Sprache'."*

## Die Zahlen

| Groesse | Suchweg | Ergebnis |
|---|---|---|
| Formate im Baum | `grep -rn "#\[repr(C)\]" --include=*.rs` | **5** |
| davon benannt | `MemRegion`, `HandoverInfo`, `TrapFrame` (+2) | 3 lesbar |
| Commits, die eine `repr(C)`-Struktur beruehren | `git log --all -S"repr(C)" -- '*.rs'` | **5** |
| Beobachtungszeitraum | `git log` erster/letzter Commit | **2026-06-23 bis 2026-08-14 — 53 Tage** |
| Eintraege in `done.md` | `grep -cE "^#{2,3} "` | 234 |
| **Fehler dieser Klasse in `done.md`** | Muster fuer falsche Offsets, Feldreihenfolge, vertauschte Bytereihenfolge, Layoutfehler | **0 als eingetretener Fehler** |

## Der einzige Beinahe-Fall, und er ist lehrreich

`done.md:1745-1750` beschreibt die virtio-Kopfgroesse: **12 Byte** unter `VIRTIO_F_VERSION_1`,
10 in der Legacy-Fassung.

> *„Wer sie einsetzt, verschiebt jeden empfangenen Rahmen um zwei Byte und findet den
> Ethertype an der falschen Stelle — ein Fehler, der wie ‚das Gegenueber antwortet nicht'
> aussieht."*

**Das ist die Falle in Reinform** — und sie steht dort als **vermiedene**, nicht als bezahlte.
Der Text ist eine Warnung, kein Nachruf.

## Urteil — und es geht gegen den Ordner

**Hochgerechnet: 5 Formataenderungen in 53 Tagen ≈ 34 im Jahr; Fehler dieser Klasse: 0.**

> **Die Basisrate traegt `format` nicht.** Fuenf Formate, null eingetretene Fehler der
> Klasse, ein dokumentierter Beinahe-Fall, den ein aufmerksamer Kommentar abgefangen hat.

**Was das NICHT heisst.** Es heisst nicht, dass `format` nutzlos ist — der Beinahe-Fall zeigt,
dass die Klasse real ist und dass ihre Erkennung heute an **Aufmerksamkeit** haengt. Es heisst:
**diese Messung rechtfertigt `format` nicht**, und wer es rechtfertigen will, braucht ein
anderes Argument als die Fehlerhaeufigkeit in diesem Baum.

**Und die ehrliche Einschraenkung dazu:** 53 Tage sind ein kurzer Zeitraum, und `done.md` ist
ein **kuratiertes** Dokument — es fuehrt, was der Autor fuer berichtenswert hielt. Ein Fehler,
der in fuenf Minuten gefunden und behoben wurde, steht dort nicht. **Die Null ist eine Null in
`done.md`, nicht eine Null im Baum.**

## Pruefpfad
```
cd ../caprock-messbasis
grep -rn "#\[repr(C)\]" --include=*.rs . | wc -l          # 5
git log --oneline --all -S"repr(C)" -- '*.rs' | wc -l      # 5
git log --format=%ad --date=short | tail -1                # 2026-06-23
sed -n '1745,1750p' done.md                                # der Beinahe-Fall
```

---

# `programs/` — die Wiederholung, 2026-08-15

> *„`programs/` brach 4 von 4 — aber die Messung ist **aelter als die Konstrukte**, die es
> betreffen (`leaves`, `transition publishes`). Ungeprueft, ob es heute traegt."* (`TODO.md`:56)

Gemessen an `../caprock-messbasis` @ `a1bf707`: **9 Rust-Dateien, 1 778 Zeilen** in vier
Gruppen.

## Was die alte Messung brach — und ob es heute noch bricht

Der Bruch war **`loop { … break … }`**: die Grammatik der zweiten Fassung hatte weder
`leave` noch `break`, und eine Dienstschleife war damit **nicht schreibbar**. Genau das
schloss `forever … leaves`/`leave`.

| Programm | Zeilen | Endlosschleifen | `break` | `dyn`/`Box` |
|---|---:|---:|---:|---:|
| `hardware/virtio-blk` | 426 | 2 | **2** | 0 |
| `trusted/fs` | 365 | 3 | **5** | 0 |
| `trusted/init` | 119 | 1 | 0 | 0 |
| `userland/hello` | 25 | 0 | 0 | 0 |
| **Summe** | **935** (4 von 9 Dateien) | **6** | **7** | **0** |

**Alle sieben `break` sitzen in einer benannten Schleife** und sind damit `leave <marke>` —
das Konstrukt, das seit der dritten Fassung steht. **Der gemessene Bruch ist zu.**

**Und der zweite Kandidat faellt ebenfalls weg:** *null* `dyn Fn`/`Box` in den vier
Programmen. Die 47 Verschluss-Stellen des Baums (`memos/M-verschluesse.md`) liegen
**vollstaendig im Kern**, nicht in den Programmen.

## Urteil — **teilweise aufgehoben, nicht aufgehoben**

> **Der gemessene Grund des Bruchs traegt nicht mehr.** Ob `programs/` heute *durchgeht*,
> sagt diese Messung **nicht** — dazu muessten die vier Programme in Gabbro ausgeschrieben
> werden, und das ist ein Fragment-Auftrag, kein Zaehlauftrag.

**Was diese Messung leistet:** sie nimmt dem Eintrag „4 von 4 gebrochen" seine Grundlage und
sagt, **was an seine Stelle tritt** — eine offene Frage statt eines gemessenen Nein.
*Ein Befund, dessen Grund weggefallen ist, ist kein Befund mehr; er ist eine ungestellte
Frage.*

## Pruefpfad
```
cd ../caprock-messbasis
find programs -name "*.rs" | wc -l                                  # 9
grep -rcE "\bbreak\b" programs/hardware/virtio-blk/src/*.rs        # 2
grep -rn "dyn Fn|Box<" programs/ --include=*.rs | wc -l             # 0
```

---

# Die aarch64-Luecke — warum eine Zahl fehlt und nicht bloss ungemessen ist

**Eingetragen 2026-08-15.** Mehrere Posten des Ordners verlangen eine **zweite Architektur**:
die Axiomschicht („wie viele Axiome braucht ein x86- **und** ein aarch64-Kernel"), die
Eager-FP-Entscheidung, und implizit jede Aussage ueber Uebertragbarkeit.

## Was da ist

| Baum | was er ist |
|---|---|
| `SEL4Lake/SEL4Lake` @ `arch/x86_64` | der gemessene Kern. **139 Dateien, 75 294 Zeilen.** In git, Commit `a1bf707` |
| `SEL4Lake/ARMTest/stm32mp25-kernel` | **kein zweiter Kernel** |

## Der Nachweis

```
$ git log --follow --name-status -- crates/caprock-cap/src/space.rs
R099   crates/sel4lake-cap/src/space.rs -> crates/caprock-cap/src/space.rs
```

**`R099` — eine Umbenennung mit 99 % Aehnlichkeit.** Der ARM-Baum traegt die Paketnamen von
**vor** dieser Umbenennung (`sel4lake-cap`), liegt ausserhalb von git und ist damit ein
**aelterer Schnappschuss derselben Abstammung**. Dieselbe Autorenlinie, dieselbe Datei.

## Warum das die Zahl nicht bloss ungenau macht, sondern falsch

Eine Axiomtabelle aus beiden Baeumen wuerde **Uebereinstimmung** zeigen — und diese
Uebereinstimmung waere kein Befund ueber Architekturen, sondern ueber **Kopieren**. Sie
wuerde genau die Frage beantworten, die niemand gestellt hat.

> **Und sie irrte in die schmeichelhafte Richtung.** „Die Axiomschicht traegt ueber
> Architekturen hinweg" ist die Aussage, die der Ordner gern haette. *Genau deshalb ist sie
> die, bei der man zweimal hinsehen muss* — und genau diese Bewegung (aus
> Oberflaechenaehnlichkeit auf Herkunft schliessen) steht seit dem 2026-08-15 in
> [`HISTORIE.md`](HISTORIE.md) als bezahlter Fehler.

## Die ehrliche Fassung, bis ein zweiter Baum da ist

> *„Gemessen fuer x86. Fuer aarch64 steht keine Zahl, und der vorhandene Baum kann sie nicht
> liefern — er ist derselbe Kernel in aelterer Fassung."*

**Was den Posten entsperrt:** ein aarch64-Kernel mit eigener Abstammung. Nichts sonst — kein
Werkzeug, keine Sorgfalt, kein zweiter Anlauf am selben Baum.

## Pruefpfad
```
cd ../caprock-messbasis
git log --follow --name-status -- crates/caprock-cap/src/space.rs | grep '^R'
ls ../SEL4Lake/ARMTest/stm32mp25-kernel/crates/     # traegt die Namen VOR der Umbenennung
cd ../SEL4Lake/ARMTest/stm32mp25-kernel && git rev-parse --show-toplevel   # scheitert: kein git
```

---

# VORAB — Neuerhebung der Klempnerei-Klassen gegen x86

**Eigener Commit, VOR der Erhebung.** Nach dem Lauf wird hier nichts geaendert.
Messbasis: `../caprock-messbasis` = `SEL4Lake/SEL4Lake` @ `arch/x86_64`, `a1bf707`.
**Ausdruecklich nur x86** — die aarch64-Seite ist blockiert, s. *Die aarch64-Luecke*.

## Warum neu und nicht wiederhergestellt

Fuenf der elf Klassen lagen nur im Scratchpad und sind **nicht rekonstruierbar** — auch ihre
**Namen** nicht: die sechs dokumentierten sind benannt, die fuenf uebrigen nur als „die
uebrigen fuenf" erwaehnt. **Eine Messung, deren Gegenstand man nicht mehr nennen kann, ist
nicht halb vorhanden, sondern gar nicht.**

Deshalb werden **alle elf** neu erhoben. Das Ergebnis heisst **N_neu** und ist mit den 19
**nicht vergleichbar** — es ersetzt sie, es setzt sie nicht fort.

> **Kennzeichnung, die in jeder spaeteren Zitierung mitlaufen muss:
> „neu erhoben 2026-08-15, nicht wiederhergestellt; nur x86."**

## Die elf Klassen — der Bestand nennt sie (`README.md`:13)

Index · Ueberlauf · Alias · Rahmen · Sperre · Rennen · Terminierung · Phase · Blattheit ·
Publikation · Verfeinerung

## Was gezaehlt wird, je Klasse

**Zwei Zahlen, streng getrennt:**

1. **Fundstellen** — mechanisch, mit dem Suchweg daneben. Das ist die **Groesse** der Klasse.
2. **Haengt die Klasse?** — traegt ein *heutiges* Konstrukt sie **durch Konstruktion**, oder
   bleibt Menschenarbeit? Antwort ist **ein Konstruktname oder eine benannte Luecke**, nie
   „vermutlich".

**N_neu = Zahl der Klassen, die haengen.** Nicht die Zahl der Fundstellen — eine Klasse mit
40 000 Indexzugriffen und einem tragenden Konstrukt haengt **nicht**.

## Kippregel

* Traegt ein Konstrukt eine Klasse **nur teilweise**, zaehlt die Klasse als **haengend** und
  der gedeckte Teil wird benannt. *Grenzfaelle in die teurere Spalte.*
* Ist eine Klasse im x86-Baum **nicht auffindbar** (null Fundstellen), zaehlt sie **nicht als
  gedeckt**, sondern als **nicht gemessen** — getrennt gefuehrt.
* **R16:** bricht ein Suchweg ab, ist seine Zahl eine untere Schranke und heisst so.

## Das zweiseitige Tor

| | |
|---|---|
| **bestanden** | **N_neu = 0** — jede der elf Klassen wird von einem benannten Konstrukt getragen |
| **verfehlt** | **N_neu > 0**, mit Klasse, Fundstelle und benannter Luecke je Posten |
| **ungueltig** | eine Klasse laesst sich nicht mechanisch aufsuchen **und** nicht von Hand entscheiden — dann fehlt das Kriterium, nicht die Antwort |

**Das Tor ist NICHT „19 → 0".** Die 19 sind nicht rekonstruierbar; ein Tor auf einer Zahl,
die niemand mehr belegen kann, waere Falle 80 in Reinform. **Das neue Tor ist `N_neu → 0`,
und N_neu wird in diesem Lauf zum ersten Mal bestimmt.**

## R14 — das Geschirr zuerst

Vor der ersten Zahl: jeder Suchweg wird **einmal gegen eine Stelle gefahren, von der ich
weiss, dass sie existiert** (z. B. `refcount -= 1` fuer Ueberlauf, `CAPS.write()` fuer
Sperre). Findet er sie nicht, misst er nicht, was er behauptet.

## ERGEBNIS der Neuerhebung — 2026-08-15, **nur x86**

**Kennzeichnung, die mitzulaufen hat: neu erhoben, nicht wiederhergestellt.**
Die 19 aus der alten Zaehlung werden **ersetzt, nicht fortgesetzt** — ihr Gegenstand war
nicht mehr benennbar.

### R14 — die Suchwege finden ihre bekannten Stellen

`refcount -= 1` → 1 · `CAPS.write()` → 45 · `self.slots[slot]` → 15 · Atomics → 704 ·
Schleifen → 276. **Alle fuenf Proben treffen.**

### Die elf Klassen

| # | Klasse | Fundstellen | traegt ein Konstrukt sie? |
|---:|---|---:|---|
| 1 | **Index** | 2 143 | **ja** — `index into T` erbt die Schranke aus `count N` (A3), `M103` prueft |
| 2 | **Ueberlauf** | 1 758 | **ja** — M1-Bereichstypen, `M101`/`M104`; der gewollte Umlauf ist seit «B32» am Slot **und** am Register aussprechbar |
| 3 | **Alias** | 628 | **ja** — aufgeloest statt geschlossen: Kernzustand braucht keinen Zeiger (A1); wo doch, macht `own` ihn linear |
| 4 | **Rahmen** | 296 | **HAENGT — halb.** `effects` prueft **Schreiben** und `locks` (`E005`/`E006`/`E007`), **Lesen nicht und Aufrufwirkungen nicht** |
| 5 | **Sperre** | 419 | **ja** — `lock … rank … held`, `locks`/`locks shared`, `K002`/`K004`, `H001`–`H005` |
| 6 | **Rennen** | 2 276 | **HAENGT.** Der Paarungspass (P6) ist **nicht gebaut**; `publishes`/`awaits` werden nicht gegenuebergestellt |
| 7 | **Terminierung** | 276 | **ja** — drei Schleifenformen, `bounded`/`on_exceeded`/`progress`, `M4`; `forever` ist erlaubt und benannt |
| 8 | **Phase** | **1** | **HAENGT — und die Klasse ist im Baum fast leer** (s. u.) |
| 9 | **Blattheit** | 180 | **ja** — `descendants of` + `by consuming` mit Zeugenordnung (§9.2) |
| 10 | **Publikation** | 824 | **HAENGT.** `publishstmt` steht in der Grammatik, der **Paarungspass fehlt** — dieselbe Luecke wie 6 |
| 11 | **Verfeinerung** | 792 (168 `asm!`) | **HAENGT.** Die Absenkung ist Vertrauensbasis, kein Konstrukt; die C-Formentabelle ist ungeschrieben |

### **N_neu = 5** — Tor **VERFEHLT**

Haengend: **Rahmen · Rennen · Phase · Publikation · Verfeinerung.**

Und **Rennen und Publikation sind dieselbe Luecke** — beide warten auf den Paarungspass.
Zaehlt man Luecken statt Klassen, sind es **vier**. *Die Kippregel sagt: Klassen zaehlen, und
Grenzfaelle in die teurere Spalte.* **N_neu = 5.**

### Der Nebenbefund zur Klasse Phase, und er ist der interessanteste

**Eine einzige Fundstelle im ganzen Baum:**

```
crates/caprock-slab/src/lib.rs:173
    /// Wie [`Slab::attach`]. Zusätzlich: **nur beim Boot** aufrufen, bevor andere Kerne
```

**Der Kernel fuehrt keine Bootphase als Wert.** Die Pflicht existiert — sie steht als
**Kommentar**, und nichts erzwingt sie. Das ist genau die Lage, gegen die Gabbros
`BootPhase` als linearer Wert geschrieben ist.

> **Zwei Lesarten, und der Unterschied ist gross.** Entweder: *die Klasse ist im Baum so
> selten, dass ein Konstrukt dafuer nicht traegt* (dieselbe Logik, an der `locks ordered`
> starb). Oder: *sie ist selten SICHTBAR, weil es keine Schreibweise gibt* — ein Kommentar
> ist billig, ein linearer Wert nicht, und was man nicht schreiben kann, zaehlt niemand.
>
> **Diese Messung kann die zwei nicht trennen**, und das gehoert dazugesagt. Was sie trennen
> wuerde: eine Suche nach Funktionen, die **faktisch** nur im Bringup gerufen werden — ein
> Aufrufgraph, denselben, an dem `H005` und die Aufrufwirkungen haengen. **Dritter Posten am
> selben fehlenden Werkzeug.**

### Was die Zahl NICHT sagt

Die Fundstellenzahlen sind **Groessen der Klassen**, keine Pflichten. 2 143 Indexzugriffe
heissen nicht 2 143 Beweise — sie heissen, dass ein tragendes Konstrukt dort 2 143-mal
greift. *Genau deshalb zaehlt `N_neu` Klassen und nicht Fundstellen.*

### Vergleich mit den 19 — **es gibt keinen**

Die alte Zahl zaehlte **Pflichten**, diese zaehlt **Klassen**. Beide sind legitim, keine ist
in die andere umrechenbar, und die alte ist nicht mehr belegbar. *Wer beide nebeneinander
stellt, vergleicht zwei Mengen, die nie dieselbe waren.*

---

# Die 17er-Zaehlung — **UNGUELTIG, und zwar nach ihrer eigenen Bedingung**

**Angesetzt 2026-08-15**, nach dem committeten Protokoll, **unveraendert angewandt**.

## Schritt 1 des Protokolls entscheidet, und er faellt

> *„1. die 17 Pflichten mit `Datei:Zeile` auffinden (sonst ungueltig, s. u.);"*
>
> *„Lassen sich weniger als 17 Pflichten mit `Datei:Zeile` wiederfinden, ist die **Quelle**
> nicht reproduzierbar — dieselbe Protokollklasse wie die fuenf Scratchpad-Klassen, und dann
> wird nicht gezaehlt, sondern erst die Grundlage hergestellt."*

**Gefunden: EINE.** Der ganze Abschnitt *Der Logik/Klempnerei-Split* (`MESSUNGEN.md`:268–300)
fuehrt genau **eine** Fundstelle mit Datei und Zeile — `kernel/src/system.rs:1215` —, und die
gehoert zur Eager-FP-Frage, nicht zu den 17.

Die Quelle sagt: *„Zehn handuebersetzte Fragmente aus acht Bereichen, 74 Beweispflichten
einzeln zugeordnet."* **Die Zuordnung selbst ist nicht im Ordner.** Was dasteht, ist das
**Aggregat** — 74 / 17 / 57 / 19 / 1 — und eine Aufteilung nach Bereichen ohne Fundstellen.

## Urteil: **ungueltig, nicht unguenstig**

**Die Zaehlung wird nicht gefahren.** Nach dem Protokoll ist jetzt die **Grundlage
herzustellen**, nicht das Ergebnis zu schaetzen.

> **Und das ist derselbe Befund wie bei den fuenf Scratchpad-Klassen, zum zweiten Mal an
> einem Tag:** eine Zahl steht im Ordner, ihr Gegenstand nicht. **Beide Male ist das Aggregat
> ueberliefert und die Zuordnung verloren.**

## Was das ueber die Buchfuehrung sagt — der eigentliche Ertrag

Drei Messungen dieses Ordners ruhen auf Zuordnungen, die nicht im Ordner liegen:

| Zahl | Aggregat vorhanden | Zuordnung vorhanden |
|---|---|---|
| 74 Beweispflichten (17 L / 57 K) | ja | **nein** |
| 19 haengende Pflichten, elf Klassen | ja | **nur 6 von 11** |
| `delete_leaf` 3,6–6 : 1 | ja | **nein** (deshalb kippte sie bei der Neuaufteilung auf 1,75 : 1) |

**Das ist ein Muster, kein Einzelfall.** Und es ist maschinell verhinderbar: *eine Zahl ohne
Fundstellenliste gehoert nicht ins Dokument.* **Das ist eine Waechterregel, keine
Stilfrage** — dieselbe Klasse wie „`[x]` in einer Datei, die ausschliesslich Offenes
behauptet".

## Was jetzt zu tun ist, in dieser Reihenfolge

1. **Die 74 neu zuordnen** — an den zehn Fragmenten, mit `Datei:Zeile` je Pflicht. Das ist
   Handarbeit und der Grund, warum sie beim ersten Mal verlorenging.
2. **Erst dann** die 17er-Aufteilung nach K/A/W, mit Zeilenumfang **vor** der Klassifikation
   (so steht es im Protokoll, und die Reihenfolge ist der Punkt).
3. Die Kennzeichnung mitfuehren: **neu zugeordnet, nicht wiederhergestellt.**

**Nicht getan, weil es nicht in diesen Lauf passt** — die Neuzuordnung von 74 Pflichten an
zehn Fragmenten ist ein eigener Auftrag, kein Nebenpunkt. *Ein ehrliches „blockiert, weil"
schlaegt eine Zahl mit Restzweifel.*

---

# Die Klasse *Rahmen* — neu beurteilt, 2026-08-15 (Nachtrag zur Neuerhebung)

Die Neuerhebung buchte **Rahmen** als haengend, mit dem Grund: *„`effects` prueft Schreiben
und `locks`, **Lesen nicht und Aufrufwirkungen nicht**."* Die zweite Haelfte ist seit dem
Aufrufgraphen zu.

| | vorher | jetzt |
|---|---|---|
| Schreiben | `E005` | `E005` |
| `locks`, mit Staerke | `E006`/`E007` | `E006`/`E007` |
| **Aufrufwirkungen** | **fehlte** | **`E008` — transitiv, ueber den Aufrufgraphen** |
| **Lesen** | fehlt | **fehlt weiterhin** — `memos/M-effects-lesen.md`, und die Entscheidung liegt beim Ordner (R5) |

## Urteil: **Rahmen haengt weiter — an EINER Haelfte statt an zweien**

**N_neu bleibt bei 5.** Die Kippregel ist eindeutig: *traegt ein Konstrukt eine Klasse nur
teilweise, zaehlt sie als haengend, und der gedeckte Teil wird benannt.* Was sich geaendert
hat, ist nicht die Zahl, sondern **woran sie haengt** — und das ist der Unterschied zwischen
einem Posten und einer Baustelle.

**Und der Rest ist keine Bauarbeit mehr, sondern ein Urteil.** Die Lesehaelfte ist gemessen
(Lesart A: 10 von 32 Funktionen, Lesart C: 3 von 32 — Faktor drei), das Memo liegt vor, und
**was fehlt, ist die Entscheidung des Ordners, nicht ein Werkzeug.**

## Was der Aufrufgraph an den anderen Klassen geaendert hat: nichts

* **Rennen** und **Publikation** warten weiter auf den Paarungspass — dieselbe Luecke.
* **Verfeinerung** wartet auf die C-Formentabelle.
* **Phase** wartet auf das Lader-Fragment, nicht auf ein Werkzeug (R18: eine Klasse mit einer
  Fundstelle, deren Schreibweise fehlt, wird **am Fragment** entschieden, nicht per Zaehlung).

> **Der Aufrufgraph hat drei Blocker geloest und keine Klasse abgeraeumt.** Das ist kein
> Widerspruch: er war Voraussetzung, nicht Ursache. *R17 sagt, womit man anfaengt, nicht was
> dabei herauskommt.*

---

# W7-KEHRAUS — Zahlen ohne Fundstellenliste, 2026-08-15

**Suchweg, mechanisch:** je Absatz in `MESSUNGEN.md`, `BEWEIS.md`, `README.md`, `SPRACHE.md`
alle fettgesetzten oder tabellierten Zahlen ≥ 10 sammeln und fragen, ob **im selben Absatz**
ein Beleg steht — `Datei:Zeile`, ein `grep`/`git log`/`wc`-Aufruf, oder ein Verweis auf eine
Liste.

```
MESSUNGEN.md   20 Absaetze mit Zahl ohne Beleg im Absatz
BEWEIS.md       5
SPRACHE.md      4
README.md       0
```

**Die Rohzahl ist eine obere Schranke, kein Befund** — Tabellenkoepfe zaehlen mit, deren Rumpf
die Belege trägt. Einzeln nachgesehen wurden die drei bekannten Aggregate und die vier
groessten uebrigen.

## Ergebnis je Fall

| Zahl | Stand | Befund |
|---|---|---|
| **2 231** `Ordering::`-Fundstellen | **belegt** | `grep -rhoE "Ordering::" --include=*.rs . \| wc -l` liefert **exakt 2231**. *Der Suchweg stand nicht dabei; jetzt schon.* |
| **74** Beweispflichten (17/57/19/1) | **unbelegt — markiert** | Aggregat ueberliefert, Zuordnung fehlt. Die 17er-Zaehlung ist daran ungueltig geworden |
| **19** haengende Pflichten, elf Klassen | **unbelegt — ersetzt** | durch `N_neu = 5` mit Fundstellen (Neuerhebung 2026-08-15) |
| **3,6–6 : 1** (`delete_leaf`) | **unbelegt — ersetzt** | durch **1,75 : 1** mit Zeilentabelle |
| **106** Axiome (→ 65, 30, ~130 Namen) | **unbelegt — markiert** | keine Liste je Axiom, kein Suchweg. **Und die aarch64-Haelfte (58) ruht zusaetzlich auf dem versiegelten Baum** |
| **1 398** Bereichspruefungen | **unbelegt — markiert** | Nachzaehlen liefert **2 143**; welcher Suchweg zu 1 398 fuehrte, steht nirgends |

## Was der Kehraus ueber den Ordner sagt

**Fuenf von sechs geprueften Grosszahlen waren unbelegt, eine war exakt reproduzierbar.**
Und die eine reproduzierbare ist die, bei der jemand den Suchweg im Kopf hatte — nicht im
Dokument. *Der Unterschied zwischen 2 231 und 106 ist nicht Sorgfalt, sondern ob die
Zaehlung mechanisch war.*

> **Die Regel, die daraus folgt, steht schon** (`WERKZEUGKASTEN.md` W7). Was dieser Kehraus
> hinzufuegt: **eine Zahl, die aus einem `grep` stammt, traegt das `grep`** — dann ist sie
> jederzeit nachfahrbar, auch wenn niemand eine Liste pflegt. *Fuer mechanisch erhebbare
> Groessen ist der Suchweg die Liste.*

**Nichts geloescht.** Fuenf Markierungen stehen im Text, wo die Zahlen stehen.

---

# GRUNDLAGE N_L — die Logik-Pflichten, neu abgeleitet mit Fundstellen

**2026-08-15, nur x86.** Kennzeichnung, die mitlaufen muss: **neu erhoben, nicht
wiederhergestellt.** Die 17 sind **ersetzt**, nicht fortgesetzt — ihre Zuordnung war nicht
im Ordner (W7-Kehraus).

> **Jede Pflicht traegt ihre `Datei:Zeile` ab dem ersten Entwurf.** Ein Zwischenstand ohne
> Fundstelle waere ein Aggregat auf dem Weg zur Liste — genau das, was beim ersten Mal
> entstand. Diese Liste ist deshalb **zuerst** die Liste und **dann** eine Zahl.

## Wo Logik-Pflichten im Baum stehen — der Suchweg

Nach dem Kriterium (`BEWEIS.md`: *„Logik, wenn die Aussage die SACHE erwaehnt"*) sind das die
Stellen, an denen der Baum eine **Invariante ueber seinem Gegenstand** fuehrt und ihre
**Erhaltung** behauptet:

```
grep -rn "spec fn [a-z_]*inv\b" Verification/ --include=*.rs     # die Invarianten
grep -rc "proof fn "             Verification/ --include=*.rs     # die Erhaltungssaetze
```

*Nicht gezaehlt:* Hilfsdefinitionen (`slot_live`, `contrib`, `refs_to`, `unlink`) — sie sind
Vokabular der Invariante, nicht selbst eine Pflicht. **Grenzfaelle nach Kippregel in die
teurere Klasse:** wo unklar war, ob eine `spec fn` Definition oder Aussage ist, zaehlt sie als
Aussage.

## Die acht Invarianten, einzeln

| # | Invariante | Fundstelle | Gegenstand |
|---:|---|---|---|
| 1 | `pool_inv` | `Verification/region-runtime/proofs/conservation.rs:42` | Speicherregionen |
| 2 | `dma_inv` | `Verification/dma-lifetime/proofs/dma_revoke.rs:33` | DMA-Lebensdauer |
| 3 | `ntfn_inv` | `Verification/notifications/proofs/notification.rs:32` | Benachrichtigungen |
| 4 | `ep_inv` | `Verification/ipc/proofs/endpoint.rs:199` | Endpunkte |
| 5 | `token_inv` | `Verification/ipc/proofs/endpoint.rs:206` | Antwortmarken |
| 6 | `budget_inv` | `Verification/scheduler/proofs/runqueue.rs:116` | Zeitbudgets |
| 7 | `sched_inv` | `Verification/scheduler/proofs/runqueue.rs:130` | Laufwarteschlange |
| 8 | `cap_inv` | `Verification/capability-system/proofs/cap_space.rs:56` | **CapSpace + CDT, Klauseln 1–7 in EINER spec fn** |

## Die Erhaltungssaetze je Bereich

| Bereich | Datei | Saetze |
|---|---|---:|
| Capability-System | `capability-system/proofs/cap_space.rs` | **16** |
| IPC | `ipc/proofs/endpoint.rs` | **29** |
| Scheduler | `scheduler/proofs/runqueue.rs` | **12** |
| Notifications | `notifications/proofs/notification.rs` | 7 |
| DMA-Lebensdauer | `dma-lifetime/proofs/dma_revoke.rs` | 6 |
| Lader | `loader/proofs/load_gate.rs` | 6 |
| Regionen | `region-runtime/proofs/conservation.rs` | 5 |
| **Summe** | | **81** |

## **N_L = 8 Invarianten mit 81 Erhaltungssaetzen**

**Die Zahl, die in die K/A/W-Rechnung geht, ist 81** — eine Invariante *formulieren* ist eine
Pflicht, sie *je Operation zu erhalten* sind so viele, wie es Operationen gibt, und **die
Erhaltung ist die Arbeit.**

> **Und das ist etwas anderes als die 17.** Die alte Zahl zaehlte Pflichten an
> **handuebersetzten Fragmenten**; diese zaehlt sie an den **Verus-Beweisen, die es gibt**.
> Beide sind legitim, keine ist in die andere umrechenbar — *und nur diese hier hat eine
> Liste.*

**Was diese Grundlage NICHT deckt:** Bereiche ohne Verus-Beweis (MMU/Seitentabellen, Parser,
Bringup) haben hier **null** Pflichten stehen — nicht, weil sie keine haetten, sondern weil
niemand sie aufgeschrieben hat. **Das ist eine Untergrenze und heisst so** (R16).

---

# VORAB — die K/A/W-Zaehlung ueber N_L = 81, neu registriert

**Eigener Commit, VOR der ersten Klassifikation.** Danach wird hier nichts geaendert (R2).

## Warum neu registriert wird — und warum das KEINE Torverschiebung ist

> **Die alte Grundgesamtheit war unbelegt (W7), nicht das alte Ergebnis unbequem (R2).**

Das ist der ganze Grund, und er ist nachpruefbar: die 17 hatten **eine** `Datei:Zeile` im
ganzen Ordner, und die gehoerte zur Eager-FP-Frage. Die neue Grundgesamtheit hat **89
Fundstellen** (8 Invarianten + 81 Erhaltungssaetze), alle im Text darueber.

*Wuerde ich hier die Latte verschieben, waere es an dieser Stelle sichtbar — deshalb steht
sie hier und nicht im Ergebnis.*

## Die drei Spalten — **unveraendert uebernommen**

| Spalte | Entscheidungsregel (woertlich aus dem alten Protokoll) |
|---|---|
| **K — durch Konstruktion** | Die Aussage erwaehnt **nur die Maschine**, ODER sie ist eine **deklarierte Invariante**, deren Erhaltung der Erzeuger **einmal ueber der Deklaration** zeigt. Ein Mensch schreibt nichts. |
| **A — Abstiegsaussage** | Schreibbar als *„fuer alle x in ⟨deklarierter Domaene⟩: P(x)"*, und P(x) folgt aus P auf den **echt kleineren** Elementen **plus genau einer deklarierten Schrittzusage**. |
| **W — Wertaussage** | Alles Uebrige: das Argument betrifft **Werte, die ein Rumpf rechnet** und die keine Deklaration festlegt. |

## Die K-Bedingung, mechanisch je Pflicht

**K gilt nur, wenn ALLE Schreibstellen des Traegers erzeugt oder methodengebunden sind.**
Geprueft per Fundstellensuche im Baum: schreibt irgendetwas ausserhalb der Methoden des
Traegers auf seine Felder, faellt K.

```
grep -rn "<traeger>\.<feld>\s*[-+]\?=" --include=*.rs .     # je Pflicht
```

*Der Uebersetzer fuehrt dieselbe Pruefung fuer Gabbro-Quelltext als `gabbro k-bedingung`.*

## Die vier Kippregeln — **immer nach W**

1. Ist unklar, ob die Domaene **deklariert** ist, kippt A nach **W**.
2. Ist unklar, ob der Erzeuger die Erhaltung **einmal** zeigt, kippt K nach **W**.
3. Braucht die Pflicht **mehr als eine** Schrittzusage, ist sie **W**.
4. Braucht eine Begruendung **mehr als einen Satz**, ist sie ein Kippfall und damit **W**.
   *Eine lange Begruendung ist ein Kippfall, der sich verteidigt.*

## Ausgaenge — als MEHRHEITSREGEL ueber N_L, nicht als absolute Zahl

| | |
|---|---|
| **W > N_L/2** (also **> 40,5**, d. h. ab 41) | die Wertaussagen sind die Mehrheit — **die Decke der Schrittzusagen traegt nicht**, und das erzeugte Induktionsschema loest den Grossteil nicht |
| **W ≤ 40** | die Mehrheit faellt unter K oder A — **die Decke traegt**, und der Rest ist benennbar |

**Beide Ausgaenge sind vorab gute Ergebnisse.** Der erste toetet eine Zusage, der zweite
belegt sie; keiner ist ein Misserfolg.

## Ungueltig (getrennt von unguenstig)

* Lassen sich **weniger als 81** Erhaltungssaetze mit `Datei:Zeile` auffinden → **ungueltig**,
  Grundlage herstellen. *(Sie sind aufgefunden, s. Liste — diese Bedingung ist bereits
  erfuellt.)*
* Braucht **mehr als ein Drittel** der Pflichten eine Begruendung ueber einem Satz →
  **ungueltig**: dann trennen die Spalten nicht, und das Kriterium ist das Problem, nicht die
  Verteilung.

## Die Gewichtsformel — festgeschrieben, Reihenfolge verbindlich

**Zuerst** je Pflicht den Zeilenumfang des betroffenen Beweisrumpfs messen, **dann**
klassifizieren. *Werden die Anteile nach der Zaehlung bestimmt, ist die Versuchung strukturell,
W-Pflichten klein zu wiegen.*

```
F        = Zeilen aller 81 Beweisruempfe
W_zeilen = Zeilen der Ruempfe, deren Pflicht als W gebucht ist
w        = W_zeilen / F
Ueberschlag = w * 5,0  +  (1 - w) * 0,3
```

**Der Vorbehalt in derselben Zeile:** die 81 sind **kein Zufallsschnitt** durch den Kernel —
sie sind die Bereiche, fuer die **jemand einen Verus-Beweis geschrieben hat**, also die
**gut verstandenen**. Die Hochrechnung traegt diese Verzerrung, und **ihre Richtung ist
bekannt**: gut verstandene Bereiche haben *weniger* Wertaussagen. **Der Ueberschlag ist damit
eine Untergrenze fuer w, keine Schaetzung.**

## «B34» ist W-Kandidat und wird nicht vergessen

Die `revoke`-Schranke (16 452 480 gegen zugesagte 200) ist eine **Wertaussage ueber eine
gerechnete Groesse** — sie steht in der Liste und wird nicht stillschweigend unter K gebucht.

## ERGEBNIS der K/A/W-Zaehlung — 2026-08-15

**Reihenfolge eingehalten:** Zeilenumfang je Pflicht **zuerst** (F = 1 389 Zeilen ueber 81
Pflichten), **dann** klassifiziert.

| | | |
|---|---:|---|
| **K — durch Konstruktion** | **28** | die Zusicherung nennt `requires <inv> … ensures <inv>` — Erhaltung einer deklarierten Invariante |
| **A — Abstiegsaussage** | **13** | Hilfssaetze ueber eine deklarierte Domaene (alle `lemma_*`) |
| **W — Wertaussage** | **40** | alles Uebrige |
| **N_L** | **81** | |

```
F = 1389   W_zeilen = 474   w = 0,341
Ueberschlag = 0,341 · 5,0 + 0,659 · 0,3 = 1,90
```

## BUCHUNG (2026-08-16): **VERFEHLT** — und die Begruendung liegt in der POPULATION

> **Die acht Werkzeugartefakte gehoerten nie in `N_L`, und das ist ex ante begruendbar.**
>
> `lemma_refs_push`, `lemma_live_update` und ihresgleichen quantifizieren ueber rohe `Seq<…>`
> und behaupten etwas ueber `push`/`update`/`len`. **Das sind Bibliothekslemmata eines
> Beweisers, den Gabbro nicht benutzt.** In Gabbros Welt existieren sie gar nicht — das
> Manifest exportiert `ensures`-Pflichten, nicht die Hilfssaetze, die ein SMT-Loeser braucht,
> um ueber eine Sequenz zu rechnen. **Die Frage wird dort nie gestellt.**
>
> **Also: `N_L = 73`, K = 28, A = 7, W = 38 gegen 36,5 — die Wertaussagen sind die Mehrheit,
> die Decke der Schrittzusagen deckt eine MINDERHEIT.**

### Warum das R2 nicht verletzt

**R2 verbietet, ein Tor nach dem Lauf zu verschieben. Hier wird die Grundgesamtheit
berichtigt, und zwar aus einem Grund, der vom Ergebnis unabhaengig ist** — er haette
genauso gegolten, wenn er in die andere Richtung gezeigt haette.

**Die Probe darauf ist die Richtung:** die Korrektur bewegt das Ergebnis **gegen die
schmeichelhafte Lesart**. *In die unbequeme Richtung zu irren ist unter den Regeln dieses
Ordners nie eine Umdeutung; nur die Gegenrichtung waere eine gewesen.* Waere `N_L = 73` das
bequemere Ergebnis, stuende hier die 81.

### Die Randlage ist selbst ein Befund

**Eine Pflicht Abstand in der einen Population, zwei in der anderen.**

> **Ein Tor, das an der Populationsdefinition kippt, misst die Definition mit.**

Das ist kein Nebensatz: die Zahl beantwortet nicht nur *„wieviel bleibt fuer den Menschen"*,
sondern auch *„was haben wir als Pflicht gezaehlt"* — und die zweite Frage war bis zu dieser
Buchung unbeantwortet.

### Was `W = 38 von 73` noch NICHT ist

**Nicht der Ueberschlag.** Die Gewichtsformel braucht die **Zeilenanteile**, und die kommen
erst mit der **B3-Bezifferung aus Welle 4** (welche Ruempfe sind keine Traversierungen, mit
Zeilenanteil). *Die 1,90 bzw. 1,98 sind Einsetzungen mit den Zeilen der Verus-Ruempfe — nicht
mit den Zeilen des Kernels.* Bis Welle 4 steht die Kennzahl als **offen**, nicht als 1,98.

### EINSETZUNG (2026-08-16): **B3 ist gemessen — und schliesst die Kennzahl NICHT**

**Die Zahl steht** (B3-Abschnitt weiter unten): `p_B3 = 0,0096` — 584 nicht-leere Zeilen in
22 Ruempfen von 60 756, Tor bestanden mit Faktor 5 Abstand, **als untere Schranke** zu fuehren.

```
Aufschlag_B3 = p_B3 · 5,0  =  +0,048   ->   >= +0,05
```

**Und der Absatz darueber hat zu viel von ihr erwartet. Das ist eine Berichtigung, keine
Fussnote:**

> **B3 liefert nicht die Zeilenanteile der Gewichtsformel, weil es eine andere Groesse
> misst.** Die Formel gewichtet **Beweispflichten** (welcher Anteil der Beweiszeilen gehoert
> zu einer Wertaussage). B3 zaehlt **Codeform** (welcher Anteil der Kernelzeilen laesst sich
> nicht als Traversierung schreiben). **Ein Rumpf kann traversierungsfoermig sein und
> trotzdem 5 : 1 kosten** — wegen `effects`, `locks`, Linearitaet oder der
> Schachtelungsgrenze. Die beiden Zahlen sind **Summanden, keine Ersetzungen.**

**Die Falle steht in der Einsetzung selbst**, deshalb ausgeschrieben:

| eingesetzt aus | Anteil | Ueberschlag nach derselben Formel |
|---|---:|---:|
| **Pflichtseite** (Verus-Ruempfe, `w = W_zeilen/F`) | 0,341 | **1,90** |
| **Codeseite** (B3, `p_B3`) | 0,0096 | **0,345** |

**Wer B3 als das kernelseitige `w` liest, bekommt 0,345 — und damit eine Kennzahl UNTER dem
seL4-Anker 0,56, also einen Triumph.** Das waere falsch: die 0,345 sagt nur, dass der
*Schleifenvorrat* fast den ganzen Kernel traegt. Sie sagt nichts ueber `effects`, `locks`,
Linearitaet — und nichts ueber die 38 Wertaussagen, die daneben stehen bleiben.

**Beide Zahlen sind untere Schranken. Die bindende ist die groessere:**

```
Kennzahl  >=  1,90        (Pflichtseite, Population 81; 1,98 mit N_L = 73)

Aufschlag aus B3  =  >= +0,05  UNTER GETRAGENER INDEX-BUCHUNG
                     +1,03     FAELLT SIE
```

> **Der Aufschlag wird BEDINGT eingesetzt, nicht absolut** — und die Bedingung steht in der
> Formel, nicht drei Absaetze darueber. *Eine Einsetzung, die ihre Bedingung nicht mitfuehrt,
> ist die naechste Zahl, die parallel zur Wahrheit laeuft, sobald jemand die Buchung anfasst.*

**Die Bedingung ist stabil, und das gehoert dazu, sonst liest sich die Zeile bedrohlicher als
sie ist:** die Klasse *Index* ruht auf **2 143 Fundstellen** und auf **purer M1-Mechanik**
(`index into T` erbt die Schranke aus `count N`, A3, geprueft von `M103`) — **sie ist die
bestbelegte Klasse der Neuerhebung** (Rang 1 der elf, s. o.). *Bedingt heisst nicht wackelig;
es heisst benannt.*

**Der Vorbehalt der Messung steht hier woertlich, weil er genau an dieser Stelle gebraucht
wird und nirgends sonst:**

> **„Der Aufschlag aus B3 ist nicht der Abstand des Entwurfs zum Boden, sondern ein Summand
> darin."**

**Und die Rueckrechnung gehoert mit eingesetzt, sonst ist die +0,05 zu ruhig gelesen:** faellt
die Buchung der Klasse *Index*, wird aus dem Summanden **+1,03** — Faktor 21. *Die Einsetzung
traegt damit dieselbe Bedingung wie die Messung: sie steht auf `index into T` erbt `count N`.*

**Damit ist B3 als Kostenposten erledigt und die Kennzahl weiter offen.** Was sie
schliessen wuerde, ist benannt und steht in `TODO.md`: die Zeilenanteile der **Gabbro-Seite**
— also was ein Beweis in Gabbro fuer dieselben 73 Pflichten tatsaechlich kostet. *Das ist
keine Messung an Caprock mehr; dafuer muessen die Pflichten in Gabbro geschrieben sein.*

### Und was der vorregistrierte Text fuer diesen Ausgang vorgesehen hat

> *„beide Ausgaenge sind vorab gute Ergebnisse. Der erste toetet eine Zusage, der zweite
> belegt sie; keiner ist ein Misserfolg."*

**Das ist kein Stimmungsdaempfer.** Der verfehlte Ausgang ist die Zahl, die **k beziffert** —
den Anteil, der funktionale Korrektheit braucht — und **erst damit wird der seL4-Vergleich
ehrlich**: seL4 traegt 0,32 Invarianten / 0,40 Verfeinerung / 0,28 crefine, und Gabbros These
lautet, die letzten zwei fielen weg. **Ob die erste faellt, entscheidet genau diese Mehrheit.**

---

## Das Tor, wie zuerst gerechnet: **bestanden um EINE Pflicht** (Population 81)

**W = 40 gegen N_L/2 = 40,5.** Die Mehrheit faellt unter K oder A; die Decke der
Schrittzusagen traegt.

> **Und das ist die unbequemste Zahl des ganzen Ordners, weil sie an einem einzigen Posten
> haengt.** Eine Umbuchung in beide Richtungen kippt das Tor. **Das steht hier, statt als
> „bestanden" zitiert zu werden** — wer diese Zahl weiterverwendet, muss die Eins mitnehmen.

**Die 13 A-Pflichten sind sämtlich Kippkandidaten** und stehen einzeln in der Liste; ebenso
die 28 K. *Die Kippregel des Protokolls sagt: im Zweifel nach W* — und im Zweifel faellt das
Tor.

## Die Klassifikation ist mechanisch, und der erste Versuch war es NICHT

**Erster Durchgang: K=22, A=12, W=47 → Tor verfehlt.** Er klassifizierte nach **Namen**
(`*_preserves` → K). Die Handprobe an den vier groessten W zeigte: `copy`, `mint`, `install`
und `delete` stehen als

```
requires cap_inv(cs), slot_live(cs, src)
ensures  cap_inv(cs2)
```

da — **das ist Erhaltung einer deklarierten Invariante, also K nach dem Vorab-Protokoll.**
Der Namensklassierer hatte sie falsch, weil ihre Namen die Operation nennen und nicht die
Zusage.

**Zweiter Durchgang: aus der `ensures`-Klausel** — `K` genau dann, wenn dieselbe `*_inv` in
`requires` **und** `ensures` steht. Ergebnis K=28, A=13, W=40.

> **Beinahe haette ich `W = 47` und ein gefallenes Tor berichtet, auf Namensbasis.** Das ist
> derselbe Fehler, an dem die erste `narrow`-Zaehlung starb — ein Klassierer, der auf die
> Oberflaeche sieht. *Der Unterschied ist, dass diesmal die Handprobe VOR dem Bericht kam.*

## Die K-Bedingung, mechanisch geprueft

Das Protokoll verlangt sie je Pflicht: *K gilt nur, wenn alle Schreibstellen des Traegers
erzeugt oder methodengebunden sind.*

| Feld des Traegers | Schreibstellen | ausserhalb der Traegermethoden? |
|---|---:|---|
| `refcount` | 2 | nein — beide in `caprock-cap/src/space.rs` |
| `used` | 14 in 3 Dateien | **geprueft:** die Stellen in `kernel/src/system.rs` schreiben `VSPACES` und `DmaCtx`, **nicht** `CapSpace.slots` |
| `first_child` | 10 | nein |
| `next`, `prev`, `rank`, `parent` | 2 / 0 / 0 / 3 | `pcie.rs:463` schreibt eine **PCIe-Topologie**, nicht den CDT |
| | | **K-Bedingung haelt fuer `cap_inv`.** |

*Zwei der Treffer waren Fehlalarme desselben Suchmusters — gleiche Feldnamen, andere
Traeger. Ohne die Einzelpruefung waere die K-Bedingung faelschlich gefallen und das Tor mit
ihr.*

## Der Ueberschlag und sein Vorbehalt

**1,90** — und der Bezug dazu ist zu berichtigen.

> **W7-Verstoss von mir, im selben Commit wie die Messung — und die Berichtigung hat einen
> zweiten Verstoss darin gefunden.**
>
> Ich schrieb „gegen die Zielmarke, die der Ordner mit 0,56 (seL4) fuehrt". **Die 0,56 steht
> nirgends im Ordner ausser in diesem meinem Satz.** Dann berichtigte ich mit *„gegen seL4s
> C-Kern von rund 10 kZeilen"* — **und auch diese Zahl steht nirgends ausser in meinem Satz.**
> *Eine Berichtigung, die eine unbelegte Zahl durch eine andere ersetzt, ist keine.*
>
> **Und die zwei Groessen sind nicht dieselbe.** Das gehoert getrennt:
>
> | | Zaehler | Nenner | Wert |
> |---|---|---|---|
> | **Beweis zu C** | 239 458 (`proof/`, ARM) — **gemessen** | seL4s C-Kern — **nicht gezaehlt** | „jenseits von 20 : 1" ist eine Schaetzung |
> | **Spezifikation zu C** | **10 280** (`spec/abstract`, neutral + ARM) — **gemessen**, `f4940273` | seL4s C-Kern — **nicht gezaehlt** | **offen** |
>
> **Der 0,5 : 1-Boden der Sprache ist aus dem ZWEITEN Verhaeltnis hergeleitet, nicht aus dem
> ersten** — eine Sprache, die Verfeinerung und Klempnerei abnimmt, traegt am Ende die
> Spezifikation. *Mein „jenseits von 20 : 1" ersetzt den 0,56-Anker deshalb nicht; es
> beantwortet eine andere Frage.*
>
> **Was fehlt, ist genau ein `wc -l`:** seL4s C-Kern an einem zum l4v-Stand passenden Punkt.
> Der Zaehler (10 280) liegt gemessen vor, das l4v-Repo ist gepinnt (`f4940273`), **und der
> seL4-Baum liegt nicht in diesem Ordner** — deshalb steht die Zahl hier als **blockiert mit
> genanntem Suchweg**, nicht als geschaetzt.
>
> > **Solange sie fehlt, haengt das Kennzahlziel der Sprache an einem Satz von mir.**
> > Das ist der teuerste offene W7-Posten, und er kostet einen einzigen Befehl.

Die belegten Bezugsgroessen sind die aus `PLAN.md`:341 — der Ordner rechnete mit **0,8 : 1**
unter der Annahme, ein Zehntel des Kernels brauche den 5 : 1-Aufwand.
**Gemessen sind es 34 % der Beweiszeilen, nicht 10 %** — daher 1,90 statt 0,8.

**Und der Vorbehalt steht im Vorab-Protokoll, nicht hier erfunden:** die 81 sind **kein
Zufallsschnitt**, sondern die Bereiche mit Verus-Beweis — die **gut verstandenen**. Deren
Richtung ist bekannt: gut verstandene Bereiche haben **weniger** Wertaussagen. **Damit ist
w = 0,341 eine Untergrenze und 1,90 ebenso.** Der wahre Wert liegt hoeher, nicht tiefer.

## «B34», wie vorab versprochen

`revoke`s Kostenzusage steht als **W** — eine Aussage ueber eine gerechnete Groesse. Sie ist
nicht unter K gebucht worden.

---

# Empfindlichkeitsprobe: **taugt Verus ueberhaupt als Grundgesamtheit?**

**Die Frage kam von aussen, und sie ist beziffert zu beantworten.** Nachtraeglich und getrennt
gefuehrt — **die berichtete Zahl (W = 40, Tor bestanden) wird nicht angetastet** (R2).

## Was in den 81 steckt, das keine Logik-Pflicht ist

**Acht der 81 sind Werkzeugartefakte**: sie quantifizieren ueber rohe `Seq<…>` und behaupten
etwas ueber `push`/`update`/`len` — *das ist die Datenstruktur des BEWEISERS, nicht der
Gegenstand.*

```
region-runtime/lemma_live_push:47        ensures live_bytes(regions.push(r)) == …
capability-system/lemma_refs_push:90     ensures refs_to(slots.push(sl), o) == …
capability-system/lemma_refs_update:117  requires 0 <= i < slots.len(), …
…  (8 Stueck, 122 Zeilen)
```

Ein Faltungslemma ueber `Seq::push` sagt nichts ueber Capabilities. **Es existiert, weil der
SMT-Loeser einen Hinweis brauchte.** In Gabbro gaebe es diese Pflicht nicht — nicht weil die
Sprache klueger waere, sondern weil die Frage nie gestellt wuerde.

## Und ihre Entfernung KIPPT das Tor

| | N_L | K | A | W | Tor |
|---|---:|---:|---:|---:|---|
| wie berichtet | 81 | 28 | 13 | **40** | **bestanden** (40 ≤ 40,5) |
| ohne die 8 Werkzeugartefakte | 73 | 28 | 7 | **38** | **VERFEHLT** (38 > 36,5) |

`w` steigt von 0,341 auf 0,358, der Ueberschlag von 1,90 auf **1,98**.

> **Das Torergebnis haengt daran, ob Verus' Sequenzlemmata als Logik-Pflichten zaehlen.**
> Sie sollten es nicht. **Damit ist das Tor nicht robust**, und das ist ein groesserer Befund
> als die Richtung, in die es faellt.

## Die Antwort auf die Frage

**Verus ist eine gute VERFUEGBARKEITS-Grundlage und eine schlechte SEMANTISCHE.**

| dafuer | dagegen |
|---|---|
| Die 81 sind **aufgeschrieben und maschinell geprueft** — anders als jede Handzaehlung, die einen Klassierer braucht (und genau daran starb die erste `narrow`-Zaehlung) | Ein `proof fn` entsteht, **wenn der Loeser einen Hinweis braucht** — nicht, wenn die Sache eine Pflicht hat. Das ist eine Aussage ueber das Werkzeug |
| Sie tragen `Datei:Zeile`, also W7-tauglich | Sie beweisen ueber einem **MODELL** (`cap_space.rs`), nicht ueber dem Code (`space.rs`). **Die Verfeinerung — bei seL4 27,8 % des Aufwands — kommt gar nicht vor** |
| Sie sind die einzige Grundlage, die im Baum existiert | Bereiche ohne Verus-Beweis zaehlen **null**: MMU, Parser, Bringup. Die gut verstandenen sind ueberrepraesentiert, und die Richtung der Verzerrung ist bekannt |

**Der schwerste Punkt ist die Verfeinerung.** Gabbros Zusage lautet *„Absenkung ist nahe 0"*,
und die Verus-Grundgesamtheit kann diese Zusage **nicht pruefen**, weil sie dieselbe Luecke
hat: sie beweist ueber einem Modell. **Eine Messung, die den groessten Posten des Vergleichs
gar nicht enthaelt, kann ihn auch nicht widerlegen.**

## Was eine bessere Grundlage waere

Keine, die heute verfuegbar ist — und das ist der ehrliche Schluss. Was sie haben muesste:

1. Pflichten **am Code**, nicht am Modell (also mit Verfeinerung).
2. Eine Herkunft, die **nicht am Automatisierungsgrad eines Loesers haengt**.
3. Fundstellen (W7).

**Bedingung 1 und 2 schliessen einander heute aus:** was am Code beweist, tut es mit einem
Loeser, und dessen Hinweise landen in der Zaehlung. *Das ist kein Mangel dieser Messung,
sondern der Grund, warum die Zahl 1,90 mit ihrer Grundlage zitiert werden muss und nicht
allein.*

---

# Rennen und Publikation — neu beurteilt, 2026-08-16

Die Neuerhebung buchte beide als haengend, **mit demselben Grund**: *der Paarungspass ist
nicht gebaut.* Er ist gebaut.

## Was der Pass deckt, mit Fundstellen (W7)

| | Absage | Fundstelle im Pruefer | Probe |
|---|---|---|---|
| verwaistes `publishes` | `V001` | `crates/gabbro-check/src/paarung.rs:123` | `beispiele/gift/51-verwaistes-publishes.gab` |
| verwaistes `awaits` | `V002` | `paarung.rs:139` | `gift/50-verwaistes-awaits.gab` |
| unentscheidbar (Zyklus) | `V003` | `paarung.rs:108` | — (W10, dritter Zustand) |
| `relaxed` mit Nutzlast | `V004` | `paarung.rs:153` | `gift/52-relaxed-mit-nutzlast.gab` |
| **Paarung ueber Zwischenfunktion** | — | `paarung.rs:94-101` (vereinigte Menge) | `beispiele/14-paarung-ueber-zwischenfunktion.gab` |

Mutationen: `paarung-je-funktion`, `verwaistes-awaits-egal`, `relaxed-darf-tragen` —
**alle drei gefangen**, 44 von 44 auf der Flaeche *pruefer*.

## Urteil je Klasse

**Publikation — GETRAGEN.** `publishstmt` nennt die Nutzlast am Store, der Pass haelt beide
Haelften gegeneinander, und `relaxed` kann keine tragen. *Die Klasse faellt.*

**Rennen — HAENGT WEITER, und der Grund ist jetzt ein anderer.**

> Der Pass prueft, dass die **Deklarationen** paaren. Er prueft **nicht**, dass
> `release`/`acquire` auf der Zielmaschine die Sichtbarkeit herstellen, die die Paarung
> behauptet — das ist eine Aussage ueber das **Speichermodell**, und sie faellt in die
> **Axiomschicht**, nicht in den Pass.

**Das ist kein Mangel des Passes, sondern die Grenze dessen, was ein Pass hier leisten kann.**
Und es verschiebt die Klasse von *„ungebaut"* nach *„gebaut, ruht auf benannten Axiomen"* —
derselbe Ort, an dem `Verfeinerung` steht.

*Die Axiomschicht ist im W7-Kehraus als unbelegt markiert (106 ohne Liste). **Rennen haengt
damit an einer Zahl, die selbst offen ist.***

## N_neu: **5 → 4**

| | Stand |
|---|---|
| Index, Ueberlauf, Alias, Sperre, Terminierung, Blattheit | getragen |
| **Publikation** | **getragen (neu)** |
| Rahmen | haengt an EINER Haelfte (Lesen) — eine Entscheidung, keine Arbeit |
| **Rennen** | haengt an der **Axiomschicht**, nicht mehr am Pass |
| Phase | unentschieden — wird am Lader-Fragment entschieden (R18) |
| Verfeinerung | ruht auf der Absenkung; Uebersetzungsvalidierung je Bau ist der Weg |

**Sieben von elf getragen.** Und die vier uebrigen sind vier **verschiedene** Arten von
Entfernung — eine Entscheidung, eine Axiomzahl, ein Fragment, ein Teilprojekt.

---

# VORAB — das Lader-Fragment entscheidet die Klasse *Phase*

**Eigener Commit, VOR dem Schreiben des Fragments.** Danach wird hier nichts geaendert.
Messbasis: `../caprock-messbasis` @ `a1bf707`, `kernel/src/arch/x86_64/bringup.rs`
(**6 706 Zeilen, 36 Funktionen**).

## Warum am Fragment und nicht per Zaehlung (R18)

Die Neuerhebung fand fuer *Phase* **eine einzige Fundstelle im ganzen Baum**, und die ist ein
**Kommentar**: `caprock-slab/src/lib.rs:173` — *„nur beim Boot aufrufen, bevor andere Kerne"*.

> **Eine Klasse mit einer Fundstelle, deren Schreibweise fehlt, wird nicht per Zaehlung
> entschieden.** Was man nicht schreiben kann, zaehlt niemand: ein Kommentar ist billig, ein
> linearer Wert nicht. **Am Fragment zeigt sich, ob die Form traegt oder fehlt.**

*`locks ordered` bleibt gueltig gestorben — Doppelnahme war schreibbar und kam trotzdem nicht
vor. Hier ist es umgekehrt.*

## Was gezaehlt wird

**Stellen, an denen `BootPhase` als linearer Wert eine Pflicht traegt, die heute nichts
traegt.** Eine Stelle zaehlt, wenn **eine** der drei Bedingungen gilt:

1. **Einkern-Annahme** — die Operation ist nur korrekt, solange die weiteren Kerne stehen
   (kein Lock, weil noch niemand nebenlaeufig ist).
2. **Reihenfolgezwang** — sie muss nach einem benannten Bootschritt laufen und vor einem
   anderen, und nur Prosa sagt das.
3. **Einmaligkeit** — sie darf genau einmal laufen, und nichts erzwingt es.

**Belegt wird jede Stelle mit `Datei:Zeile`** — ab dem ersten Entwurf, nicht im Endstand (W7).

## Das zweiseitige Tor — **k = 5**

| | |
|---|---|
| **konstruktwuerdig** | die Marke traegt an **≥ 5** Stellen |
| **stirbt wie `locks ordered`** | sie traegt an **≤ 4** — dann ist der heutige Kommentar die angemessene Form, und `BootPhase` kommt aus der Sprache |
| **ungueltig** | die drei Bedingungen lassen sich an `bringup.rs` nicht entscheiden — dann fehlt das Kriterium, nicht die Antwort |

**Warum 5 und nicht 1:** ein Konstrukt, das eine einzige Stelle traegt, ist eine Sonderregel.
Fuenf ist die Schwelle, ab der eine Form sich lohnt — dieselbe Groessenordnung, mit der die
`Sonderform`-Klasse zum Muster wird.

**Und die Zahl steht hier, weil sie danach nicht mehr gewaehlt werden kann.** Faellt die
Messung auf 4, ist das ein Ergebnis; faellt sie auf 6, ebenso. *Beides ist vorab ein gutes
Ergebnis — der eine Ausgang spart ein Konstrukt, der andere begruendet eines.*

## ERGEBNIS des Lader-Fragments — die Klasse *Phase* ist **konstruktwuerdig**

**Gemessen: 7 Stellen gegen ein Tor von k = 5.** Jede mit `Datei:Zeile` in `FRAGMENTE.md`
(F7). *Konservativ gezaehlt* — `main.rs:144` und `:151` beschreiben **dieselbe** Grenze von
zwei Seiten und sind als **eine** Stelle gebucht, nicht als zwei.

| | |
|---|---|
| Kandidaten roh | 8 |
| nach Zusammenfassung der MMU-Grenze | **7** |
| Tor | **5** |
| **Urteil** | **traegt — die Klasse kommt nicht aus der Sprache** |

## Der Beleg, der schwerer wiegt als die Zahl

`main.rs:251`, woertlich:

> *„D5: erst das Autoritaetsdokument melden, dann den Root-Task starten. **Genau diese Zeile
> fehlte auf ARM** — hier lief der Manifest-Pfad ungeprueft mit."*

**Ein bezahlter Fehler genau dieser Klasse.** Die Reihenfolge stand als Kommentar in einer
Architektur und **fehlte in der anderen**; kein Werkzeug konnte es sagen. *Das ist der
Unterschied zwischen „selten" und „selten sichtbar", den R18 verlangt hat — und er faellt
zugunsten der Sichtbarkeit.*

## Und der Ertrag ist nicht die Zahl, sondern «B37»

**Die Marke traegt „vor der MMU" gegen „nach der MMU"** — dort liegt ein Verbrauch, und
Linearitaet macht die zwei Seiten unterscheidbar.

**Die vier Reihenfolgezwaenge INNERHALB einer Phase traegt sie nicht.** `cap_tabellen` vor
`ipc_tabellen` steht im Fragment nur, weil ich es hingeschrieben habe: der Uebersetzer sieht
eine Kette von Verbraeuchen und sagt **nichts ueber ihre Ordnung**.

> **«B37»: Linearitaet erzwingt *genau einmal*, nicht *in dieser Ordnung*.**
>
> Fuer die Reihenfolge braeuchte es je Schritt eine **eigene Marke** — dann waechst der
> Wortschatz mit jedem Bootschritt, und das ist die Bewegung, gegen die `abi { … }` und
> `locks ordered` gestorben sind — oder eine **Ordnung auf Marken**, und die gibt es nicht.

**Damit ist die Klasse *Phase* halb getragen**, und die Kippregel sagt, wohin das faellt:
*traegt ein Konstrukt eine Klasse nur teilweise, zaehlt sie als haengend, und der gedeckte
Teil wird benannt.* **Phase bleibt in N_neu.**

## Konvergenzmetrik — der erste Datenpunkt aus einem Bereichsfragment

| Fragment / Anlass | neue Konstrukte | kumulativ |
|---|---:|---:|
| F1–F6 (Bestand) | — | Basis |
| «B32» virtio-Ringzaehler | 1 (`wrapping` am `regdecl`) | 1 |
| «B34» revoke-Schranke | 0 — die Praemisse fiel | 1 |
| «B29» refcount-Unterlauf | 0 — `narrow` genuegte | 1 |
| `heldpred` (aus H005) | 1 | 2 |
| «B35» `Some`/`None` | 1 | 3 |
| **F7 Lader/Bringup** | **0** | **3** |

**Das Lader-Fragment hat kein neues Konstrukt gekostet** — es hat eines *begruendet*
(`BootPhase`, das es schon gab) und eine **Grenze** gefunden («B37»).

> **Ein Datenpunkt ist keine Kurve.** Drei weitere Bereichsfragmente stehen aus, und erst mit
> ihnen sagt die Metrik etwas ueber Konvergenz. *Aber sie ist nicht mehr leer.*

---

# KONVERGENZMETRIK — vollständig, 2026-08-16

**Die Probe auf das stärkste Produktargument des Ordners:** *neue Konstrukte je
ausgeschriebenem Bereichsfragment müssen fallen.* Sie hatte bis heute **null Datenpunkte aus
Bereichsfragmenten**; jetzt hat sie **vier**.

> **Zwei Spalten, nicht eine — und das ist der ehrliche Rahmen um die Zahl.**
> **Null neue Wörter ist nicht null Sprachbewegung.** Die Wortschatz-Konvergenz misst nur
> *eine* der beiden Unterhaltsgrössen; die andere ist die **Schablonen- und Axiomfläche**,
> und sie wächst weiter. Ohne die zweite Spalte wird die zweite Bewegung unsichtbar, sobald
> die erste glänzt.

| Fragment / Anlass | **neue Konstrukte** | **veränderte Bedeutung Bestehender** | kumul. Wörter |
|---|---:|---|---:|
| F1–F6 (Bestand, 2. Fassung) | — | — | Basis |
| «B32» virtio-Ringzähler | 1 — `wrapping` am `regdecl` | — | 1 |
| «B34» revoke-Schranke | 0 — die Prämisse fiel | — | 1 |
| «B29» refcount-Unterlauf | 0 — `narrow` genügte | — | 1 |
| `heldpred` (aus `H005`) | 1 | `Held` trägt jetzt seine **Stärke** | 2 |
| «B35» `Some`/`None` | 1 | — | 3 |
| **F7 Lader/Bringup** | **0** | **«B37»:** `BootPhase` trägt *genau einmal*, **nicht** *in dieser Ordnung* — eine benannte **Grenze** | 3 |
| **F8 Scheduler** | **0** | **«B38»:** Sperrgrenze verlangt Neuvalidierung **oder benannten Träger** — Semantik erweitert | 3 |
| **F9 MMU/Seitentabellen** | **0** | **«B39»:** die Axiomschicht wird **länger** (`A`/`D` als Hardwareschreiber) | 3 |
| **F10 Parser/Checkpoint** | **0** | — | 3 |
| **B3 (ganzer Kernel, keine Fragmentzeile)** | **1** — `ancestors of` | **«B41»:** zwei weitere Lücken, **keine davon ein Konstrukt** (offene Frage bzw. Vorhersage) | 3 |

## **Vier Bereichsfragmente, null neue Konstrukte — und drei veränderte Bedeutungen.**

**Das ist der erste echte Beleg für die Konvergenzwette** — und er ist stärker, als die Zahl
aussieht: die vier Bereiche waren **nie ausgeschrieben** und galten als die schwersten
(Scheduler, MMU, Lader, Parser). *Jeder von ihnen hätte ein Konstrukt fordern können.*

## Was sie STATTDESSEN gefordert haben — und das ist der ehrliche Teil

**Kein neues Konstrukt, aber vier Befunde und zwei Prüferlücken:**

| | Befund | Art |
|---|---|---|
| «B37» | `BootPhase` trägt *genau einmal*, nicht *in dieser Ordnung* | **Grenze eines vorhandenen Konstrukts** |
| «B38» | `Stale(T)` in der Zwangsfassung ist **widerlegt** — 2 von 5 Übergängen ruhen auf `masks IRQ`, nicht auf Neuvalidierung | **Kandidat gestorben** |
| «B39» | die MMU schreibt `A`/`D` selbst — ein Schreiber, den keine `effects`-Zeile nennt | **gehört in die Axiomschicht** |
| «B40» | der DTB-Parser prüft 145 Zeilen fehlerfrei ohne Werkzeug — `format` gewinnt **Kürze, nicht Sicherheit** | **geht gegen den Ordner** |
| «B41» | **drei Domänen fehlen, und zwar gemessen** (B3): `ancestors of` (die Gerätetopologie wird aufwärts gelaufen), Union-Find (`find` schreibt die Kette, die es läuft), Kette über eine **Kantenfunktion** (`kante: impl Fn(u16) -> Option<u16>`) | **erste gemessene Konstruktforderung** |

Dazu **zwei Lücken im Prüfer**, beide am MMU-Fragment gefunden und beide geschlossen:

1. Die Domäne `mappings of` hatte **keine Schranke**, obwohl `levels × Knotenlänge` in der
   `walk`-Deklaration steht — dieselbe Klasse wie die `queue`-Domäne.
2. **Ein `walk` war dem Typsystem gar nicht bekannt.** `ptr<normal, r> Seitenabstieg` war
   schlicht `Unbekannt`; die Kette kannte Formate, Geräte und Tabellen — und keine Walks.
   *Die Schranke stand schon da und griff trotzdem nicht.*

> **Die Wette hält an vier Punkten, und der Preis steht daneben.** Die Fragmente kosteten
> kein Konstrukt — sie kosteten **zwei Prüferreparaturen, einen toten Kandidaten und einen
> Befund gegen das eigene Produktargument.** *Das ist ein besseres Ergebnis als eine glatte
> Null, weil man es nachrechnen kann.*

## Und die zweite Spalte ist die, die weiterwächst

**Der Wortschatz konvergiert (Spalte 1). Die Vertrauensfläche nicht (Spalte 2).**
«B39» verlängert die Axiomschicht, «B38» erweitert eine Semantik, «B37» zieht eine Grenze in
ein vorhandenes Konstrukt. **Keine dieser drei Bewegungen erscheint in der Wortzählung**, und
alle drei erhöhen, was ein Leser glauben muss.

> *Wer die Konvergenzwette zitiert, zitiert Spalte 1. Der Unterhalt steht in Spalte 2.*

## NACHTRAG (2026-08-16): **«B41» steht neben der Null in Spalte 1, nicht darunter**

**Die Null in Spalte 1 gilt für die vier Bereichsfragmente F7–F10. B3 misst eine andere
Grundgesamtheit — den ganzen Kernel — und findet dort eine Forderung nach drei Domänen.**

| | Grundgesamtheit | neue Konstrukte |
|---|---|---:|
| Konvergenzmetrik F7–F10 | vier ausgeschriebene Bereichsfragmente | **0** |
| **B3** | **`kernel/` + `crates/`, 2 186 Rümpfe** | **1** (`ancestors of`) |

**Die Eins ist gereiht, nicht gerundet.** Von den drei Lücken zählt hier **nur `ancestors
of`** — eine Domänenzeile mit derselben Erzeugungslogik wie `descendants of`, also ein
Konstrukt im Sinn der Metrik. Die **Kantenfunktion** ist eine offene Frage nach der Linie
(der allgemeine Fall von `chain(a,b)`), und **Union-Find bekommt voraussichtlich gar keine
Traversierungsform** — es ist die getarnte Verschränkung aus P0.1-Versuch 1, kein fehlender
Vorrat. *Wer alle drei als Konstrukte zählt, zählt eine Vorhersage und eine offene Frage mit.*

> **`ancestors of` ist damit der erste konvergenzmetrisch GEMESSENE Konstruktbedarf:
> null aus vier Fragmenten, eins aus einer Messung.**

**Die Zahlen widersprechen sich nicht — sie beantworten verschiedene Fragen**, und genau
deshalb steht die zweite hier: **wer „null neue Konstrukte" zitiert, muss «B41» mitnehmen.**
Ein Fragment schreibt man in der Sprache, die man hat; ein Kernel enthält, was er enthält.
*Der Konvergenzbeleg wird schwächer, wenn man die Grundgesamtheit wechselt — und das ist
der ehrlichere Satz als die Null allein.*

> **Und die Forderung ist noch kein Bau.** W3 verlangt für ein Konstrukt einen **gemessenen
> Bedarf** — der liegt jetzt vor, mit `Datei:Zeile`. Er verlangt nicht, ihm zu folgen: drei
> Domänen mehr sind drei Domänen mehr, die jeder Leser glauben muss (Spalte 2). *Die
> Entscheidung steht im `TODO.md`, nicht hier.*

---

# B3 beziffern: welche Rümpfe sind NICHT als Traversierung schreibbar

> ## **Diese Messung hat R1 NICHT eingehalten, und das steht vor dem Ergebnis.**
>
> **Die Markenregel wurde mit sichtbaren Zahlen geschärft.** Der Ablauf im Protokoll des
> Laufs: Werkzeug gebaut und gefahren (Fassungen 1–4), *danach* der Vorab-Text geschrieben.
> Es gibt **keinen Vorregistrierungs-Commit**; das „VORAB" unten ist nachträglich
> aufgeschrieben. Genau die Versuchung, gegen die R1 steht — vier Fassungen, vier Zahlen,
> jede im Wissen um die vorige.
>
> **Was trotzdem hält, und warum die Zahl nicht in den Papierkorb geht:**
>
> 1. **Das Tor war vorregistriert, die Regel nicht.** Die 5 %-Latte steht in
>    `TODO.md` @ `642e4c0`:112–118, Eintrag „B3 beziffern“ — dort seit `75c9841`
>    (2026-08-13), also **drei Tage vor diesem Lauf**. Der Eintrag ist mit dieser Buchung nach
>    `DONE.md` gewandert; die Fundstelle nennt deshalb den Commit, nicht nur die Zeile. **R2 ist eingehalten** — verschoben
>    wurde nichts.
> 2. **Das Torurteil ist regelinvariant.** Die vier Fassungen ergaben 0,03 % · 4,36 % ·
>    0,74 % · 0,95 %. **Alle vier bestehen die 5 %-Latte** — auch die bewusst zu grobe
>    Fassung 2. *Von der Regelwahl hängt die Zahl ab, nicht das Urteil.*
> 3. **Jede Verschärfung ging in die teurere Spalte.** 19 → 26 Rümpfe: jeder Schritt fügte
>    hinzu, keiner entfernte. Wer eine Regel schärft, während das Tor „≤ 5 %" lautet,
>    schärft **gegen** das eigene Bestehen.
>
> **Was nicht heilbar ist:** eine Wiederholung „nach Protokoll" stellt die Vorregistrierung
> nicht her, weil die Regel jetzt bekannt ist. **R1 ist eine Einmalregel, und sie ist hier
> verfehlt.** Die Zahl gilt als *untere Schranke mit bestandenem, regelinvariantem Tor* —
> nicht als vorregistrierte Messung.
>
> ---
>
> ## **Der Satz, auf den die ganze Messung hinausläuft:**
>
> ## **Das Tor ist regelinvariant, aber buchungsvariant.**
>
> | | Spanne | Wirkung aufs Tor |
> |---|---|---|
> | **Regelfassungen** (0,03 % … 4,36 %) | **Faktor 130** | **keine** — alle vier bestehen |
> | **eine einzige Buchungsentscheidung** (Klasse *Index*) | **Faktor 21** | **das Tor kippt** |
>
> **Die Regelinvarianz trägt als Rettung mehr, als sie klingt:** ein Ergebnis, das über eine
> Faktor-130-Spanne **bewusst zu grober** Regeln stabil bleibt, ist gegen Regel-Fitting gut
> verteidigt. **Und ihre Grenze steht im selben Satz:** sie gilt nur innerhalb der
> **erprobten** Fassungen. Vier Fassungen sind keine Stichprobe aus dem Regelraum; sie sind
> vier Punkte, die ich gewählt habe. *Genau deshalb bleibt R1 als verfehlt gebucht, statt
> durch die Invarianz aufgehoben zu werden.*

## VORAB — nachträglich aufgeschrieben (s. Kasten), Wortlaut wie beim Lauf verwendet

**Messbasis:** `../caprock-messbasis` = `SEL4Lake/SEL4Lake` @ `arch/x86_64`, `a1bf707`.
Nur gelesen; `git status --porcelain` dort ist nach dem Lauf leer.
**Grundgesamtheit:** `kernel/` + `crates/`, 105 `.rs`-Dateien.

### Was „als Traversierung schreibbar" mechanisch heisst

Gabbro hat **drei** Schleifenformen (`dokumente/SYNTAX.md`:459–478) und **acht** Domänen
(`dokumente/SPRACHE.md`:778–783):

```
traverse … over <domäne> by (unvisited | consuming | decreasing e)
retry   … until <pred> bounded N ops on_exceeded <name>
forever … per_pass bounded N ops on_exceeded <name> effects { … }

Domänen: slots of · chain(a,b) in · descendants of · queue · fields of
         elems of · threads · mappings of
```

Ein Rumpf ist **nicht** als Traversierung schreibbar, wenn er mindestens eine der drei
Marken trägt. Die Marken sind syntaktisch und werden von `zaehle-b3.py` erhoben.

| Marke | Bedingung |
|---|---|
| **Na — Kettenlauf ohne Domäne** | In einem `while`/`loop` ist der Rundenfortschritt ein Kettenschritt: `x = …x….<feld>` (Zeigerkette), `x = A[x]` (Indexkette, ein Feld dessen Elemente Indizes in dasselbe Feld halten), oder `let Some(n) = f(x)` gefolgt von `x = n` (Kantenkette, eine erst durch einen Aufruf entstehende Kette). **Ausgenommen**, weil von einer Domäne gedeckt: `first_child`/`next_sibling` (`chain(first_child,next_sibling) in slots`, `descendants of`) und `qnext`/`qprev` (`queue`). |
| **Nb1 — Zeigerchirurgie ohne Domäne** | Der Rumpf **schreibt** ein Verkettungsfeld — Elementauswahl (`[…]`, `*`-Deref, `&mut`-Bindung) **und** ein Feld, das ein anderes Element derselben Sammlung benennt — an einer Struktur, für die keine der acht Domänen erklärbar ist. |
| **Nb2 — Zeigerchirurgie mit Domäne** | Dasselbe Schreiben an einer Struktur, die eine Domäne **hat**. |

**Warum Nb2 überhaupt zählt, und das ist die einzige wertende Entscheidung im Protokoll:**
eine Domäne gibt das **Lesen** einer Verkettung, nicht das **Umhängen**. `by consuming`
deckt genau das Entfernen des *gerade besuchten* Elements, also **einen** Schreibort je
Runde. Wer drei Nachbarn in einem Zug umbiegt, traversiert nicht. Das ist ein Grenzfall —
und Grenzfälle kippen nach Regel in die **teurere** Spalte.

**Beide Zahlen werden getrennt berichtet:** *Buchstabe* = Na + Nb1 (Wortlaut der
Definition), *berichtet* = Na + Nb1 + Nb2 (mit Kippregel). Wer die Kippentscheidung nicht
teilt, kann die andere Zahl ablesen, ohne nachzurechnen.

### Zählregel

* **Einheit ist der Funktionsrumpf**, nicht die Schleife. Ein Rumpf mit fünf Schleifen, von
  denen eine kippt, zählt einmal — mit **allen** seinen Zeilen.
* **Zeilen je Rumpf = nicht-leere Zeilen zwischen den Rumpfklammern**, Kommentare
  eingeschlossen. Die Bezugsgrösse ist mit derselben Regel gebildet.
* **Rümpfe ohne Schleife zählen mit.** Die zweite Hälfte der Definition kennt keine
  Schleifenbedingung: Zeigerchirurgie ist Zeigerchirurgie, ob geradeaus oder in einer
  Schleife. *Diese Festlegung war nötig, weil die namentlich erwartete
  Warteschlangenchirurgie des Schedulers gar keine Schleife hat (s. u.).*
* **Geschachtelte `fn` zählen nicht doppelt** — nur der äusserste Rumpf.
* **Bezugsgrösse:** nicht-leere Zeilen von `kernel/` + `crates/`. Zusätzlich wird die
  Grösse **ohne `#[cfg(test)]`-Module** geführt; berichtet wird die Paarung mit dem
  **grösseren** Verhältnis (teurere Spalte).

### Kippregel

1. Ist unklar, ob ein Feld ein **Verkettungsfeld** ist, gilt es als eines.
2. Ist unklar, ob eine Struktur eine **Domäne** hat, zählt sie als Nb2 — also mit.
3. Ist unklar, ob eine Schleife eine **Kette** läuft oder nur nachschlägt, zählt sie als Kette.
4. Prozente werden **aufgerundet**, nie wohlwollend gerundet.

### Das zweiseitige Tor

Das Tor ist **nicht neu gesetzt**, sondern aus `TODO.md` @ `642e4c0`:112–118 übernommen
(dort seit `75c9841`, 2026-08-13; heute in `DONE.md`): *„5 % des Kernels sind +0,25 auf die Kennzahl, 10 % sind +0,5"*, also
Aufschlag = Anteil · 5.

| | |
|---|---|
| **bestanden** | **p ≤ 5 %** — der Rest kostet höchstens **+0,25**, die Schleifenformen tragen den Kernel |
| **gefallen** | **p > 5 %** — die drei Schleifenformen decken zu wenig, und der Vorrat ist zu erweitern oder der Aufschlag zu tragen |

**Ungültig — getrennt von ungünstig, und keine dieser Bedingungen sagt etwas über die Höhe von p:**

* **U1** Der Klammerabgleich bricht in mehr als 2 % der Dateien ab → das Rumpfverzeichnis
  ist unvollständig, die Zahl ist keine Messung (R16).
* **U2** R14(b) schlägt fehl: eine Änderung am Prüfling ändert die Zahl nicht → das
  Werkzeug hängt nicht am Gegenstand.
* **U3** Die Handstichprobe (**n = 13**: jeder 4. der nach `Datei:Zeile` sortierten
  N-Liste, plus 6 gleichabständige aus der Menge der Rümpfe mit Schleife ohne Marke)
  zeigt **mehr als 1** Fehlklassifikation.
* **U4** Mehr als ein Drittel der Marken lässt sich nur mit Fliesstext begründen statt mit
  einer Fundstelle → dann trennt das Kriterium nicht.

### R14 — das Geschirr zuerst

* **(a) Ein Abbruch muss sich von einem Treffer unterscheiden.** Eine unbalancierte Klammer
  wird in die *Kopie* eines Prüflings gesetzt; das Werkzeug muss `Abbrueche: 1` melden und
  darf nicht stillschweigend eine Zahl liefern.
* **(b) Die Zahl muss am Prüfling hängen.** Drei Mutationen an der Kopie: einen N-Rumpf
  **entfernen**, einen künstlichen N-Rumpf **einfügen**, einen N-Rumpf in eine
  **Traversierung umschreiben**. Jede muss die Zahl in die vorhergesagte Richtung bewegen,
  die Rücknahme muss den Ausgangswert wiederherstellen.
* **(c) Vollzählung statt Regelvertrauen bei den `for`-Köpfen.** Die Domänenerkennung im
  `for`-Kopf ist eine Musterliste und damit angreifbar. Deshalb werden **alle** verschiedenen
  `for … in`-Ausdrücke aufgezählt und die ohne Musterteffer **einzeln** von Hand entschieden.

---

## ERGEBNIS — 2026-08-16, nur x86, gegen `a1bf707`

### Die Grundgesamtheit

```
./zaehle-b3.py ../caprock-messbasis
find kernel crates -name '*.rs' -exec cat {} + | wc -l              # 69 283 roh
find kernel crates -name '*.rs' -exec cat {} + | grep -c '[^[:space:]]'   # 65 168 nicht leer
```

| | |
|---|---:|
| Dateien | 105 |
| Zeilen roh / nicht leer | 69 283 / **65 168** |
| davon `#[cfg(test)]`-Module (nicht leer) | 4 412 |
| Bezugsgrösse ohne Testmodule | **60 756** |
| Funktionsrümpfe | 2 536 (davon 2 186 ausserhalb der Testmodule) |
| Rümpfe mit Schleife | 462 |
| Schleifen: `for` / `while` / `loop` | 571 / 146 / 117 |

### R14 — alle drei Proben bestanden

**(a) Abbruch.** Unbalancierte Klammer in `dmar.rs` → `Abbrueche: 1`. Wichtiger als das
Melden ist, **was daneben passierte**: die berichtete Zahl fiel dabei still von 26 auf 24,
weil zwei Rümpfe aus dem Verzeichnis fielen. **Ohne den Abbruchzähler hätte die Messung
eine um zwei zu niedrige Zahl geliefert und dabei gesund ausgesehen.**

**(b) Die Zahl hängt am Prüfling.**

| Mutation an der *Kopie* | erwartet | gemessen |
|---|---|---|
| `dmar::union` (6 Z) entkernt | −1 Rumpf | 26 → **25**, 621 → 615 Z |
| künstlicher Kettenlauf über eine Kantenfunktion angehängt | +1 Rumpf | 26 → **27**, 621 → 631 Z |
| Rücknahme beider | Ausgangswert | **26 / 621 Z** |

**(c) Die `for`-Köpfe, vollzählig.** 347 verschiedene `for … in`-Ausdrücke. 331 treffen ein
Domänenmuster. Die **16 übrigen wurden einzeln entschieden** und sind **alle** Domänen:
elf blosse Orte (`segs`, `endow`, `caps`, `regions`, `runs`, `w`, `holes`, `bytes`,
`entries`, `data`, `paare` → `elems of`), zwei Feldliterale (`&[true,false]`,
`&[0u32,1,4242]`), ein Pfad (`system::ERLAUBTE_SPAETBINDUNGEN`) und zwei eigene Iteratoren,
die beide domänengestützt sind: `img.segments()` = `(0..self.phnum).filter_map(…)`
(`elf.rs`:166 → `slots of`) und `self.ops()` = `&[Op]` (`irte.rs`:1023 → `elems of`).

> **Befund, und er geht gegen die Erwartung:** **keine einzige der 571 `for`-Schleifen im
> Kern läuft über etwas, das keine Domäne ist.** Die Nicht-Traversierbarkeit sitzt
> vollständig in `while`, `loop` und in schleifenlosen Rümpfen.

### Die Zahl

| | Rümpfe | Zeilen | Anteil | Aufschlag |
|---|---:|---:|---:|---:|
| **Buchstabe** (Na + Nb1) — ohne Testmodule | 12 | 387 | 0,637 % | +0,032 |
| **berichtet** (+ Nb2, Kippregel) — ganzer Baum | 26 | 621 | 0,953 % | +0,048 |
| **berichtet** — ohne Testmodule | 22 | 584 | **0,961 %** | **+0,048** |
| nachrichtlich, gegen den TODO-Nenner 75 294 (roh, ganzer Baum) | 26 | 621 | 0,825 % | +0,041 |

**Berichtet wird die teuerste Paarung: p = 0,961 %, aufgerundet p = 1,0 %.**

#### **Tor BESTANDEN** — p = 1,0 % gegen eine Latte von 5 %, mit Faktor 5 Abstand.

Abbrüche: **0**. U1–U4 sämtlich nicht ausgelöst. Die Handstichprobe (n = 13) ergab
**0 Fehlklassifikationen** bei einer Toleranz von 1 — geprüft wurden `move_cap`,
`abstieg_terminiert_auf_einem_zyklus`, `scope_covers`, `build_groups`,
`handler_kante_loesen`, `remove_from_ready`, `alloc` aus der N-Liste und `classify_all`,
`exception::init`, `arbitrary_mutations_never_panic`, `ring3_worker`, `loader::probe`,
`run_certfuzz` aus der Gegenmenge.

### **Und der Ertrag steht nicht in der Zahl. Er steht in der Verdachtsliste, die falsch war.**

> **Alle drei namentlich erwarteten Kandidaten waren falsch getippt, und der grösste Posten
> stand in keinem Verdachtsbereich.** DMAR/PCIe stellt **226 der 584 Zeilen (38,7 %)** —
> mehr als Scheduler und CDT einzeln.

**Das ist R18 von der anderen Seite.** Die Regel steht als *Sichtbarkeitsverzerrung*: was
laut ist, wird gezählt. Hier war es die Umkehrung — **die Verdachtsliste stammte aus dem, was
*berühmt* schwer ist** (IPC-Fastpath, `revoke`, Scheduler-Warteschlange), **nicht aus dem, was
*gemessen* schwer ist** (Gerätetopologie, Union-Find, Handler-Ketten). *Ein Verdacht aus dem
Ruf einer Sache ist keine Messung; er ist die Erinnerung an fremde Kernel.*

**Und `revoke` liefert nebenbei den schönsten Beleg, den `by consuming` je bekommen wird.**
Der Rumpf, für den das Konstrukt **auf Papier entworfen** wurde, existiert im echten Kernel
bereits in genau dieser Form — `space.rs`:619–657, Wort für Wort `descendants of s by
consuming`, samt handgeschriebener `bounded N ops`-Disziplin. **Nicht ein Konstrukt, das zu
einem Rumpf passt, sondern ein Rumpf, der ohne die Sprache dieselbe Form gefunden hat.**

### Die 26 Rümpfe, je mit `Datei:Zeile` (W7)

| `Datei:Zeile` | Rumpf | Marke | Z |
|---|---|---|---:|
| `crates/caprock-cap/src/space.rs:557` | `move_cap` | Nb2 | 34 |
| `crates/caprock-cap/src/space.rs:783` | `audit_cdt` | Na | 100 |
| `crates/caprock-cap/src/space.rs:1032` | `link_child` | Nb2 | 10 |
| `crates/caprock-cap/src/space.rs:1044` | `unlink` | Nb2 | 15 |
| `crates/caprock-cap/src/space.rs:1138` | `abstieg_terminiert_auf_einem_zyklus` *(Testmodul)* | Nb2 | 10 |
| `crates/caprock-cap/src/space.rs:1152` | `abstieg_weist_index_ausserhalb_der_tabelle_ab` *(Testmodul)* | Nb2 | 7 |
| `crates/caprock-cap/src/space.rs:1163` | `kinderliste_zaehlt_und_bricht_ab` *(Testmodul)* | Nb2 | 14 |
| `crates/caprock-cap/src/space.rs:1182` | `kinderliste_weist_index_ausserhalb_der_tabelle_ab` *(Testmodul)* | Nb2 | 6 |
| `crates/caprock-hal/src/x86_64/dmar.rs:374` | `scope_covers` | Na | 24 |
| `crates/caprock-hal/src/x86_64/dmar.rs:519` | `find` | Na, Nb1 | 7 |
| `crates/caprock-hal/src/x86_64/dmar.rs:526` | `union` | Nb1 | 6 |
| `crates/caprock-hal/src/x86_64/dmar.rs:538` | `alias_rid` | Na | 13 |
| `crates/caprock-hal/src/x86_64/dmar.rs:553` | `build_groups` | Na | 106 |
| `crates/caprock-hal/src/x86_64/dmar.rs:689` | `is_below` | Na | 12 |
| `crates/caprock-hal/src/x86_64/pcie.rs:406` | `read_topology` | Nb1 | 58 |
| `crates/caprock-microkit/src/lib.rs:779` | `handler_kante_setzen` | Nb1 | 8 |
| `crates/caprock-microkit/src/lib.rs:793` | `handler_kante_loesen` | Nb1 | 10 |
| `crates/caprock-sched/src/lib.rs:926` | `switch_to` | Nb2 | 21 |
| `crates/caprock-sched/src/lib.rs:1700` | `end_donation` | Nb2 | 10 |
| `crates/caprock-sched/src/lib.rs:1873` | `enqueue_ready` | Nb2 | 18 |
| `crates/caprock-sched/src/lib.rs:1893` | `remove_from_ready` | Nb2 | 25 |
| `crates/caprock-sched/src/lib.rs:1922` | `record_zombie` | Nb2 | 46 |
| `crates/caprock-sched/src/redirect.rs:577` | `pruefe_bindung` | Na | 31 |
| `crates/caprock-sched/src/redirect.rs:625` | `kettenlaenge` | Na | 12 |
| `crates/caprock-slab/src/lib.rs:258` | `alloc` | Nb2 | 10 |
| `crates/caprock-slab/src/lib.rs:271` | `free` | Nb2 | 8 |

Verteilung der 584 Zeilen ausserhalb der Testmodule: **DMAR/PCIe 226 Z (38,7 %) ·
Scheduler 163 Z (27,9 %) · CDT 159 Z (27,2 %) · Microkit 18 Z · Slab 18 Z.**

---

### Was gegen die eigene These spricht

#### 1. Alle drei namentlich erwarteten Kandidaten waren falsch getippt — zwei ganz, einer halb.

**`revoke` ist die sauberste Traversierung im ganzen Baum.**
`crates/caprock-cap/src/space.rs`:619–657 ist Wort für Wort
`traverse it of s over descendants of s by consuming { delete_leaf(it) }` — und trägt die
`bounded N ops`-Form bereits von Hand: `limit = self.cdt_step_limit()`, `ops > limit`,
`note_overrun()`. Der Rumpf steht **nicht** in der Liste, und zwar nicht durch eine
wohlwollende Regel, sondern weil `descendants of` ihn deckt. *Der TODO-Eintrag hat hier
das Gegenteil vermutet.*

**Ein IPC-Fastpath existiert — aber nicht dort, wo gesucht wurde, und er kostet aus einem
anderen Grund.** `grep -rniE 'fastpath|fast_path' kernel crates` → 12 Fundstellen; der
Pfad ist `Scheduler::switch_to` (`crates/caprock-sched/src/lib.rs`:926). Das
Nachrichtenkopieren, das man verdächtigt hätte, ist `for i in 0..MSG_WORDS`
(`crates/caprock-ipc/src/lib.rs`:171–177) = `slots of`, und die Endpunkt-Warteschlange ist
ein Ringpuffer über einem Feld (`head`/`tail` mod `QCAP`, ebd. 68–95) = `queue`. **Was
`switch_to` teuer macht, ist die Chirurgie an den Spendenkanten** `sc_donor`/`sc_donee` —
zwei wechselseitige Verweise zwischen TCBs, für die keine der acht Domänen erklärbar ist,
weil **niemand sie je läuft** (kein `for`/`while`/`loop` im Baum folgt ihnen). 21 Zeilen,
nicht der Nachrichtenpfad.

**Die Warteschlangenchirurgie des Schedulers ist echt — hat aber gar keine Schleife.**
`enqueue_ready` (18 Z) und `remove_from_ready` (25 Z) sind geradeaus, O(1). Und die
Bereitliste **hat** eine Domäne (`queue`); ihre Läufer — `migration_candidate`:1415 und
`audit`:1743, beide `while i != NIL { i = t.qnext }` — sind saubere Traversierungen und
stehen **nicht** in der Liste. Die Chirurgie landet nur über die **Kippregel** in der
teuren Spalte, nicht nach dem Wortlaut der Definition. *Hätte ich die Kippregel nicht
vorab festgeschrieben, wäre der namentlich erwartete Posten mit 43 Zeilen ganz
herausgefallen.*

#### 2. Der grösste Posten steht in keinem der drei Verdachtsbereiche.

**DMAR/PCIe stellt 226 der 584 Zeilen — 38,7 %, mehr als Scheduler und CDT einzeln.** Und
er benennt eine **konkrete Sprachlücke**, die keine Zählung vorher hatte:

* **Gabbro hat `descendants of`, aber kein `ancestors of`.** Vier der fünf DMAR-Rümpfe
  (`scope_covers`, `alias_rid`, `build_groups`, `is_below`) laufen die Gerätetopologie
  **aufwärts**: `cur = topo[cur].parent`. Abwärts wäre es eine Domäne; aufwärts ist es keine.
* **Union-Find ist keiner der acht Domänen zugänglich** — `dmar.rs`:519 `find` schreibt die
  Kette, die es gerade läuft (`parent[x] = parent[parent[x]]`). Das ist Traversierung und
  Chirurgie in derselben Anweisung.
* **Eine Kette, die erst durch einen Aufruf entsteht,** ist nicht deklarierbar:
  `pruefe_bindung`/`kettenlaenge` (`redirect.rs`:577, 625) laufen die Handler-Kante über
  einen Parameter `kante: impl Fn(u16) -> Option<u16>`.

**Diese drei Lücken sind der eigentliche Ertrag der Messung, und sie wiegen mehr als die Zahl.**

##### **Sie sind aber NICHT gleichrangig — und die Reihung gehört daneben, sonst schlägt jemand eine `union_find`-Domäne vor**

| | Lücke | Urteil |
|---|---|---|
| **billig** | **`ancestors of`** | **eine Domänenzeile mit derselben Erzeugungslogik wie `descendants of`** — dieselbe Kante, andere Richtung. Die Konvergenzmetrik verkraftet sie als *gemessenen* Bedarf. |
| **mittel, offen** | **Kette über eine Kantenfunktion** | der **allgemeine Fall von `chain(a,b)`**. Die Frage ist nicht, ob es geht, sondern **wo die Linie liegt**: hält eine *deklarierte* Kantenfunktion — rein, M1-typisiert, wie der `update`-Rumpf von `exchange` — oder ist sie **Quantorenvorrat durch die Hintertür**? |
| **gar nicht** | **Union-Find** | **prinzipiell anders. Bekommt voraussichtlich gar keine Traversierungsform.** |

> **Union-Find ist keine fehlende Domäne, sondern eine getarnte Verschränkung.**
> `find` mit Pfadkompression **mutiert die Struktur, über die es läuft** — das ist nicht
> *„keine Domäne vorhanden"*, das ist **die Verschränkung aus P0.1-Versuch 1, als
> Leseoperation verkleidet.** Wer sie zur Domäne macht, holt genau den Fall zurück, an dem
> der erste Anlauf gescheitert ist.
>
> **Die ehrliche Vorhersage, damit sie später widerlegbar ist:** Union-Find bleibt
> **entweder ein 5 : 1-Posten** oder wird **Gruppen-`ops`-Material** — die Kompression als
> *erzeugte Operation* mit Erhaltung der Repräsentanten-Invariante, nicht als Schleifenform.
> *Das ist eine Vorhersage, keine Messung. Sie steht hier, damit der nächste Vorschlag sie
> zuerst schlagen muss.*

#### 3. Das Werkzeug hätte die Messung zweimal ruiniert — nicht der Gegenstand.

Vier Regelfassungen, vier Zahlen: **2 → 27 → 19 → 26 Rümpfe**, entsprechend
**0,03 % → 4,36 % → 0,74 % → 0,95 %.** (Die vierte Fassung ist die berichtete; die
Korrektur des `==`-Fehlers senkte sie noch von 27 auf 26.)

* Fassung 1 (0,03 %) sah nur Rümpfe **mit** Schleife — die schleifenlose Chirurgie war unsichtbar.
* Fassung 2 (4,36 %) las `for x in segs` als Nicht-Domäne; ein einziger falsch markierter
  Rumpf (`demo_report_then_idle`, 1 360 Z) machte allein 2 % aus.
* Fassung 3 übersah Indexketten (`find`/`union`), Kantenketten (`pruefe_bindung`,
  `kettenlaenge`) und die Spendenkanten (`switch_to`, `record_zombie`).
* Fassung 4 las `==` als Zuweisung und markierte `migration_candidate` (18 Z) falsch.

**Die beiden verworfenen Fassungen spannen einen Faktor 130 auf und klammern die richtige
Antwort ein.** Beide hätten sich mit derselben Fundstellenliste vorführen lassen. Der
Unterschied zwischen ihnen und der Endfassung ist **ausschliesslich R14** — die
Vollzählung der `for`-Köpfe und die drei Mutationsproben. **Eine Zahl aus dieser
Werkzeugklasse ohne R14 ist wertlos, und das ist kein Nebensatz: drei von vier Fassungen
waren falsch.**

#### 4. Die Zahl ist eine UNTERE SCHRANKE — mit vier benannten Gründen.

Nicht wegen R16 (0 Abbrüche), sondern aus der Bauart des Werkzeugs:

1. **Die Reihe konvergiert nicht sichtbar von oben.** Jede Verschärfung nach Fassung 2 hat
   **echte** Rümpfe hinzugefügt, keine entfernt (19 → 26). Es gibt keinen Grund
   anzunehmen, dass eine fünfte Fassung nichts mehr fände.
2. **`unsafe`/`asm!`-Blöcke werden nicht gemessen.** Der Bereiniger ersetzt Stringliterale
   durch Leerzeichen; die 168 `asm!`-Fundstellen sind für dieses Werkzeug leer.
3. **Chirurgie hinter einem Aufruf zählt beim Helfer, nicht beim Aufrufer.** Das ist die
   richtige Einheit, heisst aber: `revoke` bleibt sauber, obwohl es `delete_leaf` ruft, das
   `unlink` ruft, das umhängt. Wer den 5 : 1-Aufschlag auch den Aufrufern zurechnet, kommt
   höher.
4. **B3 fragt nur nach dem Schleifenvorrat.** Ein Rumpf kann traversierungsförmig sein und
   trotzdem 5 : 1 kosten — wegen `effects`, `locks`, Linearität oder der
   Schachtelungsgrenze zwei (`arbitrary_mutations_never_panic`, `manifest.rs`:867, schachtelt
   drei tief und steht als **T** in der Zählung). **Der Aufschlag aus B3 ist nicht der
   Abstand des Entwurfs zum Boden, sondern ein Summand darin.**

#### 5. Eine Annahme, die zugunsten der These wirkt und die hier steht, damit sie nicht untergeht.

Die Zählung liest jede Rust-Slice-/Feld-Iteration als `elems of` bzw. `slots of`. In
Gabbro setzt das voraus, dass der Ort eine **deklarierte** Sammlung mit `count N` ist.
Diese Pflicht ist nicht neu und nicht hier gebucht — sie hängt an der Klasse *Index*, die
die Neuerhebung vom 2026-08-15 als **getragen** verbucht hat (`index into T` erbt die
Schranke aus `count N`, A3/`M103`). **Fällt jene Buchung, fällt diese Zahl mit ihr** — und
zwar nicht um ein paar Zeilen, sondern um die 449 Rümpfe mit Schleife, die hier als
traversierbar zählen.

##### **Die Rückrechnung, damit die spätere Neubuchung ein EINSETZEN wird und keine Neumessung**

Ein Vorbehalt, der eine Zahl an eine **offene Entscheidung** koppelt, muss die betroffene
Teilmenge beziffern — sonst ist er eine Warnung ohne Preisschild. **Das Werkzeug weist sie
seit dieser Buchung mit aus** (`./zaehle-b3.py … ` → Abschnitt *RUECKRECHNUNG*):

| | Rümpfe | Zeilen | Anteil | Aufschlag | Tor (Latte 5 %) |
|---|---:|---:|---:|---:|---|
| **heute** — Klasse *Index* getragen | 22 | 584 | **0,96 %** | +0,05 | **bestanden** |
| **daran hängend** (jeder Rumpf mit `for`) | +268 | +11 974 | | | |
| **fiele die Index-Buchung** | **290** | **12 558** | **20,67 %** | **+1,03** | **GEFALLEN** |

**Die Gegenrechnung ist exakt und nicht geschätzt:** die Vollzählung aus R14(c) hat ergeben,
dass **alle** 347 verschiedenen `for … in`-Ausdrücke eine Domäne treffen und **alle
getroffenen Domänen `elems of`/`slots of`** sind — die Kettendomänen (`descendants of`,
`queue`) laufen in `while`, nicht in `for`. *Die betroffene Menge ist deshalb genau: jeder
Rumpf mit mindestens einem `for`.*

> **Faktor 21. Das Tor kippt, und es kippt nicht knapp.**
>
> **Damit misst B3 nicht in erster Linie den Schleifenvorrat, sondern die Index-Buchung.**
> Die 0,96 % sagen: *„wenn `index into T` seine Schranke aus `count N` erbt, trägt der
> Vorrat den Kernel."* Sie sagen **nicht**, dass der Vorrat ihn unbedingt trägt. **Der
> tragende Posten dieser Messung ist eine Buchung vom 2026-08-15, nicht eine Schleifenform.**
>
> *Und die Richtung des Restrisikos ist damit benannt: **das einzige, was diese Messung
> umwerfen kann, ist keine Nachzählung an ihr selbst, sondern eine Umbuchung woanders.***

#### 6. Was auffällt und was diese Messung NICHT belegen kann.

Vier der grössten N-Rümpfe sind **Prüfer**: `audit_cdt` (100 Z) sucht Zyklen im CDT,
`pruefe_bindung` (31 Z) sucht Zyklen in der Handler-Kette, `is_below`/`scope_covers`
(36 Z) prüfen Topologiezugehörigkeit — zusammen **167 der 584 Zeilen, 29 %**. Es liegt
nahe zu sagen, dass diese Rümpfe in Gabbro gar nicht existierten, weil die Invariante im
Typ steht statt in einem Auditor. **Das ist eine Vermutung, und diese Messung stützt sie
nicht.** Sie zählt Rümpfe im Bestand, nicht Rümpfe in einem Gegenentwurf. Notiert, nicht
verrechnet.

---

### Die Zahl für die K/A/W-Gewichtsformel

```
p_B3        = 0,0096   (584 nicht-leere Zeilen von 60 756; aufgerundet 0,010)
Aufschlag   = p_B3 · 5,0  =  +0,048   ->  gerundet  +0,05
```

**In die Formel einzusetzen: `p_B3 = 0,010`, Aufschlag `+0,05`.**

**Es ist eine UNTERE SCHRANKE** — aus den vier Gründen unter Punkt 4, nicht wegen eines
Abbruchs. Sie ist als `≥ +0,05` zu führen und **nicht** als Schätzung.

**Und der nüchternste Befund zum Schluss:** der Aufschlag liegt **unter der Auflösung der
Kennzahl**. Selbst die falsche Fassung 2 mit 4,36 % hätte nur +0,22 ergeben. **B3 ist
damit als Kostenposten erledigt — und als Fundstellenliste für drei fehlende Domänen
(`ancestors of`, Union-Find, Kette-über-Kantenfunktion) offen.** Der zweite Teil ist der
wertvollere.

### Prüfpfad

```
./zaehle-b3.py ../caprock-messbasis                 # 26 Ruempfe, 621 Z, 0,953 % / 0,961 %
./zaehle-b3.py ../caprock-messbasis --json=b3.json  # Marken + Belege je Rumpf
cd ../caprock-messbasis
grep -rniE 'fastpath|fast_path' --include=*.rs kernel crates              # 12
grep -rnE '\.(next|prev|first_child|next_sibling|prev_sibling|head|tail|link|sibling|parent|qnext|qprev)\s*=[^=]' \
     --include=*.rs kernel crates | wc -l                                 # 45
find kernel crates -name '*.rs' -exec cat {} + | grep -c '[^[:space:]]'   # 65 168
git status --porcelain | wc -l                                            # 0 — nur gelesen
```

Werkzeug: [`zaehle-b3.py`](../zaehle-b3.py), Marken und Ausnahmen im Kopfkommentar und
in den Regexen `KETTE`/`IDXKETTE`/`KANTENKETTE`/`CHIR`/`DOM_LINK_ABSTIEG`.

---

# SWEEP — die anderen Verbindungs-Invarianten, 2026-08-16

**Was hier NICHT wiederholt wird:** der Papierdurchgang am CapSpace/CDT-Paar. Der ist
gefahren (K1–K3 plus vier strukturelle, die Gruppe existiert als `CapSpace`-Struktur mit
genau drei `refcount`-Schreibstellen, Sperrabdruck eine `CAPS`-RwSperre), und E1–E3 im
`TODO.md` zitieren ihn. **Offen war nicht der Durchgang, sondern der Quantor des
Prüfsatzes** — *„**jede** im Baum vorkommende Verbindungs-Invariante hat eine Gruppe, deren
`ops` sie schliessen"* —, und dafür fehlte der Durchlauf nach den **anderen**.

**Und B3 hatte den zweiten Prüffall schon geliefert**, ohne dass er als solcher gebucht war:
die Spendenkanten `sc_donor`/`sc_donee`, der gemessen teure Teil von `switch_to`, sind
wörtlich eine Verbindungs-Invariante — Reziprozität über **zwei TCBs**, dieselbe Form wie die
Mdb-Geschwister.

## Die vier gefundenen, je mit Träger und Sperrabdruck

| | Verbindungs-Invariante | Träger | Sperrabdruck der Gruppen-`ops` |
|---|---|---|---|
| **V1** | `refcount_matches` — Zähler in A gegen Verweise in B | **eine** Struktur (`CapSpace`) | **eine** Sperre: `CAPS`, zweistufig |
| **V2** | **Reziprozität der Spendenkanten** — `tcbs[t].sc_donor == Some(a)` ⟺ `tcbs[a].sc_donee == Some(t)` | **eine** Struktur (`Scheduler.tcbs`) | **eine** Sperre: `SCHEDS[core]` |
| **V3** | Warteschlangenmarke gegen Bereitliste — `tcbs[t].queued` gegen die tatsächliche Verkettung | **eine** Struktur (`Scheduler`) | **eine** Sperre: `SCHEDS[core]` |
| **V4** | **Endpoint-Warteschlange gegen Thread-Zustand** — `t ∈ ep.receivers` ⟺ `IPC ∈ tcbs[t].reasons` | **ZWEI Strukturen, zwei Kisten** (`caprock-ipc::Endpoint` / `caprock-sched::Scheduler`) | **ZWEI Sperren, zwei Klassen, deklarierte Ordnung `EPS[i] < SCHEDS[core]`** |

**Fundstellen (W7):** V2 — `crates/caprock-sched/src/lib.rs`:958–959 (setzen), 1704–1705,
1937–1938, 1947–1948 (lösen), 1537/1596 (lesen). V3 — ebd. 1881, 1912, 1823. V4 —
`crates/caprock-ipc/src/lib.rs`:513, 625, 652, 675, 692 gegen
`crates/caprock-sched/src/lib.rs`:930, 935, 1004, 1008; Ordnung in
`kernel/src/system.rs`:724 und :881.

## **V4 ist der erste Abdruck, der nicht eine einzelne Sperre ist — und damit der erste echte Test für die `locks`-Zeile der Gruppengrammatik**

> Eine Gruppen-`ops` über V4 müsste **`EPS[i]` und `SCHEDS[core]` halten**, in dieser
> Reihenfolge, über zwei Kisten hinweg. **Das beantwortet die `locks ordered`-Frage
> empirisch: es sind zwei Sperren mit Ordnung, nicht eine gemeinsame.**

**Und der Kernel sagt es selbst, in derselben Zeile, in der er sich absichert:** der
Fault-Hook in `crates/caprock-microkit/src/lib.rs`:1303–1305 steht dort, wo er steht, **weil
er sonst `EPS` unter `SCHEDS` nähme und die Ordnung umdrehte.** *Eine Gruppe, deren `ops` die
Ordnung deklarieren, hätte diesen Kommentar überflüssig gemacht — er ist eine von Hand
getragene Verbindungs-Invariante zwischen zwei Sperren.*

## Was der Sweep NICHT gefunden hat, und das ist ein eigener Befund

**Keine Doppelnahme derselben Sperrklasse.** `kernel/src/system.rs`:15 sagt es ausdrücklich:
*„kein Pfad nimmt zwei verschiedene `SCHEDS[*]` gleichzeitig"* — die Migration läuft über eine
Übergabe, nicht über zwei gehaltene Instanzen.

> **Damit fällt der erwartete Prüffall für `locks ordered` aus, und der gefundene ist ein
> anderer:** nicht *„zwei Sperren derselben Klasse"*, sondern **zwei Klassen mit Ordnung über
> zwei Kisten.** *Die Grammatikzeile muss den zweiten Fall tragen; den ersten gibt es im Baum
> nicht.*

## W12 — dies ist eine gefüllte Karte, kein Beleg für eine vollständige

**Der Quantor des Prüfsatzes ist damit NICHT bewiesen.** Vier gefunden heisst vier gefunden.
Die Suchwege waren: reziproke Feldschreibungen (`sc_donor`/`sc_donee`), Marke-gegen-Struktur
(`queued`), Warteschlange-gegen-Zustand (`receivers`/`reasons`), zählerartige Grössen
ausserhalb der Caps. **Was sie systematisch verfehlen:** Invarianten, deren beide Hälften
**denselben Namen** nicht teilen und **nicht** über ein Indexfeld verbunden sind — etwa eine
Summenbedingung über zwei Tabellen. *Wer den Prüfsatz schliessen will, braucht einen
mechanischen Durchlauf, keinen Suchweg; dieser hier ist eine Kandidatenliste mit
Fundstellen.*

---

# Lesart A gebaut — und der vorhergesagte Preis ist NICHT eingetreten

**Die Entscheidung** (`TODO.md`, Schlitz `M-effects-lesen`): das Lesen wird genauso
vollständig deklariert wie das Schreiben. **Der vorregistrierte Preis war Faktor drei** —
*„A lässt 10 von 32 Funktionen fallen, C drei"*.

## Gemessen, nachdem der Pass gebaut war

| | |
|---|---:|
| Fragmentfunktionen, die an `E010` fallen | **0 von 32** |
| meine eigenen Beispiele, die fielen | **2 Dateien, 5 Stellen** |
| Fehler in `E010` selbst, die der erste Lauf aufdeckte | **4** |

> **Der vorhergesagte Preis war eine Schätzung, und sie war zu hoch.** `FRAGMENTE.md`
> deklariert seine Lesungen bereits — die zehn erwarteten Ausfälle gibt es nicht. **Was
> gefallen ist, waren meine eigenen Beispiele**, und das ist keine Eigenschaft der Lesart,
> sondern meiner Sorgfalt beim Schreiben.

## Was der erste Lauf an `E010` selbst gefunden hat — vier Dinge, zwei davon fremd

1. **Der Binder eines `match`-Zweiges galt als Weltzustand.** `Some(p) => …` meldete `p`.
   **Und das war ein Fehler der SCHREIBhälfte**: `lokale()` sammelte Binder nicht, also
   hätte `E005` für ein `Some(p) => { p.feld = … }` dasselbe getan. *Die Lesehälfte hat einen
   Fehler gefunden, der seit dem 2026-08-14 in `E005` lag.*
2. **Der Binder von `update(v)`** — der alte Wert eines `exchange` — ebenso.
3. **Eine Konstante ist kein Weltzustand.** `v1_erhoehen liest GRENZE, erklaert aber pure`
   hatte im Wortlaut recht und in der Sache unrecht. Ohne diese Ausnahme wäre `pure`
   praktisch unerreichbar.
4. **Eine Variante ist kein Ort.** `IpcResult::Ok` und `Fehler::Buchfuehrung` wurden als
   ungenannte Lesungen gemeldet.

## Die Einschränkung, die daraus folgt — und was sie kostet

**`E010` spricht nur über bekannten Weltzustand**: `static`, `atomic`, `table`, `device`,
`state`. *In einer vollständigen Übersetzungseinheit geht dabei nichts verloren* — ein
unbekannter Name fällt bereits im Namenspass. **Im Ausschnitt kostet sie die ganze Bissigkeit**,
und das ist der ehrliche Satz dazu:

> **Auf dem Fragmentkorpus hat `E010` heute NULL Biss** — nicht weil dort alles deklariert
> ist, sondern weil Ausschnitte ihren Zustand nicht deklarieren. **Der Beleg, dass die Regel
> greift, kommt deshalb nicht vom Korpus**, sondern von drei anderen Stellen: zwei eigene
> Beispiele fielen (`09`, `14`), `beispiele/gift/62-lesen-ohne-reads.gab` fällt mit genau
> einer Absage, und **zwei Mutationen** in `mutiere-pruefer.py` beschädigen die Regel — eine
> schaltet sie ab, die zweite *lockert* sie (jede `reads`-Zeile deckt jede Stelle).

*Die zweite Mutation ist die wichtigere, und das Gift ist eigens dafür gebaut: `pruefe_grenze`
deklariert `reads Protokoll.slots` wahrheitsgemäss und liest `Objekte.slots` daneben. **Eine
Wirkungsliste, die eine Lesestelle nennt, sieht vollständig aus.***

---

# Die Traegergruppe gebaut — Pass 10, und die Passliste ist gewachsen

**R7 zuerst, und diesmal ohne Abkürzung:** der Schablonen-Eintrag stand vor der Grammatik.
`S16 gruppe.ops` gab es schon (aus «B13»); der Sweep verlangte einen **zweiten**, weil er
einen Fall fand, den der erste nicht deckt:

| | Schablone | deckt |
|---|---|---|
| S16 | `gruppe.ops` | Gruppen über Trägern unter **einer** Sperre (V1–V3) |
| **S17** | **`gruppe.sperrabdruck`** | Gruppen über Trägern mit **verschiedenen** Sperren (V4) |

> **Eine Schablone, die beide Fälle als einen führt, versteckt den Unterschied, an dem sie
> scheitern kann:** unter einer Sperre ist die Erhaltung ein sequenzielles Argument, unter
> zweien hängt sie an der **Ordnung** und daran, dass zwischen den zwei Nahmen kein fremder
> Schreiber dazwischenkommt.

## Die Grammatikzeile — und was sie NICHT deklariert

```gabbro
group Zustellung over { Endpunkte, Faeden };
```

**Die Sperrordnung steht nicht an der Gruppe.** Jeder Träger liegt unter einer
`lock … rank N`, und die Ränge geben die Ordnung. *Eine zweite Deklaration wäre eine zweite
Wahrheit über dieselbe Sache* — dieselbe Fehlerklasse wie zwei Etikettensysteme mit denselben
Namen.

## Fünf Absagen, und `U003` ist die, die V4 gebraucht hätte

| | |
|---|---|
| `U001` | die Gruppe nennt etwas, das **deklariert und kein Träger** ist |
| `U002` | ein Träger der Gruppe steht **unter keiner Sperre** |
| `U003` | **eine Funktion schreibt zwei Träger der Gruppe und hält nicht alle ihre Sperren** |
| `U004` | eine Gruppe mit **einem** Mitglied — das ist eine Tabelle |
| `U005` | zwei Sperren der Gruppe tragen **denselben Rang** — es gibt keine Ordnung |

> **`U003` macht einen Kommentar überflüssig.** `caprock-microkit/src/lib.rs`:1303 erklärt,
> warum eine Funktion dort steht, wo sie steht — nähme sie `EPS` unter `SCHEDS`, drehte sie
> die Ordnung um. **Das ist eine von Hand getragene Verbindungs-Invariante zwischen zwei
> Sperren**, und sie ist der gemessene Bedarf, nicht ein Entwurfswunsch.

## Zwei Wächter haben unterwegs zugeschlagen, und beide zu Recht

1. **Die Wortschatz-Ratsche** hielt `group` an, bevor es im Lexer sein durfte — das Wort
   musste erst in `SYNTAX.md` stehen.
2. **Der Passlisten-Test** hielt den zehnten Pass an: `assert_eq!(liste.len(), 9, "die
   Reihenfolge steht in SPRACHE.md Teil III §6")`.

> **Der zweite ist der wichtigere, und er hat genau das getan, wofür er gebaut ist.**
> *„Die Spezifikation ist die Passliste"* heisst umgekehrt: **ein neuer Pass ist eine Änderung
> der Spezifikation.** Ohne den Test wäre der zehnte Pass ein Modul mehr gewesen, und
> `SPRACHE.md` hätte weiter neun behauptet. **Er ist jetzt in `SPRACHE.md` Teil III §6
> gebucht, mit seinem Grund.**

## Und die Deckung, so klein wie sie ist

**Gebaut ist der Sperrabdruck, nicht die Invariante.** Die Gruppe nennt heute ihre Träger,
nicht ihre Verbindungsaussage. `U003` sagt, dass nicht alles gehalten wird, was angefasst
wird — **nicht, dass die Invariante hält.** *Das steht hier, damit niemand die Deckung grösser
liest, als sie ist.*

**Belege:** `beispiele/17-gruppe-ueber-zwei-sperren.gab` (die richtige Fassung),
`beispiele/gift/63-gruppe-halb-gesperrt.gab` (fällt mit genau `U003`), und **zwei Mutationen**
— eine schaltet `U003` ab, die zweite *lockert* sie: eine gehaltene Sperre deckt die ganze
Gruppe. **58 von 58 gefangen.**

---

# `U006` — die dritte S17-Pflicht, und eine überlebende Mutation

**Von den drei Pflichten, die S17 an eine Gruppenoperation stellt, stehen jetzt zwei:**

| | Pflicht | Stand |
|---|---|---|
| (a) | Sperren in Rangordnung | **`U003`/`U005`** |
| (b) | Invariante am Anfang **und** am Ende | **offen** — braucht die Klausel |
| (c) | **kein Zwischenaustritt** | **`U006`** |

**(c) war ohne jede Erzeugung prüfbar**, und das war nicht abzusehen: die Pflicht klingt nach
einer Aussage über einen erzeugten Zug, ist aber eine über den **Kontrollfluss zwischen dem
ersten und dem letzten Schreibzugriff**. *Wer Träger A geschrieben hat und den Rumpf
verlässt, bevor er B geschrieben hat, hinterlässt die Gruppe im Zwischenzustand — und der
Fehlerpfad ist genau die Stelle, an der das passiert, weil dort niemand hinsieht.*

## Die überlebende Mutation ist der Ertrag, nicht die Panne

Nach Gift 64 (`return` zwischen den Schreibzugriffen) stand die Probe bei **59 von 60**:

```
!! UEBERLEBT  gruppe-austritt-nur-return   U006 -- `let … else` ist kein Austritt
```

**63 Giftproben merkten nicht, dass der Prüfer eine seiner drei Türen verloren hatte.** Gift
64 hätte es nie gefangen — es nimmt `return`.

> **Eine Regel mit drei Wegen braucht drei Proben, nicht eine.**

**Und der zweite Anlauf reichte auch nicht.** Gift 65 nahm zuerst
`let g = … else (fehler) { return false; }` — der Sonst-Zweig enthielt ein `return`, also fing
die **`return`-Regel** den Fall, und die Mutation überlebte weiter. Erst ein Sonst-Zweig, der
**divergiert** statt zurückzukehren (`aufgeben()`), isoliert die `let … else`-Tür.

> **Zweimal am selben Tag dieselbe Bauart:** eine Probe, die den beabsichtigten Fall auslöst,
> aber über eine **andere** Regel. Bei `E010` war es die Schreibhälfte, hier die
> `return`-Hälfte. *Eine Giftprobe belegt nur dann eine Regel, wenn sie ohne diese Regel
> durchginge — und das sagt keine Absage, das sagt nur die Mutation.*

**Stand: 60 von 60.** `beispiele/gift/64-gruppe-zwischenaustritt.gab` (`return`),
`beispiele/gift/65-gruppe-austritt-durch-else.gab` (`let … else`, divergenter Sonst-Zweig),
und die Gegenprobe: dieselbe Funktion mit der Prüfung **vor** dem ersten Schreibzugriff geht
sauber durch.

## Die Grobheit hat eine Richtung (W9)

Die Reihenfolge ist die **Quellreihenfolge** des rekursiven Abstiegs, nicht der Kontrollfluss.
Ein Austritt in einem Zweig, der den zweiten Schreibzugriff gar nicht erreichen kann, wird
trotzdem gemeldet. **Zu viel zu melden ist hier die sichere Seite** — die Absage sagt *„hier
verlässt ein Weg den Zug"*, und wer weiss, dass dieser Weg nicht existiert, hat den Beweis
dafür zu schreiben, nicht der Pass.

---

# `U007` — die Verbindungsaussage, und wo der Prüfer aufhört

**Die dritte S17-Pflicht ist jetzt als FORM gebaut, nicht als Beweis.** Der Unterschied ist
die ganze Aussage dieses Abschnitts:

| | Frage | wer beantwortet sie |
|---|---|---|
| **Form** | *Nennt diese Invariante mehr als einen Träger der Gruppe?* | **`U007`, mechanisch** |
| **Erhaltung** | *Hält sie unter jeder Operation?* | **S16/S17 — Beweisersache** |

> **`U007` ist dieselbe Absage wie `U004`, eine Ebene tiefer:** dort ist die **Deklaration**
> einelementig, hier die **Aussage**. Und der Grund ist derselbe: *ohne diese Prüfung wäre
> `group` eine bequemere Schreibweise für `table … invariant` — und ein Konstrukt, das nur
> bequemer ist, hat nach W3 keinen Beleg.*

## Die Zeile, wie sie jetzt aussieht

```gabbro
group Zustellung over { Endpunkte, Faeden } {
    invariant wartende_haben_grund cost O(n) runs offline :
        forall e in slots of Endpunkte :
            Faeden.slots[Endpunkte.slots[e].wartet].gruende > 0;
}
```

**Der Rumpf ist freigestellt.** Ohne ihn greifen Sperrabdruck (`U003`/`U005`) und Zug
(`U006`) — die Gruppe ist also schon vor ihrer Invariante nützlich. *Das war nicht geplant und
ist der zweite Befund dieses Baus: die zwei mechanischen Pflichten aus S17 hängen gar nicht
an der Aussage, sondern am Kontrollfluss und an den Rängen.*

## Stand der Trägergruppe

| | | |
|---|---|---|
| `U001`–`U002` | Träger existiert, Träger ist gesperrt | |
| `U003`, `U005` | **(a)** Sperren, Rangordnung | S17 |
| `U006` | **(c)** kein Zwischenaustritt | S17 |
| `U007` | **(b)** die Aussage verbindet | S17, **Form** |
| — | **(b)** die Aussage **hält** | **offen, Beweisersache** |

**61 von 61 Mutationen.** Belege: `beispiele/17-gruppe-ueber-zwei-sperren.gab` (Gruppe mit
Invariante, sauber), Gift 63 (`U003`), 64 (`U006` via `return`), 65 (`U006` via `let … else`
mit divergentem Sonst-Zweig), 66 (`U007`).

---

# NACHBUCHUNG: **Rahmen** ist getragen — `N_neu = 3`

**Die Klasse hing an einer Hälfte und an einem Wort.** Die Neuerhebung buchte sie als hängend
mit dem Grund *„`effects` prüft Schreiben, nicht Lesen"*, und das Urteil vom 2026-08-15 sagte:
*„der Rest ist keine Bauarbeit mehr, sondern ein Urteil"*.

**Beides ist am 2026-08-16 gefallen:** die Richtung steht (**A**), und sie ist gebaut
(`E010`). Damit hält `effects` alle vier Teile — Schreiben (`E005`), `locks` (`E006`/`E007`),
**Lesen** (`E010`) und die **Aufrufwirkungen** (`E008` über dem Aufrufgraphen).

## Die Grenze wird mitgebucht, sonst ist die Buchung geschönt

> **`E010` spricht nur über deklariertem Weltzustand** (`static`, `atomic`, `table`, `device`,
> `state`). Auf dem Fragmentkorpus hat die Regel deshalb **null Biss** — Ausschnitte
> deklarieren ihren Zustand nicht.

**In einer vollständigen Übersetzungseinheit geht dabei nichts verloren**, weil ein
unbekannter Name bereits im Namenspass fällt. *Die Klasse gilt damit als getragen für
Übersetzungseinheiten und nicht für Ausschnitte — und weil Gabbro Programme übersetzt und
keine Ausschnitte, ist das die richtige Grundgesamtheit.*

## Stand der elf Klassen

| | |
|---|---|
| **getragen (8)** | Index · Überlauf · Alias · Sperre · Terminierung · Blattheit · Publikation · **Rahmen** |
| **hängend (3)** | **Rennen** · **Phase** · **Verfeinerung** |

**Und die drei hängen nicht mehr an fehlenden Pässen, sondern jede an etwas anderem** — das
ist der eigentliche Fortschritt gegenüber `N_neu = 5`:

* **Rennen** hängt an der **Axiomschicht**, nicht an einem Pass: der Paarungspass steht
  (`V001`–`V004`), aber dass `release`/`acquire` die Sichtbarkeit *herstellen*, die die
  Paarung behauptet, ist eine Aussage über das Speichermodell.
* **Phase** hängt an «B37» — `BootPhase` trägt *genau einmal*, nicht *in dieser Ordnung*.
* **Verfeinerung** hängt an der **Emission**, die es nicht gibt.

> *Drei Klassen, drei verschiedene Gründe, kein gemeinsamer Bau.* Wer `N_neu` senken will,
> hat ab hier drei Projekte vor sich und nicht mehr eine Baustelle.

---

# BERICHTIGUNG: was „0 von 571" sagt — und was nicht

**Die Zahl bleibt, der Satz daneben ändert sich.** Bisher stand sie als *„99,04 % der
Kernelzeilen sind als Traversierung schreibbar"*. Das ist die Überschreibungsform als
Statistik, und die B3-Kette hat den richtigen Rahmen selbst geliefert.

> **`for`-Köpfe treffen Domänen — die KETTEN laufen in `while`.**

Union-Find, Kantenfunktionen, die drei «B41»-Lücken: sie liegen **konstruktionsbedingt
ausserhalb der Grundgesamtheit dieser Zählung.** Die 571 sind die `for`-Schleifen; die harte
Minderheit hat gar keine `for`-Form, also konnte sie in dieser Zahl nie auftauchen.

**Die zwei Sätze gehören nebeneinander, und beide sind stark:**

1. **Der Domänenvorrat ist für die zählschleifenförmige Mehrheit VOLLSTÄNDIG** — 0 von 571,
   und das ging gegen die Erwartung.
2. **Über die harte Minderheit sagt die Zahl NICHTS**, weil deren Schleifenform nicht
   mitgezählt wurde.

*Der erste allein wäre eine Statistik, die ihre eigene Grundgesamtheit verschweigt — dieselbe
Bauart wie ein Filter, der die Grundgesamtheit schrumpft und als Erfolg erscheint (W11).*

---

# VORAB — die 89 Verschlüsse nach Verwendungsart, 2026-08-16

**R1 diesmal eingehalten: dieser Abschnitt ist committet, BEVOR gezählt wurde.** Bei B3 war
er es nicht, und die Buchung dort sagt das ausdrücklich. *Eine Regel, die einmal verfehlt
wurde, wird beim nächsten Mal sichtbar eingehalten oder sie ist keine.*

## Die Frage

`dyn FnMut`/`Fn` — **89 Fundstellen**, und Gabbro hat **keine Form** dafür. Der Posten galt
als der schwerste der fünf Nötigen, weil bei ihm die Frage *ob* lautet statt *wie*.

> **Die These, die geprüft wird: die Frage ist entscheidbarer, als sie aussieht, weil die 89
> Stellen nach Verwendungsart zerfallen — und jede Klasse hat schon eine Antwort.**

## Die drei vorhergesagten Klassen, mit ihrer Antwort

| | Klasse | erwartete Antwort |
|---|---|---|
| **V-a** | **Rückruf mit EINER Implementierung** | wird ein gewöhnlicher Aufruf — **die Gabbro-Antwort existiert schon: A2** |
| **V-b** | **gespeicherter Handler in einer Tabelle** | Zeiger-plus-Kontext, **entwerfbar als deklarierte Verteilertabelle** — dieselbe Medizin wie `entry … dispatch`, nur benutzerseitig |
| **V-c** | **echter Kombinatorfall** (Iterator-Adapter, `map`/`filter`-Ketten) | **Verbot** — sie wären in einer Sprache ohne Generizität ohnehin nicht tippbar |

**Fällt die Zählung so aus, ist „ob" ein dreifaches „wie / wie / nein", und der Posten
verliert seinen Sonderstatus.**

## Das zweiseitige Tor, vor dem Lauf festgeschrieben

| | |
|---|---|
| **bestanden** | **jede der 89 Stellen fällt in V-a, V-b oder V-c**, und keine Klasse ist die Mehrheit *durch* die Restkategorie |
| **gefallen** | **mehr als 10 %** der Stellen passen in keine der drei → es gibt eine vierte Verwendungsart, und *die* ist der Entwurfsposten |

**Ungültig** (getrennt von ungünstig): die Fundstellenzahl weicht um mehr als 10 % von 89 ab
→ dann misst die Zählung etwas anderes als die Quelle der 89, und die Klassen sind über einer
fremden Grundgesamtheit gebildet.

## Die Kippregel

1. Ist unklar, ob ein Rückruf **eine** Implementierung hat, zählt er als **V-b** (teurer).
2. Ist unklar, ob eine Kette ein Kombinator ist, zählt sie als **V-b**, nicht als V-c —
   *Verbot ist die billigste Antwort und darf deshalb nie die Zweifelsantwort sein.*
3. Was in keine Klasse fällt, wird **einzeln aufgeführt**, nicht in eine gerundet.

# ERGEBNIS — die Verschlüsse, 2026-08-16: **das Tor ist VOID, und der Grund ist die Zahl selbst**

## Zuerst die Ungültigkeit, weil sie vor dem Ergebnis kommt

**Die vorregistrierte Ungültigkeitsbedingung ist ausgelöst.** Sie lautete: *„die
Fundstellenzahl weicht um mehr als 10 % von 89 ab → dann misst die Zählung etwas anderes als
die Quelle der 89."*

```
grep -rnoE "(dyn|impl|&|Box<)\s*(dyn\s*)?(FnMut|FnOnce|Fn)\s*\(" kernel crates   ->  64
grep -rnE  "\bdyn\b"                                              kernel crates   ->  67
```

**Die 67 `dyn`-Stellen reproduzieren exakt** — es ist derselbe Baum. **Die 89 nicht: der
reproduzierbare Wert ist 64, eine Abweichung von −28 %.** Und kein plausibler Suchweg trifft
89: Verschlussliterale `|…|` ergeben **441**, `move`-Verschlüsse **16**, `Box<dyn Fn*>` **0**.

> **Die 89 ist eine Zahl ohne Suchweg** — genau die Klasse, gegen die W7 steht, und sie hat
> den W7-Kehraus vom 2026-08-15 überlebt, weil sie in einer *Tabelle* stand und nicht in
> einem Satz. **Wer nur Sätze prüft, findet sie nicht.**

**Das Tor ist damit void. Ein neues wird jetzt NICHT gesetzt** — das wäre R2. Was folgt, ist
eine **beschreibende Zählung ohne Tor**, und sie ist als solche gekennzeichnet.

## Die beschreibende Zählung über der reproduzierbaren Grundgesamtheit (64)

| Klasse | vorhergesagt | **gemessen** |
|---|---|---|
| **V-a** Rückruf, als Parameter übergeben | Mehrheit | **praktisch alle** — 39 direkt in Parameterlisten, der Rest in mehrzeiligen Signaturen |
| **V-b** gespeicherter Handler in einer Tabelle | eigene Klasse | **NULL.** `Box<dyn Fn*>` = 0, Strukturfelder mit Fn-Typ = 0 (alle 20 Treffer sind mehrzeilige *Parameter*) |
| **V-c** Kombinator (Iterator-Adapter) | eigene Klasse | **nicht in dieser Grundgesamtheit** — sie lebt in den 441 Verschlussliteralen, davon **270** in `.map`/`.filter`/… |

## **Der eigentliche Befund: es sind ZWEI Populationen, und „89" benennt keine davon**

| | Population | Zahl |
|---|---|---:|
| **P1** | Nennungen der `Fn`-Traits als **Typ** | **64** |
| **P2** | **Verschlussliterale** `\|…\|` | **441**, davon 270 in Iterator-Adaptern |

**Die Vorhersage mischt sie:** V-a und V-b sind Aussagen über P1, V-c ist eine über P2. *Eine
Klassifikation über einer Grundgesamtheit, die zwei Dinge zugleich meint, kann nicht bestehen
oder fallen — sie kann nur so aussehen.*

## Was die Vorhersage trotzdem richtig hatte, und es ist die teure Hälfte

**V-b ist LEER, und das ist die günstigste Widerlegung, die möglich war.** Die Klasse war die
einzige, die ein **neues Konstrukt** gefordert hätte (deklarierte Verteilertabelle,
benutzerseitiges `entry … dispatch`). *Sie kommt im Baum nicht vor.*

**Und die dominante Verwendung ist EINE:**

```
&mut dyn FnMut() -> Option<u64>      25 Fundstellen   (mmu, smmu, vtd)
```

**Der Seitentabellen-Allokator, denselben Rückruf 25-mal durchgereicht.** Das ist kein
Verschluss im Sinne der Frage — es ist **ein Rückruf mit einer Implementierung**, also
wörtlich A2, und Gabbros Antwort steht seit dem 2026-08-14 fest.

**Die zweitgrösste ist ein alter Bekannter:**

```
impl Fn(u16) -> Option<u16>           3 Fundstellen   (sched/redirect.rs)
```

**Das ist die Kantenfunktion aus «B41».** Der Verschluss-Posten und die dritte
Domänenlücke sind **derselbe Gegenstand**, und keine der beiden Untersuchungen hat das
bemerkt, bis beide Zahlen nebeneinander lagen.

## Urteil

> **Der Verschluss-Posten verliert seinen Sonderstatus — aber nicht, weil die Vorhersage
> aufging, sondern weil die Grundgesamtheit falsch war.**

* **P1 (64)** zerfällt in *„Rückruf mit einer Implementierung"* (A2, entschieden) und
  *„Kantenfunktion"* (die Linienfrage aus «B41»). **Kein neues Konstrukt, eine offene Linie.**
* **P2 (441)** ist eine andere Frage und heisst richtig *„braucht Gabbro Iterator-Adapter?"* —
  und sie hängt an der **Generizität**, nicht an Verschlüssen.

**Was als „der schwerste der fünf Nötigen, weil die Frage *ob* lautet" gebucht war, ist nach
dieser Zählung zwei Fragen, von denen eine schon beantwortet ist und die andere Generizität
heisst.** *Der Posten war nicht schwer, er war unscharf.*

## Nachtrag zur Verschluss-Zählung: **die Fehlerform hat einen Vorgänger im selben Ordner**

**Eine Klassifikation über einer Doppelmenge kann nicht bestehen oder fallen — sie kann nur
so aussehen.** Die Vorhersage behandelte *„89 Verschlüsse"* als **eine** Menge, die **zwei**
war: Typnennungen (P1) gegen Literale (P2).

> **Das ist dieselbe Fehlerform wie die zwei Generatorquoten über verschiedenen Stichproben
> — nur im ENTWURF statt in der Messung.**

*Dort waren es zwei Quoten über zwei Grundgesamtheiten, die als eine gelesen wurden; hier ist
es eine Vorhersage über zwei Grundgesamtheiten, die als eine geschrieben wurde.* Die Regel,
die daraus folgt, steht schon (W11: jede Quote nennt ihr N) — **sie gilt auch für Vorhersagen,
nicht nur für Messungen.**

## Und die Konvergenz, die niemand gesucht hat

**Der schwerste „ob"-Posten und die letzte «B41»-Lücke waren derselbe Gegenstand.**

| | | |
|---|---|---|
| **25×** | `&mut dyn FnMut() -> Option<u64>` | der Allokator-Rückruf — **wörtlich A2, seit dem 2026-08-14 beantwortet** |
| **3×** | `impl Fn(u16) -> Option<u16>` | die **Kantenfunktion** — die Domänenzeile, deren Linie seit dem Schnitt steht |

**Damit ist die Fünferliste der Nötigen real eine VIERERLISTE**, und der Posten, der als
einziger *„ob"* hiess, ist auf **zwei bereits entschiedene „wie"** zerfallen.

> **Keine der beiden Untersuchungen sah es, bis die Zahlen NEBENEINANDER lagen.**

*Das ist ein leises Argument dafür, dass dieses Dokument irgendwann eine Querverweisspalte
braucht — welche Messungen teilen Fundstellen. Buchführung für später, kein Posten für jetzt.*

---

# VORAB — `table.induktion` nach Isabelle, die erste Schablone

**Vorregistriert am 2026-08-16, bevor eine Zeile Isabelle geschrieben ist.** Dieselbe
Disziplin wie bei den Verschlüssen, und aus demselben Grund: *bei B3 fehlte sie, und die
Buchung dort sagt das ausdrücklich.*

## Warum dieser Posten den Kopf des kritischen Pfads bekommt

**Nicht wegen des Aufwands — wegen einer Kurve.** Das Amortisierungsargument des ganzen
Entwurfs lautet: *eine Schablone fällt **einmal**, nicht je Programm.* Es ist der einzige
Unterschied zwischen der Schablonenliste und seL4s Beweisberg.

> **Und es gilt erst ab der ersten BEWIESENEN Schablone.** Bis dahin ist es eine Zusage über
> eine Fläche, die niemand betreten hat. **Eine bewiesene von achtzehn ist qualitativ etwas
> anderes als null von siebzehn:** das Register wechselt von *„Liste mit Länge"* zu *„Liste
> mit Fallrichtung"*.

## **Der erwartete Ausgang — und er ist NICHT „bestätigt"**

**Die Vorhersage, damit das Ergebnis nicht überlesen wird:** das Formalisieren wird die
Schablone fast sicher **nicht einfach bestätigen**. Der wahrscheinliche Ausgang ist, dass es
die **Nebenbedingungen ausspült**, die die Prosa-Fassung stillschweigend trägt. Vier stehen
namentlich als Kandidaten da, damit man nachher nicht sagen kann, man habe sie gemeint:

| | erwartete stille Annahme |
|---|---|
| **N-1** | **Endlichkeit der Domäne** — die Prosa sagt „wohlfundiert", nicht „endlich"; für `slots of` fällt es aus `count N`, für `descendants of` nicht ohne Weiteres |
| **N-2** | **Stabilität der Zeugenordnung** unter **genau den erzeugten Mutationen** — nicht unter beliebigen |
| **N-3** | **die Leere-Menge-Klausel** — sie stand schon einmal als blosse **Implikation** da, statt als eigene Pflicht (`consuming.leermenge`) |
| **N-4** | **Vollständigkeit des Schemas** — dass das erzeugte Induktionsprinzip **alle** Fälle deckt, nicht nur die vorkommenden |

## Wie das Ergebnis gebucht wird — vorab festgelegt, damit die Richtung nicht wandert

> **Jede ausgespülte Nebenbedingung ist ein GEWINN und wird als solcher gebucht** — als
> **Präzisierung des Schablonen-Eintrags**, nicht als Rückschlag.

*Genau dafür klettert man den ersten Hang: nicht um „bewiesen" ins Register zu schreiben,
sondern um zu erfahren, **was das Register bisher verschwiegen hat**.*

## Das Tor, zweiseitig — und das verdächtige Ergebnis ist das glatte

| | |
|---|---|
| **gut** | die Schablone geht durch, **und mindestens eine stille Annahme ist ausgespült** und steht danach im Eintrag |
| **auch gut** | die Schablone geht **nicht** durch — dann ist eine Zusage des Ordners widerlegt, und zwar die billigste von allen |
| **VERDÄCHTIG** | die Schablone geht **glatt** durch, **ohne eine einzige stille Annahme auszuspülen** |

> **Der dritte Ausgang ist der einzige, der eine Gegenprüfung auslöst.** Eine Prosa-Schablone,
> die beim Formalisieren nichts verliert, war entweder schon formal geschrieben — oder die
> Formalisierung hat dieselben Annahmen stillschweigend übernommen. *Bei einem Eintrag, der
> seit Tagen als „die kleinste" gilt und nie drankam, ist die zweite Erklärung die
> wahrscheinlichere.*

**Ungültig** (getrennt von ungünstig): die Isabelle-Fassung formalisiert **eine andere
Aussage** als der Schablonentext — dann misst der Gang die Übersetzung, nicht die Schablone.
Die Probe darauf ist mechanisch: **jeder Satz des Eintrags `table.induktion` muss sich einer
Zeile der Formalisierung zuordnen lassen, und umgekehrt.**
