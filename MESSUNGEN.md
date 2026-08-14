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
| **G1** | ein `ensures` ist **falsch**, nicht bloss unbewiesen: `e.caller is Some(cl) => cl == current_id(...)`. Bei offenem Rendezvous A und Aufrufer B behauptet es `A == B` — **nachgeprueft**: der zweite Aufrufer geht in `senders`, ohne `caller` anzufassen. **Und es ist im Zaehler mitgezaehlt** | `crates/caprock-ipc/src/lib.rs:652` |
| **G2** | `msg_copied` — die **einzige** funktionale Eigenschaft eines Fastpaths — steht in **keinem** `ensures`. Gezaehlt und an nichts gebunden; `transfer()` hat gar keine Nachbedingung | — |
| **G3** | `effects` vergisst `locks SCHEDS[owner_core(...)]` auf dem Cross-Core-Pfad — **vom Autor der Regel** | — |

**G3 und der Fund F12 („`effects` ist fail-open") sind dasselbe Loch von zwei Seiten:** eine
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
