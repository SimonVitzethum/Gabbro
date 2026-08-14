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
  [`TODO.md`](TODO.md) als offene Klempnerei-Pflicht gefuehrt;
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
| **F > 0** | **Jede dieser Stellen braucht `requires a >= b` am Gerufenen** — und damit ist die Frage aus [`TODO.md`](TODO.md) beantwortet, nicht vermutet. |

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
| `FnMut`/`Fn` | 89 | — (**Verschluesse**, s. u.) |

**Die beiden Traits, die dynamisch benutzt werden, haben je EINE Implementierung.** Das ist
keine Polymorphie, sondern eine Schichtgrenze — der Aufruf ist statisch bekannt, und in
Gabbro verschwindet das Trait-Objekt.

> **`fnptr` braucht keinen Vertrag.** Der Posten aus «B9» faellt weg, und die Verbotsliste
> waechst statt der Grammatik.

**Der Rest ist eine Frage, die der Plan nicht vorgesehen hat: 89 Verschluesse.** Gabbro hat
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
(A1), die **89 Verschluesse** ohne Form in der Sprache (A2), und `costs` an einer **rekursiven**
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
