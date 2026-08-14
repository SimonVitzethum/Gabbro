# P0 GEFAHREN — soweit der Ordner es zulässt

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

## Teil 1 — die 19 hängenden Pflichten gegen die Konstrukte

Dokumentiert in `LOGIK-KLEMPNEREI.md` sind sechs Klassen mit Fundstellen. Abgleich:

| Klasse (dokumentiert) | Konstrukt | Urteil |
|---|---|---|
| `forever`/`per_pass`-Ritual (8 Schleifen, Ticket-Spinlock ohne `try_lock`, Ed25519 über Manifest) | `on_exceeded`-Pflicht, `held <= K ops` an der Sperre (ohne sie in Dienstschleifen nicht nehmbar), eingabeabhängige Schranke | **fällt** — der Spinlock `caprock-sync:821` wird unschreibbar statt falsch beschrieben |
| `per_pass` in Zyklen (D10) | Einheit `ops`, definiert in FESTLEGUNG §7 | **fällt** |
| `publishes` an der Deklaration (671 Stellen; `FP_OWNER[core]` selbstbezüglich; Aussage-Nutzlast; virtio-`avail` volatil ans Gerät; Zähler ohne Schreibweise) | `publishstmt` am Store, `ghost static`-Reifizierung, `transition publishes`, `publishes nothing` | **fällt** — alle vier benannten Unterfälle haben eine Schreibweise |
| PTE = Zeiger UND Bitfeld → fehlende achte Domäne (`mmu.rs:1283`) | `embeds` + `walk` + `mappings of` | **fällt, mit einer Konstrukterweiterung** (s. Teil 4b) |
| 54 relationale Vorbedingungen | V2 | **fällt der Form nach** (s. Teil 3) |
| `break`/`continue` unerwähnt | `leave`/`next` mit Zielname, Verbotsliste ergänzt | **fällt** |

**Die übrigen fünf Klassen** („die übrigen fünf Klassen aus dem Bericht im Scratchpad",
`LOGIK-KLEMPNEREI.md`) **existieren im Repo nicht.** Damit sind schätzungsweise 6 der 19
Pflichten nicht gegen die Festlegung prüfbar — nicht, weil ein Konstrukt fehlt, sondern weil die
Messung fehlt. **Das Tor „19 → 0" ist so formuliert nicht entscheidbar, und das ist ein Befund
über das Protokoll, nicht über die Sprache.** Auftrag: die fünf Klassen mit Fundstellen ins Repo,
dann diesen Teil wiederholen.

---

## Teil 2 — Ordering-Stichprobe: 36 Stellen, sechs Schichten, kein vierter Ausgang

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

## Teil 3 — `narrow`: nur die Formprüfung war fahrbar

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

## Teil 4 — Nebenbefunde, zwei davon mit Entscheidungsbedarf

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

## Was jetzt zu tun ist, in Reihenfolge

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
