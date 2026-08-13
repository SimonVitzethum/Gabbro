# P0.4 — die Gegenprobe: ein Entwurf, ein Pruefer, und ein Loch in der MESSVORSCHRIFT

**Gefahren am 2026-08-13.** Ein Agent entwarf eine vollstaendige Grammatik (1 882 Zeilen), ein
zweiter prueft sie gegen echten Caprock-Code. Beide nur auf Papier. Die tragenden Zahlen habe ich
nachgeprueft.

---

## Der wichtigste Fund betrifft nicht die Sprache, sondern die Kennzahl

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

### Was daraus fuer das Messprotokoll folgt

- [ ] **Eine Kennzahl ohne Gueltigkeitspruefung ihrer Zusagen ist eine Untergrenze mit BENANNTER
      Fehlerrichtung** — falsche und unvollstaendige Zusagen sind kuerzer als richtige. Das gehoert
      neben jede Zahl, sonst liest sie sich wie ein Messwert.
- [ ] **Drei Regeln, ohne die nicht gemessen wird:** (1) jedes gezaehlte `ensures` wird gegen den
      echten Code gehalten; (2) eine benannte, aber an keine Nachbedingung gebundene Eigenschaft
      zaehlt **nicht** — sie ist Zierat; (3) `effects` wird gegen die tatsaechlichen Zugriffe
      geprueft, nicht gelesen.

---

## Die Zahlen

### Der Anti-Katalog-Prueftein: **3 neue Woerter, nicht zwoelf — bestanden**

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

### Das Verhaeltnis, ausgeschrieben statt behauptet

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

## Die drei Nachpruefungen

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

## Wo der Entwurf an echtem Code scheitert — vom Entwerfer selbst gemeldet

**CAS-/Warteschleifen: keine Loesung.** `move_cap` ist eine Knotenumbenennung ohne Baumkonstrukt
(**neuer B3-Kandidat, stand auf keiner Liste**). `install` braucht **Transaktionen**, sonst
existiert zwischen `alloc_object` und `alloc_slot` ein Zustand, den kein Konstrukt beschreibt.
`Finalized<'a>` braucht Lebenszeiten, die es nicht gibt. **Und die zentrale Fastpath-Eigenschaft
(„darf dieser Thread in diesen Rahmen schreiben?") ist eine AUTORITAETS-, keine Adressraumfrage —
M1–M4 sagen dazu nichts.**

**Ein Positivbefund:** virtio-`used`/`avail`-Eigentum ist phasenabhaengig und faellt aus **demselben**
Mechanismus wie die Bootphase — **zweite unabhaengige Fundstelle** fuer den linearen Geisterzeugen.
