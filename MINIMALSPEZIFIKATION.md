# Die Umkehrung der Frage — jedes „geht nicht" wird zu „was muss minimal dastehen"

**2026-08-13.** Beide Papiertests fragten *„geht das?"* und meldeten Loecher. **Die Frage war
falsch.** Gabbro ist eine sehr enge Sprache, die schwer sein darf; die richtige Frage lautet:

> **Was muss der Code MINIMAL spezifizieren, damit es geht — und laesst sich das nach C absenken?**

Beides ist Bedingung. Eine Angabe, die sich nicht absenken laesst, ist keine Antwort.

**Das gilt fuer ganz Gabbro, nicht nur fuer Schleifen.** Unten steht die vollstaendige Umwandlung
aller achtzehn „geht nicht"-Befunde aus beiden Berichten.

---

## Der Fall, an dem die Umkehrung am deutlichsten wird: Schleifen

**Gemeldet war:** *„CAS-/Warteschleifen: keine Loesung. Kein Abstiegsmass, `divergent` ist falsch."*

**Das stimmt fuer `variant` und ist die falsche Frage.** Eine Warteschleife ist nicht masslos —
sie ist durch **Bedingungen an ihre Umgebung** begrenzt, und die lassen sich hinschreiben:

```gabbro
retry until slot_free(q)
    bounded    4096 attempts        -- oder: 2 ticks
    progress   assume holder_releases
    on_exceeded EP_FULL             -- benannte Absage, kein stiller Abbruch
    effects    { reads q }
{ }
```

| Angabe | wozu | Absenkung nach C |
|---|---|---|
| `bounded` | Terminierung — **eine Zahl, kein Abstiegsmass** | Zaehlschleife `for(i=0;i<N;i++)` |
| `progress` | **wer** die Schleife beendet: eine Lebendigkeitsannahme mit Falsifikator | verschwindet (Geist) |
| `on_exceeded` | Regel 3: der Ueberlauf ist **benannt**, nicht gedeutet | `break` in den Fehlerzweig |

**Minimal: drei Zeilen.** Und Caprock schreibt sie heute **von Hand** an jeder begrenzten Schleife
(`cdt_step_limit`, `note_overrun`, `ERR_EP_FULL`) — die Sprache macht zur Pflicht, was das Projekt
ohnehin tut, und faengt die Stellen, an denen es vergessen wurde (`migration_candidate`).

**Der Ticket-Lock** ist derselbe Fall: er terminiert, weil der Halter freigibt. Das ist eine
Annahme ueber die Umgebung — also `assume` mit Falsifikator (der Watchdog **ist** der Falsifikator),
plus eine Schranke, deren Ueberschreitung ein Befund ist. **Nicht „unbeweisbar", sondern
„beweisbar unter einer benannten, falsifizierbaren Annahme".**

---

## Die vollstaendige Umwandlung

| # | gemeldet als „geht nicht" | **was minimal dastehen muss** | Absenkung |
|---|---|---|---|
| 1 | CAS-/Warteschleifen | `bounded` + `progress assume` + `on_exceeded` — **3 Zeilen** | Zaehlschleife + Fehlerzweig |
| 2 | **ELF ist kein `format`** (offsetbasiert) | `e_phoff : u64 offset_into Self where + e_phentsize*e_phnum <= Self.len` — **1 Attribut + 1 `where`** | Bereichspruefung |
| 3 | `caprock-fat` nur halb `format` | `traverse over chain(fat, cluster) by unvisited` + Absage `Zyklus` — **2 Zeilen** | Schleife + Generationsstempel |
| 4 | `move_cap` — Knotenumbenennung | erzeugte Mutation `relabel` mit **1 `maintains`** | Zeigerumhaengung |
| 5 | `install` — Zustand ohne Namen | `linear Uninstalled(Object)`, nur von `alloc_slot` verbraucht — **1 Typ** | **verschwindet** |
| 6 | `Finalized<'a>` — keine Lebenszeiten | Recht `own` + `Duty` — **1 Rechtsangabe** | verschwindet |
| 7 | **Fastpath-Autoritaet** („darf dieser Thread hierhin schreiben?") | `linear ghost MayWrite(t, f)`, erzeugt von der Cap-Aufloesung — **1 Zeuge + 1 `requires`** | **verschwindet** |
| 8 | Berichtsgeruest braucht Formatierung | **die `measures`-Liste IST die Berichtszeile** — 0 zusaetzliche Zeilen | erzeugtes `printf` |
| 9 | Beziehung zwischen zwei Layouts (das verlorene `US`) | `maintains` **ueber zwei Deklarationen**: Aufteilen erhaelt die Rechtebits — **1 Zeile** | keine |
| 10 | kein Summentyp (13 `ObjectKind`-Varianten) | `tagged` — Deklaration | C-Union mit Marke |
| 11 | **kein `old`** | `ensures old(x) + 1 == x` — **1 Schluesselwort** | verschwindet |
| 12 | `maintains` kennt kein Oeffnen/Schliessen | `breaking I { … }` — der Bereich, in dem die Invariante ruht, wird **benannt** | keine |
| 13 | `fields` nur Einzelbits, keine Laufzeitoffsets | Bitbereich `FRO @[12:8]`; Basis `@ base + CAP.FRO*16`, M1-beschraenkt | Adressrechnung |
| 14 | 2 231 Atomics, null Woerter | `atomic` + `publishes { … }` — **1 Klausel je Atomic** | `_Atomic` + Barriere |
| 15 | **`device` toetet Falle 4 nicht** | `transition` nennt **das ganze geschriebene Wort**, nicht ein Bit — RMW wird damit unformulierbar | ein `store` |
| 16 | `effects` ist fail-open | `effects` **verpflichtend**; leer heisst rein und wird **geprueft** — 0 Zeilen fuer richtigen Code | keine |
| 17 | Registerbank an laufzeitberechneter Basis | parametrisiertes `device Bank(base: Pa)` | Adressrechnung |
| 18 | bedingte Uebersetzung (335 `cfg`-Stellen) | `when <const>` an der Deklaration | `#if` |

---

## Der Befund, der beim Umwandeln entsteht

**Sechs der achtzehn faellen auf DENSELBEN Mechanismus: den linearen Geisterzeugen (M2).**
Nummern 5, 6, 7 — dazu die Bootphase, das virtio-`used`/`avail`-Eigentum und die `check`-Pflicht.

> **Sechs unabhaengige Fundstellen fuer einen Mechanismus sind kein Entwurfswunsch mehr, sondern ein
> Befund.** Und es ist genau der Mechanismus, den **kein vorhandenes Werkzeug liefert**: Verus'
> `tracked` ist affin, Rust ist affin, SPARKs Leckpruefung haengt an einer Allokation.

**Die zweite Zahl: der Median der Zusatzangabe liegt bei ein bis zwei Zeilen je Stelle.** Keine
davon ist ein Lemma, keine ein Schleifeninvariant — es sind **Deklarationen**. Das ist der
Unterschied, auf den es fuer die Kennzahl ankommt.

---

## Was das NICHT heisst — sonst ist es Ueberschreibung Nr. 14

* **Die 2 : 1-Messung wird dadurch nicht besser.** Die Zeilen, die hier „minimal" heissen, sind
  genau die, die der Zaehler zaehlt. Was sich aendert, ist ihr **Charakter**: Deklaration statt
  Beweis — und ob ein Loeser die daraus entstehenden Pflichten **ohne Hinweise** erledigt, ist
  **ungeprueft**.
* **Papier, nicht Uebersetzer.** Achtzehn Umwandlungen auf Papier sind achtzehn Behauptungen ueber
  Absenkbarkeit. Keine davon ist uebersetzt worden.
* **Zwei bleiben unbequem.** Nr. 12 (`breaking`) legalisiert eine Invariantenverletzung — der Preis
  ist, dass der Bereich, in dem nichts gilt, sichtbar wird statt versteckt. Und Nr. 14 verlangt eine
  Klausel an **2 231** Stellen; ob das traegt, entscheidet keine Papieruebung.

---

## Die Folge fuer die Methode

- [ ] **Kein Pruefauftrag fragt mehr „geht das?".** Er fragt: *„was muss minimal dastehen, und laesst
      es sich nach C absenken?"* Ein Bericht, der ein Loch meldet, ohne die minimale Angabe zu
      nennen, ist unvollstaendig — **er hat die Arbeit an der Stelle abgebrochen, an der sie
      anfaengt.**
