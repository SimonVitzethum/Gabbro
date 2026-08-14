# FERTIG — wann Plan und Syntax stehen

**Diese Datei existiert, weil dieser Ordner ein Muster hat.** `HISTORIE.md` fuehrt es: **jedes
gefallene Tor wurde durch Neugruendung ueberlebt**, und das harte Tor wanderte dabei hinter den
Uebersetzer. Ein autonomer Lauf ohne benannte Ziellinie ist dasselbe Muster mit mehr Durchsatz.

**Hier steht die Ziellinie, vorab, und sie ist mechanisch pruefbar, wo das geht.**

---

## Das Ziel, gegen das geprueft wird

> **Eine Sprache, in der man Kernel, Treiber und Programme DIREKT schreibt — Hardwarezugriff ueber
> Hardwareannahmen — und die alles fuer einen Gold-Beweis liefert AUSSER dem Logikbeweis selbst.**

---

## A — Die Syntax steht, wenn alle acht Punkte zutreffen

| | Bedingung | pruefbar durch | Stand |
|---|---|---|---|
| **A1** | Die Grammatik ist **geschlossen**: kein benutztes, nie definiertes Nichtterminal | `./pruefe-syntax.sh` | **erfuellt** (100 Regeln, 0 offen) |
| **A2** | Alle offenen Punkte am Ende von `SYNTAX.md` sind **entschieden oder gemessen** — nicht „spaeter" | Auszaehlen | **1 von 9** (`narrow`, gemessen) |
| **A3** | **Jeder Caprock-Bereich hat ein Urteil** — ausdrueckbar / braucht Konstrukt X / nicht ausdrueckbar —, **je mit einem ausgeschriebenen Fragment als Beleg** | Liste unten | offen |
| **A4** | Der **Logik/Klempnerei-Split** ist an mindestens fuenf Fragmenten gemessen, und **keine Klempnerei-Pflicht bleibt unbenannt haengen** | `KRITERIUM.md` | **nie gemessen** |
| **A5** | Ein **Treiber** ist vollstaendig ausgeschrieben: Geraeteregister, Ringe, Geraeteeigentum, Barrieren, Annahmen | Fragment | offen |
| **A6** | Ein **Userspace-Programm** ist vollstaendig ausgeschrieben | Fragment | offen |
| **A7** | Das **Pruefgeruest** (15,7 % des Codes) ist ausgeschrieben — `check` traegt es oder nicht | Fragment | offen |
| **A8** | **Jedes Konstrukt hat seine C-Absenkung hingeschrieben**, nicht behauptet | je Regel | 18 Behauptungen offen |

### Die Bereiche zu A3

`caprock-cap` (Tabelle+CDT) · `caprock-sched` (Warteschlangen) · IPC/`threads` (Nebenlaeufigkeit,
872 `Ordering::`) · `mmu` (Hardwarevertrag+Algorithmus) · IOMMU (`vtd`/`irte`/`dmar`/`smmu`) ·
`caprock-virtio` (Ringe, Geraeteeigentum) · Parser (`part`/`fat`/`checkpoint`) · Lader (Code als
Daten) · Pruefgeruest · `programs/` (Userspace).

---

## B — Der Plan steht, wenn

| | Bedingung | Stand |
|---|---|---|
| **B1** | Jede Phase hat ein **Tor**, und solange es ohne Uebersetzer pruefbar ist, ist es das | erfuellt |
| **B2** | Die Abbruchbedingungen stehen auf dem **Kriterium**, nicht auf einer Zahl | erfuellt |
| **B3** | Die Phasen sind **mit den gemessenen Ergebnissen konsistent** — kein Tor, das eine Messung schon widerlegt hat | zu pruefen nach jedem Ergebnis |
| **B4** | Es gibt **keinen zweiten Weg** und keinen Rueckfallzuschnitt | erfuellt |

---

## C — Wann der autonome Lauf ENDET, auch ohne Fertigstellung

**Drei Abbruchgruende, und jeder verlangt einen Bericht statt einer weiteren Schicht:**

1. **Eine Klempnerei-Pflicht bleibt nachweislich haengen und kein Konstrukt nimmt sie ab.**
   Das ist die Abbruchbedingung aus `KRITERIUM.md` — sie beendet den Lauf, nicht nur den Punkt.
2. **Zwei aufeinanderfolgende Runden erzeugen mehr Entwurfstext als Messung.**
   Gemessen an Zeilen: neue Zeilen in `SYNTAX.md`/`SPRACHE.md`/`PLAN.md` gegen neue Zeilen in
   Ergebnisdateien (`P0-*`, `NARROW-GEMESSEN`, `logik-klempnerei`). **Ueberwiegt der Entwurf
   zweimal hintereinander, ist der Korrekturkreislauf wieder schneller als der Messkreislauf** —
   genau der Befund, den `HISTORIE.md` als Trajektorie fuehrt.
3. **Ein Punkt aus A ist dreimal angefasst und nicht geschlossen worden.** Dann ist er kein
   offener Punkt, sondern ein verdeckter Blocker, und gehoert als solcher benannt.

---

## D — Was NICHT als Fertigstellung zaehlt

* **Ein Uebersetzer.** Er steht als P3 im Plan, hinter fuenf Toren. Diese Datei beschreibt Papier.
* **Eine schoene Zahl.** Das Kriterium ist eine Art, keine Menge (`KRITERIUM.md`).
* **„Alle Konstrukte vorhanden".** Ein Konstrukt ohne ausgeschriebenes Fragment und ohne
  C-Absenkung ist eine Behauptung.
* **Ein gruener Waechter.** `pruefe-syntax.sh` prueft Geschlossenheit und Wortschatz — **nicht**,
  ob echter Code hineinpasst. Er hat selbst schon ein falsches Gruen geliefert.
