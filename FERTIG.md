# FERTIG — wann Plan und Syntax stehen

**Diese Datei existiert, weil dieser Ordner ein Muster hat.** `HISTORIE.md` fuehrt es: **jedes
gefallene Tor wurde durch Neugruendung ueberlebt**, und das harte Tor wanderte dabei hinter den
Uebersetzer. Ein autonomer Lauf ohne benannte Ziellinie ist dasselbe Muster mit mehr Durchsatz.

**Hier steht die Ziellinie, vorab, und sie ist mechanisch pruefbar, wo das geht.**

> **Der Lauf bricht nicht ab.** Was frueher Abbruch war, ist seit dem 2026-08-14 **Eskalation** —
> s. Abschnitt C. Abgebrochen wird nur bei **bewiesener** Unmoeglichkeit, und wie die aussaehe,
> steht dort ebenfalls, damit der Grund nicht leer ist.

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

## C — ESKALATION statt Abbruch

**Entschieden am 2026-08-14: der Lauf bricht nicht ab.** Abgebrochen wird **nur bei bewiesener
Unmoeglichkeit** — und ein Befund „geht nicht" ist keine. Er ist eine **Entwurfsaufgabe**, genau wie
in [`MINIMALSPEZIFIKATION.md`](MINIMALSPEZIFIKATION.md): nicht *„geht das?"*, sondern *„was muss
minimal dastehen, damit es geht?"*

| Lage | **frueher: Abbruch** | **jetzt: Eskalation** |
|---|---|---|
| Eine **Klempnerei-Pflicht bleibt haengen** und kein Konstrukt nimmt sie ab | Lauf endet | **das Konstrukt wird entworfen**, das sie abnimmt — mit minimaler Angabe und C-Absenkung. Gelingt das nicht, wird die **Unmoeglichkeit hingeschrieben**, nicht die Arbeit beendet |
| Ein Punkt aus **A** ist dreimal angefasst und nicht geschlossen | Lauf endet | er wird **benannter Blocker** und bekommt eine eigene, gezielte Runde statt weiterer Nebenbei-Versuche |
| Zwei Runden erzeugen **mehr Entwurf als Messung** | Lauf endet | **die Zahl wird berichtet, nicht befolgt** — s. unten |

### Was von Abbruchgrund 2 bleibt: die Zahl, ohne die Wirkung

Der Zaehler wird **weitergefuehrt und in jeder Runde genannt**: neue Zeilen in `SYNTAX.md`,
`SPRACHE.md`, `PLAN.md` gegen neue Zeilen in Ergebnisdateien. **Er stoppt nichts mehr, aber er bleibt
sichtbar** — ein Signal, das man abschaltet, ist beim naechsten Mal nicht da, und genau diese Klasse
fuehrt `HISTORIE.md` als Falle 30 („ein Waechter, der nach seiner Behebung weiterschreit, wird
abgeschaltet"). Hier ist die Loesung, ihn vom Urteil zu **entkoppeln**, statt ihn zu entfernen.

### Was „bewiesen unmoeglich" heissen wuerde

Damit der einzige verbliebene Abbruchgrund nicht leer ist, steht hier, wie er aussaehe. **Zwei
Formen, und nur diese:**

1. **Eine geforderte Eigenschaft ist nicht entscheidbar** und auch nicht durch eine benannte
   Annahme ersetzbar. *Beispiel der Form:* allgemeine Lebendigkeit („dieser Thread laeuft
   irgendwann") ueber unbeschraenkten Abläufen — kein Typsystem entscheidet das, und ein
   `progress assume` ersetzt es nur, wenn sich ein Falsifikator bauen laesst.
2. **Zwei geforderte Eigenschaften widersprechen einander.** *Der heute schon bekannte Kandidat:*
   **Generizitaet verlangt Monomorphisierung, und die ist die erste nicht-flache Absenkung** —
   sie greift M-Gold-2 („syntaxgesteuert, nicht optimierend") an. Beides zugleich zu wollen ist
   moeglicherweise widerspruechlich; **das ist zu zeigen, nicht zu vermuten.**

**Beides muss hingeschrieben werden, mit dem Argument.** „Ich sehe keinen Weg" ist kein Beweis —
das waere ein Nullbefund ohne Groesse, und die Falle steht im Register.

## D — Was NICHT als Fertigstellung zaehlt

* **Ein Uebersetzer.** Er steht als P3 im Plan, hinter fuenf Toren. Diese Datei beschreibt Papier.
* **Eine schoene Zahl.** Das Kriterium ist eine Art, keine Menge (`KRITERIUM.md`).
* **„Alle Konstrukte vorhanden".** Ein Konstrukt ohne ausgeschriebenes Fragment und ohne
  C-Absenkung ist eine Behauptung.
* **Ein gruener Waechter.** `pruefe-syntax.sh` prueft Geschlossenheit und Wortschatz — **nicht**,
  ob echter Code hineinpasst. Er hat selbst schon ein falsches Gruen geliefert.
