#!/usr/bin/env python3
"""**How much open work sits on which GOAL?** -- the block count over `TODO.md`

**The occasion, 2026-08-23.** `TODO.md` is cut into STUFEN, and that is a work order. The four
goals at the head of the same file are a different axis. As long as nobody joins the two, the
question *"what am I working on, measured against the goal?"* has no answer -- and the answer,
the first time it was worked out, was uncomfortable: **the block with the lowest state of
completion had not a single heading of its own.**

> **A block without a heading does not get worked off, it gets grazed.**

**Why a tool and not a table:** a written-down distribution is wrong the next day and nobody
notices. The mark therefore stands in the HEADING (`⟨A⟩ … ⟨Z⟩`), the count is derived from it,
and the block column of the table *Die Reihenfolge* is held against the same marks --
**one register, two readers** (W7).

**And what this figure is NOT:** a weighting. It counts items, not effort. One item can be a
line of grammar or a proof project. *What it measures is the distribution of ATTENTION, and
that is interesting exactly when it contradicts the state of completion.*
"""

import pathlib
import re
import sys

W = pathlib.Path(__file__).resolve().parent.parent
FRIST = 60  # this tool only reads text; the deadline stands for the day that changes

BLOECKE = {
    "A": "die Maschine — Sprache, Prüfer, Erzeuger",
    "B": "die Kennzahl — eine W-Pflicht, die entsteht",
    "C": "K100 — die Klempnereiabdeckung",
    "D": "Ziel 2 — Gabbro formal verifiziert",
    "E": "Ziel 3 — Nutzbarkeit",
    "Q": "Querschnitt — die Messschicht",
    "Z": "zurückgestellt und Buchführung",
}

# The headings BEFORE the first stage carry no block: they are the head of the file and hold
# no items. Should one ever appear there, the guardian falls at the mark, not here.
KOPF = ("# Gabbro — offene Punkte", "# Die vier Ziele", "# Die Reihenfolge",
        "# DIE REGEL ÜBER ALLEM")

MARKE = re.compile(r"⟨([A-Z])⟩")


def lies(text):
    """Returns (distribution, unmarked, unknown, items_total).

    An item inherits the block of its section; an own mark in the FIRST line of the item
    trumps it. *The second form is the more expensive one and therefore the rare one:* it
    stands where an item has to stay in its context but pays into a different goal.
    """
    verteilung = {k: 0 for k in BLOECKE}
    ohne_marke, unbekannt, gesamt = [], [], 0
    block = None
    for nr, z in enumerate(text.split("\n"), 1):
        if z.startswith("# "):
            if any(z.startswith(k) for k in KOPF):
                block = None
                continue
            m = MARKE.search(z)
            if not m:
                ohne_marke.append((nr, z[:64]))
                block = None
                continue
            block = m.group(1)
            if block not in BLOECKE:
                unbekannt.append((nr, block))
                block = None
        elif z.lstrip().startswith("- [ ]"):
            gesamt += 1
            eigen = MARKE.search(z)
            b = eigen.group(1) if eigen else block
            if b in verteilung:
                verteilung[b] += 1
            elif b is not None:
                unbekannt.append((nr, b))
    return verteilung, ohne_marke, unbekannt, gesamt


def tabelle(text):
    """The block column of *Die Reihenfolge* against the marks of the headings.

    **Two readers over one register.** Whoever changes the table and not the heading gets a
    finding here instead of a silent divergence.
    """
    marken = {}
    for z in text.split("\n"):
        if z.startswith("# STUFE "):
            m = re.match(r"# STUFE (\d)", z)
            b = MARKE.search(z)
            if m and b:
                marken[m.group(1)] = b.group(1)
    befunde = []
    for m in re.finditer(r"^\| \*\*(\d)\*\* \| [^|]* \| \*\*([A-Z])\*\* \|", text, re.M):
        stufe, block = m.group(1), m.group(2)
        if stufe not in marken:
            befunde.append(f"Tabelle führt Stufe {stufe}, die Überschrift dazu fehlt")
        elif marken[stufe] != block:
            befunde.append(f"Stufe {stufe}: Tabelle sagt ⟨{block}⟩, Überschrift sagt "
                           f"⟨{marken[stufe]}⟩")
    for stufe, block in sorted(marken.items()):
        if not re.search(rf"^\| \*\*{stufe}\*\* \|", text, re.M):
            befunde.append(f"Stufe {stufe} hat eine Überschrift, aber keine Tabellenzeile")
    return befunde


def sprechprobe():
    """**Both directions, on invented text.** A counter that reads only its own file measures
    how well that file fits it."""
    roh = "# STUFE 1 — X  ⟨A⟩\n- [ ] eins\n- [ ] zwei\n"
    ohne = "# STUFE 1 — X\n- [ ] eins\n- [ ] zwei\n"
    fremd = "# STUFE 1 — X  ⟨W⟩\n- [ ] eins\n"
    stich = "# STUFE 1 — X  ⟨A⟩\n- [ ] eins\n- [ ] zwei ⟨B⟩\n"
    a = lies(roh)[0]["A"] == 2 and not lies(roh)[1]
    b = len(lies(ohne)[1]) == 1
    c = len(lies(fremd)[2]) == 1
    d = lies(stich)[0]["A"] == 1 and lies(stich)[0]["B"] == 1
    e = bool(tabelle("# STUFE 1 — X  ⟨A⟩\n| **1** | y | **C** | z |\n"))
    print("== Sprechprobe der Blockzählung ==")
    print(f"  saubere Marke zählt:        {'ok' if a else 'FEHLER'}")
    print(f"  fehlende Marke fällt auf:   {'ok' if b else 'FEHLER'}")
    print(f"  erfundener Block fällt auf: {'ok' if c else 'FEHLER'}")
    print(f"  Marke am Punkt sticht:      {'ok' if d else 'FEHLER'}")
    print(f"  Tabelle gegen Überschrift:  {'ok' if e else 'FEHLER'}")
    return all((a, b, c, d, e))


def main():
    # **TOOTH 0 -- THE SUBJECT HAS TO BE THERE** (2026-08-31). Over a tree without
    # its subject this tool died of a `FileNotFoundError`: return code **1**, a
    # traceback, and in a chain that reads like a finding. *A crash is not a refusal
    # -- a NAMED refusal is*, and a missing subject says the SETUP has to change.
    if not (W / "TODO.md").is_file():
        print("ABBRUCH: TODO.md fehlt -- es wird NICHT null gezaehlt.", file=sys.stderr)
        return 2
    if not sprechprobe():
        print("\n== BLOECKE: die Sprechprobe faellt -- die Zahlen darunter sind wertlos ==")
        # **Every refusal in this file ends with 2, not 1** (2026-08-31). This counter joined
        # `abnahme.py` that day, so its return code is now read as a VERDICT -- and the sixth
        # requirement applies: `1` means the TREE has to change, `2` means the SETUP does.
        # Every site below says NOTHING WAS MEASURED, so every one of them is a `2`.
        return 2
    text = (W / "TODO.md").read_text(encoding="utf-8")
    verteilung, ohne_marke, unbekannt, gesamt = lies(text)
    t_befunde = tabelle(text)

    print(f"\n== Offene Punkte je Ziel: {gesamt} in {len(BLOECKE)} Bloecken ==")
    breite = max(len(v) for v in BLOECKE.values())
    for k in sorted(BLOECKE):
        n = verteilung[k]
        anteil = (100.0 * n / gesamt) if gesamt else 0.0
        balken = "#" * int(round(anteil / 2))
        print(f"  ⟨{k}⟩ {BLOECKE[k]:<{breite}}  {n:4d}  {anteil:5.1f} %  {balken}")

    befunde = []
    for nr, z in ohne_marke:
        befunde.append(f"TODO.md:{nr}: Ueberschrift ohne Blockmarke -- '{z}'")
    for nr, b in unbekannt:
        befunde.append(f"TODO.md:{nr}: Block ⟨{b}⟩ steht in keinem Register")
    befunde += [f"Die Reihenfolge: {b}" for b in t_befunde]

    print(f"\n== Arbeitsmenge: {gesamt} offene Punkte, {len(BLOECKE)} Bloecke, "
          f"{len(ohne_marke)} Ueberschriften ohne Marke, {len(befunde)} Befunde, 5 Proben ==")
    if befunde:
        print(f"\n== BLOECKE: {len(befunde)} BEFUNDE ==")
        for b in befunde:
            print(f"  BEFUND  {b}")
        return 1

    print("== BLOECKE: ALL PASS -- jede Ueberschrift traegt ihr Ziel ==")
    print("\n== Und was das NICHT heisst ==")
    print("  Gezaehlt werden PUNKTE, nicht Aufwand. Ein Punkt kann eine Zeile Grammatik")
    print("  sein oder ein Beweisprojekt; die Verteilung misst die AUFMERKSAMKEIT und")
    print("  nicht die Arbeit. Und die Marke steht am ABSCHNITT: ein Punkt, der auf ein")
    print("  anderes Ziel zahlt, ist nur dann richtig gezaehlt, wenn ihn jemand eigens")
    print("  markiert hat. **Die Zahlen sind damit eine obere Schranke je Block** (W10).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
