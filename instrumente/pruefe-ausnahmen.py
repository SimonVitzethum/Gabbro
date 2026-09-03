#!/usr/bin/env python3
"""**The exception list of `E2` -- counted, and held against `HISTORIE.md`.**

`AUFTRAG-GABBROV.md` §1 defines `E2` as the decision share: how many of the obligations
GabbroV treats end *passed* or *refuted* rather than *undecided*. Its claim is **all of them,
except the structurally undecidable -- and those stand by name in `dokumente/AUSNAHMEN.md`.**

The mandate says in the same breath why that needs a guardian:

> *"A percentage lets the exception list grow silently with every obligation that turns out to
> be hard."* And: *"Without this guardian `E2` is a declaration of intent."*

WHAT IT HOLDS, AND WHY IT IS TWO THINGS AND NOT ONE
---------------------------------------------------
1. **The count against a booked mark.** Growing the list means editing this file, which is a
   diff a reader sees. `AUFTRAG-GABBROV.md` §9 puts every addition beyond the four big-step
   rows on the stop-list; the mark is where that stop is mechanised.
2. **Every row's obligation name against `dokumente/HISTORIE.md`.** A row whose obligation is
   not written up there falls. So an exception cannot be created by editing a table alone --
   the reason has to land where this folder keeps its corrections.

*Either check alone can be met by accident.* A pure count is satisfied by swapping one row for
another; a pure cross-reference is satisfied by a list that quietly doubles in length while
every name happens to occur somewhere in a long document.

WHAT IT DOES NOT DO
-------------------
**It does not judge whether a reason is really structural.** That is the sentence in the
fourth column, and no script decides it. What it excludes is the one thing a script can: that
the list grows without anybody noticing, and that a row appears whose reason nobody wrote down.
*The same division of labour `zaehle-pflichten.py` states in its own head -- the tool makes
sure no line is overlooked, the hand makes sure no line is miscounted.*

    ./instrumente/pruefe-ausnahmen.py
"""
import re
import sys
from pathlib import Path

# **Whoever leaves mid-run says WHERE** -- the shared form, out of `abschnitt.py`. Without it
# a `return 1` here is a half measurement that reads like a whole one: output before it,
# nothing after, and a return code that says *finding* rather than *cut short*.
sys.path.insert(0, str(Path(__file__).resolve().parent))
import abschnitt  # noqa: E402

W = Path(__file__).resolve().parent.parent
LISTE = W / "dokumente" / "AUSNAHMEN.md"
HISTORIE = W / "dokumente" / "HISTORIE.md"

# **The booked size of the list.** Raising this number is the diff `AUFTRAG-GABBROV.md` §9
# wants to see. The four are `L24`, `L34`, `L50`, `L52` -- one missing means seen four times,
# and not four separate findings.
MARKE = 4

# A row of the table: `| 1 | **L24** -- ... | reason | 2026-09-03 |`. The obligation name is
# what carries the identity, and it has to be an `L` row of `PFLICHTEN.md`.
ZEILE = re.compile(r"^\|\s*\d+\s*\|\s*\*\*(L\d{2})\*\*\s*(?:—|--)\s*(.+?)\s*\|"
                   r"\s*(.+?)\s*\|\s*(\d{4}-\d{2}-\d{2})\s*\|\s*$")


def eintraege(text):
    """The rows of the list, as `(name, subject, reason, date)`."""
    return [m.groups() for m in (ZEILE.match(z) for z in text.splitlines()) if m]


def pruefe(liste_text, historie_text):
    """Returns `(rows, over_the_mark, without_a_history_entry)`."""
    zeilen = eintraege(liste_text)
    zuviel = max(0, len(zeilen) - MARKE)
    ohne = [n for n, _, _, _ in zeilen if not re.search(r"`?%s`?\b" % re.escape(n),
                                                        historie_text)]
    return zeilen, zuviel, ohne


def sprechprobe():
    """**R14, in both directions -- a guardian nobody has seen say no is an ornament.**

    Three poisons and one clean control, because this guardian has two teeth and a tooth that
    never bites is indistinguishable from one that is not there.
    """
    echt = LISTE.read_text(encoding="utf-8")
    hist = HISTORIE.read_text(encoding="utf-8")
    proben = []

    # ONE -- a fifth row must break the mark.
    fuenfte = echt.replace(
        "\n\n**Four rows, one cause.**",
        "\n| 5 | **L11** -- erfunden | Sprechprobe | 2026-09-03 |\n\n**Four rows, one cause.**",
        1)
    _, zuviel, _ = pruefe(fuenfte, hist)
    proben.append(("eine fuenfte Zeile bricht die Marke", zuviel == 1))

    # TWO -- a row whose obligation is nowhere in `HISTORIE.md` must fall, even at four rows.
    # `L99` cannot occur there: `PFLICHTEN.md` has 66 `L` rows.
    getauscht = echt.replace("**L52**", "**L99**", 1)
    _, zuviel2, ohne2 = pruefe(getauscht, hist)
    proben.append(("ein Name ohne HISTORIE-Eintrag faellt bei GLEICHER Zahl",
                   zuviel2 == 0 and ohne2 == ["L99"]))

    # THREE -- the empty list must not look like a clean one. This is the W17 shape: over an
    # empty population both checks hold and the run is the greenest it can ever be.
    leer, zuviel3, ohne3 = pruefe("# nothing here\n", hist)
    proben.append(("die LEERE Liste ist keine saubere Liste",
                   leer == [] and zuviel3 == 0 and ohne3 == []))

    # FOUR -- the control. Without it the three above also pass over a guardian that always
    # says no.
    _, zuviel4, ohne4 = pruefe(echt, hist)
    proben.append(("die echte Liste bleibt frei", zuviel4 == 0 and not ohne4))

    for was, ok in proben:
        print("  %-58s %s" % (was + ":", "ja" if ok else "NEIN"))
    return all(ok for _, ok in proben)


def main():
    # **TOOTH 0 -- the subject has to be there.** Without this the whole run is a positive
    # verdict about nothing (W17), and it would look exactly like a clean list.
    if not LISTE.is_file() or not HISTORIE.is_file():
        print("ABBRUCH: %s -- es wurde NICHTS gemessen."
              % ("`dokumente/AUSNAHMEN.md` fehlt" if not LISTE.is_file()
                 else "`dokumente/HISTORIE.md` fehlt"))
        print("  Ueber einer fehlenden Liste halten beide Pruefungen, und `ALL PASS` waere")
        print("  ein Urteil ueber nichts.")
        return 2

    liste_text = LISTE.read_text(encoding="utf-8")
    hist_text = HISTORIE.read_text(encoding="utf-8")
    zeilen, zuviel, ohne = pruefe(liste_text, hist_text)

    print("== Sprechprobe (R14) ==")
    if not sprechprobe():
        print("== AUSNAHMEN: der Waechter misst nicht ==")
        return 2
    print()

    if not zeilen:
        print("ABBRUCH: `dokumente/AUSNAHMEN.md` traegt KEINE Zeile im erwarteten Format.")
        print("  Entweder ist die Liste leer -- dann ist dieser Lauf ein Urteil ueber")
        print("  nichts -- oder die Tafel hat ihre Gestalt geaendert und dieser Waechter")
        print("  liest sie nicht mehr. **Beides ist ein Befund, kein gruener Lauf.**")
        return 2

    print("== Die namentlichen Ausnahmen von `E2` ==")
    for n, gegenstand, _grund, datum in zeilen:
        print("  %-5s %-10s %s" % (n, datum, gegenstand[:58]))
    print("  -------------------------------------------------")
    print("  %d Zeilen, gebucht sind %d" % (len(zeilen), MARKE))
    print()

    fehler = 0
    if zuviel:
        print("  RATSCHE GEBROCHEN: %d Zeilen, gebucht sind %d." % (len(zeilen), MARKE))
        print("  `AUFTRAG-GABBROV.md` §9 stellt jeden Zuwachs ueber die vier")
        print("  Grossschritt-Zeilen hinaus unter Halt. **Eine Ausnahme mehr ist eine")
        print("  Entscheidung und keine Buchung** -- fragen, dann `MARKE` heben.")
        fehler = 1
    if ohne:
        print("  OHNE GRUND IM ORDNER: %s" % ", ".join(ohne))
        print("  `dokumente/HISTORIE.md` nennt diese Pflicht nicht. Eine Ausnahme, deren")
        print("  Grund nirgends aufgeschrieben ist, ist eine Zeile in einer Tabelle --")
        print("  und `E2` haengt daran, dass der Grund STRUKTURELL ist, was nur ein")
        print("  geschriebener Grund zeigen kann.")
        fehler = 1

    if fehler:
        print("\n== AUSNAHMEN: BEFUND ==")
        return 1

    print("== AUSNAHMEN: ALL PASS -- %d Zeilen, jede mit einem Grund in `HISTORIE.md` =="
          % len(zeilen))
    print("   Und was das NICHT heisst: ob ein Grund wirklich STRUKTURELL ist, steht in")
    print("   der vierten Spalte und entscheidet kein Skript. Ausgeschlossen ist nur, dass")
    print("   die Liste still waechst und dass eine Zeile ohne geschriebenen Grund dasteht.")
    return 0


if __name__ == "__main__":
    sys.exit(abschnitt.fahre(main))
