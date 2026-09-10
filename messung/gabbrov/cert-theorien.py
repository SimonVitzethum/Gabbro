#!/usr/bin/env python3
"""Which of GabbroV's sayable obligations fall in theories with a usable
certificate path -- the number AUFTRAG-GABBROV.md section 8 asks for.

Criterion (from section 8 itself): for bitvectors there is a usable path,
for quantifiers and arrays practically none. So per row of
programmlogik/gabbrov/V1.lean:

    QF     -- the Prop is quantifier-free boolean/integer arithmetic over
              fixed places (QF_LIA/QF_BV shape: decidable, certificates exist)
    QUANT  -- it quantifies over a table domain (allD, a plain `forall`, a
              `List` membership) -- no usable path
    REACH  -- it uses reachesIn/cdtWf (needs unrolling or closure) -- none
    FOLD   -- it uses countD/firstD (aggregation beyond one quantifier) -- none

A row counts as QF only if none of the other three fire. The population is
the sayable set: 66 L rows minus the ten `notSayable` minus L66, which the
assumption layer rebooked (zaehle-pflichten.py --gabbrov derives the same 55).

`cdtWf` is expanded one level (it is allD + reachesIn); everything else is
read off the row's own def block.
"""
import re
import sys
from pathlib import Path

W = Path(__file__).resolve().parent.parent.parent
V1 = W / "programmlogik" / "gabbrov" / "V1.lean"

NOT_SAYABLE = set(re.findall(r"def (L\d\d) : Prop := notSayable",
                             V1.read_text(encoding="utf-8")))
REBOOKED = {"L66"}  # assumption layer, messung/GABBROV-V2.md section 1


def bloecke(text):
    """Map def name to its block, plus L-number to row def name.

    Most rows define `LNN` directly; three do not: L04's statement is
    `cdtWf`, L07's is `istBlatt`, L23's is `antwortpflichtPaarig`. All three
    are caught by the `**LNN` marker in the doc comment above the def.
    Returns (defs, zeile) with zeile[LNN] = def name of the row.
    """
    defs, zeile = {}, {}
    cur, name, markiert = None, None, None
    for z in text.splitlines():
        m = re.search(r"\*\*(L\d\d)\b", z)
        if m:
            markiert = m.group(1)
        d = re.match(r"def (\w+)", z)
        if d:
            name, cur = d.group(1), [z]
            defs[name] = cur
            # The `**LNN` marker names the row, whatever the def is called.
            if markiert and not re.fullmatch(r"L\d\d", name):
                zeile[markiert] = name
            elif re.fullmatch(r"L\d\d", name):
                zeile[name] = name
            markiert = None
        elif cur is not None:
            if z.strip() == "" or z.startswith("/--") or z.startswith("/-"):
                cur = None
            else:
                cur.append(z)
    return defs, zeile


def eigen(body):
    """Features of one block, helpers NOT expanded."""
    feats = set()
    if re.search(r"\ballD\b|forallSlots|∀|forall\b| List ", body):
        feats.add("QUANT")
    if re.search(r"\breachesIn\b|\bcdtWf\b|\.reaches\b", body):
        feats.add("REACH")
    if "countD" in body:
        feats.add("FOLD-count")
    if "firstD" in body:
        feats.add("FOLD-first")
    return feats


def alle_merkmale(defs):
    """Features per def, with one in-file helper expansion.

    A row that calls `antwortpflichtPaarig` quantifies even though its own
    block shows no quantifier -- the same reason `cdtWf` is matched by name
    above. Without the expansion the row would be booked QF and the share
    would be too green.
    """
    feat = {n: eigen("\n".join(b)) for n, b in defs.items()}
    changed = True
    while changed:
        changed = False
        for n, b in defs.items():
            body = "\n".join(b)
            for h, f in feat.items():
                if h != n and re.search(r"\b%s\b" % h, body) and not f <= feat[n]:
                    feat[n] |= f
                    changed = True
    return feat


def main():
    text = V1.read_text(encoding="utf-8")
    defs, zeile = bloecke(text)
    alle = ["L%02d" % i for i in range(1, 67)]
    pop = [n for n in alle if n not in NOT_SAYABLE and n not in REBOOKED]
    assert len(pop) == 55, "population moved: %d" % len(pop)
    assert all(n in zeile for n in pop), \
        "rows without a def block: %s" % [n for n in pop if n not in zeile]
    feat = alle_merkmale(defs)
    klassen = {n: feat[zeile[n]] for n in pop}
    qf = sorted(n for n in pop if not klassen[n])
    print("== Certificate-path share over the 55 sayable obligations ==")
    for n in pop:
        marke = "QF" if n in qf else ",".join(sorted(klassen[n]))
        print("  %s  %s" % (n, marke))
    print()
    print("  sayable                              55")
    print("  in QF_LIA/QF_BV shape (usable path)  %d (%s)" % (len(qf), " ".join(qf) or "none"))
    print("  needing quantifiers/folds/reachability %d" % (55 - len(qf)))


if __name__ == "__main__":
    sys.exit(main())
