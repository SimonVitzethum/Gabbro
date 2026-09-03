#!/usr/bin/env python3
"""The draw for AUFTRAG-GABBROV.md §3 -- fixed BEFORE the rows were looked at.

Seed: the commit this lane produced at Gate 1, `b15ef79`. It existed before any row's
difficulty was inspected and it is not a value I could tune afterwards without the draw
changing visibly.
"""
import hashlib
import re
import sys
from pathlib import Path

W = Path("/home/simon/Dokumente/Gabbro/.claude/worktrees/agent-abde0442a4bb8e45c")
SAAT = "b15ef79"

v = (W / "programmlogik" / "gabbrov" / "V1.lean").read_text(encoding="utf-8")
nicht = set(re.findall(r"def (L\d\d) : Prop := notSayable", v))
zwei = set(re.findall(r"def (L\d\d) \(s s' : State\)", v))
dom = set(re.findall(r"def (L\d\d) [^\n]*\bDomain\b", v))
alle = ["L%02d" % i for i in range(1, 67)]
pop = [n for n in alle if n not in nicht and n != "L66"]
TABELLE = {"L04", "L05", "L09", "L15", "L16"}   # the cdtWf / table-invariant class

print("population %d   not sayable %d   L66 rebooked" % (len(pop), len(nicht)))
print("two-state in the population: %d" % len(zwei & set(pop)))
print("table identity              : %s" % " ".join(sorted(TABELLE)))
print()

rang = sorted(pop, key=lambda n: hashlib.sha256((SAAT + ":" + n).encode()).hexdigest())
gezogen = rang[:5]
print("hash order, first five      : %s" % " ".join(gezogen))

# The two constraints of §3, applied AFTER the blind order and by REPLACING the last
# element -- so the draw stays the draw and the correction is visible.
def erzwinge(gez, bedingung, name):
    if any(bedingung(n) for n in gez):
        print("  constraint %-16s already met" % name)
        return gez
    for n in rang[5:]:
        if bedingung(n):
            print("  constraint %-16s NOT met -- %s replaces %s" % (name, n, gez[-1]))
            return gez[:-1] + [n]
    sys.exit("no member for " + name)

gezogen = erzwinge(gezogen, lambda n: n in TABELLE, "table identity")
gezogen = erzwinge(gezogen, lambda n: n in zwei, "two-state")
print()
print("THE FIVE: %s" % "  ".join(sorted(gezogen, key=lambda n: int(n[1:]))))
for n in sorted(gezogen, key=lambda n: int(n[1:])):
    marken = []
    if n in TABELLE:
        marken.append("table identity")
    if n in zwei:
        marken.append("two-state")
    if n in dom:
        marken.append("domain")
    print("  %s  %s" % (n, ", ".join(marken) or "single state"))
