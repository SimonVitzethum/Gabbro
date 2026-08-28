#!/usr/bin/env python3
"""Zuschnitt (c) gemessen: wie viele Lesungen GETEILTER Plaetze stehen im Korpus WEDER
unter einer Sperre/`observes` NOCH hinter einem `awaits`?

Grob und in die sichere Richtung: es zaehlt Textzeilen, keine Ausdruecke.
"""
import pathlib, re

W = pathlib.Path(__file__).resolve().parent.parent.parent
dateien = sorted(list(W.glob("beispiele/*.gab")))
STATIK = re.compile(r'^\s*(?:pub\s+)?static\s+mut\s+([A-Za-z_][A-Za-z0-9_]*)\s*:')
ATOM = re.compile(r'^\s*(?:pub\s+)?atomic\s+([A-Za-z_][A-Za-z0-9_]*)\s*:')
ges = 0
ungeordnet = 0
for d in dateien:
    zeilen = d.read_text().splitlines()
    namen = set()
    for z in zeilen:
        for r in (STATIK, ATOM):
            m = r.match(z)
            if m:
                namen.add(m.group(1))
    if not namen:
        continue
    tiefe_sperre = []      # Stapel: Klammertiefe, bei der ein locks/observes anfing
    tiefe = 0
    erwartet = set()       # Namen, die in diesem Rumpf schon `awaits`-gedeckt sind
    for i, z in enumerate(zeilen, 1):
        s = z.strip()
        if s.startswith("--"):
            tiefe += z.count("{") - z.count("}")
            continue
        am = re.search(r'awaits\s*\{([^}]*)\}', s)
        if am:
            for t in am.group(1).split(","):
                erwartet.add(t.strip().split(".")[0].split("[")[0])
        if re.match(r'^\s*(?:pub\s+)?(?:impl|divergent|spec|raw)?\s*fn\b', z):
            erwartet = set()
        if re.match(r'^\s*(locks|observes)\b', s):
            tiefe_sperre.append(tiefe)
        # Lesungen
        if not STATIK.match(z) and not ATOM.match(z) and not s.startswith("effects") \
           and not s.startswith("touches") and not s.startswith("measures") \
           and not s.startswith("protects") and "reads " not in s and "writes " not in s:
            for n in namen:
                for m in re.finditer(r'\b%s\b' % re.escape(n), s):
                    nach = s[m.end():].lstrip()
                    if nach.startswith("=") and not nach.startswith("=="):
                        continue
                    if nach.startswith("awaits") or nach.startswith("exchange"):
                        continue
                    ges += 1
                    if not tiefe_sperre and n not in erwartet:
                        ungeordnet += 1
                        print("%-38s :%4d %-16s | %s" % (d.name, i, n, s[:60]))
        tiefe += z.count("{") - z.count("}")
        while tiefe_sperre and tiefe <= tiefe_sperre[-1]:
            tiefe_sperre.pop()
print()
print("Lesungen geteilter Plaetze insgesamt:", ges)
print("davon weder unter Sperre noch hinter `awaits`:", ungeordnet)
