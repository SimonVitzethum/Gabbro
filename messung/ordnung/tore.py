#!/usr/bin/env python3
"""Welche Werte aus einem `atomic` GATTERN im Korpus einen Zweig?

Drei Quellen je Bindung: `awaits` (die Paarung steht), `exchange` (RMW), schlicht (nichts).
Gezaehlt wird, welche davon danach in einer Bedingung stehen.
"""
import pathlib, re

W = pathlib.Path(__file__).resolve().parent.parent.parent
dateien = sorted(list(W.glob("beispiele/*.gab")) + list(W.glob("beispiele/gift/*.gab"))
                 + list(W.glob("messung/**/*.gab")) + list(W.glob("passlogik/**/*.gab"))
                 + list(W.glob("programmlogik/**/*.gab")))
DEKL = re.compile(r'^\s*(?:pub\s+)?atomic\s+([A-Za-z_][A-Za-z0-9_]*)\s*:')
LET = re.compile(r'^\s*let\s+(?:mut\s+)?([A-Za-z_][A-Za-z0-9_]*)\s*(?::[^=]*)?=\s*(.*)$')
summe = {"awaits": 0, "exchange": 0, "schlicht": 0}
gattert = {"awaits": 0, "exchange": 0, "schlicht": 0}
for d in dateien:
    zeilen = d.read_text().splitlines()
    namen = {m.group(1) for z in zeilen for m in [DEKL.match(z)] if m}
    if not namen:
        continue
    bindungen = {}          # lokaler Name -> (art, atomic, zeile)
    for i, z in enumerate(zeilen, 1):
        s = z.strip()
        if s.startswith("--"):
            continue
        m = LET.match(z)
        if m:
            lok, rest = m.group(1), m.group(2)
            am = re.match(r'([A-Za-z_][A-Za-z0-9_]*)\b\s*(.*)$', rest)
            if am and am.group(1) in namen:
                folge = am.group(2)
                # das Ordnungswort kann in der naechsten Zeile stehen
                weiter = " ".join(zeilen[i:i + 3])
                art = ("awaits" if folge.startswith("awaits") or " awaits" in folge
                       else "exchange" if folge.startswith("exchange")
                       else "schlicht")
                bindungen[lok] = (art, am.group(1), i)
                summe[art] += 1
        if s.startswith("if ") or s.startswith("match ") or s.startswith("narrow "):
            for lok, (art, at, zl) in list(bindungen.items()):
                if re.search(r'\b%s\b' % re.escape(lok), s):
                    gattert[art] += 1
                    print("%-42s :%4d  %-8s %-14s gattert in Z.%d | %s"
                          % (d.relative_to(W), zl, art, at, i, s[:60]))
print()
print("Bindungen aus einem atomic:", summe)
print("davon gattern einen Zweig:", gattert)
