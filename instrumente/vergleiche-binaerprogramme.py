#!/usr/bin/env python3
"""Two `gabbro` binaries over the WHOLE corpus, byte for byte.

**The counter-direction for a change to the checker.** A change that is meant to be additive
has to prove it: over every `.gab` file in the tree, `pruefe` output and emitted C must be
byte-identical between the two binaries -- stdout, stderr and exit code. *What moves and
should not is the finding.*

    ./instrumente/vergleiche-binaerprogramme.py OLD NEW

Why bytes and not codes: a diagnostic whose CODE is unchanged but whose line number moved is
a changed diagnostic, and counting codes would call that green. The same class as `W16` -- a
measuring device that reads a mixture looks plausible doing it.

The locale is pinned (`LC_ALL=C`). `gabbro` speaks English, but the libraries under it may
report translated, and a comparison of two runs in two locales measures the locale.

Exit: 0 nothing moved, 1 something moved, 2 the run itself did not happen.
"""
import os
import subprocess
import sys
import pathlib

FRIST = 60


def korpus(wurzel):
    """Every `.gab` file of the tree, in a stable order.

    Sorted, because an unordered walk makes two runs of THIS tool incomparable -- and a
    measuring tool that cannot be compared with itself measures nothing.
    """
    return sorted(p for p in wurzel.rglob("*.gab") if ".git" not in p.parts)


def lauf(binaer, unterbefehl, datei, wurzel):
    umgebung = dict(os.environ, LC_ALL="C")
    try:
        r = subprocess.run(
            [str(binaer), unterbefehl, str(datei)],
            capture_output=True, text=True, timeout=FRIST, cwd=wurzel, env=umgebung)
        return (r.returncode, r.stdout, r.stderr)
    except subprocess.TimeoutExpired:
        return ("TIMEOUT", "", "")


def main():
    if len(sys.argv) != 3:
        print(__doc__)
        return 2
    alt, neu = pathlib.Path(sys.argv[1]).resolve(), pathlib.Path(sys.argv[2]).resolve()
    for b in (alt, neu):
        if not b.is_file() or not os.access(b, os.X_OK):
            print(f"ABBRUCH: {b} ist kein ausfuehrbares Programm -- das ist KEIN gruener Lauf.",
                  file=sys.stderr)
            return 2
    wurzel = pathlib.Path(__file__).resolve().parent.parent
    dateien = korpus(wurzel)
    if not dateien:
        print("ABBRUCH: kein `.gab` gefunden -- das ist KEIN gruener Lauf.", file=sys.stderr)
        return 2

    beweg = {"pruefe": [], "emit": []}
    for i, p in enumerate(dateien, 1):
        rel = p.relative_to(wurzel)
        for unterbefehl in ("pruefe", "emit"):
            a = lauf(alt, unterbefehl, rel, wurzel)
            n = lauf(neu, unterbefehl, rel, wurzel)
            if a != n:
                beweg[unterbefehl].append((rel, a, n))
        if i % 100 == 0:
            print(f"  ... {i}/{len(dateien)}", file=sys.stderr)

    print(f"Korpus: {len(dateien)} `.gab`-Dateien, je zwei Unterbefehle, "
          f"{len(dateien) * 4} Prozesse.")
    schlecht = 0
    for unterbefehl, liste in beweg.items():
        print(f"  {unterbefehl}: {len(liste)} Datei(en) bewegt")
        for rel, a, n in liste[:20]:
            print(f"    {rel}")
            print(f"      alt exit={a[0]}  neu exit={n[0]}")
            if a[1] != n[1]:
                print("      stdout unterscheidet sich")
            if a[2] != n[2]:
                print("      stderr unterscheidet sich")
        if len(liste) > 20:
            print(f"    ... und {len(liste) - 20} weitere")
        schlecht += len(liste)
    print(f"== BEWEGT: {schlecht} ==" if schlecht else "== NICHTS BEWEGT ==")
    return 1 if schlecht else 0


if __name__ == "__main__":
    sys.exit(main())
