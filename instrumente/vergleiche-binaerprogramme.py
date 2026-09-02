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

**AND IT HAD NO SPEECH TEST AT ALL UNTIL 2026-09-02.** Every other instrument in this set
carries one in both directions; this one checked `is_file()` and `os.access(X_OK)` and
nothing else. Measured, literally, on the tree of `178e260`::

    $ ./instrumente/vergleiche-binaerprogramme.py target/debug/gabbro target/debug/gabbro
    Korpus: 601 `.gab`-Dateien, je zwei Unterbefehle, 2404 Prozesse.
      pruefe: 0 Datei(en) bewegt
      emit: 0 Datei(en) bewegt
    == NICHTS BEWEGT ==                     exit=0

    $ ./instrumente/vergleiche-binaerprogramme.py /bin/true /bin/true
    == NICHTS BEWEGT ==                     exit=0

*The same path twice, and two programs that are not `gabbro` at all, both green.* 2404
processes, eight seconds, and zero information -- and the caller had asked whether a change
to the checker was additive. **A green over nothing looks exactly like a green over
everything**, and this is the tool whose whole job is to say which of the two it is.

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


def sprechprobe(binaer, datei, wurzel):
    """**Does this program answer its argument at all?**

    The comparison below is a tuple comparison of `(code, stdout, stderr)`. A program that
    IGNORES its arguments returns the same tuple for every input, so it compares equal to
    every other such program -- and 2404 processes then print `== NICHTS BEWEGT ==` about
    nothing at all. `/bin/true` against `/bin/true` did exactly that until today.

    The probe is the tool's own machinery pointed at a subject it brings along: the SAME
    binary under the two subcommands the run compares. `gabbro pruefe` and `gabbro emit`
    cannot agree on a file -- one prints a verdict, the other prints C. If they do agree,
    this run cannot see a difference and must not report the absence of one.

    > *A comparison that has never been seen catching a difference is not a green; it is an
    > untested instrument* (R11).
    """
    a = lauf(binaer, "pruefe", datei, wurzel)
    b = lauf(binaer, "emit", datei, wurzel)
    return a != b


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
    # **TWO NAMES FOR ONE PROGRAM ARE NEITHER A BEFORE NOR AN AFTER.** `resolve()` above
    # makes `./target/debug/gabbro` and an absolute path the same object, and the bytes settle
    # the rest: a copy is no second measurement either. *What cannot move must never be
    # asked whether it moved* -- the answer is `0`, worth nothing.
    if alt == neu:
        print(f"ABBRUCH: beide Argumente nennen DASSELBE Programm ({alt}) -- ein Lauf gegen",
              file=sys.stderr)
        print("  sich selbst kann nichts bewegen und beweist damit nichts. Das ist KEIN",
              file=sys.stderr)
        print("  gruener Lauf, sondern ein Fehlaufruf.", file=sys.stderr)
        return 2
    if alt.read_bytes() == neu.read_bytes():
        print(f"ABBRUCH: {alt} und {neu} sind BYTEIDENTISCH -- zwei Namen fuer dasselbe",
              file=sys.stderr)
        print("  Erzeugnis. Es gibt kein Vorher und kein Nachher zu vergleichen.",
              file=sys.stderr)
        return 2
    wurzel = pathlib.Path(__file__).resolve().parent.parent
    dateien = korpus(wurzel)
    if not dateien:
        print("ABBRUCH: kein `.gab` gefunden -- das ist KEIN gruener Lauf.", file=sys.stderr)
        return 2

    # **The speech test, both ways, over a single file -- four processes.** It runs BEFORE
    # the corpus walk: whatever fails here turns the 2404 processes below into a measurement
    # of the wrong question.
    print("== Sprechprobe ==")
    probe = dateien[0].relative_to(wurzel)
    schlecht = []
    for name, b in (("alt", alt), ("neu", neu)):
        spricht = sprechprobe(b, probe, wurzel)
        print(f"  {name} ({b.name}) antwortet auf sein Argument: "
              f"{'ok (`pruefe` und `emit` gehen auseinander)' if spricht else 'GESCHEITERT'}")
        if not spricht:
            schlecht.append(b)
    if schlecht:
        print(f"ABBRUCH: {len(schlecht)} der zwei Programme geben auf `pruefe` und auf `emit`",
              file=sys.stderr)
        print(f"  DIESELBE Antwort ueber `{probe}` -- sie lesen ihr Argument nicht. Ein",
              file=sys.stderr)
        print("  Programm, das sein Argument ignoriert, ist von jedem anderen solchen nicht",
              file=sys.stderr)
        print("  zu unterscheiden, und der Vergleich unten meldet dann `NICHTS BEWEGT` ueber",
              file=sys.stderr)
        print("  nichts. Das ist KEIN gruener Lauf.", file=sys.stderr)
        return 2
    print(f"  gemessen an `{probe}` -- der Vergleich SIEHT einen Unterschied")

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
