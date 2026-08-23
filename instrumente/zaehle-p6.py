#!/usr/bin/env python3
"""**P6 -- how many of the counted obligations can a PROVER read?**

`gabbro pflichten` counts what a human owes. `gabbro pflichten --isabelle` writes that same
register as an Isabelle theory -- per obligation **either a goal or a NAMED refusal**. This
tool adds up both columns over the corpus.

**The second number is the one that matters.** An emitter that swallows forty-nine
obligations and emits one looks, in the first column, exactly like one that refuses
forty-nine and emits one -- *and only the second has measured anything.* Hence this run
FAILS when `goals + refused` does not come to the total, and it fails again when the reasons
do not add up to the refusals.

    ./instrumente/zaehle-p6.py                 over `beispiele/` and `messung/`
    ./instrumente/zaehle-p6.py --je-datei      with the table, file by file

The binary is built on `ki-pc-fisch-101` (CLAUDE.md); this tool only calls an existing
`target/debug/gabbro`.
"""
import collections
import glob
import pathlib
import re
import subprocess
import sys

W = pathlib.Path(__file__).resolve().parent.parent
GABBRO = W / "target" / "debug" / "gabbro"

# **Every execution under a deadline.** A hang looks like "still running", not like a
# finding -- the same lesson `mutiere-pruefer.py` carries at the top of its file.
FRIST = 120

# The refusal reasons exactly as `refinement.rs` writes them. **The list stands here in
# FULL** -- a reason the emitter knows and this tool does not shows up below as `UNKNOWN`
# instead of quietly landing in no column at all.
REASONS = [
    ("lock-witness", "`Held(…)` -- the lock passes carry it, no prover does"),
    ("foreign-body", "an `ensures` at a foreign body -- an ASSUMPTION, not a goal"),
    ("body-effect", "speaks about the world AFTER a body ran -- there is no body semantics"),
    ("no-term", "a form the emitter has no Isabelle term for"),
    ("argument-not-stable", "the argument is neither a literal nor an untouched parameter"),
]

HEAD = re.compile(r"@duty 1  (\S+)  total (\d+)  goals (\d+)  refused (\d+)")
LINE = re.compile(r"^  (\S+) \((\d+)\): ")


def lies_kopf(text):
    """`(total, goals, refused)` off the header, or `None` when there is none."""
    m = HEAD.search(text)
    return (int(m.group(2)), int(m.group(3)), int(m.group(4))) if m else None


def sprechprobe():
    """**In both directions: a lying balance must fall, an honest one must not.**

    The whole verdict of this tool rests on one arithmetic check, and *a check nobody has
    seen fail is a decoration* (R11). So the check is run first against two hand-made
    headers -- one that adds up and one that does not.
    """
    gut = "        @duty 1  x.gab  total 4  goals 1  refused 3\n"
    gift = "        @duty 1  x.gab  total 4  goals 1  refused 1\n"
    stumm = "        nothing here about itself\n"
    a = lies_kopf(gut)
    b = lies_kopf(gift)
    c = lies_kopf(stumm)
    ok_gut = a is not None and a[1] + a[2] == a[0]
    ok_gift = b is not None and b[1] + b[2] != b[0]
    ok_stumm = c is None
    print("== Sprechprobe ==")
    print("  ehrliche Bilanz geht durch:  %s" % ("ja" if ok_gut else "NEIN"))
    print("  luegende Bilanz faellt:      %s" % ("ja" if ok_gift else "NEIN"))
    print("  fehlender Kopf faellt:       %s" % ("ja" if ok_stumm else "NEIN"))
    return ok_gut and ok_gift and ok_stumm


def main() -> int:
    per_file = "--je-datei" in sys.argv
    if not sprechprobe():
        print("== P6: der Waechter misst nicht ==")
        return 2
    if not GABBRO.exists():
        print(f"ABBRUCH: {GABBRO} fehlt -- gebaut wird auf ki-pc-fisch-101 (CLAUDE.md).")
        return 1
    files = sorted(glob.glob(str(W / "beispiele" / "*.gab"))) + sorted(
        glob.glob(str(W / "messung" / "*" / "*.gab"))
    )
    total = goals = refused = 0
    no_register = 0
    per_reason: collections.Counter = collections.Counter()
    table = []
    for f in files:
        rel = str(pathlib.Path(f).relative_to(W))
        try:
            run = subprocess.run(
                [str(GABBRO), "pflichten", "--isabelle", rel],
                cwd=W,
                capture_output=True,
                text=True,
                timeout=FRIST,
            )
        except subprocess.TimeoutExpired:
            print(f"ABBRUCH: {rel} -- Frist {FRIST} s ueberschritten. Ein Haenger ist kein Befund.")
            return 1
        # **A unit with errors carries no register**, and that is the same rule
        # `gabbro pflichten` follows -- not a skipped file but a file that has no answer yet.
        if run.returncode != 0:
            no_register += 1
            continue
        kopf = lies_kopf(run.stdout)
        if kopf is None:
            print(f"ABBRUCH: {rel} -- kein `@duty`-Kopf. Der Erzeuger schweigt ueber sich selbst.")
            return 1
        t, g, a = kopf
        if g + a != t:
            print(f"ABBRUCH: {rel} -- {g} + {a} != {t}. Die Bilanz des Erzeugers geht nicht auf.")
            return 1
        total += t
        goals += g
        refused += a
        for line in run.stdout.splitlines():
            m = LINE.match(line)
            if m:
                per_reason[m.group(1)] += int(m.group(2))
        if t:
            table.append((rel, t, g, a))

    print()
    print("-- P6: der Bestand, wie ein BEWEISER ihn sieht --")
    print()
    if per_file:
        for rel, t, g, a in table:
            print(f"   {rel:<44} {t:>3} gesamt  {g:>3} Ziele  {a:>3} abgesagt")
        print()
    width = max(len(r) for r, _ in REASONS)
    for reason, sentence in REASONS:
        print(f"   {reason:<{width}}  {per_reason.get(reason, 0):>3}   {sentence}")
    unknown = set(per_reason) - {r for r, _ in REASONS}
    for u in sorted(unknown):
        print(f"   {u:<{width}}  {per_reason[u]:>3}   UNKNOWN -- dieses Werkzeug kennt ihn nicht")
    sum_reasons = sum(per_reason.values())
    print()
    print(f"== P6: {total} Pflichten, {goals} Ziele, {refused} abgesagt "
          f"({no_register} Einheiten mit Fehlern, ohne Register; "
          f"{len(files)} Dateien angesehen) ==")
    if sum_reasons != refused:
        print(f"ABBRUCH: die Gruende summieren zu {sum_reasons}, abgesagt sind {refused}.")
        return 1
    if unknown:
        return 1
    print("   Und was das NICHT heisst: ein Ziel ist keine bewiesene Pflicht. Es heisst,")
    print("   dass die Pflicht GESCHLOSSEN dasteht -- jede Voraussetzung, die sie braucht,")
    print("   steht in derselben Datei. Ob sie durchgeht, sagt `isabelle build`, und der")
    print("   Weg dorthin ist `./instrumente/pruefe-p6-beweis.sh`.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
