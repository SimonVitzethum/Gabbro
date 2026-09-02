#!/usr/bin/env python3
"""**How far does `gabbro lean` reach over an ARBITRARY program?**

`instrumente/zaehle-lean.py` counts the OBLIGATION channel (`gabbro pflichten --lean`):
goals and named refusals over the register Gabbro itself states. This tool counts the other
half -- `gabbro lean`, the PROGRAM export, which carries no specification and against which a
hand-written Lean specification is held.

The two are different denominators and were never counted together. What this tool adds up,
per file and over the corpus:

  * how many `.gab` files the export ACCEPTS at all (a file with errors carries none),
  * per accepted file: `routines`, `bodies`, `refused`, `places` off the `@program` header,
  * every REFUSED routine with its `LeanReason` tag,
  * every DROPPED `requires` conjunct and every NOT SAID `ensures` conjunct, by tag.

**A routine is all-or-nothing.** `lean::routines` calls `block_term` over the whole body and
files the FIRST form it cannot render as the reason for the entire routine -- so `bodies` is
a count of routines, never of statements, and a routine of forty statements with one `+=`
in it lands in `refused` exactly like a routine of one.

This tool builds nothing; it calls an existing `target/debug/gabbro` (CLAUDE.md).
"""
import collections
import json
import pathlib
import re
import subprocess
import sys

W = pathlib.Path(__file__).resolve().parent.parent
GABBRO = W / "target" / "debug" / "gabbro"
FRIST = 120

KOPF = re.compile(
    r"@program 1  units (\d+)  routines (\d+)  bodies (\d+)  refused (\d+)  places (\d+)"
)
REFUSED = re.compile(r"^-- REFUSED  (\S+)  \(([a-z-]+)\): ")
# `requires #1 (quantified), requires #2 (builtin)` -- the list is comma separated and may
# wrap over lines, so the tags are picked up one by one rather than by splitting the line.
TAG = re.compile(r"(requires|ensures) #(\d+) \(([a-z-]+)\)")


def lauf(argv):
    return subprocess.run(
        [str(GABBRO)] + argv, cwd=W, capture_output=True, text=True, timeout=FRIST
    )


def main() -> int:
    if not GABBRO.exists():
        print(f"ABORT: {GABBRO} is missing -- it is built on ki-pc-fisch-101 (CLAUDE.md).")
        return 2
    muster = [a for a in sys.argv[1:] if not a.startswith("--")] or [
        "beispiele/*.gab",
        "messung/*/*.gab",
    ]
    dateien = []
    for m in muster:
        dateien.extend(sorted(str(p.relative_to(W)) for p in W.glob(m)))
    if not dateien:
        print("ABORT: the globs chose nothing -- nothing was measured.")
        return 2

    ohne = []
    tafel = []
    gruende: collections.Counter = collections.Counter()
    vor_ab: collections.Counter = collections.Counter()
    nach_ab: collections.Counter = collections.Counter()
    s_routinen = s_koerper = s_orte = 0
    s_vor_getragen = s_nach_getragen = 0

    for rel in dateien:
        r = lauf(["lean", rel])
        if r.returncode != 0:
            ohne.append(rel)
            continue
        m = KOPF.search(r.stdout)
        if m is None:
            print(f"ABORT: {rel} -- no `@program` header. The emitter is silent about itself.")
            return 2
        _, routinen, koerper, abgelehnt, orte = (int(x) for x in m.groups())
        if koerper + abgelehnt != routinen:
            print(f"ABORT: {rel} -- {koerper} + {abgelehnt} != {routinen}.")
            return 2
        hier_ref: collections.Counter = collections.Counter()
        for zeile in r.stdout.splitlines():
            mm = REFUSED.match(zeile)
            if mm:
                hier_ref[mm.group(2)] += 1
        if sum(hier_ref.values()) != abgelehnt:
            print(
                f"ABORT: {rel} -- {sum(hier_ref.values())} REFUSED lines, header says "
                f"{abgelehnt}."
            )
            return 2
        gruende.update(hier_ref)
        # The dropped clauses. They are counted off the doc comments, which is where the
        # emitter writes them -- there is no header field for them, and that is itself a
        # finding: the balance line does not have to add up over the clauses.
        v = n = 0
        for art, _, tag in TAG.findall(r.stdout):
            if art == "requires":
                vor_ab[tag] += 1
                v += 1
            else:
                nach_ab[tag] += 1
                n += 1
        # What is CARRIED: `_pre`/`_post` conjuncts that come from a clause. A parameter
        # shape conjunct is not a clause, so it is not counted here -- it is a typing
        # hypothesis and it is read off the DECLARATION.
        vor_get = len(re.findall(r"eval s .* = some \(\.bool true\)", r.stdout))
        s_routinen += routinen
        s_koerper += koerper
        s_orte += orte
        s_vor_getragen += vor_get
        tafel.append((rel, routinen, koerper, abgelehnt, orte, v, n, vor_get))

    print(f"== `gabbro lean` over {len(dateien)} file(s) ==")
    print()
    print(f"   {'unit':<48} {'rout':>5} {'body':>5} {'refus':>6} {'place':>6} "
          f"{'req!':>5} {'ens!':>5} {'kept':>5}")
    for row in tafel:
        print(f"   {row[0]:<48} {row[1]:>5} {row[2]:>5} {row[3]:>6} {row[4]:>6} "
              f"{row[5]:>5} {row[6]:>5} {row[7]:>5}")
    print()
    print(f"   accepted: {len(tafel)} of {len(dateien)}   ({len(ohne)} with errors, no export)")
    print(f"   routines: {s_routinen}   bodies carried: {s_koerper}   "
          f"refused: {s_routinen - s_koerper}   places: {s_orte}")
    print(f"   clause conjuncts kept in `_pre`/`_post`: {s_vor_getragen}")
    print(f"   `requires` conjuncts DROPPED: {sum(vor_ab.values())}")
    print(f"   `ensures`  conjuncts NOT SAID: {sum(nach_ab.values())}")
    print()
    print("-- why a ROUTINE is refused --")
    for tag, n in gruende.most_common():
        print(f"   {tag:<26}{n:>5}")
    print()
    print("-- why a `requires` conjunct is dropped --")
    for tag, n in vor_ab.most_common():
        print(f"   {tag:<26}{n:>5}")
    print()
    print("-- why an `ensures` conjunct is not said --")
    for tag, n in nach_ab.most_common():
        print(f"   {tag:<26}{n:>5}")
    if "--json" in sys.argv:
        print("JSON " + json.dumps({
            "files": len(dateien), "accepted": len(tafel), "routines": s_routinen,
            "bodies": s_koerper, "places": s_orte, "reasons": dict(gruende),
            "pre_dropped": dict(vor_ab), "post_dropped": dict(nach_ab),
        }))
    return 0


if __name__ == "__main__":
    sys.exit(main())
