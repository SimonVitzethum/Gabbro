#!/usr/bin/env python3
"""**Does a carrier a BODY addresses stand in the place dictionary of the same export?**

`gabbro lean` writes two things about a table's slot fields, and it writes them from two
different names:

  * `places` / `wellFormed` come from `dictionary(&tab)` -- the TABLE names, `"Kappenraum"`.
  * a body's `.place "c" i "benutzt"` comes from `field_shape`, which returns the SOURCE
    name of the base -- the parameter `c`, never the table it points at.

`Gabbro.Body.Place.slot` carries the carrier as a `String`, so `.slot "c" k f` and
`.slot "Kappenraum" k f` are DIFFERENT places. Where a routine reaches its table through a
pointer parameter, `wellFormed` therefore constrains no cell the body touches -- and a
hand-written specification written against `places` speaks about a part of the world the
program never writes.

`instrumente/pruefe-lean-programm.sh` holds a SPECIFICATION's places against the dictionary.
Nothing holds the BODY's against it. This tool does.

    ./instrumente/miss-lean-traeger.py                 over `beispiele/` and `messung/*/`

It builds nothing; it calls an existing `target/debug/gabbro` (CLAUDE.md).
"""
import collections
import pathlib
import re
import subprocess
import sys

W = pathlib.Path(__file__).resolve().parent.parent
GABBRO = W / "target" / "debug" / "gabbro"
FRIST = 120

PLACE_DEF = re.compile(r"^def (places|fields) .*:=$")
DICT_ROW = re.compile(r'\("([^"]+)", "([^"]+)", "[^"]+"\)')
BODY_SLOT = re.compile(r'\(\.place "([^"]+)" ')
BODY_FIELD = re.compile(r'\(\.fieldOf "([^"]+)" ')


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

    n_export = 0
    n_mit_koerper = 0
    n_sauber = 0
    n_fremd = 0
    fremde: collections.Counter = collections.Counter()
    stellen_gesamt = 0
    stellen_fremd = 0
    beispiele = []
    for rel in dateien:
        r = subprocess.run(
            [str(GABBRO), "lean", rel], cwd=W, capture_output=True, text=True, timeout=FRIST
        )
        if r.returncode != 0:
            continue
        n_export += 1
        # The dictionary: every `(carrier, field, shape)` row of `places` and `fields`.
        traeger = set()
        in_dict = False
        for zeile in r.stdout.splitlines():
            if PLACE_DEF.match(zeile):
                in_dict = True
                continue
            if in_dict:
                m = DICT_ROW.search(zeile)
                if m:
                    traeger.add(m.group(1))
                elif zeile.startswith("  ]") or zeile.strip() == "[]":
                    in_dict = False
        # Every carrier a BODY addresses. Only `_body` lines carry `.place`/`.fieldOf`
        # written by `block_term`; the `_pre`/`_post` conjuncts carry them too and are
        # counted, because a precondition over an unreachable cell is the same hazard.
        benutzt: collections.Counter = collections.Counter()
        for zeile in r.stdout.splitlines():
            for t in BODY_SLOT.findall(zeile):
                benutzt[t] += 1
            for t in BODY_FIELD.findall(zeile):
                benutzt[t] += 1
        if not benutzt:
            continue
        n_mit_koerper += 1
        stellen_gesamt += sum(benutzt.values())
        hier_fremd = {t: n for t, n in benutzt.items() if t not in traeger}
        if hier_fremd:
            n_fremd += 1
            fremde.update(hier_fremd)
            stellen_fremd += sum(hier_fremd.values())
            if len(beispiele) < 12:
                beispiele.append((rel, sorted(traeger), sorted(hier_fremd)))
        else:
            n_sauber += 1

    print("== Carriers a BODY addresses, against the dictionary of the SAME export ==")
    print()
    print(f"   files with an export:                {n_export}")
    print(f"   of those, with at least one place:   {n_mit_koerper}")
    print(f"   every carrier IS in the dictionary:  {n_sauber}")
    print(f"   at least one carrier is NOT:         {n_fremd}")
    print()
    print(f"   place mentions in bodies/clauses:    {stellen_gesamt}")
    print(f"   of those, carrier NOT declared:      {stellen_fremd}")
    print()
    print("-- the undeclared carriers, by name --")
    for t, n in fremde.most_common(30):
        print(f"   {t:<24}{n:>5}")
    print()
    print("-- examples --")
    for rel, decl, fremd in beispiele:
        print(f"   {rel}")
        print(f"     dictionary: {', '.join(decl) or '(empty)'}")
        print(f"     addressed but not in it: {', '.join(fremd)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
