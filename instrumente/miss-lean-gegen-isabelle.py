#!/usr/bin/env python3
"""**Two exporters over ONE register: where do they disagree?**

`gabbro pflichten --lean` and `gabbro pflichten --isabelle` walk the SAME obligation list --
`lean::verdicts` and `refinement::verdicts` both run over `pflichten::sammle`, in the same
order, and both number the entries `duty_1 …`. So every obligation has two verdicts and they
can be laid side by side.

The cross table this tool prints is the seam nobody had measured:

    goal / goal        both channels state it
    goal / refused     Lean carries it, Isabelle does not
    refused / goal     Isabelle carries it, Lean does not
    refused / refused  neither -- and then: do they name the SAME thing?

**And one documented CLAIM is checked against it.** `LeanReason::CallSite` carries the
sentence *"a precondition at a call site -- the Isabelle channel carries these"*. That is a
statement about the OTHER channel, and nothing held it. This tool does: of every obligation
the Lean channel refuses as `call-site`, it counts how many the Isabelle channel really
turns into a goal.

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

# A refusal block heading: `  lock-witness (2): …`, then indented `    duty_9  V  …` lines.
KOPF = re.compile(r"^  ([a-z][a-z-]+) \((\d+)\): ")
ZEILE = re.compile(r"^    (duty_\d+)\s+([A-Z])\s+(.*)$")
# A goal, in either channel. Lean: `theorem duty_3 …`. Isabelle: `lemma duty_1:` / `theorem`.
GOAL = re.compile(r"^(?:theorem|lemma) (duty_\d+)\b")


def urteile(rel, flag):
    """`{duty_N: ("goal", None) | ("refused", tag)}` for one unit, or `None` with no register."""
    r = subprocess.run(
        [str(GABBRO), "pflichten", flag, rel],
        cwd=W,
        capture_output=True,
        text=True,
        timeout=FRIST,
    )
    if r.returncode != 0:
        return None
    out = {}
    grund = None
    for zeile in r.stdout.splitlines():
        m = KOPF.match(zeile)
        if m:
            grund = m.group(1)
            continue
        m = ZEILE.match(zeile)
        if m and grund:
            out[m.group(1)] = ("refused", grund, m.group(2), m.group(3))
            continue
        m = GOAL.match(zeile)
        if m:
            out[m.group(1)] = ("goal", None, None, None)
    return out


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

    kreuz: collections.Counter = collections.Counter()
    paar: collections.Counter = collections.Counter()
    nur_lean = []
    nur_isa = []
    beide_ab = 0
    n_dateien = 0
    for rel in dateien:
        a = urteile(rel, "--lean")
        b = urteile(rel, "--isabelle")
        if a is None or b is None:
            continue
        if set(a) != set(b):
            print(f"ABORT: {rel} -- the two channels number the register differently: "
                  f"{sorted(set(a) ^ set(b))}. They were supposed to walk one list.")
            return 2
        n_dateien += 1
        for d in sorted(a, key=lambda x: int(x.split("_")[1])):
            la, lt = a[d][0], a[d][1]
            ia, it = b[d][0], b[d][1]
            kreuz[(la, ia)] += 1
            if la == "goal" and ia == "refused":
                nur_lean.append((rel, d, it, b[d][2], b[d][3]))
            elif la == "refused" and ia == "goal":
                nur_isa.append((rel, d, lt, a[d][2], a[d][3]))
            elif la == "refused" and ia == "refused":
                beide_ab += 1
                paar[(lt, it)] += 1

    ges = sum(kreuz.values())
    print(f"== {ges} obligations over {n_dateien} unit(s), two verdicts each ==")
    print()
    print(f"   {'':<12}{'isabelle goal':>16}{'isabelle refused':>20}")
    print(f"   {'lean goal':<12}{kreuz[('goal','goal')]:>16}{kreuz[('goal','refused')]:>20}")
    print(f"   {'lean refus':<12}{kreuz[('refused','goal')]:>16}"
          f"{kreuz[('refused','refused')]:>20}")
    print()
    print(f"   only Lean states it:     {len(nur_lean)}")
    print(f"   only Isabelle states it: {len(nur_isa)}")
    print(f"   neither:                 {beide_ab}")
    print()
    print("-- the pair of reasons, where BOTH refuse --")
    print(f"   {'lean':<26}{'isabelle':<26}{'n':>5}")
    for (lt, it), n in paar.most_common():
        mark = "" if lt == it else "   <- different names"
        print(f"   {lt:<26}{it:<26}{n:>5}{mark}")
    print()
    print("-- what only ISABELLE states (Lean refuses it) --")
    for rel, d, lt, art, txt in nur_isa[:40]:
        print(f"   {rel:<44} {d:<9} {art}  lean says `{lt}`   {txt}")
    if len(nur_isa) > 40:
        print(f"   … and {len(nur_isa) - 40} more")
    print()
    print("-- the CLAIM at `LeanReason::CallSite`: \"the Isabelle channel carries these\" --")
    cs_goal = sum(1 for (lt, _), n in [] for _ in range(0))
    cs = collections.Counter()
    for (lt, it), n in paar.items():
        if lt == "call-site":
            cs[it] += n
    cs_isa_goal = sum(1 for r, d, lt, a_, t in nur_isa if lt == "call-site")
    ges_cs = sum(cs.values()) + cs_isa_goal
    print(f"   obligations Lean refuses as `call-site`: {ges_cs}")
    print(f"   of those, a GOAL in the Isabelle channel: {cs_isa_goal}")
    for it, n in cs.most_common():
        print(f"   of those, refused by Isabelle as `{it}`: {n}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
