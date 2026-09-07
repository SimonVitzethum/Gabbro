#!/usr/bin/env python3
"""**What the checker DEMANDS, measured by striking the ceremony out and re-running.**

    ./instrumente/miss-zeremoniedifferenz.py [narrow|ranges|effects|costs|alle]
                                            [--stellen] [--selbstprobe]

THE PROBLEM THIS EXISTS FOR
---------------------------
Over the 70 tracked clean examples `gabbro pruefe` says `0 errors` on all seventy. **A
correct program raises no diagnostic**, so "what does the checker demand of its user?"
cannot be read off a run at all. It has to be measured against a perturbation: remove one
class of clause from every file, run the checker again, and count what it then says.

Each diagnostic that appears is a place where the removed clause was LOAD-BEARING -- the
user wrote it because the checker would otherwise have refused.

NOT THE SAME QUESTION AS `zaehle-zeremonie.py`, AND THE DIFFERENCE IS THE POINT (W7)
------------------------------------------------------------------------------------
That tool asks *"does this fact stand a SECOND time in this unit?"* -- redundancy, a
property of the text. This one asks *"if it did not stand at all, would the checker
complain?"* -- necessity, a property of the passes. **A clause can be non-redundant and
still not demanded**, and `costs` is exactly that case: 238 of them come out of the corpus
and 12 diagnostics come back, 7 of them `A003` on `asm` bodies, which is a different rule.
Neither number replaces the other and they are never to be added.

WHAT THIS TOOL DOES NOT MEASURE, SAID AT THE TOOL AND NOT IN A FOOTNOTE
-----------------------------------------------------------------------
**A demand is not plumbing.** Striking the declared range off a counter makes `x += 1`
genuinely able to overflow, so the `M104` that comes back is CORRECT and the site belongs to
the user's own logic. *This tool measures how much the corpus DEPENDS on its clauses, not
how much of it a compiler could have proved.* Reading the second off the first is the
mistake `messung/KLEMPNEREI-2026-09-07.md` §7 was written to stop.

AND THE STRIPPERS ARE TEXTUAL, SO THEY DAMAGE SOME FILES
--------------------------------------------------------
`P001` in the output is the tool's own wound, not a finding: the `ranges` stripper eats the
`=` of a `type X = T in a .. b` declaration, and the grammar REQUIRES `effects` at four
positions (`progress`, `falsifier`), so removing it there is a parse error rather than a
demand. **Those counts are printed separately and never folded into the total** -- a file
that did not parse says nothing about any pass behind the reader.

*Every file is run and every code is counted.* No `set -e`, no stop at the first hit: a
measurement that stops there answers "does at least one fire", not "which fire".
"""
import collections
import pathlib
import re
import subprocess
import sys

WURZEL = pathlib.Path(__file__).resolve().parent.parent
GABBRO = WURZEL / "target/release/gabbro"
# **Every run under a deadline.** A hang looks like "still going", not like a finding.
FRIST = 600


def dateien():
    """The 70 tracked clean examples -- the denominator, and it is stated once."""
    r = subprocess.run(
        ["git", "ls-files", "beispiele/*.gab"],
        cwd=WURZEL, capture_output=True, text=True, check=True,
    )
    return [p for p in r.stdout.split() if "/gift/" not in p]


def ohne_narrow(text):
    """Every `narrow` statement and its `else` block. Counted by braces, not by indent."""
    aus, zeilen, i, n = [], text.splitlines(keepends=True), 0, 0
    while i < len(zeilen):
        if re.match(r"\s*narrow\s", zeilen[i]):
            n += 1
            tiefe = zeilen[i].count("{") - zeilen[i].count("}")
            i += 1
            while i < len(zeilen) and tiefe > 0:
                tiefe += zeilen[i].count("{") - zeilen[i].count("}")
                i += 1
            continue
        aus.append(zeilen[i])
        i += 1
    return "".join(aus), n


def ohne_bereiche(text):
    """`u32 in 0 .. 100` becomes a bare `u32` -- the declared range, widened away."""
    n = 0

    def sub(m):
        nonlocal n
        n += 1
        return m.group(1)

    # **`=` belongs in the stop set, and leaving it out cost the first run four files.**
    # `let a : u32 in 0 .. 100 = 1;` swallowed `100 = 1` up to the `;` and left `let a : u32;`
    # -- a source the reader refuses with `P001`, and four `P001` is exactly what the first
    # measurement reported. *The speech test found it; reading the pattern had not.*
    pat = re.compile(
        r"\b(u8|u16|u32|u64|i8|i16|i32|i64|usize|isize|f32|f64)\s+in\s+"
        r"[^,;){}=\n]+?(?=\s*(?:,|;|\)|\{|\}|=|$|--))"
    )
    return pat.sub(sub, text), n


def ohne_wirkungen(text):
    """Every `effects { … }` clause, brace-counted."""
    n, aus, i = 0, [], 0
    while i < len(text):
        m = re.compile(r"effects\s*\{").search(text, i)
        if not m:
            aus.append(text[i:])
            break
        aus.append(text[i:m.start()])
        n += 1
        tiefe, j = 1, m.end()
        while j < len(text) and tiefe > 0:
            if text[j] == "{":
                tiefe += 1
            elif text[j] == "}":
                tiefe -= 1
            j += 1
        i = j
    return "".join(aus), n


def ohne_kosten(text):
    """Every `costs <= N ops` clause. `retry … bounded N ops` is a different production."""
    n = 0

    def sub(_):
        nonlocal n
        n += 1
        return ""

    return re.compile(r"costs\s+<=\s*[^\n]*?ops").sub(sub, text), n


VARIANTEN = {
    "narrow": (ohne_narrow, "`narrow … else` statements"),
    "ranges": (ohne_bereiche, "declared integer and float ranges"),
    "effects": (ohne_wirkungen, "`effects { … }` clauses"),
    "costs": (ohne_kosten, "`costs <= N ops` clauses"),
}

ZEILE = re.compile(r"(error|warning|hint): \[([A-Z][0-9]{3})\] .*?:(\d+):(\d+): (.*)")


def messe(welche, stellen):
    fn, was = VARIANTEN[welche]
    codes, orte, entfernt = collections.Counter(), [], 0
    tmp = WURZEL / "target" / "zeremoniedifferenz"
    tmp.mkdir(parents=True, exist_ok=True)
    for d in dateien():
        neu, k = fn((WURZEL / d).read_text())
        entfernt += k
        if k == 0:
            continue
        ziel = tmp / pathlib.Path(d).name
        ziel.write_text(neu)
        # **Visibly abort rather than count zero** (R14a): if the checker does not run,
        # that is not a result of zero demands, it is no result.
        r = subprocess.run(
            [str(GABBRO), "pruefe", str(ziel)],
            capture_output=True, text=True, timeout=FRIST,
        )
        for line in (r.stdout + r.stderr).splitlines():
            m = ZEILE.match(line)
            if m:
                codes[m.group(2)] += 1
                orte.append((d, m.group(2), m.group(3), m.group(5)))
    kaputt = codes.pop("P001", 0)
    print(f"== {welche}: {entfernt} {was} removed from {len(dateien())} files ==")
    for c, n in codes.most_common():
        print(f"   {c}  {n}")
    print(f"   -- {sum(codes.values())} diagnostics the checker DEMANDED")
    if kaputt:
        print(f"   -- and {kaputt} `P001`: the stripper damaged the SOURCE, not a finding.")
        print("      Those files did not parse, so nothing behind the reader ran in them.")
    if stellen:
        for d, c, z, t in orte:
            print(f"      {d}:{z}\t{c}\t{t}")
    return sum(codes.values()), kaputt


def selbstprobe():
    """**Both directions, on sources this run brings along** -- `--selbstprobe`.

    A stripper that silently removes nothing reports zero demands, and **zero reads exactly
    like a clean corpus**. That is `W17`, success without work, and it is the failure this
    tool is most exposed to: every one of its four strippers is a regular expression over
    text, and a grammar change would retire one without a word.

    So the probe is not "does it run": it plants a source that MUST lose a clause and one
    that must NOT, and checks the count both ways.
    """
    faelle = [
        ("narrow", "    narrow x to 0 .. 3 else { return 0; }\n", "    return 0;\n"),
        ("ranges", "let a : u32 in 0 .. 100 = 1;\n", "let a : u32 = 1;\n"),
        ("effects", "effects { pure }\n", "costs <= 4 ops\n"),
        ("costs", "costs <= 4 ops\n", "effects { pure }\n"),
    ]
    ergebnisse = []
    for welche, mit, ohne in faelle:
        fn, _ = VARIANTEN[welche]
        _, k_mit = fn(mit)
        _, k_ohne = fn(ohne)
        ergebnisse.append((f"`{welche}` sieht seine Klausel:      {k_mit}", k_mit == 1))
        ergebnisse.append((f"`{welche}` sieht eine FREMDE nicht:  {k_ohne}", k_ohne == 0))
    # And the range stripper must WIDEN rather than delete -- a stripper that eats the type
    # leaves a source no pass can read, and every later count is then about the wound.
    weit, _ = ohne_bereiche("let a : u32 in 0 .. 100 = 1;\n")
    ergebnisse.append((f"`ranges` weitet statt zu loeschen: {weit.strip()}",
                       weit.strip() == "let a : u32 = 1;"))
    print("== Sprechprobe ==")
    alles_gut = True
    for was, ok in ergebnisse:
        print(f"  {was}  --  {'ok' if ok else 'GESCHEITERT'}")
        alles_gut &= ok
    if not alles_gut:
        print("  SPRECHPROBE GESCHEITERT -- dieses Werkzeug misst NICHTS. Kein Lauf.")
        return 2
    print("  beide Richtungen an mitgebrachten Quellen, ohne den Korpus zu fragen.")
    return 0


def main():
    if not GABBRO.exists():
        print(f"ABBRUCH: {GABBRO} is not there -- build first, then measure.")
        return 2
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    stellen = "--stellen" in sys.argv
    # **The probe runs FIRST, and a fallen probe stops the run.** A stripper that has
    # stopped matching reports zero demands, and zero reads like a clean corpus (W17).
    if (r := selbstprobe()) != 0:
        return r
    print()
    if "--selbstprobe" in sys.argv:
        return 0
    welche = args[0] if args else "alle"
    if welche == "alle":
        for w in VARIANTEN:
            messe(w, stellen)
            print()
    elif welche in VARIANTEN:
        messe(welche, stellen)
    else:
        print(f"unknown variant `{welche}` -- one of {', '.join(VARIANTEN)}, or `alle`")
        return 2
    print("   And what that does NOT mean: a demanded clause is not PLUMBING. Removing a")
    print("   declared range lets the arithmetic genuinely overflow, so the `M104` that")
    print("   comes back is right. This tool measures DEPENDENCE, not derivability.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
