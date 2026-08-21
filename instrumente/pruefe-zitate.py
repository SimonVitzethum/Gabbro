#!/usr/bin/env python3
"""**A note that claims a check its rule does not perform.**

The class has now appeared twice with a name. On 2026-08-20 at `R003`: its note *spoke the
sentence* about the register offset, and no line did it -- `return d.NUR_W.A;` gave zero
errors. On 2026-08-21 in the emission layer: two comments in `emit.rs` cited `N027` and `N029`
as enforcing things they do not enforce. **The second one was found by re-reading, not by a
tool** -- and that is the whole reason this file exists.

    A comment that cites an identifier makes a claim about the CHECKER, not about the code
    it sits next to. An unchecked claim in a comment is worse than none: it is read as
    evidence.

## The rule, mechanically

Every identifier cited in a comment must either

  * be **issued in the same file** -- then the comment speaks about its own rule; or
  * be marked as a **foreign rule**, by naming the file it lives in, or by one of the
    connectives this folder already writes (*„same class as", „unlike", „is caught by"*).

Everything else is a candidate. **This is a candidate list, not a verdict** -- the same
framing as `pruefe-vergabe.py`, and for the same reason: whether a citation is a claim or a
cross-reference is a judgement, and a tool that guessed would be the silent answer this folder
writes against.

## The direction of its error

  * **false positive:** a legitimate cross-reference whose wording this file does not know;
  * **false negative (W10):** a claim about a rule that IS issued in the same file but says
    something else. *This tool cannot read.* `R003` -- the case that named the class -- would
    NOT be caught here, because its note and its rule sit in one file.

*That limit is the reason the mark below is a ratchet and not a target.* It measures the
cheap half; the expensive half stays with the reader.

    ./instrumente/pruefe-zitate.py            checks
    ./instrumente/pruefe-zitate.py --liste    every candidate with its line
"""
import pathlib
import re
import sys

W = pathlib.Path(__file__).resolve().parent.parent
FRIST = 120  # seconds; this tool executes nothing, the deadline covers the whole run.

# Where an identifier is ISSUED -- the same definition `pruefe-vergabe.py` uses. A register
# NAMES identifiers, it does not issue them.
VERGABE = re.compile(r'Absage::(?:fehler|hinweis|warnung)\s*\(\s*"([A-Z][0-9]{3})"')
NICHT = {"saetze.rs"}

# A citation in a comment: `M101` in backticks. Bare text is not counted -- `M101` without
# backticks is prose, and this folder writes its identifiers in backticks.
ZITAT = re.compile(r"`([A-Z][0-9]{3})`")

# **Connectives that mark a citation as a CROSS-REFERENCE rather than a claim.** They are
# taken from the wording this folder already uses; the list is closed and short on purpose --
# a long one would acquit everything.
FREMD = re.compile(
    r"\b(same class|dieselbe klasse|same shape|dieselbe gestalt|unlike|anders als|"
    r"wie bei|as at|siehe|see |vgl|is caught by|faengt|gefangen von|belongs to|"
    r"gehoert (zu|in)|lives in|steht in|\.rs\b|siblings?|schwester)", re.I)

MARKE = 230  # measured 2026-08-21; a ratchet, not a target -- it may fall, not rise


def vergeben():
    """File name -> set of identifiers issued in it."""
    aus = {}
    for q in sorted(W.glob("crates/*/src/*.rs")):
        if q.name in NICHT:
            continue
        aus[q.name] = set(VERGABE.findall(q.read_text(encoding="utf-8", errors="replace")))
    return aus


def erhebe(zusatz=None):
    """Candidates: (file, line, identifier, comment text)."""
    je_datei = vergeben()
    aus = []
    for q in sorted(W.glob("crates/*/src/*.rs")):
        if q.name in NICHT:
            continue
        text = q.read_text(encoding="utf-8", errors="replace")
        if zusatz and q.name == zusatz[0]:
            text += zusatz[1]
        eigene = je_datei.get(q.name, set())
        for n, zeile in enumerate(text.splitlines(), 1):
            s = zeile.strip()
            if not (s.startswith("//") or s.startswith("*")):
                continue
            if FREMD.search(s):
                continue
            for k in ZITAT.findall(s):
                if k not in eigene:
                    aus.append((q.name, n, k, s[:96]))
    return aus


def sprechprobe():
    """Both directions -- and the poison direction RECONSTRUCTS the real case.

    On 2026-08-21 `emit.rs` claimed `N027` and `N029`. `emit.rs` issues neither, and neither
    citation named a file. This probe puts exactly that line back.
    """
    echt = erhebe()
    gift = erhebe(zusatz=("emit.rs", "\n// the pass guarantees `N027` here, so nothing else has to\n"))
    a = len(gift) > len(echt)
    b = not any(d == "emit.rs" and k == "N027" for d, _, k, _ in echt)
    print("== Speech test, both directions ==")
    print("  reconstructed: %s" % ("ok (the false N027 citation is found)" if a
                                   else "FAILED -- the guardian does not see it"))
    print("  today's state: %s" % ("ok (the corrected comment passes)" if b
                                   else "FAILED -- false red"))
    return a and b


def main():
    # **Red on abort, not a quiet zero.** If the source tree cannot be read at all, this tool
    # must fall -- a guardian that reports „0 candidates" over an empty set is
    # indistinguishable from one that looked.
    if not list(W.glob("crates/*/src/*.rs")):
        print("ABORT: no checker sources found -- this is NOT a count of zero.")
        sys.exit(1)
    if not sprechprobe():
        sys.exit(2)
    kand = erhebe()
    je_datei = {}
    for d, _, _, _ in kand:
        je_datei[d] = je_datei.get(d, 0) + 1

    print("\n== Citations in comments that name a FOREIGN identifier: %d ==" % len(kand))
    if je_datei:
        schwer = sorted(je_datei.items(), key=lambda x: -x[1])[:6]
        print("   heaviest: " + ", ".join("%s %d" % (a, b) for a, b in schwer))
    print("   A comment citing an identifier makes a claim about the CHECKER. Where the")
    print("   identifier is issued elsewhere and the comment does not say so, the claim")
    print("   is unchecked -- and it is read as evidence.")

    if "--liste" in sys.argv:
        print("\n== Every candidate ==")
        for d, n, k, s in kand:
            print("  %s:%d  [%s]  %s" % (d, n, k, s))

    print("\n== And what this does NOT mean ==")
    print("  A candidate list, not a verdict: whether a citation is a claim or a")
    print("  cross-reference is a judgement. And the expensive half stays with the reader --")
    print("  a note about a rule that IS issued in the same file but says something else")
    print("  passes here. **`R003`, the case that named the class, would NOT be caught.**")

    schlecht = 0
    if MARKE is not None and len(kand) > MARKE:
        print("\n  RATCHET BROKEN: %d candidates, %d booked." % (len(kand), MARKE))
        schlecht = 1
    print("\n== Work done: %d files, %d issued identifiers, %d candidates, 2 probes ==" % (
        len(list(W.glob("crates/*/src/*.rs"))),
        sum(len(v) for v in vergeben().values()), len(kand)))
    return schlecht


if __name__ == "__main__":
    sys.exit(main())
