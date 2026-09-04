#!/usr/bin/env python3
"""**The `unfalsifiable` category -- counted against the corpus, and latched twice.**

`dokumente/UNFALSIFIZIERBAR.md` states the bar: which KINDS of reason make an assumption
genuinely unfalsifiable (`U1`, `U2`), which kinds do not (`R1`..`R4`), and a register in which
every `unfalsifiable` clause of the tree stands with its verdict.

WHY THE CATEGORY NEEDS A GUARDIAN AT ALL
----------------------------------------
`K100`'s open gate is `A = 19` against 44 assumptions. The grammar offers two ways to satisfy
`assume`: name a probe, or write a reason why none can exist. **The second is free.** If
"unfalsifiable with a reason" is a judgement call made while the classification runs, twenty
of the twenty-five surplus assumptions can become unfalsifiable one at a time, each with a
plausible sentence beside it, and the gate closes by being emptied rather than passed.

`dokumente/AUSNAHMEN.md` gives the shape of the answer, and this file copies it deliberately
rather than inventing a second one (`W7`): **a register that is COUNTED cannot grow in
silence, because growing it is a diff.**

WHAT IT HOLDS, AND WHY IT IS THREE THINGS AND NOT ONE
-----------------------------------------------------
1. **Set equality against the corpus.** The clauses are found by reading the `.gab` files and
   the checker's own generated entries; the register is read from the document. The two sets
   have to be equal. *A row cannot be created by editing a table, and a clause cannot be added
   without a row appearing.*
2. **Two ratchets.** The POPULATION may fall and not rise, and the ADMITTED count may fall and
   not rise. The second is the sharp one: it is the number that says how much of the trust
   surface no probe can ever reach.
3. **Every row's rule is defined in the document, and matches its verdict.** `ADMITTED` takes
   a `U`, `REFUSED` takes an `R`. *A reason invented at the moment of classification has
   nowhere to land.*

*Each alone is satisfiable by accident.* A pure count survives swapping one row for another; a
pure set comparison survives a register that doubles in size; a pure rule check survives a row
that names `U1` and means nothing of the sort.

WHAT IT DOES NOT DO
-------------------
**It does not decide whether a criterion was applied correctly.** That is the reader's work,
and the document keeps the argument for each row in prose beneath the table. What is excluded
is the pair of things a script can exclude: that the category grows without anybody seeing it,
and that a row stands under a rule nobody wrote down.

**And it reads the SITE softly.** A moved clause is reported as a drift notice rather than a
finding: line numbers in `beispiele/06-annahmen.gab` belong to whoever edits that file, and a
register that goes red because a neighbour added a comment would be measuring the wrong thing.
*The hard half -- the name is declared in the file the row names -- is checked.*

    ./instrumente/pruefe-unfalsifizierbar.py
"""
import re
import sys
from pathlib import Path

# **Whoever leaves mid-run says WHERE** -- the shared form, out of `abschnitt.py`.
sys.path.insert(0, str(Path(__file__).resolve().parent))
import abschnitt  # noqa: E402

W = Path(__file__).resolve().parent.parent
DOC = W / "dokumente" / "UNFALSIFIZIERBAR.md"
GENERATOR = W / "crates" / "gabbro-check" / "src" / "manifest.rs"

# **The booked size of the population.** Eight `unfalsifiable` clauses stand in the non-poison
# tree on 2026-09-04. Raising this is the diff the category exists to force.
MARK_POPULATION = 8

# **The booked size of the ADMITTED half** -- rows that a criterion of the document lets
# through. One: `ipi_kommt_an`, under `U2`. *This is the number that measures the category;
# the one above only measures how often the word was written.*
MARK_ADMITTED = 1

# **Construction sites of `Klasse::NichtFalsifizierbar` in `manifest.rs`.** Four on 2026-09-04:
# the enum variant, the one GENERATED entry (`sperrabdruckannahme`), the conversion out of the
# AST, and the display arm. Only a field initialiser (`klasse: Klasse::NichtFalsifizierbar`)
# is a generated entry, and that is what the scanner below looks for.
#
# *The count stands beside it because the scanner would be BLIND to a fifth site written in
# another shape* -- and a blind scanner over a shrunken population reads exactly like a clean
# tree (`W17`). If this breaks, the reader is not wrong, the reader is out of date.
MARK_RS_SITES = 4

# A row of the register: `| 1 | **name** | `site`:12 | ADMITTED | `U2` | 2026-09-04 |`
ROW = re.compile(r"^\|\s*\d+\s*\|\s*\*\*([A-Za-z_][A-Za-z_0-9]*)\*\*\s*\|"
                 r"\s*`([^`]+)`:(\d+)\s*\|\s*(ADMITTED|REFUSED)\s*\|"
                 r"\s*`([UR]\d)`\s*\|\s*(\d{4}-\d{2}-\d{2})\s*\|\s*$")

# A rule heading of the document: `### `U1` — the observation IS the violation`
RULE = re.compile(r"^###\s+`([UR]\d)`\s+")

# The declaration a `.gab` clause hangs under. `retires` carries the same tail but names no
# assumption of its own -- one is in the corpus and it uses `falsifier`, so an `unfalsifiable`
# that cannot be attributed is reported rather than dropped.
DECL = re.compile(r"^\s*(?:assume|axiom)\s+([A-Za-z_][A-Za-z_0-9]*)")


def corpus_files():
    """Every `.gab` outside `beispiele/gift/`, sorted.

    **The poison files are excluded on purpose.** A poison file is a program built to be
    refused; its assumptions are not part of anybody's trust surface, and six of them carry an
    `unfalsifiable` copied from the clean corpus for the sake of one rejected line.
    """
    # **The parts are taken RELATIVE to the tree**, and that is not a detail: an agent runs in
    # `…/Gabbro/.claude/worktrees/<id>/`, so an absolute path carries `.claude` in every one of
    # its `parts` and an absolute filter would exclude the whole corpus. *A guardian that
    # measures nothing prints the same `ALL PASS` as one that measures everything.*
    return sorted(p for p in W.rglob("*.gab")
                  if not {"gift", ".claude", "target"} & set(p.relative_to(W).parts))


def clauses_in(text, wo):
    """`(name, file, line)` for every `unfalsifiable` clause, plus the ones with no owner."""
    gefunden, waisen = [], []
    zeilen = text.splitlines()
    for i, z in enumerate(zeilen):
        if "unfalsifiable" not in z or z.lstrip().startswith("--"):
            continue
        name = None
        for j in range(i, max(-1, i - 14), -1):
            m = DECL.match(zeilen[j])
            if m:
                name = m.group(1)
                break
        (gefunden if name else waisen).append(
            (name, wo, i + 1) if name else (wo, i + 1))
    return gefunden, waisen


def generated(text):
    """The entries the CHECKER builds -- a field initialiser with a `name:` above it."""
    raus = []
    zeilen = text.splitlines()
    for i, z in enumerate(zeilen):
        if not re.match(r"^\s*klasse:\s*Klasse::NichtFalsifizierbar", z):
            continue
        for j in range(i, max(-1, i - 25), -1):
            m = re.match(r'^\s*name:\s*"([A-Za-z_][A-Za-z_0-9]*)"', zeilen[j])
            if m:
                raus.append((m.group(1), "crates/gabbro-check/src/manifest.rs", j + 1))
                break
    return raus


def sammle(dateien, rs_text):
    """The whole population, as `(name, file, line)`, plus the unattributable clauses."""
    alle, waisen = [], []
    for p in dateien:
        g, w = clauses_in(p.read_text(encoding="utf-8"), str(p.relative_to(W)))
        alle += g
        waisen += w
    alle += generated(rs_text)
    return sorted(alle), waisen


def rows(doc_text):
    """The register rows, as `(name, file, line, verdict, rule, date)`."""
    return [m.groups() for m in (ROW.match(z) for z in doc_text.splitlines()) if m]


def rules(doc_text):
    """The rule keys the document DEFINES with a heading of their own."""
    return {m.group(1) for m in (RULE.match(z) for z in doc_text.splitlines()) if m}


def pruefe(doc_text, population, rs_sites):
    """Returns the five findings, each a list, and the drift notices.

    `(missing_row, missing_clause, over_population, over_admitted, bad_rule, drift, sites)`
    """
    zeilen = rows(doc_text)
    bekannt = rules(doc_text)
    im_baum = {n: (f, l) for n, f, l in population}
    im_buch = {r[0]: r for r in zeilen}

    ohne_zeile = sorted(set(im_baum) - set(im_buch))
    ohne_klausel = sorted(set(im_buch) - set(im_baum))

    zuviel = max(0, len(zeilen) - MARK_POPULATION)
    anerkannt = [r for r in zeilen if r[3] == "ADMITTED"]
    zuviel_a = max(0, len(anerkannt) - MARK_ADMITTED)

    falsche_regel = []
    for n, _f, _l, urteil, regel, _d in zeilen:
        if regel not in bekannt:
            falsche_regel.append((n, regel, "no such rule in the document"))
        elif urteil == "ADMITTED" and not regel.startswith("U"):
            falsche_regel.append((n, regel, "ADMITTED needs a criterion, not a rejection"))
        elif urteil == "REFUSED" and not regel.startswith("R"):
            falsche_regel.append((n, regel, "REFUSED needs a rejection, not a criterion"))

    # The site: the FILE is hard, the LINE is a notice. See the head of this file.
    drift, falscher_ort = [], []
    for n, f, l, _u, _r, _d in zeilen:
        if n not in im_baum:
            continue
        wf, wl = im_baum[n]
        if wf != f:
            falscher_ort.append((n, f, wf))
        elif str(wl) != l:
            drift.append((n, l, wl))

    return (ohne_zeile, ohne_klausel, zuviel, zuviel_a, falsche_regel,
            falscher_ort, drift, len(zeilen), len(anerkannt),
            max(0, rs_sites - MARK_RS_SITES))


def sprechprobe(doc_text, population, rs_sites):
    """**R14, in both directions -- a guardian nobody has seen say no is an ornament.**

    Six poisons and one clean control. Every tooth gets one, because a tooth that never bites
    is indistinguishable from one that is not there.
    """
    proben = []

    def lauf(t, pop, sites=rs_sites):
        return pruefe(t, pop, sites)

    # ONE -- a ninth clause in the corpus with no row must be named.
    mehr = population + [("erfunden_zur_probe", "beispiele/00-probe.gab", 1)]
    ohne_z, _, _, _, _, _, _, _, _, _ = lauf(doc_text, mehr)
    proben.append(("a clause with no row is named", ohne_z == ["erfunden_zur_probe"]))

    # TWO -- a row whose clause is gone must fall, and the two directions are NOT the same
    # finding: one is a bin filling up, the other is a register going stale.
    weniger = [e for e in population if e[0] != "wbinvd"]
    _, ohne_k, _, _, _, _, _, _, _, _ = lauf(doc_text, weniger)
    proben.append(("a row with no clause is named", ohne_k == ["wbinvd"]))

    # THREE -- a ninth ROW must break the population ratchet.
    anker = "\n\n**8 rows of 8 clauses in the tree"
    neunte = doc_text.replace(
        anker,
        "\n| 9 | **erfunden** | `beispiele/00.gab`:1 | REFUSED | `R2` | 2026-09-04 |" + anker,
        1)
    _, _, zu, _, _, _, _, n9, _, _ = lauf(neunte, population)
    proben.append(("a ninth row breaks the population mark", zu == 1 and n9 == 9))

    # FOUR -- and the sharper ratchet has to bite at UNCHANGED size. Turning one refusal into
    # an admission is exactly the move this guardian exists for.
    gedreht = doc_text.replace("| REFUSED | `R2` |", "| ADMITTED | `U1` |", 1)
    _, _, zu4, zu4a, _, _, _, n4, a4, _ = lauf(gedreht, population)
    proben.append(("a REFUSED turned ADMITTED breaks the sharp mark at EQUAL size",
                   zu4 == 0 and zu4a == 1 and n4 == 8 and a4 == 2))

    # FIVE -- a rule the document does not define, and a verdict that contradicts its letter.
    erfunden = doc_text.replace("| REFUSED | `R2` |", "| REFUSED | `R9` |", 1)
    _, _, _, _, fr5, _, _, _, _, _ = lauf(erfunden, population)
    proben.append(("a rule the document does not define falls",
                   [f[1] for f in fr5] == ["R9"]))
    verdreht = doc_text.replace("| ADMITTED | `U2` |", "| ADMITTED | `R2` |", 1)
    _, _, _, _, fr6, _, _, _, _, _ = lauf(verdreht, population)
    proben.append(("an ADMITTED under a REJECTION falls",
                   [f[0] for f in fr6] == ["ipi_kommt_an"]))

    # SIX -- a fifth construction site in `manifest.rs` must say that the scanner may be blind.
    *_, blind = lauf(doc_text, population, rs_sites + 1)
    proben.append(("a new construction site in the checker is named", blind == 1))

    # SEVEN -- the control. Without it the six above also pass over a guardian that always
    # says no.
    oz, ok, z, za, fr, fo, _, _, _, bl = lauf(doc_text, population)
    proben.append(("the real register stays clear",
                   not oz and not ok and not z and not za and not fr and not fo and not bl))

    for was, ok_ in proben:
        print("  %-62s %s" % (was + ":", "yes" if ok_ else "NO"))
    return all(ok_ for _, ok_ in proben)


def main():
    # **TOOTH 0 -- the subject has to be there.** Over a missing document every check below
    # holds, and `ALL PASS` would be a verdict about nothing (`W17`).
    if not DOC.is_file() or not GENERATOR.is_file():
        fehlt = "dokumente/UNFALSIFIZIERBAR.md" if not DOC.is_file() \
            else "crates/gabbro-check/src/manifest.rs"
        print("ABBRUCH: `%s` is missing -- NOTHING was measured." % fehlt, file=sys.stderr)
        print("ABBRUCH: `%s` is missing -- NOTHING was measured." % fehlt)
        print("  Over a missing register all three teeth hold, and a green run would be a")
        print("  judgement about nothing.")
        return 2

    doc_text = DOC.read_text(encoding="utf-8")
    rs_text = GENERATOR.read_text(encoding="utf-8")
    rs_sites = rs_text.count("Klasse::NichtFalsifizierbar")
    population, waisen = sammle(corpus_files(), rs_text)

    print("== Speech test (R14) ==")
    if not sprechprobe(doc_text, population, rs_sites):
        print("== UNFALSIFIABLE: the guardian does not measure ==")
        return 2
    print()

    (ohne_zeile, ohne_klausel, zuviel, zuviel_a, falsche_regel,
     falscher_ort, drift, n_zeilen, n_anerkannt, blind) = pruefe(
        doc_text, population, rs_sites)

    if not n_zeilen:
        print("ABBRUCH: `dokumente/UNFALSIFIZIERBAR.md` carries NO row in the expected shape.",
              file=sys.stderr)
        print("ABBRUCH: `dokumente/UNFALSIFIZIERBAR.md` carries NO row in the expected shape.")
        print("  Either the register is empty -- then this run is a judgement about nothing")
        print("  -- or the table changed shape and this guardian no longer reads it.")
        print("  **Both are a finding, not a green run.**")
        return 2

    print("== The `unfalsifiable` clauses of the tree ==")
    im_buch = {r[0]: r for r in rows(doc_text)}
    for n, f, l in population:
        z = im_buch.get(n)
        print("  %-38s %-10s %s:%d" % (n, z[3] if z else "NO ROW", f, l))
    print("  ---------------------------------------------------------------")
    print("  %d clauses, %d rows, %d ADMITTED -- booked are %d and %d"
          % (len(population), n_zeilen, n_anerkannt, MARK_POPULATION, MARK_ADMITTED))
    print("  %d construction site(s) of `Klasse::NichtFalsifizierbar` in `manifest.rs`, "
          "booked are %d" % (rs_sites, MARK_RS_SITES))
    print()

    for n, gebucht, wirklich in drift:
        print("  NOTICE: `%s` moved from line %s to %d -- the row is stale, not wrong."
              % (n, gebucht, wirklich))
    if drift:
        print()

    abschnitt.fertig()

    fehler = 0
    if ohne_zeile:
        print("  CLAUSE WITHOUT A ROW: %s" % ", ".join(ohne_zeile))
        print("  An `unfalsifiable` stands in the tree that the register does not carry.")
        print("  **That is the category growing in silence** -- the one thing this guardian")
        print("  exists to make impossible. Classify it against the bar, then add the row.")
        fehler = 1
    if ohne_klausel:
        print("  ROW WITHOUT A CLAUSE: %s" % ", ".join(ohne_klausel))
        print("  The register names an assumption that carries no `unfalsifiable` any more.")
        print("  *This is the good direction and still a finding*: a register that keeps a")
        print("  row nobody can check reads like a measurement and is a memory.")
        fehler = 1
    if falscher_ort:
        for n, gebucht, wirklich in falscher_ort:
            print("  WRONG FILE: `%s` is booked in `%s` and stands in `%s`."
                  % (n, gebucht, wirklich))
        fehler = 1
    if zuviel:
        print("  RATCHET BROKEN: %d rows, booked are %d." % (n_zeilen, MARK_POPULATION))
        print("  **One `unfalsifiable` more is a decision, not a booking** -- ask, then")
        print("  raise `MARK_POPULATION` with its reason at the mark.")
        fehler = 1
    if zuviel_a:
        print("  SHARP RATCHET BROKEN: %d ADMITTED, booked are %d."
              % (n_anerkannt, MARK_ADMITTED))
        print("  This is the number that says how much of the trust surface no probe can")
        print("  ever reach. **`K100`'s gate `A = 19` is reachable by admitting rows here,")
        print("  and that is the failure the category was written against.**")
        fehler = 1
    if falsche_regel:
        for n, regel, warum in falsche_regel:
            print("  RULE DOES NOT HOLD: `%s` names `%s` -- %s." % (n, regel, warum))
        print("  A row stands under a rule the document defines, or it does not stand.")
        fehler = 1
    if blind:
        print("  THE READER MAY BE BLIND: %d construction site(s) of "
              "`Klasse::NichtFalsifizierbar`, booked are %d." % (rs_sites, MARK_RS_SITES))
        print("  A generated entry written in another shape is invisible to the scanner")
        print("  above, and a shrunken population reads exactly like a clean tree.")
        fehler = 1
    if waisen:
        for f, l in waisen:
            print("  UNATTRIBUTABLE: `%s`:%d carries an `unfalsifiable` under no `assume`"
                  " or `axiom`." % (f, l))
        fehler = 1

    if fehler:
        print("\n== UNFALSIFIABLE: FINDING ==")
        return 1

    print("== UNFALSIFIABLE: ALL PASS -- %d clauses, %d of them ADMITTED under a criterion =="
          % (len(population), n_anerkannt))
    print("   And what that does NOT mean: whether a criterion was applied CORRECTLY stands")
    print("   in the prose beneath the table and is decided by no script. Excluded is only")
    print("   that the category grows unseen, and that a row stands under a rule nobody")
    print("   wrote down.")
    return 0


if __name__ == "__main__":
    sys.exit(abschnitt.fahre(main))
