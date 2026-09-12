#!/usr/bin/env python3
"""**`A_p` -- the probe quota that replaces `K100`'s gate `A = 19`, with a floor it FAILS.**

`dokumente/SONDENDECKUNG.md` states the measure: `A_p` = falsifiable assumptions whose named
probe stands as a program in `sonden/`, over falsifiable assumptions. It carries the register
of all 38 rows, the four classes that say what a probe would need in order to exist, and the
derivation of the floor.

WHY A PROPORTION AND NOT A COUNT
--------------------------------
`A = 19` was 14 plus the five rebookings of `K100.2` -- a prediction of a delta, and it came
true on 2026-08-17. Since then its measurand grew, and `messung/AXIOMSCHICHT.md` §8.4 drew the
conclusion: **a target a new example file can miss is pointed the wrong way.** Under `A = 19`
the cheapest way to pass is to write fewer programs.

A count in the other direction has the same defect mirrored. So the guarded figure is a SHARE:
a new example file lifts no gate, and it may not dilute the quota either.

WHY A RATCHET IS NOT ENOUGH, AND THIS IS THE WHOLE POINT
--------------------------------------------------------
**A proportion-ratchet forbids regression and demands nothing.** Booked at today's 1 of 38 it
passes forever while nothing is written. So the quota carries a FLOOR as well, and the floor
is one this tree fails today -- `A_p = 0.026` against `1/8 = 0.125`.

*A bound the tree already meets is a decoration, not a gate.* This guardian is therefore RED
by construction, in the same way `pruefe-manifest.py` is, and it stays red until four userland
probes exist. The four are named in the document with what each one does.

THREE STATES, AND THE THIRD IS THE ONE NOBODY WATCHED
------------------------------------------------------
    unfalsifiable, under a criterion       6 clauses    `pruefe-unfalsifizierbar.py`, down
    falsifiable, probe stands as a program  1 of 38     here, up
    falsifiable, probe MISSING             37 of 38     nobody, until this file

A ratchet on the first does not fall when nobody writes a probe; a ratchet on the second only
rises when somebody does. **The state the tree is in is the one neither can see.**

BOTH DIRECTIONS OF THE SAME BROKEN CONNECTION
----------------------------------------------
A `falsifier` naming a probe that does not exist is an assurance about the ABSENCE of a
refutation. **A program in `sonden/` that no `falsifier` names is the same build type
reversed**, and `N024` -- a probe belongs to exactly ONE obligation -- has nothing to hold it
to. One of each stands in the tree today; both are booked here.

WHAT IT DOES NOT DO
-------------------
**It does not decide whether a probe would really refute its assumption.**
`instrumente/pruefe-sonden.sh` says the same of itself: what is measured is THAT one runs, not
WHAT ABOUT. And the class of a row is an estimate a reader may dispute -- `sonden/README.md`
says so about the table these classes are read from. Excluded is only what a script can
exclude: that the quota falls unseen, and that a row stands under a class nobody wrote down.

    ./instrumente/pruefe-sondendeckung.py
"""
import re
import sys
from collections import Counter
from pathlib import Path

# **Whoever leaves mid-run says WHERE** -- the shared form, out of `abschnitt.py`.
sys.path.insert(0, str(Path(__file__).resolve().parent))
import abschnitt  # noqa: E402
import korpus  # noqa: E402

W = Path(__file__).resolve().parent.parent
DOC = W / "dokumente" / "SONDENDECKUNG.md"
GENERATOR = W / "crates" / "gabbro-check" / "src" / "manifest.rs"
SONDEN = W / "sonden"

# **The booked quota, as a fraction -- numerator and denominator of the day it was booked.**
# The check is `covered * 38 >= falsifiable * 1`, so it is a comparison of shares and not of
# counts: adding an assumption WITH its probe passes, adding one without does not.
#
# *Raising this is the diff a written probe earns.* 1 of 38 on 2026-09-04, and **5 of 38 the
# same day**: `sonde_mxcsr_rne`, `sonde_keine_ueberbreite`, `sonde_tsc` and `sonde_rdtscp` were
# written, so the whole of class `P4` now stands as a program. *The raise is not a decision,
# it is the diff four programs earned* -- and it is the one move this mark exists to record.
#
# **5 of 39 since 2026-09-10, and this move is NOT earned.** `beispiele/71` dates one
# function, so the checker generates `frist_zaehle_werte_eingehalten` -- a falsifiable
# assumption whose probe (`sonde_tick`) stands as no program. The floor section foresaw
# exactly this dilution (`5 / 39 = 0.1282`, still above `1/8`), and the manifest carries
# the entry because omitting it would claim more than proved (the `stilllegung_` rule).
# What is NOT decided here is the metrology a date probe would need: falsifying a CYCLE
# count needs an ops-to-cycles map the tree refuses to write (D10) -- that is L4, a
# subproject, not a probe. Until it stands, every dated function costs share, and this
# mark records the cost instead of hiding it. *The next silent dilution from 39 breaks it
# again, which is what the mark is for.*
#
# **(5, 39) -> (6, 39) on 2026-09-10.** `sonde_tick` arrived WITH its program (measured
# p99 337-339 against booked 512, both R14 controls, one obligation N024), so the raise
# is earned the same way the four P4 probes earned theirs -- not a dilution decision.
# The metrology gap above stands unchanged: the probe reports cycles, it does not
# convert ops, and the date stays a sample (R15/W10), not a proof.
#
# **(6, 39) -> (9, 42) on 2026-09-10 (lane-59).** Lane-49's three parked P0 date probes
# (`sonde_abnahme`, `sonde_freigabe`, `sonde_byte_legen`) are bound by three `deadline`
# clauses in `beispiele/06` and `beispiele/25`, each WITH its program -- three earned
# diffs at once, same rule as `sonde_tick` (N = 10x the declared `costs` bound, the
# `beispiele/71` precedent: 500 -> 5000, here 4 -> 40 and 2 -> 20). The orphan mark falls
# back to 1; the metrology gap above still stands.
#
# **(13, 46) -> (17, 50) on 2026-09-10 (lane-80).** Four earned diffs at once: the next
# runnable date probes in `messung/FRIST-SONDEN-NOTIZ.md` order after lane-72's
# fence/write rows -- note rows 22-25 (`zaehle`, `takt_verteiler`, `bearbeite`,
# `ruf_verteiler` in `beispiele/59`), the lock-excluding `P3` rows whose timed body
# minus the unemitted lock runs in userland. Same 10x rule (8 -> 80, 40 -> 400).
# Ring-zero rows 7-10 and device rows 12-19 stay unprobed: `invlpg`/`outb` fault in
# ring 3 and no device stands on the bench. Orphan and outside marks unchanged.
#
# **(17, 50) -> (18, 51) on 2026-09-12 (lane S5, syscall).** One earned diff: the
# first per-call OS assumption (`linux_write_contract` in `beispiele/74`) arrives
# WITH its program (`sonden/sonde_write.c`, row 51, class `P4` userland -- a pipe
# stands in for the descriptor, the admitted errno is answered, `--kaputt` is
# the control that must fall). Same rule as every earned diff before it: the
# assumption and its probe land together, so the quota rises because the object
# grew, not because a rule was issued twice.
MARK_QUOTE = (18, 51)

# **The FLOOR -- and it is not a round number.** `dokumente/SONDENDECKUNG.md` derives it: five
# of the 38 rows are class `P4` (the probe needs nothing but a userland C program), and the
# work that is actually possible reaches 5 of 38 = 0.1316. **All five have a program since
# 2026-09-04, so the class is empty of open work and that ceiling is now also the state.**
# `1/8` = 0.125 is the largest unit fraction under that; `1/7` = 0.143 is already out of reach.
#
# **The tree stood at 1 of 38 = 0.026 and missed it by a factor of 4.75.** That was deliberate:
# a floor the tree already meets forbids nothing. **Since 2026-09-04 it stands at 5 of 38 =
# 0.1316 and MEETS the floor by 0.0066** -- three more falsifiable assumptions without a probe
# break it, and the ratchet above bites one earlier than that. *The floor may be RAISED and may
# not be lowered*, and there is no `P4` row left with which to reach a higher one.
BODEN = (1, 8)

# **The class whose probe needs NOTHING but a C compiler**, and the word the document has to
# use when it defines it. Tooth 7 asks whether the floor is still REACHABLE by writing every
# probe of this class -- and a class silently redefined would make that question meaningless.
FREI = "P4"
FREI_WORT = "userland"

# **Programs in `sonden/` that no `falsifier` names.** One on 2026-09-04:
# `sonde_release_sichtbarkeit`, built 2026-08-21 for an assumption the corpus books
# `unfalsifiable`. **A plain count and not a share** -- every program should be bound to an
# obligation, so the target is zero. May fall, not rise.
MARK_WAISEN = 1

# **Probe names in the non-poison corpus that stand OUTSIDE the register's corpus** --
# `messung/fragmente/`, `messung/proben/`, `messung/treiber/`. 13 on 2026-09-04, none with a
# program. The register's denominator is `beispiele/` plus the generated entries, and this
# number is what keeps that narrowing honest: *a figure left out of a quota has to be printed
# somewhere, or the quota measures the boundary instead of the tree.*
#
# **No 14th from `beispiele/71` (2026-09-10):** its `deadline` names `sonde_tick`, but the
# name attributes to `frist_zaehle_werte_eingehalten` (`klauseln_in`, deadline branch),
# so it stands INSIDE the assumption set, not outside it.
MARK_AUSSEN = 13

# **Construction sites of `Klasse::Falsifizierbar` in `manifest.rs`.** Five on 2026-09-04: the
# two GENERATED entries, the conversion out of the AST, and the two display arms. Only a
# field initialiser with a quoted `sonde:` under a `name:` is a generated entry, and that is
# what the scanner below looks for.
#
# *The count stands beside it because the scanner would be BLIND to a sixth site written in
# another shape* -- and a blind scanner over a shrunken population reads exactly like a covered
# tree (`W17`). If this breaks, the reader is not wrong, the reader is out of date.
MARK_RS_SITES = 5

# A row of the register: `| 1 | **name** | `sonde_x` | `P1` | -- |`
ROW = re.compile(r"^\|\s*\d+\s*\|\s*\*\*([A-Za-z_][A-Za-z_0-9]*)\*\*\s*\|"
                 r"\s*`([A-Za-z_][A-Za-z_0-9]*)`\s*\|\s*`(P\d)`\s*\|"
                 r"\s*(\*\*PROGRAM\*\*|--)\s*\|\s*$")

# A class definition of the document: `| **`P1`** | **ring 0** -- … | 14 |`
KLASSE = re.compile(r"^\|\s*\*\*`(P\d)`\*\*\s*\|\s*(.*?)\s*\|")

# The declaration a `falsifier` hangs under. `retires` names its assumption after the
# FUNCTION (`manifest.rs::stilllegungsannahmen`), so the search accepts both shapes and a
# clause that fits neither is reported rather than dropped.
DECL = re.compile(r"^\s*(?:assume|axiom)\s+([A-Za-z_][A-Za-z_0-9]*)")
FN = re.compile(r"^\s*(?:pub\s+)?fn\s+([A-Za-z_][A-Za-z_0-9]*)")
FALS = re.compile(r"\bfalsifier\s+([A-Za-z_][A-Za-z_0-9]*)")

# `pub const SONDEN_MIT_PROGRAMM: &[&str] = &["a", "b"];`
LISTE = re.compile(r"SONDEN_MIT_PROGRAMM[^=]*=\s*&\[(.*?)\]\s*;", re.S)

# **A construction site of the CLASS, and not of the AST variant it is built from.** A plain
# `count("Klasse::Falsifizierbar")` reads `AnnahmeKlasse::Falsifizierbar(i) =>
# Klasse::Falsifizierbar {` as TWO sites and would have booked six where there are five --
# *a mark that counts a substring measures the spelling, not the code.*
BAUSTELLE = re.compile(r"(?<![A-Za-z])Klasse::Falsifizierbar")


def korpus_dateien(unterordner):
    """The `.gab` files of a subtree, poison and worktrees excluded.

    **The parts are taken RELATIVE to the tree**, and that is not a detail: an agent runs in
    `…/Gabbro/.claude/worktrees/<id>/`, so an absolute path carries `.claude` in every one of
    its `parts` and an absolute filter would exclude the whole corpus. *A guardian that
    measures nothing prints the same `ALL PASS` as one that measures everything.*
    """
    wurzel = W / unterordner if unterordner else W
    if not wurzel.is_dir():
        return []
    # **The directory blacklist below fixed ONE incident, not the class** (2026-09-04,
    # `messung/K100-VERDICT-2026-09-04.md` §2): `arbeitsprotokoll/` was added after two
    # UNTRACKED scratch files there moved this guardian's population. Any OTHER untracked
    # `.gab`, anywhere the blacklist does not name, still would -- demonstrated by dropping
    # one at the repository root and watching this guardian abort with `ABGESCHNITTEN`
    # instead of its expected single finding. `korpus.verfolgt()` closes the class: a file
    # nobody `git add`ed is never part of the corpus, wherever it sits.
    return sorted(p for p in wurzel.rglob("*.gab")
                  if not {"gift", ".claude", "target",
                          "arbeitsprotokoll"} & set(p.relative_to(W).parts)
                  and korpus.verfolgt(p, W))


FN_BELEGT = re.compile(r"^\s*(?:pub\s+)?(?:impl\s+|spec\s+|extern\s+)?fn\s+([A-Za-z_][A-Za-z_0-9]*)")


def klauseln_in(text):
    """`(assumption, probe)` for every `falsifier` clause, plus the ones with no owner."""
    gefunden, waisen = [], []
    zeilen = text.splitlines()
    for i, z in enumerate(zeilen):
        m = FALS.search(z)
        if not m or z.lstrip().startswith("--"):
            continue
        name = None
        # **A `deadline` carries its falsifier in a `fn` clause, not under an
        # assumption** («SG-22»): it attributes as the manifest names it
        # (`frist_<fn>_eingehalten`, `manifest.rs::fristannahmen`), never as a
        # stilllegung -- and the enclosing `fn` may carry any qualifier (`impl`
        # included), which `FN` below does not read.
        if re.search(r"\bdeadline\b", z):
            for j in range(i, max(-1, i - 14), -1):
                f = FN_BELEGT.match(zeilen[j])
                if f:
                    name = "frist_%s_eingehalten" % f.group(1)
                    break
            (gefunden if name else waisen).append(
                (name, m.group(1)) if name else i + 1)
            continue
        for j in range(i, max(-1, i - 14), -1):
            d = DECL.match(zeilen[j])
            if d:
                name = d.group(1)
                break
            f = FN.match(zeilen[j])
            if f:
                name = "stilllegung_%s_ist_unerreichbar" % f.group(1)
                break
        (gefunden if name else waisen).append(
            (name, m.group(1)) if name else i + 1)
    return gefunden, waisen


def erzeugt(text):
    """The falsifiable entries the CHECKER builds -- a `sonde:` with a `name:` above it."""
    raus = []
    zeilen = text.splitlines()
    for i, z in enumerate(zeilen):
        m = re.match(r'^\s*sonde:\s*"([A-Za-z_][A-Za-z_0-9]*)"', z)
        if not m:
            continue
        for j in range(i, max(-1, i - 25), -1):
            n = re.match(r'^\s*name:\s*"([A-Za-z_][A-Za-z_0-9]*)"', zeilen[j])
            if n:
                raus.append((n.group(1), m.group(1)))
                break
    return raus


def sammle(dateien, rs_text):
    """`({assumption: probe}, orphan clauses)` -- the first declaration wins, as `vereinige`
    does: the same name declared twice with the same content is ONE assumption."""
    alle, waisen = {}, []
    for p in dateien:
        g, w = klauseln_in(p.read_text(encoding="utf-8"))
        for name, sonde in g:
            alle.setdefault(name, sonde)
        waisen += [(str(p.relative_to(W)), z) for z in w]
    for name, sonde in erzeugt(rs_text):
        alle.setdefault(name, sonde)
    return alle, waisen


def sondennamen(dateien, rs_text):
    """**Every probe name a `falsifier` writes, as a flat SET** -- no assumption behind it.

    *This is deliberately not `sammle().values()`.* That map keys on the assumption name, and
    two files that are never compiled together may declare one name with two different probes;
    the map then keeps one and the other name disappears from the count. **A figure that
    exists to say what was left out must not lose a row to a collision.**

    **And it reads CODE, not prose** (2026-09-04). Until this date it ran the regex over the
    whole file text while `klauseln_in` three functions up skipped comment lines -- *two
    readings of one word inside one guardian*, and only the stricter one was written down.
    The looser one counts the English sentence *"an assumption with a falsifier and not a
    check"* as a probe named `and`: found by `messung/k3-fragmente/K08-test-func.gab`:211,
    where ONE word of a comment pushed `aussen` from 13 to 14 and broke the mark.
    **A ratchet a sentence can move is not a ratchet** -- and the whole tree carries exactly
    one such match, so the repair moves no figure: 13 before, 13 after.

    Only a WHOLE-LINE comment is skipped, which is the same test `klauseln_in` makes. A
    trailing `--` is deliberately not cut: a `falsifier` clause can stand behind a string,
    and splitting on `--` would drop a real one to hide a false one.
    """
    namen = set()
    for p in dateien:
        for z in p.read_text(encoding="utf-8").splitlines():
            if z.lstrip().startswith("--"):
                continue
            for m in FALS.finditer(z):
                namen.add(m.group(1))
    return namen | {s for _n, s in erzeugt(rs_text)}


def programme():
    """The probe names that stand as a program: `sonden/<name>.c`."""
    return sorted(p.stem for p in SONDEN.glob("*.c")) if SONDEN.is_dir() else []


def gelistet(rs_text):
    """`SONDEN_MIT_PROGRAMM` -- the checker's OWN claim about which probes exist."""
    m = LISTE.search(rs_text)
    return sorted(re.findall(r'"([A-Za-z_][A-Za-z_0-9]*)"', m.group(1))) if m else []


def zeilen_der_tafel(doc_text):
    """The register rows, as `(assumption, probe, class, has_program)`."""
    return [(m.group(1), m.group(2), m.group(3), m.group(4) != "--")
            for m in (ROW.match(z) for z in doc_text.splitlines()) if m]


def klassen(doc_text):
    """The classes the document DEFINES, as `{key: wording}`."""
    return {m.group(1): m.group(2)
            for m in (KLASSE.match(z) for z in doc_text.splitlines()) if m}


def pruefe(doc_text, annahmen, progs, liste, waisen_aussen, rs_sites, aussen):
    """Every finding, each a list or a count. Nothing here exits; the caller decides."""
    zeilen = zeilen_der_tafel(doc_text)
    bekannt = klassen(doc_text)
    im_buch = {z[0]: z for z in zeilen}

    ohne_zeile = sorted(set(annahmen) - set(im_buch))
    ohne_klausel = sorted(set(im_buch) - set(annahmen))

    # **A name twice in the register is not a cosmetic defect.** Set equality survives it --
    # the two directions above compare SETS -- and the duplicate would still be counted in
    # `frei_offen` below, which is what says the floor is still reachable. *A doubled `P4` row
    # buys reachability that nobody can write.*
    doppelt = sorted(n for n, z in Counter(z[0] for z in zeilen).items() if z > 1)

    falsche_sonde, falsche_klasse, falsches_programm = [], [], []
    for name, sonde, kl, hat in zeilen:
        if name in annahmen and annahmen[name] != sonde:
            falsche_sonde.append((name, sonde, annahmen[name]))
        if kl not in bekannt:
            falsche_klasse.append((name, kl, "no such class in the document"))
        if hat != (sonde in progs):
            falsches_programm.append((name, sonde, hat))

    gedeckt = sorted(n for n, s in annahmen.items() if s in progs)
    n_ann = len(annahmen)
    n_ged = len(gedeckt)

    # **The share, compared as a fraction and never as a float** -- a rounding error in a
    # ratchet is a ratchet that sometimes gives way.
    zn, zd = MARK_QUOTE
    quote_gefallen = n_ged * zd < n_ann * zn
    bn, bd = BODEN
    boden_verfehlt = n_ged * bd < n_ann * bn

    # **Tooth 8: is the floor still REACHABLE?** Every row of the free class that has no
    # program yet, plus what is already covered. If even that misses the floor, the corpus has
    # grown past what a bench without ring 0 and without a device can ever cover -- and the
    # answer to that is a decision about apparatus, not a smaller number here.
    frei_offen = [n for n, s, kl, hat in zeilen if kl == FREI and not hat]
    erreichbar = n_ged + len(frei_offen)
    unerreichbar = erreichbar * bd < n_ann * bn
    frei_falsch = FREI in bekannt and FREI_WORT not in bekannt[FREI].lower()

    # **Tooth 10.** `manifest::gedeckt` decides from a CONSTANT LIST whether a probe name
    # stands or is struck. A string added there raises the quota with no program written.
    liste_zuviel = sorted(set(liste) - set(progs))
    liste_zuwenig = sorted(set(progs) - set(liste))

    return (ohne_zeile, ohne_klausel, falsche_sonde, falsche_klasse, falsches_programm,
            quote_gefallen, boden_verfehlt, unerreichbar, frei_falsch,
            max(0, len(waisen_aussen) - MARK_WAISEN), liste_zuviel, liste_zuwenig,
            max(0, rs_sites - MARK_RS_SITES), max(0, aussen - MARK_AUSSEN), doppelt,
            n_ann, n_ged, len(zeilen), len(frei_offen))


def sprechprobe(doc_text, annahmen, progs, liste, waisen_aussen, rs_sites, aussen):
    """**R14, in both directions -- a guardian nobody has seen say no is an ornament.**

    Every tooth gets one, because a tooth that never bites is indistinguishable from one that
    is not there, and the last probe is the control: without it the others also pass over a
    guardian that always says no.
    """
    proben = []

    def lauf(t=None, a=None, p=None, li=None, wa=None, rs=None, au=None):
        return pruefe(doc_text if t is None else t,
                      annahmen if a is None else a,
                      progs if p is None else p,
                      liste if li is None else li,
                      waisen_aussen if wa is None else wa,
                      rs_sites if rs is None else rs,
                      aussen if au is None else au)

    # ONE -- a 39th assumption in the corpus with no row must be named.
    mehr = dict(annahmen, erfunden_zur_probe="sonde_erfunden")
    r = lauf(a=mehr)
    proben.append(("an assumption with no row is named", r[0] == ["erfunden_zur_probe"]))

    # TWO -- and a row whose assumption is gone is the OTHER finding: one is a corpus growing
    # past its register, the other a register going stale.
    weniger = {k: v for k, v in annahmen.items() if k != "invlpg"}
    r = lauf(a=weniger)
    proben.append(("a row with no assumption is named", r[1] == ["invlpg"]))

    # THREE -- a row that names a probe the corpus does not declare for it.
    verdreht = doc_text.replace("| **invlpg** | `sonde_invlpg` |",
                                "| **invlpg** | `sonde_erfunden` |", 1)
    r = lauf(t=verdreht)
    proben.append(("a row naming the wrong probe falls",
                   [f[0] for f in r[2]] == ["invlpg"]))

    # FOUR -- a class the document does not define.
    erfunden = doc_text.replace("| `P1` | -- |", "| `P9` | -- |", 1)
    r = lauf(t=erfunden)
    proben.append(("a class the document does not define falls",
                   [f[1] for f in r[3]] == ["P9"]))

    # FIVE -- the program column has to answer to `sonden/`, in BOTH directions.
    gelogen = doc_text.replace("| `P1` | -- |", "| `P1` | **PROGRAM** |", 1)
    r = lauf(t=gelogen)
    proben.append(("a row claiming a program that is not there falls", len(r[4]) == 1))
    r = lauf(p=sorted(progs + ["sonde_invlpg"]))
    proben.append(("a program the register does not know falls",
                   [f[0] for f in r[4]] == ["invlpg"]))

    # SIX -- the RATCHET, at unchanged coverage. One more assumption without a probe is
    # exactly the move the share exists to price.
    r = lauf(a=mehr)
    proben.append(("one assumption more without a probe breaks the quota", r[5]))
    r = lauf(a=dict(mehr, noch_eine="sonde_boot_unerreichbar"))
    proben.append(("one assumption more WITH a probe does not", not r[5]))

    # SEVEN -- the FLOOR, and it has to be able to come out BOTH ways. **The direction it is
    # asked in FLIPPED on 2026-09-04**, and that is the whole point of a floor that was set
    # where the tree failed: it is MET today, and over the tree as it stood before the four
    # `P4` probes were written it must come out missed. *A test that only knew how to see the
    # floor missed would have gone silent the moment it was paid.*
    r = lauf()
    boden_heute = r[6]
    # **The counterfactual moved on 2026-09-10 (central assembly):** the four
    # probes of 2026-09-04 no longer break the floor alone (13 covered of 46
    # absorb their removal: 9 of 46 still meets it). The tooth keeps its
    # meaning -- the floor is earned, and removing the earned work breaks
    # it -- by naming the SMALLEST newest set that breaks it: the eight
    # newest PROGRAM rows (39-46: tick plus lane-59's three plus lane-72's
    # four); without them 5 of 46 miss. The rule for the next move stands
    # beside tooth EIGHT's: smallest newest breaking set, recomputed on
    # earned growth, never shrunk to fit.
    #
    # **Restored on 2026-09-10 (lane-80), same rule, grown not shrunk:**
    # 17 covered of 50 absorb the removal of any ten newest probes (7 of 50
    # still meets: 56 >= 50); the smallest newest breaking set is ELEVEN --
    # rows 40-50 (lane-59's three plus lane-72's four plus lane-80's four),
    # without which 6 of 50 miss (48 < 50). Ten or fewer removals always
    # leave 7 covered (56 >= 50), so no smaller set breaks it.
    #
    # **Grown on 2026-09-12 (lane S5, syscall), same rule:** 18 covered of 51
    # absorb the removal of any eleven newest probes (7 of 51 still meets:
    # 56 >= 51); the smallest newest breaking set is TWELVE -- rows 40-51
    # (the eleven above plus lane S5's `sonde_write`), without which 6 of 51
    # miss (48 < 51). Eleven or fewer removals always leave 7 covered
    # (56 >= 51), so no smaller set breaks it.
    elf = ("sonde_abnahme", "sonde_byte_legen", "sonde_freigabe",
            "sonde_barriere", "sonde_schreib_schranke", "sonde_speicher_schranke",
            "sonde_schreiben", "sonde_zaehle", "sonde_takt_verteiler",
            "sonde_bearbeite", "sonde_ruf_verteiler", "sonde_write")
    ohne_elf = [x for x in progs if x not in elf]
    r = lauf(p=ohne_elf)
    proben.append(("the floor is met today and MISSED without the eleven newest probes",
                   not boden_heute and r[6]))

    # EIGHT -- reachability. A corpus that grows without new `P4` rows eventually puts the
    # floor out of reach, and that is a different finding from missing it.
    #
    # **The stress size is 87 since 2026-09-10 (lane-80), 59 after the
    # central assembly, 31 after lane-59, 30 before.** Four more earned `P4`
    # rows (17 covered of 50) drowned the +59 stress (17 of 109 still meets
    # the floor: 136 >= 109). 87 is the smallest restore (17 of 137 < `1/8`;
    # 86 lands exactly on it -- 136 < 136 is false -- and strict `<` cannot
    # name a boundary). Same standing rule: smallest size that breaks,
    # recomputed on earned growth, never shrunk.
    #
    # **The stress size is 94 since 2026-09-12 (lane S5, syscall), same rule.**
    # One more earned `P4` row (18 covered of 51) drowns the +87 stress
    # (18 of 138 still meets the floor: 144 >= 138). 94 is the smallest
    # restore (18 of 145 < `1/8`; 93 lands exactly on it -- 144 < 144 is
    # false -- and strict `<` cannot name a boundary).
    viel = dict(annahmen)
    for i in range(94):
        viel["erfunden_%d" % i] = "sonde_erfunden_%d" % i
    r = lauf(a=viel)
    proben.append(("a floor grown out of reach is named", r[7]))
    r = lauf()
    proben.append(("the floor is reachable today", not r[7]))

    # NINE -- and the free class has to keep meaning what the floor was derived from.
    umbenannt = re.sub(r"(\|\s*\*\*`P4`\*\*\s*\|)[^|]*\|",
                       r"\1 ring 0 and a device |", doc_text)
    r = lauf(t=umbenannt)
    proben.append(("a redefined free class is named", r[8]))

    # TEN -- a second orphan program.
    r = lauf(wa=waisen_aussen + ["sonde_erfunden"])
    proben.append(("a second program bound to no obligation breaks the mark", r[9] == 1))

    # ELEVEN -- **the sharp one.** A string in `SONDEN_MIT_PROGRAMM` with no program behind it
    # would raise the quota inside the checker, out of sight of every row above.
    r = lauf(li=sorted(liste + ["sonde_erfunden"]))
    proben.append(("coverage claimed in the checker with no program falls",
                   r[10] == ["sonde_erfunden"]))
    # **`len(progs)` and not a literal.** The tree had two programs when this was written and
    # has six since; a number here would have turned a written probe into a red guardian.
    r = lauf(li=[])
    proben.append(("a program the checker does not list falls", len(r[11]) == len(progs)))

    # TWELVE -- one row written twice. Set equality does not see it, and it would buy
    # reachability nobody can write.
    zwiefach = doc_text.replace(
        "| 13 | **invlpg** | `sonde_invlpg` | `P1` | -- |",
        "| 13 | **invlpg** | `sonde_invlpg` | `P1` | -- |\n"
        "| 13 | **invlpg** | `sonde_invlpg` | `P1` | -- |", 1)
    r = lauf(t=zwiefach)
    proben.append(("a row written twice is named", r[14] == ["invlpg"]))

    # THIRTEEN -- a new construction site in the checker, and a wider corpus.
    r = lauf(rs=rs_sites + 1)
    proben.append(("a new construction site in the checker is named", r[12] == 1))
    r = lauf(au=aussen + 1)
    proben.append(("a probe name more outside the register is named", r[13] == 1))

    # FOURTEEN -- the control. Everything above also passes over a guardian that always says
    # no; this is the one that does not. **The floor was EXCLUDED from it until 2026-09-04**,
    # because it was missed and the run was red for that and for nothing else. *It is included
    # since the four probes were written* -- leaving it out now would be a control that steps
    # around the one figure this file exists for.
    r = lauf()
    proben.append(("the register is clear and every tooth including the floor holds",
                   not r[0] and not r[1] and not r[2] and not r[3] and not r[4]
                   and not r[5] and not r[6] and not r[7] and not r[8] and not r[9]
                   and not r[10] and not r[11] and not r[12] and not r[13]
                   and not r[14]))

    for was, ok in proben:
        print("  %-64s %s" % (was + ":", "yes" if ok else "NO"))
    return all(ok for _, ok in proben)


def main():
    # **TOOTH 0 -- the subject has to be there.** Over a missing document every check below
    # holds, and `ALL PASS` would be a verdict about nothing (`W17`).
    for pfad, wie in ((DOC, "dokumente/SONDENDECKUNG.md"),
                      (GENERATOR, "crates/gabbro-check/src/manifest.rs")):
        if not pfad.is_file():
            for strom in (sys.stderr, sys.stdout):
                print("ABBRUCH: `%s` is missing -- NOTHING was measured." % wie, file=strom)
            print("  Over a missing register every tooth holds, and a green run would be a")
            print("  judgement about nothing.")
            return 2

    doc_text = DOC.read_text(encoding="utf-8")
    rs_text = GENERATOR.read_text(encoding="utf-8")
    rs_sites = len(BAUSTELLE.findall(rs_text))
    annahmen, waisen = sammle(korpus_dateien("beispiele"), rs_text)
    progs = programme()

    if not progs:
        for strom in (sys.stderr, sys.stdout):
            print("ABBRUCH: not one probe under `sonden/` -- NOTHING was measured.",
                  file=strom)
        print("  A quota over an empty numerator is not coverage, it is an empty set --")
        print("  and `0 of 0` was a GREEN run until 2026-08-31.")
        return 2

    # **The wider corpus, for the direction that runs the other way.** A program is bound if
    # ANY `falsifier` in the non-poison tree names it -- narrowing that here would report an
    # orphan for a probe some fragment does name.
    weit = sondennamen(korpus_dateien(""), rs_text)
    waisen_aussen = sorted(set(progs) - weit)
    aussen = len(weit - set(annahmen.values()))

    print("== Speech test (R14) ==")
    if not sprechprobe(doc_text, annahmen, progs, gelistet(rs_text),
                       waisen_aussen, rs_sites, aussen):
        print("== PROBE COVERAGE: the guardian does not measure ==")
        return 2
    print()

    (ohne_zeile, ohne_klausel, falsche_sonde, falsche_klasse, falsches_programm,
     quote_gefallen, boden_verfehlt, unerreichbar, frei_falsch, zuviel_waisen,
     liste_zuviel, liste_zuwenig, blind, zuviel_aussen, doppelt,
     n_ann, n_ged, n_zeilen, n_frei_offen) = pruefe(
        doc_text, annahmen, progs, gelistet(rs_text), waisen_aussen, rs_sites, aussen)

    if not n_zeilen:
        for strom in (sys.stderr, sys.stdout):
            print("ABBRUCH: `dokumente/SONDENDECKUNG.md` carries NO row in the expected "
                  "shape.", file=strom)
        print("  Either the register is empty -- then this run is a judgement about nothing")
        print("  -- or the table changed shape and this guardian no longer reads it.")
        print("  **Both are a finding, not a green run.**")
        return 2

    print("== The falsifiable assumptions of the corpus ==")
    im_buch = {z[0]: z for z in zeilen_der_tafel(doc_text)}
    for name in sorted(annahmen):
        z = im_buch.get(name)
        print("  %-48s %-36s %-4s %s"
              % (name, annahmen[name], z[2] if z else "----",
                 "PROGRAM" if annahmen[name] in progs else "--"))
    print("  ---------------------------------------------------------------")
    zn, zd = MARK_QUOTE
    bn, bd = BODEN
    print("  %d of %d falsifiable assumptions carry a probe that stands as a program"
          % (n_ged, n_ann))
    print("  A_p = %.4f    booked %d/%d = %.4f    floor %d/%d = %.4f"
          % (n_ged / n_ann, zn, zd, zn / zd, bn, bd, bn / bd))
    print("  %d of %d rows are class `%s`, %d of them without a program -- the reachable "
          "share is %d of %d" % (
              sum(1 for z in zeilen_der_tafel(doc_text) if z[2] == FREI), n_zeilen, FREI,
              n_frei_offen, n_ged + n_frei_offen, n_ann))
    print("  %d program(s) under `sonden/`, %d of them named by no `falsifier` -- booked is %d"
          % (len(progs), len(waisen_aussen), MARK_WAISEN))
    print("  %d probe name(s) outside this register, booked are %d" % (aussen, MARK_AUSSEN))
    print("  %d construction site(s) of `Klasse::Falsifizierbar` in `manifest.rs`, booked "
          "are %d" % (rs_sites, MARK_RS_SITES))
    print()

    abschnitt.fertig()

    fehler = 0
    if ohne_zeile:
        print("  ASSUMPTION WITHOUT A ROW: %s" % ", ".join(ohne_zeile))
        print("  A falsifiable assumption stands in the corpus that the register does not")
        print("  carry. **That is the denominator growing in silence** -- classify it under")
        print("  one of the four classes, then add the row.")
        fehler = 1
    if doppelt:
        print("  ROW WRITTEN TWICE: %s" % ", ".join(doppelt))
        print("  Set equality compares SETS and does not see it, and the duplicate is still")
        print("  counted where the floor's reachability is decided. **A doubled row buys")
        print("  reachability nobody can write.**")
        fehler = 1
    if ohne_klausel:
        print("  ROW WITHOUT AN ASSUMPTION: %s" % ", ".join(ohne_klausel))
        print("  *This is the good direction and still a finding*: a register that keeps a")
        print("  row nobody can check reads like a measurement and is a memory.")
        fehler = 1
    for n, gebucht, wirklich in falsche_sonde:
        print("  WRONG PROBE: `%s` is booked with `%s` and declares `%s`."
              % (n, gebucht, wirklich))
        fehler = 1
    for n, kl, warum in falsche_klasse:
        print("  CLASS DOES NOT HOLD: `%s` names `%s` -- %s." % (n, kl, warum))
        print("  A row stands under a class the document defines, or it does not stand.")
        fehler = 1
    for n, sonde, behauptet in falsches_programm:
        print("  PROGRAM COLUMN WRONG: `%s` is booked %s and `sonden/%s.c` %s."
              % (n, "with a program" if behauptet else "without one", sonde,
                 "is not there" if behauptet else "stands"))
        fehler = 1
    if quote_gefallen:
        print("  RATCHET BROKEN: A_p = %d of %d, booked are %d of %d."
              % (n_ged, n_ann, zn, zd))
        print("  **An assumption was added and its probe was not.** The quota may not fall:")
        print("  write the probe, or book the fall here with its reason at the mark.")
        fehler = 1
    if liste_zuviel:
        print("  COVERAGE CLAIMED WITH NO PROGRAM: %s" % ", ".join(liste_zuviel))
        print("  `manifest::SONDEN_MIT_PROGRAMM` names a probe that does not stand under")
        print("  `sonden/`. **That raises the quota inside the checker with nothing written**")
        print("  -- the same move as `unfalsifiable`, one layer down and invisible from here.")
        fehler = 1
    if liste_zuwenig:
        print("  PROGRAM NOT LISTED: %s" % ", ".join(liste_zuwenig))
        print("  A program stands under `sonden/` that `SONDEN_MIT_PROGRAMM` does not carry,")
        print("  so the manifest keeps striking its name. One line repairs it.")
        fehler = 1
    if zuviel_waisen:
        print("  RATCHET BROKEN: %d program(s) named by no `falsifier`, booked is %d."
              % (len(waisen_aussen), MARK_WAISEN))
        print("  A built program nobody references is the same broken connection as a name")
        print("  without a program, reversed. `N024` -- a probe belongs to exactly ONE")
        print("  obligation -- has nothing to hold it to.")
        fehler = 1
    if frei_falsch:
        print("  THE FREE CLASS WAS REDEFINED: `%s` no longer says `%s`." % (FREI, FREI_WORT))
        print("  The floor was derived from that class. A class redefined under a floor")
        print("  leaves the number standing over a different measurement.")
        fehler = 1
    if unerreichbar:
        print("  THE FLOOR IS OUT OF REACH: %d reachable of %d, floor is %d/%d."
              % (n_ged + n_frei_offen, n_ann, bn, bd))
        print("  Writing EVERY probe that needs nothing but a C compiler no longer reaches")
        print("  the floor. **The corpus has grown past what this bench can cover** -- and")
        print("  the answer is a decision about apparatus, not a smaller number at `BODEN`.")
        fehler = 1
    if blind:
        print("  THE READER MAY BE BLIND: %d construction site(s) of "
              "`Klasse::Falsifizierbar`, booked are %d." % (rs_sites, MARK_RS_SITES))
        print("  A generated entry written in another shape is invisible to the scanner")
        print("  above, and a shrunken denominator reads exactly like a covered tree.")
        fehler = 1
    if zuviel_aussen:
        print("  MORE PROBE NAMES OUTSIDE: %d, booked are %d." % (aussen, MARK_AUSSEN))
        print("  The register's denominator is `beispiele/` plus the generated entries. What")
        print("  is left out is carried by name, or the quota measures its own boundary.")
        fehler = 1
    for f, z in waisen:
        print("  UNATTRIBUTABLE: `%s`:%d carries a `falsifier` under no `assume`, `axiom`"
              " or `fn`." % (f, z))
        fehler = 1

    if boden_verfehlt:
        print("  THE FLOOR IS NOT MET: A_p = %d of %d = %.4f, the floor is %d/%d = %.4f."
              % (n_ged, n_ann, n_ged / n_ann, bn, bd, bn / bd))
        print("  **This is the debt, not a regression.** `dokumente/SONDENDECKUNG.md` names")
        print("  the price: %d probe(s) of class `%s`, each a userland C program with a"
              % (n_frei_offen, FREI))
        print("  sensitivity arm, each entered in `manifest::SONDEN_MIT_PROGRAMM`.")
        print("  A bound the tree already meets is a decoration -- this one is a gate.")
        fehler = 1

    if fehler:
        print("\n== PROBE COVERAGE: FINDING ==")
        return 1

    print("== PROBE COVERAGE: ALL PASS -- %d of %d, floor %d/%d ==" % (n_ged, n_ann, bn, bd))
    return 0


if __name__ == "__main__":
    sys.exit(abschnitt.fahre(main))
