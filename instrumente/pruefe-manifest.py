#!/usr/bin/env python3
"""**E1 -- the obligation manifest measured against its own subject.**

`AUFTRAG-GABBROV.md` §1 states E1 as *"every `obligation` line of the manifest gets a
verdict"* and adds the sentence this file exists for: **"checkable with one command."**
§5 sharpens it -- *"E1 is WIRED INTO the tool, not hung beside it: the run ends with a
comparison of the two line counts and aborts on a divergence. A tool that does not check its
own completeness has none."*

There are TWO comparisons and they belong in two places, because one of them needs a
document the compiler has never heard of:

    INNER   what the emitter WROTE against what it COUNTED
            -> lives in `pflichten.rs::zeige` itself, one unit at a time.
               It is the check against a new obligation kind quietly missing from the
               print loop while the header line already counts it.

    OUTER   what the manifest CARRIES against the population it is about
            -> lives here, because the population is `dokumente/PFLICHTEN.md` and
               `gabbro` neither reads it nor should.

**This guard is RED today and that is the finding, not a fault.** The split is the thing
worth reading, and it has FOUR terms, not two:

    CARRIED     a manifest line states the obligation
    BLOCKED     the fragment carries checker errors, so there is no register at all
                -- NOT a defect of the manifest
    DROPPED     the clause stands in the source and the register does not book it
                -- the manifest's own hole
    NO CLAUSE   nothing in the fragment states it; a line would have to be INVENTED

*A number that mixes them is worth nothing*, so this tool never prints one without the split.

## The split is DERIVED now, and until 2026-09-03 it was a sentence

This file used to print `43 blocked upstream, 15 dropped by the manifest, 5 carried` as a
hardcoded string. **Three fragments were repaired that same day and not one of the three
numbers moved**, because none of them was derived from anything -- 43 counted F01, F05 and F09
against defects that no longer existed. *A blocker that no longer exists is not a blocker.*

The mapping itself is a judgement over `PFLICHTEN.md` and cannot be computed, so it stands
row by row in **`messung/gabbrov/PFLICHTEN-KORRESPONDENZ.md`** and this reader holds it
against a live run:

    a CARRIED row must name a line that is really in the register  -> else E1 red
    a BLOCKED row's fragment must really emit no register          -> else E1 red
    a DROPPED / NO CLAUSE row's fragment must emit one             -> else E1 red
    the table's row count must equal the population                -> else ABBRUCH, 2

**And the subtraction it replaces was a category error.** `bev - <manifest lines>` compares
GabbroV's population -- the `L` rows of `PFLICHTEN.md` alone -- against every line the
register emits, `K` and `L` together. Measured 2026-09-03: **16 of 27 lines carry a `K` row or
no row at all**, so the old arithmetic counted sixteen lines as if each had closed a logic
obligation. *It reported 36 missing where the mapping says 50.*

## Both formats, and that is deliberate

`pflichten.rs::MANIFESTFASSUNG` numbers the register. This reader understands **1 and 2**,
and refuses anything else outright: `CLAUDE.md` holds the measured shape of the alternative
-- seven guards read a document, four went **silently blind** when it moved. *A reader that
guesses at an unknown format reports a number, and a number out of a misread format is worse
than no number.*

    ./instrumente/pruefe-manifest.py                 the split, and the E1 verdict
    ./instrumente/pruefe-manifest.py --zeilen        every obligation line as it stands
    ./instrumente/pruefe-manifest.py --offen         the open obligations, by state
    ./instrumente/pruefe-manifest.py --sprechprobe   the probes only

Return codes follow the sixth requirement, as `zaehle-p6.py` states it: **`1` means the TREE
has to change, `2` means the SETUP does.** An E1 divergence is a `1`; a missing binary, a
missing fragment or an unknown format is a `2`, and every one of those says NOTHING WAS
MEASURED.
"""
import pathlib
import re
import subprocess
import sys

W = pathlib.Path(__file__).resolve().parent.parent
GABBRO = W / "target" / "debug" / "gabbro"
FRIST = 120  # seconds per unit; a hang is not a finding.

# **The mapping, and it lives in a document because it is a JUDGEMENT.**
KORRESPONDENZ = W / "messung" / "gabbrov" / "PFLICHTEN-KORRESPONDENZ.md"
# The four states, exhaustive and closed. **A fifth word in the table is an ABBRUCH, not a
# row this reader skips** -- a state it does not know is a row it cannot check, and a row it
# cannot check must not be counted into a split that reads like a measurement.
ZUSTAENDE = ("CARRIED", "BLOCKED", "DROPPED", "NO CLAUSE")

# **The formats this reader can parse.** Widening this set is the SECOND step of a format
# change, never the first and never the third -- `AUFTRAG-GABBROV.md` §4.
FASSUNGEN = (1, 2)

FASSUNGSZEILE = re.compile(r"^-- manifest-version (\d+)$")
KOPFZEILE = re.compile(r"^== (\d+) obligations: ")
# **Format 1 -- the entry line carries a name and nothing else.** Five spaces, then
# `<function> :: <subject>`. The ordinal in the subject is exactly the defect `OFFEN.md` `O3`
# names: swap two `ensures` conjuncts and the two manifests are byte-identical.
ZEILE_V1 = re.compile(r"^ {5}(\S.*?) :: (\S.*)$")
# **Format 2 -- the record `SPRACHE.md` §15 sketched**, tab-separated after the keyword:
# `obligation <name> <class> <anchor> <state> <text>`.
ZEILE_V2 = re.compile(r"^obligation\t")


class Fassungsfehler(Exception):
    """An unknown format. Nothing may be counted after one of these."""


def lies(text, woher):
    """`(fassung, [(name, ...)])` for one register -- or an exception, never a guess."""
    fassung = None
    for z in text.splitlines():
        m = FASSUNGSZEILE.match(z)
        if m:
            fassung = int(m.group(1))
            break
        # **The version field stands on line ONE**, before the file name. Anything printed
        # ahead of it means the emitter changed something this reader cannot place.
        if z.strip():
            raise Fassungsfehler(
                f"{woher}: the first line is `{z[:60]}` and not a version field"
            )
    if fassung is None:
        raise Fassungsfehler(f"{woher}: no `-- manifest-version` line at all")
    if fassung not in FASSUNGEN:
        raise Fassungsfehler(
            f"{woher}: manifest version {fassung}; this reader knows "
            f"{', '.join(str(f) for f in FASSUNGEN)}"
        )
    kopf = None
    zeilen = []
    for z in text.splitlines():
        m = KOPFZEILE.match(z)
        if m:
            kopf = int(m.group(1))
            continue
        if fassung == 1:
            m = ZEILE_V1.match(z)
            if m:
                zeilen.append((f"{m.group(1)} :: {m.group(2)}", None, None, None, None))
        else:
            if ZEILE_V2.match(z):
                felder = z.split("\t")[1:]
                # `--` is the emitter's word for *this run does not have it*, and it is
                # carried through rather than turned into an empty string: an absent field
                # and an empty one are different statements.
                felder += ["--"] * (5 - len(felder))
                zeilen.append(tuple(felder[:5]))
    return fassung, kopf, zeilen


def bevoelkerung():
    """GabbroV's obligation population, from `zaehle-pflichten.py` and not from a constant.

    *A number written twice is two numbers* -- W7. The search path is the other tool, and a
    change there moves this comparison with it instead of past it.
    """
    run = subprocess.run(
        [str(W / "instrumente" / "zaehle-pflichten.py"), "--gabbrov"],
        cwd=W, capture_output=True, text=True, timeout=FRIST,
    )
    m = re.search(r"GabbroV obligation population\s+(\d+)", run.stdout)
    return int(m.group(1)) if m else None


def fragmente():
    return sorted((W / "messung" / "fragmente").glob("F*.gab"))


def _zellen(z):
    """The cells of a markdown row, `\\|` inside a cell kept whole."""
    aus, puffer, i = [], "", 0
    while i < len(z):
        if z[i] == "\\" and i + 1 < len(z) and z[i + 1] == "|":
            puffer += "|"
            i += 2
            continue
        if z[i] == "|":
            aus.append(puffer)
            puffer = ""
            i += 1
            continue
        puffer += z[i]
        i += 1
    aus.append(puffer)
    return [c.strip() for c in aus]


def korrespondenz(text=None):
    """**The mapping table of `PFLICHTEN-KORRESPONDENZ.md` §3, one entry per obligation.**

    Returns `[(nr, fragment, anker, pflicht, zustand, grund)]` -- or raises, never guesses.

    *The row shape is the filter and it is deliberately narrow:* eight cells, an integer in
    the first, one of the four known states in the fifth. The other tables of the same file
    have five cells and no number, so they cannot be swept up by accident -- and a §3 row
    that loses its shape drops OUT rather than being read wrong, which the row count then
    reports as a divergence against the population.
    """
    if text is None:
        if not KORRESPONDENZ.exists():
            raise Fassungsfehler(f"{KORRESPONDENZ} fehlt -- ohne die Tafel gibt es keine Zuordnung")
        text = KORRESPONDENZ.read_text(encoding="utf-8")
    aus = []
    for z in text.splitlines():
        if not z.startswith("|"):
            continue
        c = _zellen(z.strip())
        if len(c) != 8 or c[0] != "" or c[-1] != "":
            continue
        if not c[1].isdigit():
            continue
        if c[5] not in ZUSTAENDE:
            raise Fassungsfehler(
                f"{KORRESPONDENZ.name}: Zeile {c[1]} nennt den Zustand `{c[5][:30]}`; "
                f"bekannt sind {', '.join(ZUSTAENDE)}"
            )
        aus.append((int(c[1]), c[2], c[3], c[4], c[5], c[6]))
    return aus


# **The line a CARRIED row names.** The cell reads `` `unlink :: cdt_wohlgeformt` `` -- the
# first backtick-quoted string IS the obligation name, and it is compared against the register
# whole. *A substring match would let `ensures #1` stand for `ensures #12`, which is the
# ordinal defect `O3` names, one reader further out.*
BENANNTE_ZEILE = re.compile(r"`([^`]+)`")


def pruefe_tafel(zeilen, lage):
    """**Every row of the mapping against the RUN**, and the row's own state decides the test.

    `lage` is `{fragment: (hat_register, {obligation names})}`. Returns the complaints, in
    table order -- **the whole list and never the first one**: a check that stops at the first
    row answers *"is at least one wrong"* and the question is *"which"* (`CLAUDE.md`).
    """
    klagen = []
    for nr, frag, _anker, pflicht, zustand, grund in zeilen:
        if frag not in lage:
            klagen.append(f"row {nr}: `{frag}` is no fragment of this run")
            continue
        hat_register, namen = lage[frag]
        if zustand == "CARRIED":
            m = BENANNTE_ZEILE.search(grund)
            if not m:
                klagen.append(f"row {nr} ({frag} {pflicht[:40]}): CARRIED names no manifest line")
            elif not hat_register:
                klagen.append(f"row {nr} ({frag}): CARRIED, but {frag} emits NO register")
            elif m.group(1) not in namen:
                klagen.append(
                    f"row {nr} ({frag}): CARRIED names `{m.group(1)}`, "
                    f"and that line is NOT in {frag}'s register"
                )
        elif zustand == "BLOCKED":
            # **The check the stale `43` needed and did not have.**
            if hat_register:
                klagen.append(
                    f"row {nr} ({frag} {pflicht[:40]}): BLOCKED, but {frag} DOES emit a "
                    f"register -- a blocker that no longer exists is not a blocker"
                )
        else:  # DROPPED / NO CLAUSE
            if not hat_register:
                klagen.append(
                    f"row {nr} ({frag}): {zustand}, but {frag} emits no register at all "
                    f"-- that is BLOCKED, and the two are not the same finding"
                )
            if not grund:
                klagen.append(f"row {nr} ({frag} {pflicht[:40]}): {zustand} without a reason")
    return klagen


def lauf(zeigen=False, offen=False):
    if not GABBRO.exists():
        print(f"ABBRUCH: {GABBRO} fehlt -- gebaut wird auf ki-pc-fisch-101 (CLAUDE.md).")
        print("  NICHTS wurde gemessen; das ist kein Bericht ueber ein leeres Manifest.")
        return 2
    dateien = fragmente()
    if not dateien:
        print("ABBRUCH: kein `messung/fragmente/F*.gab`. NICHTS wurde gemessen.")
        return 2
    bev = bevoelkerung()
    if bev is None:
        print("ABBRUCH: `zaehle-pflichten.py --gabbrov` nennt keine Bevoelkerung.")
        print("  Ohne den Nenner ist der Zaehler keine Aussage. NICHTS wurde gemessen.")
        return 2
    try:
        tafel = korrespondenz()
    except Fassungsfehler as e:
        print(f"ABBRUCH: {e}.")
        print("  NICHTS wurde gemessen -- ohne die Zuordnung ist jede Zahl hier eine Differenz")
        print("  zwischen zwei Mengen, die einander nicht enthalten.")
        return 2
    # **The denominator, checked against the table BEFORE anything is counted.** A table that
    # has fallen behind `PFLICHTEN.md` would answer a smaller question and look complete doing
    # it -- the `W16` shape at the bookkeeping layer.
    if len(tafel) != bev:
        print(f"ABBRUCH: `{KORRESPONDENZ.name}` fuehrt {len(tafel)} Zeilen, die Bevoelkerung "
              f"ist {bev}.")
        print("  Die Tafel ist die Zuordnung, nicht eine Auswahl daraus. NICHTS wurde gemessen.")
        return 2
    if [n for n, *_ in tafel] != list(range(1, bev + 1)):
        print(f"ABBRUCH: die Zeilennummern der Tafel sind nicht 1 .. {bev} in Folge.")
        print("  Eine Luecke oder eine Wiederholung macht jede Summe darueber unpruefbar.")
        return 2

    print("== E1 -- the manifest against its own subject ==")
    getragen = ohne_register = 0
    innen_schlecht = []
    lage = {}
    for f in dateien:
        rel = str(f.relative_to(W))
        try:
            run = subprocess.run(
                [str(GABBRO), "pflichten", rel], cwd=W,
                capture_output=True, text=True, timeout=FRIST,
            )
        except subprocess.TimeoutExpired:
            print(f"ABBRUCH: {rel} -- Frist {FRIST} s ueberschritten. Ein Haenger ist kein Befund.")
            return 2
        if run.returncode != 0:
            # A unit with errors carries no register, and that is the same rule
            # `gabbro pflichten` follows. **Not a manifest defect** -- it is upstream.
            fehler = sum(1 for z in run.stderr.splitlines() if z.startswith("error:"))
            ohne_register += 1
            lage[f.stem] = (False, set())
            print(f"  {f.name:<9} NO REGISTER   {fehler:2d} checker error(s)  -- blocked upstream")
            continue
        try:
            fassung, kopf, zeilen = lies(run.stdout, rel)
        except Fassungsfehler as e:
            print(f"ABBRUCH: {e}.")
            print("  NICHTS wurde gemessen -- ein Leser, der ein unbekanntes Format raet,")
            print("  meldet eine Zahl, und die ist schlechter als keine.")
            return 2
        # **The INNER E1, read back from the artefact.** `zeige` checks it while writing;
        # this is the second pair of eyes, over the text that actually left the tool.
        if kopf is not None and kopf != len(zeilen):
            innen_schlecht.append((rel, kopf, len(zeilen)))
        getragen += len(zeilen)
        lage[f.stem] = (True, {z[0] for z in zeilen})
        print(f"  {f.name:<9} v{fassung} register  {len(zeilen):2d} obligation line(s)")
        if zeigen:
            for z in zeilen:
                print(f"        {z[0]}")
                if z[1] is not None:
                    print(f"          class {z[1]}  anchor {z[2]}  state {z[3]}")
                    print(f"          text  {z[4]}")

    # **The mapping against the run, and the SPLIT comes out of it -- not out of a sentence.**
    klagen = pruefe_tafel(tafel, lage)
    je = {z: sum(1 for r in tafel if r[4] == z) for z in ZUSTAENDE}
    getragen_pflichten = je["CARRIED"]
    fehlend = bev - getragen_pflichten
    # The reverse direction: lines that no row of the table claims. They are not a defect --
    # `PFLICHTEN.md` books `K` rows too and GabbroV's population is the `L` half -- but the
    # number has to STAND somewhere, because it is exactly what the old subtraction spent.
    benannt = set()
    for _n, _f, _a, _p, zustand, grund in tafel:
        if zustand == "CARRIED":
            m = BENANNTE_ZEILE.search(grund)
            if m:
                benannt.add(m.group(1))
    ohne_zeile = sum(len(n - benannt) for _h, n in lage.values())

    print("  ------------------------------------------------------------------")
    print(f"  GabbroV's obligation population                       {bev:>3}")
    print(f"  obligation lines the register emits                   {getragen:>3}")
    print(f"     of these, claimed by no row of the mapping         {ohne_zeile:>3}"
          f"   (a `K` row, or none)")
    print("  ------------------------------------------------------------------")
    print(f"  CARRIED    a manifest line states it                  {je['CARRIED']:>3}")
    print(f"  BLOCKED    the fragment emits no register             {je['BLOCKED']:>3}"
          f"   ({ohne_register} of {len(dateien)} fragments)")
    print(f"  DROPPED    a clause stands in the source, unbooked    {je['DROPPED']:>3}")
    print(f"  NO CLAUSE  nothing in the fragment states it          {je['NO CLAUSE']:>3}")
    print()
    print("  **The split is a JUDGEMENT over `PFLICHTEN.md` and not a measurement**, so it")
    print("  stands row by row in `messung/gabbrov/PFLICHTEN-KORRESPONDENZ.md` and this run")
    print("  holds every row against the register: a CARRIED row names a line that has to be")
    print("  there, a BLOCKED row names a fragment that has to be without one.")
    print()

    schlecht = 0
    for k in klagen:
        print(f"E1 ZUORDNUNG GEFALLEN: {k}.")
        schlecht = 1
    if klagen:
        print("  Die Tafel sagt etwas, das der Lauf nicht hergibt. **Das ist der Befund, den")
        print("  die fest eingetragene `43` nie ausloesen konnte** -- eine Zahl ohne Bezug auf")
        print("  einen Lauf ueberlebt die Ursache, die sie gezaehlt hat.")
        print()
    for rel, kopf, n in innen_schlecht:
        print(f"E1 INNEN GEFALLEN: {rel} counts {kopf} obligation(s) and writes {n} line(s).")
        print("  A kind that is counted and not printed is the silent loss `SPRACHE.md` §15")
        print("  promises against, INSIDE the artefact that carries the promise.")
        schlecht = 1
    if fehlend != 0:
        print(f"E1 GEFALLEN: {fehlend} of {bev} obligations reach no manifest line.")
        print("  `SPRACHE.md` §15: *\"Nothing is silently lost\"*, and the addressee is named")
        print("  as *\"the programmer OR AN EXTERNAL TOOL\"*. A tool that reads the manifest")
        print(f"  sees {getragen_pflichten} of {bev} -- the rest is lost to it, and silently.")
        print("  **This is the gate, not a warning.** It goes green when the manifest carries")
        print("  its subject, and not before.")
        print(f"  Reachable without a language change: {je['CARRIED'] + je['DROPPED']} of {bev}"
              f" -- the {je['DROPPED']} DROPPED rows name a clause")
        print("  that already stands in the source; §6 of the mapping prices each one.")
        schlecht = 1
    if not schlecht:
        print("== E1: ALL PASS -- every obligation of the population has a manifest line ==")
    if offen:
        print()
        for zustand in ("BLOCKED", "DROPPED", "NO CLAUSE"):
            print(f"== {zustand} -- {je[zustand]} ==")
            for nr, frag, anker, pflicht, z, grund in tafel:
                if z == zustand:
                    print(f"  {nr:>3} {frag} {anker:<12} {pflicht[:62]}")
                    print(f"      {grund[:150]}")
    return schlecht


def sprechprobe():
    """**Three directions**, because this reader has three ways to be wrong quietly."""
    erg = 0
    v1 = ("-- manifest-version 1\n"
          "-- Obligation register: probe.gab\n\n"
          "D  Device promise (`reg` or `transition`) (2)\n"
          "     Vtd :: transition a requires\n"
          "     Vtd :: transition b requires\n\n"
          "== 2 obligations: 0 refinement, 0 preservation, 0 postcondition, 0 foreign, "
          "0 precondition, 2 device, 0 loop invariant, 0 walk invariant ==\n")
    v2 = ("-- manifest-version 2\n"
          "-- Obligation register: probe.gab\n\n"
          "D  Device promise (`reg` or `transition`) (2)\n"
          "obligation\tVtd :: transition a requires\tD\tprobe.gab:11\topen\tGSTS.TES == 0\n"
          "obligation\tVtd :: transition b requires\tD\tprobe.gab:12\topen\tGSTS.RTPS == 1\n\n"
          "== 2 obligations: 0 refinement, 0 preservation, 0 postcondition, 0 foreign, "
          "0 precondition, 2 device, 0 loop invariant, 0 walk invariant ==\n")

    # ONE -- both formats parse, and to the SAME count. A reader that understands only the
    # format it was written against is the step-3-before-step-2 mistake in person.
    for text, wollen in ((v1, 1), (v2, 2)):
        try:
            fassung, kopf, zeilen = lies(text, "probe")
        except Fassungsfehler as e:
            print(f"SPRECHPROBE GESCHEITERT: v{wollen} wird abgelehnt -- {e}", file=sys.stderr)
            return 2
        if (fassung, kopf, len(zeilen)) != (wollen, 2, 2):
            print(f"SPRECHPROBE GESCHEITERT: v{wollen} liest {fassung}/{kopf}/{len(zeilen)}",
                  file=sys.stderr)
            return 2
    print("  beide Fassungen: ok (v1 und v2 ergeben dieselben zwei Zeilen)")

    # TWO -- an unknown version ABORTS. Not a smaller number, not a warning.
    for gift in (v1.replace("version 1", "version 99"), v1.replace("-- manifest-version 1\n", "")):
        try:
            lies(gift, "probe")
        except Fassungsfehler:
            continue
        print("SPRECHPROBE GESCHEITERT: eine unbekannte Fassung wird GEZAEHLT statt "
              "abgelehnt.", file=sys.stderr)
        return 2
    print("  unbekannte Fassung: ok (v99 und eine fehlende Zeile fallen beide)")

    # THREE -- a dropped entry line must break the INNER comparison. Without this direction
    # the guard would notice a missing kind only through the population, i.e. never for a
    # file whose population it does not know.
    for text in (v1, v2):
        zeilen = text.splitlines(keepends=True)
        gestutzt = "".join(z for z in zeilen if not (ZEILE_V1.match(z.rstrip("\n"))
                                                     or ZEILE_V2.match(z)))
        _, kopf, gz = lies(gestutzt, "probe")
        if kopf == len(gz):
            print("SPRECHPROBE GESCHEITERT: ein unterschlagenes Manifest faellt NICHT auf.",
                  file=sys.stderr)
            return 2
    print("  unterschlagene Zeile: ok (Kopfzahl und Zeilenzahl laufen auseinander)")

    # FOUR to SIX -- **the mapping, and it gets its own three directions.** The old split was
    # a sentence, and a sentence cannot be speech-tested; these say what the reader does when
    # the table lies in each of the three ways it can.
    echt = ("| 1 | F01 | 167 | eine Pflicht | CARRIED | `f :: ensures #1` |\n"
            "| 2 | F03 | 587 | eine zweite | BLOCKED | F03 emits no register |\n"
            "| 3 | F01 | 236 | eine dritte | DROPPED | `F01.gab`:236 an der Tabelle |\n"
            "| 4 | F01 | 273 | eine vierte | NO CLAUSE | keine Klausel sagt es |\n")
    lage = {"F01": (True, {"f :: ensures #1"}), "F03": (False, set())}
    z = korrespondenz(echt)
    if len(z) != 4 or pruefe_tafel(z, lage):
        print(f"SPRECHPROBE GESCHEITERT: eine RICHTIGE Tafel wird beanstandet -- "
              f"{pruefe_tafel(z, lage)}", file=sys.stderr)
        return 2
    print("  Zuordnung, richtig: ok (vier Zeilen, vier Zustaende, keine Klage)")

    # FOUR -- a CARRIED row whose line is not in the register.
    gift = echt.replace("`f :: ensures #1`", "`f :: ensures #9`", 1)
    if not any("ensures #9" in k for k in pruefe_tafel(korrespondenz(gift), lage)):
        print("SPRECHPROBE GESCHEITERT: eine CARRIED-Zeile ohne Manifestzeile faellt NICHT auf.",
              file=sys.stderr)
        return 2
    # FIVE -- **a BLOCKED row whose fragment DOES emit a register.** This is the direction the
    # stale `43` needed: three fragments were repaired and the number stood.
    gift2 = echt.replace("| 2 | F03 |", "| 2 | F01 |", 1)
    if not any("no longer exists" in k for k in pruefe_tafel(korrespondenz(gift2), lage)):
        print("SPRECHPROBE GESCHEITERT: ein aufgehobener Blocker wird weiter als Blocker "
              "GEZAEHLT.", file=sys.stderr)
        return 2
    # SIX -- a DROPPED row at a fragment that emits nothing is a BLOCKED row wearing the
    # wrong word, and the two are different findings.
    gift3 = echt.replace("| 3 | F01 | 236 |", "| 3 | F03 | 236 |", 1)
    if not any("not the same finding" in k for k in pruefe_tafel(korrespondenz(gift3), lage)):
        print("SPRECHPROBE GESCHEITERT: eine DROPPED-Zeile an einem blockierten Fragment "
              "faellt NICHT auf.", file=sys.stderr)
        return 2
    print("  Zuordnung, drei Gifte: ok (fehlende Zeile, aufgehobener Blocker, falscher Zustand)")

    # SEVEN -- an unknown state ABORTS. Not a row this reader quietly leaves out: a state it
    # cannot check is a row it cannot count, and a split short by one row still adds up.
    gift4 = echt.replace("NO CLAUSE", "VIELLEICHT", 1)
    try:
        korrespondenz(gift4)
    except Fassungsfehler:
        print("  unbekannter Zustand: ok (er faellt, statt still aus der Summe zu fallen)")
    else:
        print("SPRECHPROBE GESCHEITERT: ein unbekannter Zustand wird UEBERGANGEN.",
              file=sys.stderr)
        return 2
    return erg


def main():
    print("== Sprechprobe des Waechters ==")
    p = sprechprobe()
    if p:
        return p
    print()
    return lauf(zeigen="--zeilen" in sys.argv, offen="--offen" in sys.argv)


if __name__ == "__main__":
    if "--sprechprobe" in sys.argv:
        print("== Sprechprobe des Waechters ==")
        sys.exit(sprechprobe())
    sys.exit(main())
