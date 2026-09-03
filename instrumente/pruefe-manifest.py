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

**This guard is RED today and that is the finding, not a fault.** 10 obligation lines stand
against a population of 63, and the split of the 53 is the thing worth reading:

    blocked upstream   the fragment carries a checker error, so there is no register
                       at all -- NOT a defect of the manifest, and another lane is
                       repairing exactly those four fragments
    dropped            the fragment checks clean, the register is emitted, and the
                       obligation is not in it -- the manifest's own hole

*A number that mixes the two is worth nothing*, so this tool never prints one without the
split. The full working of the split, obligation by obligation, stands in
`messung/gabbrov/MANIFEST-COMPLETENESS.md`.

## Both formats, and that is deliberate

`pflichten.rs::MANIFESTFASSUNG` numbers the register. This reader understands **1 and 2**,
and refuses anything else outright: `CLAUDE.md` holds the measured shape of the alternative
-- seven guards read a document, four went **silently blind** when it moved. *A reader that
guesses at an unknown format reports a number, and a number out of a misread format is worse
than no number.*

    ./instrumente/pruefe-manifest.py                 the split, and the E1 verdict
    ./instrumente/pruefe-manifest.py --zeilen        every obligation line as it stands
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


def lauf(zeigen=False):
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

    print("== E1 -- the manifest against its own subject ==")
    getragen = ohne_register = 0
    innen_schlecht = []
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
        print(f"  {f.name:<9} v{fassung} register  {len(zeilen):2d} obligation line(s)")
        if zeigen:
            for z in zeilen:
                print(f"        {z[0]}")
                if z[1] is not None:
                    print(f"          class {z[1]}  anchor {z[2]}  state {z[3]}")
                    print(f"          text  {z[4]}")

    fehlend = bev - getragen
    print("  ------------------------------------------------------------------")
    print(f"  GabbroV's obligation population                       {bev:>3}")
    print(f"  obligation lines the manifest carries                 {getragen:>3}")
    print(f"  NOT carried                                           {fehlend:>3}")
    print(f"     of which: fragments with NO register at all         {ohne_register} of {len(dateien)}")
    print()
    print("  **The split of the missing lines is NOT derivable from these numbers alone** --")
    print("  a fragment without a register hides an unknown count of obligations, and that")
    print("  count is a judgement over `PFLICHTEN.md`, not a measurement. It is worked out")
    print("  obligation by obligation in `messung/gabbrov/MANIFEST-COMPLETENESS.md`:")
    print("  43 blocked upstream, 15 dropped by the manifest, 5 carried.")
    print()

    schlecht = 0
    for rel, kopf, n in innen_schlecht:
        print(f"E1 INNEN GEFALLEN: {rel} counts {kopf} obligation(s) and writes {n} line(s).")
        print("  A kind that is counted and not printed is the silent loss `SPRACHE.md` §15")
        print("  promises against, INSIDE the artefact that carries the promise.")
        schlecht = 1
    if fehlend != 0:
        print(f"E1 GEFALLEN: {fehlend} of {bev} obligations reach no manifest line.")
        print("  `SPRACHE.md` §15: *\"Nothing is silently lost\"*, and the addressee is named")
        print("  as *\"the programmer OR AN EXTERNAL TOOL\"*. A tool that reads the manifest")
        print(f"  sees {getragen} of {bev} -- the rest is lost to it, and silently.")
        print("  **This is the gate, not a warning.** It goes green when the manifest carries")
        print("  its subject, and not before.")
        schlecht = 1
    if not schlecht:
        print("== E1: ALL PASS -- every obligation of the population has a manifest line ==")
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
    return erg


def main():
    print("== Sprechprobe des Waechters ==")
    p = sprechprobe()
    if p:
        return p
    print()
    return lauf(zeigen="--zeilen" in sys.argv)


if __name__ == "__main__":
    if "--sprechprobe" in sys.argv:
        print("== Sprechprobe des Waechters ==")
        sys.exit(sprechprobe())
    sys.exit(main())
