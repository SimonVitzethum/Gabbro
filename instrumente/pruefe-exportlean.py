#!/usr/bin/env python3
"""**EVERY ACCEPTED EXPORT MUST ELABORATE -- and only Lean can say whether it does.**

    ./instrumente/pruefe-exportlean.py [--binary PATH] [--allow-stale] [--probe]
                                       [--dateien LISTE] [--nur lean-g|obligations]

WHY THIS EXISTS -- a defect with a date
---------------------------------------
On 2026-09-15 an Opus lane ran Lean over the ten files `gabbro lean-g` accepted at that
time. **Four of them did not typecheck**, and they never had:

    error: Insufficient number of fields for `⟨...⟩` constructor: Constructor
    `Speicher.mk` has 2 explicit field, but only 1 was provided

`gSp0` printed ``⟨fun t => nomatch t, (fun g => nomatch g)⟩`` for a table-less unit, and
that is ONE field: `nomatch` takes a COMMA-SEPARATED list of discriminants and swallowed the
second half. **The defect survived because the exporter's tests compare TEXT** -- they check
that the right characters are written, which says nothing about whether the result is a
statement Lean accepts.

> *An export that does not typecheck is a refusal the exporter failed to make.* A generator
> checked against a string is checked against the author's belief about the string.

`instrumente/pruefe-genlean.py` closes the neighbouring loop -- the COMMITTED generated files
are byte for byte what the generator writes today -- and it is text all the way down by
design, because a stale paste is a text question. **This guardian asks the other half, and
it is the only reader in the tree that runs the elaborator over the exporter's output.**

WHAT IT MEASURES
----------------
For every corpus program (`beispiele/*.gab`, `git`-tracked, top level -- the population
`zaehle-kette.py` uses) it runs both generators:

    gabbro lean-g <prog>              sieve (b) of the chain
    gabbro obligations --g <prog>     the export plus the stated obligation

A REFUSAL IS NOT A FINDING. The exporter is allowed -- required -- to refuse a form it has
no G counterpart for, and 101 of 113 programs are refused today. What is a finding is an
export the generator HANDED OUT and Lean will not take:

* a nonzero exit is a refusal and is counted as one;
* an exit 0 with EMPTY output is a finding (an emitter that swallows a program looks exactly
  like one that refuses it, and only the second has said anything);
* an accepted export that Lean answers with `error:` is a finding, with the first error line
  printed beside the program that produced it;
* an accepted export that elaborates only because of a `sorry`, or that decides something by
  `native_decide`, is a finding as well -- Lean's exit code is 0 for both.

AND THE HALF THE BYTE COMPARISON CANNOT REACH
---------------------------------------------
A committed file may paste PART of a generated file -- one namespace, imports dropped. It
cannot carry `pruefe-genlean.py`'s line-1 marker, and that guardian deliberately does not see
it. `Export108.lean` is one, three other files build on its namespace, and on 2026-09-15 its
paste had **drifted**: `requires` had changed shape and `gLs`, `gCs`, `gSp0` and `gE` had
appeared in the generator and not in the paste, while the file's own header went on saying
"pasted verbatim". So a paste names its block:

    -- PASTED from `gabbro lean-g beispiele/108-disjoint-start-locks.gab` block `G108_…`

and this guardian holds that ONE namespace against the same namespace of today's output, byte
for byte -- as well defined as the comparison next door, and readable for a partial paste.
*A paste that carries no marker is seen by nothing; the run prints that as a hole with a name.*

THE VERDICT, AND THE THREE EXITS
--------------------------------
    0   green -- every accepted export elaborates
    1   a finding -- at least one accepted export does not, and each is named
    2   ABBRUCH -- nothing was measured: no binary, a stale binary, no Lean, a model that
        does not build, an empty population, or a generator/elaborator past its deadline

**The work quantity stands beside the verdict** (`pruefe-waechter.py` requirement 4):
`N of M exports checked, K Lean errors`, and the accepted/refused split per generator
underneath it. *A green run over nothing is not a green run* -- an empty population is an
ABBRUCH here, not a pass.

WHAT IT DOES NOT SAY (W10)
--------------------------
That the export is the RIGHT term. Lean answers "this is a well-formed `Einheit gD`", never
"this is the meaning of that `.gab`". The chain count (`zaehle-kette.py`) is where that
question lives, and this guardian is upstream of it: *a term that does not typecheck cannot
be the right one, and until today nothing in the tree noticed when one stopped.*
"""
import argparse
import os
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile
import time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import abschnitt                                          # noqa: E402  the shared cut notice
import korpus                                             # noqa: E402  `git ls-files`, once

W = pathlib.Path(__file__).resolve().parent.parent
GRAMMATIK = W / "grammatik"

# A hang looks like "still running", not like a finding: every foreign tool runs under a
# deadline (`pruefe-waechter.py` requirement 1).
FRIST = 120           # one generator run over one program
LEAN_FRIST = 300      # one `lake env lean` over one export
BAU_FRIST = 1800      # `lake build` of the model -- minutes from cold, 0,1 s warm

# The generators, and the ONLY two. An export is whatever one of these writes; anything else
# is a different question and gets a different guardian.
ERZEUGER = {
    "lean-g": ["lean-g"],
    "obligations --g": ["obligations", "--g"],
}

# **`error:` and nothing else.** Lean prints `info:` for every `#print axioms` a model file
# carries, and a reader that greps for the word "error" in prose reports the ledger comment
# of an export that names one. Measured while writing this: the exports carry neither, but
# the rule has to hold before they do.
LEAN_FEHLER = re.compile(r"(?m)^.*?:\d+:\d+: error: .*$")
# **Two things Lean answers `exit 0` to, and neither is an export that elaborates.**
# A `sorry` is a warning; `native_decide` is a `decide` that trusts the compiler instead of
# the kernel. Both are forbidden in this tree, and both would pass a bare exit-code test.
#
# **The quoting is the toolchain's and not this reader's** (measured 2026-09-15): Lean 4.33
# writes ``declaration uses `sorry` `` with backticks, older ones with apostrophes. A pattern
# that knows one of the two is a pattern that stops matching at the next `lean-toolchain`
# bump -- **silently**, which is the whole class this folder is built against.
LEAN_SORRY = re.compile(r"declaration uses [`'\"]sorry[`'\"]|sorryAx")
NATIVE = re.compile(r"\bnative_decide\b")

# **THE PARTIAL PASTE, and why it needs a marker of its own** (2026-09-15)
# ------------------------------------------------------------------------
# `pruefe-genlean.py` holds a COMMITTED generated file against its generator byte for byte,
# and it finds its work from the `-- GENERATED by …` line the generator writes on line 1. A
# file that pastes only PART of a generated file cannot carry that line, and it deliberately
# does not: a partial paste is not byte-comparable to a whole file, and claiming otherwise
# would be worse than not measuring.
#
# **So it was covered by nothing, and it had drifted.** `Export108.lean` pastes the
# `namespace G108_disjoint_start_locks` block of `gabbro lean-g` and drops the imports; three
# other files build on that namespace. Measured on 2026-09-15 against the generator of that
# day: `requires` had changed shape, and `gLs`, `gCs`, `gSp0` and `gE` had appeared in the
# generator and not in the paste. *The file's own header said "pasted verbatim", and the
# sentence had quietly become false.*
#
# The marker below says which BLOCK of which generator's output the paste is, so the
# comparison is exactly as well defined as the byte comparison next door -- one namespace
# against one namespace. It stands anywhere in the file, not on line 1, because the file is
# not a generated file and must not read like one.
PASTE_MARKE = re.compile(r"(?m)^-- PASTED from `gabbro ([a-z0-9 .\-]+?) (\S+\.gab)` "
                         r"block `(\S+)`")


def absage(*zeilen):
    """Print an ABORT, on stdout AND on stderr. The caller returns `2` on the NEXT line.

    **`abnahme.py` reads an abort's reason from STDERR**, and a guardian that prints it only
    on stdout gets its LAST stdout line quoted instead: here that is the shared cut notice,
    which points at a document and says nothing about why nothing was measured. Measured
    2026-09-15 in a collective run -- the row read
    *`ABBRUCH pruefe-exportlean.py [2] messung/RUECKLAUFWERTE.md, Abschnitt …`*, and the real
    reason (a binary older than its sources) stood four lines above it. *A refusal that names
    itself in the wrong channel is a refusal nobody reads.*

    **And the `return 2` stays at the call site, spelled out.** Folding it in here would
    read better and would make every abort of this guardian INVISIBLE to
    `pruefe-waechter.py`, whose cut sieve looks for a literal `return 2` -- *a tool that
    hides its exits from the tool that counts them measures itself smaller.*
    """
    for z in zeilen:
        print(z)
    print(zeilen[0], file=sys.stderr)
    return 2


def umgebung():
    """`LC_ALL=C`, and the toolchains on PATH.

    **`lake` lives in `~/.elan/bin` and is usually NOT on a non-interactive PATH** -- the
    same fall `zaehle-kette.py --lean` took on 2026-09-15, where the missing launcher
    printed no column at all and the abort read like a finding.

    `LC_ALL=C` because this guardian reads a foreign tool's MESSAGE (requirement 5): under
    `de_DE.UTF-8` a translated `error:` is an error that does not exist.
    """
    env = dict(os.environ)
    env["LC_ALL"] = "C"
    zusatz = [str(pathlib.Path.home() / ".elan" / "bin"),
              str(pathlib.Path.home() / ".cargo" / "bin")]
    pfad = env.get("PATH", "")
    env["PATH"] = os.pathsep.join([p for p in zusatz if pathlib.Path(p).is_dir()] +
                                  ([pfad] if pfad else []))
    return env


def einstufung(rc, ausgabe):
    """`("accepted"|"refused"|"BEFUND", reason)` for one generator run.

    **The one place where a return code becomes a judgement** (W7). Three cases, and the
    third is the one a bare `rc == 0` test loses: a generator that leaves with 0 and writes
    NOTHING has handed out an empty file, and an empty file elaborates green.
    """
    if rc == 0 and ausgabe.strip():
        return "accepted", ""
    if rc == 0:
        return "BEFUND", "the generator left with 0 and wrote NOTHING -- an empty export"
    if rc == 1:
        return "refused", "refused (the exporter has no G form for it)"
    return "BEFUND", f"the generator left with {rc} -- that is neither an export nor a refusal"


def lean_befunde(ausgabe, quelltext, ort=None):
    """The reasons this export is not an export, as a list of lines. Empty means green.

    Reads the ELABORATOR'S MESSAGE, not its exit code alone -- see `LEAN_SORRY`.

    `ort` is the scratch directory, stripped from the message so the reader sees the
    EXPORT and the line, not a temporary path that is different on every run. *A finding
    whose first forty characters are noise gets read as noise.*
    """
    if ort:
        ausgabe = ausgabe.replace(str(ort) + os.sep, "")
    aus = [z.strip() for z in LEAN_FEHLER.findall(ausgabe)]
    if LEAN_SORRY.search(ausgabe):
        aus.append("the export elaborates only through a `sorry`")
    if NATIVE.search(quelltext):
        aus.append("the export decides something by `native_decide`")
    return aus


def block(text, name):
    """The `namespace <name> … end <name>` block of `text`, inclusive -- or `None`.

    **Line-anchored, and the END must match the NAME.** An inner namespace of the same
    shape would otherwise end the block early, and a block that ends early compares equal
    over its first half. *A reader that stops at the first plausible boundary measures the
    boundary.*
    """
    zeilen = text.splitlines(True)
    try:
        i = next(k for k, z in enumerate(zeilen) if z.rstrip() == f"namespace {name}")
        j = next(k for k, z in enumerate(zeilen) if k > i and z.rstrip() == f"end {name}")
    except StopIteration:
        return None
    return "".join(zeilen[i:j + 1])


def pasten():
    """`[(file, subcommand, program, block name)]` for every committed partial paste.

    Read from the FILES, never from a register beside them (W7) -- a second list over one
    thing is the half that ages.
    """
    aus = []
    for p in sorted((GRAMMATIK / "Grammatik").rglob("*.lean")):
        m = PASTE_MARKE.search(p.read_text(encoding="utf-8", errors="replace"))
        if m:
            aus.append((p, m.group(1).strip(), m.group(2), m.group(3)))
    return aus


def population(dateien):
    """The corpus programs, or the list given with `--dateien`.

    Top level of `beispiele/` and `git`-tracked -- **the same population
    `zaehle-kette.py` counts its sieves over**, so the two numbers can be held against each
    other. The recursive glob would catch the poison probes and the frozen excerpts, which
    are not programs this exporter is asked about.
    """
    if dateien:
        return [W / d for d in dateien]
    return sorted(p for p in (W / "beispiele").glob("*.gab") if korpus.verfolgt(p, W))


def lean_lauf(datei):
    """`(rc, ausgabe)` of `lake env lean <datei>`, or `(None, reason)` past the deadline.

    `cwd` is `grammatik/` because that is where the `lakefile.toml` and the built `.olean`
    of the model are; the FILE is passed absolute, so nothing depends on where the caller
    stood. **`lake env lean` and not a bare `lean`**: measured 2026-09-15, the `lean` on
    `PATH` is a different toolchain than the one that wrote the `.olean`, and it answers
    `incompatible header` for every export alike -- *twelve identical failures that say
    nothing about the exports.*
    """
    try:
        r = subprocess.run(["lake", "env", "lean", str(datei)], capture_output=True,
                           text=True, cwd=GRAMMATIK, timeout=LEAN_FRIST, env=umgebung())
    except (OSError, subprocess.TimeoutExpired) as e:
        return None, f"lake env lean did not answer inside {LEAN_FRIST} s ({type(e).__name__})"
    return r.returncode, (r.stdout or "") + (r.stderr or "")


# ------------------------------------------------------------------ the speech test

def sprechprobe_text():
    """`[(what, ok)]` -- the directions that need no Lean, on INVENTED output.

    A guardian that reads only its own subject measures how well the subject fits it.
    """
    fehler = ("E_x.lean:138:2: error: Insufficient number of fields for `⟨...⟩` "
              "constructor\n")
    hinweis = ("info: Grammatik/CText108.lean:177:0: 'kette_108' depends on axioms: "
               "[propext]\n")
    return [
        ("an `error:` line is read as a finding",
         lean_befunde(fehler, "") == ["E_x.lean:138:2: error: Insufficient number of "
                                      "fields for `⟨...⟩` constructor"]),
        ("an `info:` line is NOT -- a model that prints its axioms is green",
         lean_befunde(hinweis, "") == []),
        ("the word 'error' in PROSE is not an error line",
         lean_befunde("-- NO FORM: an error of the old exporter\n", "") == []),
        ("the scratch path is stripped -- the finding names the EXPORT, not a temp dir",
         lean_befunde("/a/b/exportlean-x/lean-g_73.lean:9:1: error: boom\n", "",
                      pathlib.Path("/a/b/exportlean-x")) ==
         ["lean-g_73.lean:9:1: error: boom"]),
        ("a `sorry` is a finding although Lean leaves with 0",
         lean_befunde("x.lean:2:0: warning: declaration uses `sorry`\n", "") ==
         ["the export elaborates only through a `sorry`"]),
        ("and with the OTHER quoting too -- the toolchain picks it, not this reader",
         lean_befunde("warning: declaration uses 'sorry'\n", "") ==
         ["the export elaborates only through a `sorry`"]),
        ("`native_decide` in the export is a finding",
         lean_befunde("", "theorem t : x := by native_decide\n") ==
         ["the export decides something by `native_decide`"]),
        ("exit 0 with text is an ACCEPTED export", einstufung(0, "def gE := 1\n")[0] ==
         "accepted"),
        ("exit 0 with NOTHING is a finding, not an export", einstufung(0, "")[0] == "BEFUND"),
        ("exit 1 is a REFUSAL and not a finding", einstufung(1, "")[0] == "refused"),
        ("any other exit is a finding -- a crash is not a refusal",
         einstufung(101, "")[0] == "BEFUND"),
        ("a PASTE marker names its generator, its program and its block",
         PASTE_MARKE.search("-- PASTED from `gabbro lean-g beispiele/9.gab` block `G9`\n")
         .groups() == ("lean-g", "beispiele/9.gab", "G9")),
        ("and a file without one is not a paste",
         PASTE_MARKE.search("-- a note about a paste\n") is None),
        ("the block is cut at its OWN `end`, not at the first one",
         block("namespace A\nnamespace B\nend B\nx\nend A\nend C\n", "A") ==
         "namespace A\nnamespace B\nend B\nx\nend A\n"),
        ("a block that is not there comes back as absent, not as empty",
         block("namespace A\nend A\n", "Z") is None),
        ("one line changed is a DIFFERENT block",
         block("namespace A\nx\nend A\n", "A") != block("namespace A\ny\nend A\n", "A")),
    ]


# **The Lean half, and it is the direction this whole guardian exists for.**
#
# The broken file below is the DEFECT OF 2026-09-15, spelled out on invented text: two
# fields, and `nomatch` swallowing the second because its discriminant list is
# comma-separated. It must fall. The good one is the same file with both halves
# parenthesised -- the repair -- and it must go through.
#
# *One direction alone would pass with an elaborator that refuses everything, and the other
# alone with one that is never asked.*
PROBE_GUT = """import Grammatik.Zielsatz.Spec
namespace Gabbro.Grammatik.ProbeExportLean
structure Zwei where
  a : Empty -> Nat
  b : Empty -> Nat
def zwei : Zwei := ⟨(fun t => nomatch t), (fun g => nomatch g)⟩
#print axioms Nat.add_comm
end Gabbro.Grammatik.ProbeExportLean
"""
PROBE_KAPUTT = PROBE_GUT.replace("⟨(fun t => nomatch t), (fun g => nomatch g)⟩",
                                 "⟨fun t => nomatch t, (fun g => nomatch g)⟩")
PROBE_SORRY = """import Grammatik.Zielsatz.Spec
namespace Gabbro.Grammatik.ProbeExportLeanSorry
example : 1 = 1 := by sorry
end Gabbro.Grammatik.ProbeExportLeanSorry
"""


def sprechprobe_lean(arbeit):
    """`[(what, ok)]` -- both directions THROUGH the elaborator, on invented files."""
    aus = []
    for name, text, soll in (("gut", PROBE_GUT, True),
                             ("kaputt", PROBE_KAPUTT, False),
                             ("sorry", PROBE_SORRY, False)):
        p = arbeit / f"ProbeExportLean_{name}.lean"
        p.write_text(text, encoding="utf-8")
        rc, ausgabe = lean_lauf(p)
        if rc is None:
            aus.append((f"the {name} probe answered at all -- {ausgabe}", False))
            continue
        befunde = lean_befunde(ausgabe, text, arbeit)
        if soll:
            aus.append(("an export that IS well formed goes through "
                        "(both halves parenthesised)", not befunde and rc == 0))
        elif name == "kaputt":
            aus.append(("and the defect of 2026-09-15 FALLS -- `nomatch` swallowing the "
                        "second field", bool(befunde) and
                        any("Insufficient number of fields" in b for b in befunde)))
        else:
            aus.append(("a `sorry` falls although Lean leaves with 0",
                        bool(befunde) and rc == 0))
    return aus


# ------------------------------------------------------------------ the run

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--binary", default=str(W / "target" / "debug" / "gabbro"))
    ap.add_argument("--allow-stale", action="store_true")
    ap.add_argument("--probe", action="store_true", help="only the speech test")
    ap.add_argument("--dateien", nargs="*", default=None,
                    help="the programs to measure (default: the tracked corpus)")
    ap.add_argument("--nur", choices=sorted(ERZEUGER), default=None,
                    help="only this generator")
    args = ap.parse_args()

    print("== Speech test -- on invented output, in both directions ==")
    probe = sprechprobe_text()
    for was, ok in probe:
        print(f"  probe: {'ok  ' if ok else 'FAIL'} {was}")
    if not all(ok for _, ok in probe):
        absage("ABBRUCH: the speech test of this guardian failed -- it "
               "measured NOTHING")
        return 2

    # ---- the setup, before anything is called a finding --------------------------------
    binary = pathlib.Path(args.binary)
    if not binary.exists():
        absage(f"ABBRUCH: NO GABBRO at {binary} -- it is built on "
               f"ki-pc-fisch-101 (CLAUDE.md), or pass --binary")
        return 2
    stand = binary.stat().st_mtime
    neuer = sorted(q for q in W.glob("crates/*/src/*.rs") if q.stat().st_mtime > stand)
    if neuer and not args.allow_stale:
        absage(f"ABBRUCH: the binary is OLDER than {len(neuer)} source file(s) "
               f"under crates/ (first: {neuer[0].relative_to(W)}) -- it exports "
               f"another program",
               "  (build it, or pass --allow-stale to measure that binary anyway)")
        return 2
    if not shutil.which("lake", path=umgebung()["PATH"]):
        absage("ABBRUCH: NO LEAN -- `lake` is not on PATH (~/.elan/bin on "
               "ki-pc-fisch-101); a missing tool is not a passed test (W1)",
               "  NOTHING was measured.")
        return 2

    print()
    print("== The model -- an export is elaborated AGAINST it, so it is built first ==")
    t0 = time.monotonic()
    try:
        r = subprocess.run(["lake", "build"], capture_output=True, text=True,
                           cwd=GRAMMATIK, timeout=BAU_FRIST, env=umgebung())
    except (OSError, subprocess.TimeoutExpired):
        absage(f"ABBRUCH: `lake build` did not answer inside {BAU_FRIST} s -- "
               f"NOTHING was measured")
        return 2
    if r.returncode != 0:
        for z in (r.stdout or "").splitlines()[-8:]:
            print(f"     {z}")
        absage("ABBRUCH: the MODEL does not build -- every export would fall "
               "for its reason, not its own")
        return 2
    print(f"   grammatik/ built in {time.monotonic() - t0:.1f} s")

    # The scratch tree. **Never `/tmp`** (it is RAM on the orchestrator), and never inside
    # `grammatik/` -- a `.lean` file dropped there is a module `lake` builds, which is the
    # same class as a scratch `.gab` inside `beispiele/`: *a scratch file inside the
    # measured tree is a corpus file.* `.claude/` is gitignored, and `mkdtemp` keeps two
    # runs out of each other's files.
    kratz = W / ".claude"
    kratz.mkdir(exist_ok=True)
    arbeit = pathlib.Path(tempfile.mkdtemp(prefix="exportlean-", dir=str(kratz)))
    try:
        return messe(args, binary, arbeit)
    finally:
        shutil.rmtree(arbeit, ignore_errors=True)


def messe(args, binary, arbeit):
    print()
    print("== Speech test through the ELABORATOR -- the defect of 2026-09-15, both ways ==")
    probe = sprechprobe_lean(arbeit)
    for was, ok in probe:
        print(f"  probe: {'ok  ' if ok else 'FAIL'} {was}")
    if not all(ok for _, ok in probe):
        absage("ABBRUCH: the Lean half of the speech test failed -- this "
               "guardian cannot tell a well-formed export from a broken one, so it "
               "measured NOTHING")
        return 2
    if args.probe:
        n = len(probe) + len(sprechprobe_text())
        print(f"pruefe-exportlean: speech test only, {n} of {n} directions ok")
        return 0

    programme = population(args.dateien)
    if not programme:
        absage("ABBRUCH: the population is EMPTY -- no tracked "
               "`beispiele/*.gab`. A green judgement over nothing is none (W17).")
        return 2
    unter = [args.nur] if args.nur else sorted(ERZEUGER)

    print()
    print(f"== {len(programme)} corpus programs x {len(unter)} generator(s) ==")
    befunde = []
    angenommen = {u: 0 for u in unter}
    abgelehnt = {u: 0 for u in unter}
    geprueft = 0
    lean_fehler = 0
    bytes_geprueft = 0
    pasten_bytes = 0
    for prog in programme:
        rel = prog.relative_to(W)
        for u in unter:
            try:
                r = subprocess.run([str(binary)] + ERZEUGER[u] + [str(rel)],
                                   capture_output=True, text=True, cwd=W, timeout=FRIST,
                                   env=umgebung())
            except (OSError, subprocess.TimeoutExpired):
                absage(f"ABBRUCH: `gabbro {u} {rel}` did not answer inside "
                       f"{FRIST} s")
                return 2
            marke, grund = einstufung(r.returncode, r.stdout or "")
            if marke == "refused":
                abgelehnt[u] += 1
                continue
            if marke == "BEFUND":
                befunde.append((rel.name, u, grund))
                print(f"  BEFUND  {rel.name:<34} {u:<16} {grund}")
                continue
            angenommen[u] += 1
            ziel = arbeit / f"{u.split()[0]}_{prog.stem}.lean"
            ziel.write_text(r.stdout, encoding="utf-8")
            rc, ausgabe = lean_lauf(ziel)
            if rc is None:
                absage(f"ABBRUCH: {ausgabe} (over {rel.name}, {u})")
                return 2
            geprueft += 1
            bytes_geprueft += len(r.stdout)
            schlecht = lean_befunde(ausgabe, r.stdout, arbeit)
            if not schlecht and rc != 0:
                schlecht = [f"lean left with {rc} and printed no `error:` line"]
            if schlecht:
                lean_fehler += 1
                befunde.append((rel.name, u, schlecht[0]))
                print(f"  BEFUND  {rel.name:<34} {u:<16} LEAN: {schlecht[0]}")
                for z in schlecht[1:4]:
                    print(f"          {'':<34} {'':<16}       {z}")
            else:
                print(f"  ok      {rel.name:<34} {u:<16} {len(r.stdout)} bytes elaborate")

    gesamt = sum(angenommen.values())
    print()
    for u in unter:
        print(f"   `gabbro {u}`: {angenommen[u]} accepted, {abgelehnt[u]} refused "
              f"of {len(programme)} programs")
    print("   **A refusal is NOT a finding.** The exporter is required to refuse a form it")
    print("   has no G counterpart for; what is measured here is what it HANDED OUT.")
    if gesamt == 0:
        absage("ABBRUCH: not one program was accepted by any generator -- there "
               "is nothing to elaborate, and a green run over nothing is not a "
               "green run (W17).")
        return 2

    # ---- the committed PARTIAL pastes -------------------------------------------------
    # The half `pruefe-genlean.py` cannot reach: a file that pastes one namespace of a
    # generated file and drops the imports. See `PASTE_MARKE` for why it needs a marker of
    # its own and what had drifted behind the gap.
    print()
    p_dateien = pasten()
    print(f"== {len(p_dateien)} committed PARTIAL paste(s) -- the half a byte comparison "
          f"cannot reach ==")
    for quelle, u, prog, name in p_dateien:
        kurz = quelle.relative_to(W)
        if u not in ERZEUGER:
            befunde.append((str(kurz), u, "unknown generator -- no command line is guessed"))
            print(f"  BEFUND  {kurz}: unknown generator `gabbro {u}`")
            continue
        try:
            r = subprocess.run([str(binary)] + ERZEUGER[u] + [prog], capture_output=True,
                               text=True, cwd=W, timeout=FRIST, env=umgebung())
        except (OSError, subprocess.TimeoutExpired):
            absage(f"ABBRUCH: `gabbro {u} {prog}` did not answer inside "
                   f"{FRIST} s")
            return 2
        if r.returncode != 0 or not r.stdout:
            befunde.append((str(kurz), u, f"the generator refuses {prog} today "
                                          f"(exit {r.returncode}) -- the paste has no source"))
            print(f"  BEFUND  {kurz}: `gabbro {u} {prog}` refuses it today "
                  f"(exit {r.returncode})")
            continue
        hier = block(quelle.read_text(encoding="utf-8", errors="replace"), name)
        dort = block(r.stdout, name)
        if hier is None or dort is None:
            wo = "the committed file" if hier is None else "today's output"
            befunde.append((str(kurz), u, f"no `namespace {name}` block in {wo}"))
            print(f"  BEFUND  {kurz}: no `namespace {name}` block in {wo}")
            continue
        pasten_bytes += len(hier)
        if hier == dort:
            print(f"  ok      {kurz}: block `{name}` is byte-identical to "
                  f"`gabbro {u} {prog}` ({len(hier)} bytes)")
            continue
        stelle = next((i for i, (a, b) in enumerate(zip(hier, dort)) if a != b),
                      min(len(hier), len(dort)))
        befunde.append((str(kurz), u, f"the pasted block `{name}` is NOT what the "
                                      f"generator writes today"))
        print(f"  BEFUND  {kurz}: the pasted block `{name}` is NOT what "
              f"`gabbro {u} {prog}` writes today")
        print(f"          committed {len(hier)} bytes, generated {len(dort)} bytes, "
              f"first difference at byte {stelle}")
        print(f"          committed …{hier[max(0, stelle - 40):stelle + 20]!r}")
        print(f"          generated …{dort[max(0, stelle - 40):stelle + 20]!r}")
    if not p_dateien:
        print("   None in the tree -- the marker is a `-- PASTED from `gabbro …` block `X``")
        print("   line. **That is a hole with a name, not a tick**: a paste that carries no")
        print("   marker is seen by nothing, here or in `pruefe-genlean.py`.")

    abschnitt.fertig()      # from here on nothing more is measured
    fehler = len(befunde)
    print()
    print(f"pruefe-exportlean: {geprueft} of {gesamt} exports checked, "
          f"{lean_fehler} Lean errors, {len(p_dateien)} pasted block(s) compared, "
          f"{fehler} findings in all, "
          f"{bytes_geprueft + pasten_bytes} bytes elaborated or compared")
    print("== EXPORTLEAN: " + ("GRUEN" if fehler == 0 else f"{fehler} BEFUNDE") + " ==")
    if fehler:
        print("   An export that does not typecheck is a refusal the exporter failed to")
        print("   make, and a paste that is no longer the generator's output is a program")
        print("   the proofs beside it are not about. Each finding above names its file.")
    else:
        print("   And what that does NOT mean: that the export is the RIGHT term. Lean says")
        print("   `this is a well-formed Einheit gD`, never `this is the meaning of that")
        print("   .gab` -- that question lives in `zaehle-kette.py` (W10).")
    return 1 if fehler else 0


if __name__ == "__main__":
    sys.exit(abschnitt.fahre(main))
