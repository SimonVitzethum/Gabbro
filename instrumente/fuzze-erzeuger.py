#!/usr/bin/env python3
"""Run `gabbro emit` over every rung the boundary sweep accepts -- and hold the EMITTER to
the promise its own refusal code was written for.

    C001: THE EMITTER REFUSES INSTEAD OF GUESSING.

`fuzze-grenzen.py` holds the CHECKER to *accept, or refuse by name*. Its closing note names
what it cannot do:

    `gabbro emit` is not part of the property. A sweep holding the emitter to "lowers, or
    refuses by name" is the obvious next instrument and does not exist.

That gap cost something real. `emit.rs::konst_zahl` read every compile-time number as
`Some(*n as i128)` -- the same lossy cast the audit had repaired three times in the checker,
still live in the back end and read from sixteen sites. **The emitter did not fail; it wrote
a different number**: `entry ... vector = u128::MAX` came out as `* vector -1`. It was found
by reading C by hand, and nothing measured it.

THE PROPERTY, AND IT HAS THREE ANSWERS
--------------------------------------
For an input the checker ACCEPTS (`gabbro pruefe`, exit 0), `gabbro emit` must either

  A. LOWER it -- exit 0, C on stdout, and that C compiles under
     `cc -std=c11 -O0 -Wall -Wextra -Werror -c`; or
  B. REFUSE BY NAME -- `C001`, with a note saying what it cannot lower.

Anything else is a defect, and the shapes are named one by one below. **Both build profiles
must agree, and their C must be byte-identical** -- there is no `[profile.release]` in
`Cargo.toml`, so overflow checks are on in debug and off in release, and release is what
`cargo install` produces.

WHAT AN ORACLE COSTS, AND WHERE THIS ONE COMES FROM
---------------------------------------------------
Shape 3 -- *C that compiles and computes something else* -- is the `konst_zahl` class and the
dangerous one. It needs an oracle, and there is no oracle in general. **There is a cheap one
in particular**: a compile-time constant that appears literally in the emitted C can be
compared against the literal in the source.

The oracle CALIBRATES ITSELF and is not asserted. For every form the sweep emits the
baseline once; a form counts as oracle-able only where some accepted rung demonstrably put
its own value into the C that the baseline's C does not carry. A form whose C never carries
the swept value -- a `costs` clause, a bare range type, a ghost `spec fn` -- is excluded from
the numerator AND from the denominator, and both numbers are printed. *A denominator that
counts what could never have been measured is `W25`.*

    ./instrumente/fuzze-erzeuger.py --debug target/debug/gabbro --release target/release/gabbro

BEYOND THE PROPERTY -- three nets, each named, each with its reason
-------------------------------------------------------------------
The bare property misses defects that are visible in the emitted C, so three further nets
run beside it and are reported in their own section:

  5. NOT ISO C -- the same compile again with `-Wpedantic`. GCC accepts a zero-length array
     as an extension and says nothing under `-Wall -Wextra -Werror`; ISO C forbids it.
  6. AN IDENTIFIER PAST C11 SIGNIFICANCE -- C11 5.2.4.1 promises 63 significant characters
     in an internal identifier and 31 in an external one. A conforming compiler may fold
     everything past that, and then two distinct Gabbro names become one C object.
  7. DEGENERATE CONSTANT ARITHMETIC -- a generated expression multiplied by a literal zero
     computes the same value for every input, so the field it claims to read is not read.
     (`% 0` and `/ 0` need no rule here: `-Wdiv-by-zero` is on by default and shape 2 has
     them.)

*These three are defects, not style.* They are separated from shapes 1-4 because the mandate
this tool answers names four, and a report that quietly widens its own property is not a
measurement of the one that was asked for.

BOOKED FINDINGS -- and why a booked one is still printed
--------------------------------------------------------
`GEBUCHT` carries the findings that were standing when this tool was written, one line each
with where they are recorded. **They are printed at every run**, with their count; the
verdict counts only what is NOT booked. A booked finding whose count RISES is red, and so is
a booked finding that has VANISHED -- a stale booking hides the next one. *That is the same
bolt `pruefe-widerruf.py` puts on a withdrawal: a booking is a claim about the tree and it
expires.*

WHAT THIS TOOL DOES NOT MEASURE
-------------------------------
* **Programs, not fragments.** Every case is one declaration form with one slot moved. Two
  slots at their boundaries together is a different sweep.
* **The C is compiled, not RUN.** `pruefe-emission.sh` runs seven units under UBSan and ASan
  and compares results; this one holds 63 forms to compilation. A generated expression that
  compiles and computes the wrong thing passes here unless the oracle sees the number.
* **The checker's own answer is taken as given.** A rung both profiles accept wrongly is
  invisible to this property by construction -- the same limit `fuzze-grenzen.py` names for
  itself, one storey down.
"""

import argparse
import concurrent.futures
import importlib.util
import pathlib
import re
import subprocess
import sys
import tempfile

# `sys.path` gets the tool's own directory, the same reason as in `fuzze-grenzen.py`: this
# file may be LOADED rather than run, and then `sys.path[0]` is the working directory.
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import abschnitt  # noqa: E402

W = pathlib.Path(__file__).resolve().parent.parent

# **A DECLARED deadline.** Every subprocess carries one; a hang is a state and not a finding
# (`pruefe-waechter.py`, requirement one).
FRIST = 40

# The compile gate of the property, and the tree's own: `pruefe-emission.sh` stage 3 uses
# exactly these switches over every emitting unit.
TOR = ["-std=c11", "-O0", "-Wall", "-Wextra", "-Werror", "-c"]
# Net 5. One switch more, and it is the one that separates GCC's extensions from ISO C.
TOR_ISO = TOR + ["-Wpedantic"]

# C11 5.2.4.1. A conforming implementation need not distinguish beyond these lengths.
C11_INNEN = 63
C11_AUSSEN = 31


# ==========================================================================================
# THE FORM TABLE IS NOT COPIED -- it is READ out of `fuzze-grenzen.py`
# ==========================================================================================
#
# **Two tables over one grammar drift apart, and the drift is silent** (`W7`). The boundary
# sweep already carries 63 templates, their known-good baselines, their ladders and the EBNF
# rule each one drives; a second copy here would be green about a form the other one has
# since repaired. The file name carries a hyphen, so it is loaded by path rather than
# imported by name.
def grenzen_laden():
    pfad = pathlib.Path(__file__).resolve().parent / "fuzze-grenzen.py"
    spec = importlib.util.spec_from_file_location("fuzze_grenzen", pfad)
    if spec is None or spec.loader is None:
        return None
    modul = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(modul)
    return modul


# ==========================================================================================
# READING THE ANSWER
# ==========================================================================================

def lauf(argv, timeout=FRIST):
    """One subprocess. Returns (exit, panicked, stdout, stderr). NEVER raises."""
    try:
        p = subprocess.run(argv, capture_output=True, text=True,
                           timeout=timeout, errors="replace")
    except subprocess.TimeoutExpired:
        return (None, False, "", "<TIMEOUT>")
    except OSError as e:
        return (None, False, "", f"<NOT RUNNABLE: {e}>")
    panik = "panicked at" in p.stderr or "RUST_BACKTRACE" in p.stderr
    return (p.returncode, panik, p.stdout, p.stderr)


KODE = re.compile(r"\[([A-Z]\d{3})\]")


def kodes(text):
    """Every refusal code the diagnostic printed, as a sorted list."""
    return sorted(set(KODE.findall(text)))


def emit_antwort(exit_code, panik, aus, fehler):
    """Which of the three answers came back -- LOWER, REFUSE C001, or a third one.

    Not the full diagnostic text: two builds may word a message differently one day. What
    must agree is WHICH answer, and -- when it is a refusal -- WHICH code.
    """
    if panik:
        return "PANIC"
    if exit_code is None:
        return "TIMEOUT" if "<TIMEOUT>" in fehler else "NOT-RUNNABLE"
    k = kodes(fehler)
    if exit_code == 0:
        return "LOWER" if aus.strip() else "LOWER-EMPTY"
    if k:
        return "REFUSE " + ",".join(k)
    return f"EXIT{exit_code}-UNNAMED"


# **The note is part of the promise, not decoration.** `C001` says *no lowering*; the note
# says WHAT could not be lowered. A code without one leaves the reader with a wall.
NOTIZ = re.compile(r"^\s*= ", re.M)


# ==========================================================================================
# THE ORACLE -- literals of the source, found again in the C
# ==========================================================================================

ZAHL_IN_C = re.compile(r"(-\s*)?(0[xX][0-9a-fA-F_]+|0[bB][01_]+|\d[\d_]*)")


def ganzzahlen(text):
    """Every integer literal in a C text, as a set of ints -- sign included.

    `a - 1` is read as `-1` here, and that is the safe direction: it can only make the
    oracle MISS a finding about a negative value, never invent one.
    """
    aus = set()
    for m in ZAHL_IN_C.finditer(text):
        roh = m.group(2).replace("_", "")
        try:
            v = int(roh, 0) if roh[:2].lower() in ("0x", "0b") else int(roh, 10)
        except ValueError:
            continue
        aus.add(-v if m.group(1) else v)
    return aus


BEZEICHNER = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")


def bezeichner(text):
    """Every C identifier in the text, as a set."""
    return set(BEZEICHNER.findall(text))


def quellwert(roh):
    """The integer a swept value denotes -- or `None` when it is not one.

    The ladders carry decimal, hex, binary and signed rungs, plus shapes that are not
    numbers at all (`0xG`, `1__2`, a name, a string). Only the first four have a value the
    emitted C could carry.
    """
    s = roh.strip()
    neg = s.startswith("-")
    if neg:
        s = s[1:].strip()
    if "_" in s:
        # A separator is legal in Gabbro; `int(..., 0)` reads it too, but not `1__2`.
        if "__" in s or s.startswith("_") or s.endswith("_"):
            return None
        s = s.replace("_", "")
    try:
        v = int(s, 0) if s[:2].lower() in ("0x", "0b") else int(s, 10)
    except ValueError:
        return None
    return -v if neg else v


# ==========================================================================================
# NET 7 -- a generated expression that cannot read its input
# ==========================================================================================
#
# **Multiplication by a literal zero is the whole rule**, and it is narrow on purpose. The
# other two degenerate constants -- `% 0` and `/ 0` -- need no rule of their own:
# `-Wdiv-by-zero` is in GCC's default set, so `-Werror` already turns them into shape 2.
MAL_NULL = re.compile(r"\*\s*0[uUlL]*\b(?![.xXbB0-9])")


def entartet(c):
    """The degenerate constant expressions in an emitted C text, as a list of snippets."""
    aus = []
    for m in MAL_NULL.finditer(c):
        zeile = c[:m.start()].count("\n") + 1
        anfang = c.rfind("\n", 0, m.start()) + 1
        ende = c.find("\n", m.end())
        aus.append((zeile, c[anfang:ende if ende >= 0 else len(c)].strip()))
    return aus


# ==========================================================================================
# BOOKED FINDINGS -- what was standing when this tool was written
# ==========================================================================================
#
# Key: `(shape, form)`. Value: `(count, where it is recorded)`. **A booked finding is
# printed at every run.** The verdict counts what is not booked; a count that RISES is red,
# and so is a booking whose finding has vanished -- a stale booking hides the next one.
#
# *Each of these was found by this tool on its first full run, not entered from a list.*
GEBUCHT = {
    ("NOT-ISO", "table-count"):
        (2, "`table count 0` lowers to `T_slot slots[0]` -- ISO C forbids a zero-size "
            "array, GCC takes it as an extension. AUDIT-2026-09-02 7.7 item 4 books it as "
            "`refused at emit`, and that is the half this run corrects: it is NOT refused"),
    ("NOT-ISO", "const-als-schranke"):
        (2, "the same zero-size array through a `const` used as the table bound"),
    ("NOT-ISO", "acc-percpu"):
        (2, "`accumulates ... per cpu 0` lowers to a zero-size cell array"),
    ("NAME-LEN", "name-const"):
        (11, "AUDIT-2026-09-02 7.7 item 5 -- a name of any length is written into C"),
    ("NAME-LEN", "name-fn"): (11, "the same, at a function name"),
    ("NAME-LEN", "name-feld"): (11, "the same, at a `format` field"),
    ("NAME-LEN", "name-reg"): (11, "the same, at a device register"),
    ("NAME-LEN", "name-tabelle"): (11, "the same, at a table"),
    ("NAME-LEN", "name-typ"): (11, "the same, at an opaque type"),
    ("NAME-LEN", "name-parameter"): (11, "the same, at a parameter"),
    ("NAME-LEN", "name-modul"): (11, "the same, at a module -- it prefixes every C name"),
    ("ENTARTET", "embeds-scale"):
        (1, "AUDIT-2026-09-02 7.7 item 4 -- `embeds ... scale 0` lowers, and the extracted "
            "frame number is multiplied by zero, so every record yields address zero"),
}


# ==========================================================================================
# ONE CASE
# ==========================================================================================

def eine_probe(auftrag):
    """Everything measured about one generated file. A pure worker -- no shared state."""
    (form, wert, quelle, pfad, dbg, rel, cc, basis_zahlen, basis_namen) = auftrag
    pfad.write_text(quelle, encoding="utf-8")
    e = {"form": form, "wert": wert, "pfad": str(pfad)}

    # **The precondition is MEASURED and not inferred.** The property speaks about inputs the
    # checker accepts; reading that off the emitter's own diagnostic would let a checker
    # refusal and an emitter refusal share one number.
    pe, pp, _, pf = lauf([dbg, "pruefe", str(pfad)])
    e["angenommen"] = (pe == 0 and not pp)
    if not e["angenommen"]:
        e["pruefer"] = "PANIC" if pp else ("TIMEOUT" if pe is None else ",".join(kodes(pf)))
        return e

    de, dp, da, df = lauf([dbg, "emit", str(pfad)])
    re_, rp, ra, rf = lauf([rel, "emit", str(pfad)])
    e["debug"] = emit_antwort(de, dp, da, df)
    e["release"] = emit_antwort(re_, rp, ra, rf)
    e["gleich"] = (da == ra)
    e["panik_text"] = (df if dp else rf).strip()[:400]

    if e["debug"].startswith("REFUSE"):
        # A refusal is only a refusal when it says what it could not lower.
        e["notiz"] = bool(NOTIZ.search(df))
        e["absagetext"] = df.strip().splitlines()[0][:200] if df.strip() else ""
        return e

    if e["debug"] not in ("LOWER", "LOWER-EMPTY"):
        e["stderr"] = df.strip()[:400]
        return e

    c = da
    e["c_laenge"] = len(c)

    # Shape 2 and net 5 -- the same text, two gates.
    e["uebersetzt"], e["cc_text"] = uebersetze(cc, TOR, c, pfad)
    e["iso"], e["iso_text"] = uebersetze(cc, TOR_ISO, c, pfad)

    # Shape 3 -- the oracle. Only where the source value IS an integer.
    v = quellwert(wert)
    e["wert_zahl"] = v
    if v is not None:
        zc = ganzzahlen(c)
        e["traegt_wert"] = v in zc
        e["neu_gegen_basis"] = (v in zc) and (v not in basis_zahlen)
    # The same for a swept NAME: it must reach the C, and it must be distinguishable there.
    if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", wert or ""):
        nc = bezeichner(c)
        e["traegt_namen"] = wert in nc
        e["neuer_name"] = (wert in nc) and (wert not in basis_namen)

    # Net 6 -- C11 significance.
    lang = [n for n in bezeichner(c) if len(n) > C11_INNEN]
    e["zu_lang"] = max((len(n) for n in lang), default=0)
    # Net 7 -- degenerate constant arithmetic.
    e["entartet"] = entartet(c)
    return e


def uebersetze(cc, schalter, c, pfad):
    """Compile one emitted text. Returns (ok, first lines of the compiler's complaint)."""
    cpfad = pfad.with_suffix(".c")
    cpfad.write_text(c, encoding="utf-8")
    rc, _, _, fehler = lauf(cc + schalter + ["-o", "/dev/null", str(cpfad)], timeout=FRIST)
    if rc == 0:
        return True, ""
    return False, "\n".join(fehler.strip().splitlines()[:4])


# ==========================================================================================
# THE SPEECH TEST -- in both directions, and it runs BEFORE the sweep
# ==========================================================================================
#
# *A guardian nobody has seen fall is an ornament* (R11). Five probes, each with the
# counter-direction beside it: what must fall, falls; what must not, does not.

SP_SAUBER = "int gabbro_probe(void) { return 0; }\n"
SP_WARNUNG = "int gabbro_probe(void) { int x; return 0; }\n"
SP_NULLFELD = "struct s { int n; int a[0]; };\nint gabbro_probe(void) { return 0; }\n"


def sprechprobe(cc, arb):
    """Returns the list of FAILURES. Empty means every net can still speak."""
    tot = []
    p = arb / "sprechprobe.gab"

    ok, _ = uebersetze(cc, TOR, SP_SAUBER, p)
    if not ok:
        tot.append("the compile gate refuses a clean file -- stage 2 cannot say `passed`")
    ok, _ = uebersetze(cc, TOR, SP_WARNUNG, p)
    if ok:
        tot.append("the compile gate ACCEPTS an unused variable -- `-Werror` is not biting, "
                   "and every case would come back green")

    ok, _ = uebersetze(cc, TOR, SP_NULLFELD, p)
    if not ok:
        tot.append("the plain gate refuses a zero-size array -- then net 5 measures nothing "
                   "of its own")
    ok, _ = uebersetze(cc, TOR_ISO, SP_NULLFELD, p)
    if ok:
        tot.append("`-Wpedantic` ACCEPTS a zero-size array -- net 5 is blind")

    # The oracle, over text this tool wrote itself.
    if 4096 not in ganzzahlen("x * 4096u"):
        tot.append("the oracle does not read a decimal literal out of C")
    if 128 not in ganzzahlen("v = 0x80;"):
        tot.append("the oracle does not read a hex literal out of C")
    if -1 not in ganzzahlen("vector -1"):
        tot.append("the oracle does not read a signed literal -- the `konst_zahl` shape")
    if (1 << 128) - 1 in ganzzahlen("vector -1"):
        tot.append("the oracle finds a value that is not there")
    if quellwert("0xFF") != 255 or quellwert("-2") != -2 or quellwert("0xG") is not None:
        tot.append("`quellwert` does not read the ladder's own rungs")

    # Net 6 and net 7, both directions.
    if max((len(n) for n in bezeichner("a" * 64 + " b;")), default=0) <= C11_INNEN:
        tot.append("net 6 does not see a 64-character identifier")
    if max((len(n) for n in bezeichner("short_name x;")), default=0) > C11_INNEN:
        tot.append("net 6 fires on an ordinary name")
    if not entartet("return (x >> 12) * 0u;"):
        tot.append("net 7 does not see a multiplication by zero")
    if entartet("return x * 4096u;") or entartet("return x * 0x10u;"):
        tot.append("net 7 fires on an ordinary multiplication")
    return tot


# ==========================================================================================

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--debug")
    ap.add_argument("--release")
    ap.add_argument("--cc", default="cc")
    ap.add_argument("--nur", help="only this form")
    ap.add_argument("--faeden", type=int, default=8)
    ap.add_argument("--keep", help="keep every generated file")
    args = ap.parse_args()

    print("== EMITTER SWEEP -- `gabbro emit` lowers, or refuses by name ==")
    g = grenzen_laden()
    if g is None:
        print("   `instrumente/fuzze-grenzen.py` could not be loaded, and it carries the")
        print("   FORM TABLE this sweep runs over. NOTHING was measured.")
        return 2
    print(f"   {len(g.FORMEN)} declaration forms read out of `fuzze-grenzen.py` "
          f"-- one table, not two (W7)")

    if not args.debug or not args.release:
        print("   `--debug` and `--release` are both required: the two profiles must AGREE,")
        print("   and one binary cannot disagree with itself. NOTHING was measured.")
        return 2
    for name, pfad in (("--debug", args.debug), ("--release", args.release)):
        if not pathlib.Path(pfad).is_file():
            print(f"   `{name} {pfad}` is not a file. NOTHING was measured.")
            return 2
    rc, _, _, _ = lauf([args.cc, "--version"], timeout=20)
    if rc != 0:
        print(f"   `{args.cc}` does not run, so shapes 2 and 5 have no gate at all.")
        print("   W1: a skipped probe LOWERS the number, it does not leave it untouched.")
        return 2

    arb = pathlib.Path(args.keep) if args.keep else pathlib.Path(tempfile.mkdtemp())
    arb.mkdir(parents=True, exist_ok=True)
    cc = [args.cc]

    print()
    print("== SPEECH TEST -- what must fall, falls ==")
    tot = sprechprobe(cc, arb)
    if tot:
        for z in tot:
            print(f"   {z}")
        print("   A net that cannot speak measures nothing (R11). NOTHING below was measured.")
        return 2
    print("   11 probes, both directions: the compile gate, `-Wpedantic`, the oracle over")
    print("   decimal / hex / signed literals, net 6 and net 7. All spoke.")

    formen = {k: v for k, v in g.FORMEN.items() if not args.nur or k == args.nur}
    if not formen:
        print()
        print(f"== `--nur {args.nur}` names no form, so NOTHING was measured ==")
        return 2

    # ---------------------------------------------------------------------------------
    # The baseline, and it is the SAME bolt `fuzze-grenzen.py` carries: a template whose
    # known-good value is refused measures a constant parse error once per rung.
    # ---------------------------------------------------------------------------------
    print()
    print("== BASELINE -- every form's known-good value, through checker AND emitter ==")
    basis = {}
    kaputt = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.faeden) as pool:
        auftraege = []
        for form in sorted(formen):
            p = arb / f"basis-{form}.gab"
            auftraege.append((form, g.GUT[form],
                              formen[form].format(V=g.GUT[form]) + "\n", p,
                              args.debug, args.release, cc, set(), set()))
        for e in pool.map(eine_probe, auftraege):
            if not e["angenommen"]:
                kaputt.append((e["form"], e["wert"], "checker: " + str(e.get("pruefer"))))
                continue
            basis[e["form"]] = e
    if kaputt:
        print("   THE GENERATOR IS BROKEN, AND NOTHING BELOW WAS MEASURED")
        for form, wert, a in kaputt:
            print(f"   {form:22s} baseline `{wert}` -> {a}")
        print("   A template whose baseline is not accepted has an EMPTY population (W17).")
        return 2
    gesenkt_basis = sum(1 for e in basis.values() if e.get("debug") == "LOWER")
    print(f"   {len(basis)} of {len(formen)} baselines accepted; "
          f"{gesenkt_basis} of them lower to C, "
          f"{sum(1 for e in basis.values() if str(e.get('debug')).startswith('REFUSE'))} "
          f"are refused by name at the baseline itself")
    basis_zahlen, basis_namen = {}, {}
    for f, e in basis.items():
        cpfad = pathlib.Path(e["pfad"]).with_suffix(".c")
        text = cpfad.read_text(encoding="utf-8") if cpfad.is_file() else ""
        basis_zahlen[f] = ganzzahlen(text)
        basis_namen[f] = bezeichner(text)

    # ---------------------------------------------------------------------------------
    print()
    print("== THE SWEEP ==")
    auftraege = []
    n = 0
    for form in sorted(formen):
        leiter = g.LEITERN[g.LEITER.get(form, "zahl")]
        for wert in leiter:
            n += 1
            p = arb / f"{form}--{n:05d}.gab"
            auftraege.append((form, wert, formen[form].format(V=wert) + "\n", p,
                              args.debug, args.release, cc,
                              basis_zahlen.get(form, set()), basis_namen.get(form, set())))
    print(f"   {n} cases over {len(formen)} forms, {args.faeden} at a time")

    ergebnisse = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.faeden) as pool:
        for e in pool.map(eine_probe, auftraege):
            ergebnisse.append(e)
    return bericht(ergebnisse, formen, n, arb, args)


def bericht(ergebnisse, formen, n, arb, args):
    angenommen = [e for e in ergebnisse if e["angenommen"]]
    for e in angenommen:
        e["_gesenkt"] = e["debug"] in ("LOWER", "LOWER-EMPTY")
    gesenkt = [e for e in angenommen if e["_gesenkt"]]
    abgelehnt = [e for e in angenommen if e["debug"].startswith("REFUSE")]

    # ---- the four shapes of the property ---------------------------------------------
    dritte, nichtueb, orakel, uneinig = [], [], [], []
    for e in angenommen:
        if not e["_gesenkt"] and not e["debug"].startswith("REFUSE"):
            dritte.append((e, f"{e['debug']} -- "
                              f"{(e.get('panik_text') or e.get('stderr', ''))[:120]}"))
        elif e["debug"].startswith("REFUSE") and not e.get("notiz"):
            dritte.append((e, "a code with no note -- it does not say WHAT it "
                              "could not lower"))
        if e["debug"] != e["release"]:
            uneinig.append((e, f"debug={e['debug']} release={e['release']}"))
        elif not e.get("gleich", True):
            uneinig.append((e, "the same answer, and the C is NOT byte-identical"))
        if e["_gesenkt"] and e.get("uebersetzt") is False:
            roh = e.get("cc_text", "")
            m = re.search(r"(?:error|Error): .*", roh)
            nichtueb.append((e, (m.group(0) if m else roh.splitlines()[0] if roh else "")))

    # The oracle calibrates itself: a form is oracle-able only where some accepted rung
    # demonstrably put its own value into the C.
    orakelbar = {f for f in formen
                 if any(e["form"] == f and e.get("neu_gegen_basis") for e in gesenkt)}
    namen_orakelbar = {f for f in formen
                       if any(e["form"] == f and e.get("neuer_name") for e in gesenkt)}
    orakel_n = 0
    for e in gesenkt:
        if e["form"] in orakelbar and e.get("wert_zahl") is not None:
            orakel_n += 1
            if not e.get("traegt_wert"):
                orakel.append((e, f"the source says {e['wert']}, and the C carries no "
                                  f"such number"))
        if e["form"] in namen_orakelbar and "traegt_namen" in e:
            orakel_n += 1
            if not e["traegt_namen"]:
                orakel.append((e, "the name does not appear in the C at all"))

    # ---- the three nets beside the property ------------------------------------------
    nicht_iso, namelang, entart = [], [], []
    for e in gesenkt:
        if e.get("uebersetzt") and e.get("iso") is False:
            nicht_iso.append((e, e.get("iso_text", "")))
        if e.get("zu_lang", 0) > C11_INNEN:
            namelang.append((e, f"{e['zu_lang']} characters, C11 promises {C11_INNEN} "
                                f"internal / {C11_AUSSEN} external"))
        for zeile, text in e.get("entartet") or []:
            entart.append((e, f"line {zeile}: {text[:110]}"))

    def zeige(titel, liste, erklaerung):
        print()
        print(f"-- {titel}: {len(liste)} --")
        if erklaerung and liste:
            print(f"   {erklaerung}")
        gesehen = {}
        for e, was in liste:
            gesehen.setdefault(e["form"], []).append((e, was))
        for form in sorted(gesehen):
            treffer = gesehen[form]
            print(f"   {form}  ({len(treffer)})")
            for e, was in treffer[:3]:
                w = e["wert"]
                kurz = w if len(w) <= 40 else f"{w[:20]}...<{len(w)} chars>"
                print(f"      `{kurz}`  {was}".rstrip())
            if len(treffer) > 3:
                print(f"      ... and {len(treffer) - 3} more of the same form")

    print()
    print("== THE PROPERTY: LOWERS, OR REFUSES BY NAME ==")
    # **A count of CASES is not a count of DEFECTS**, and the difference is the whole
    # readability of this section. One missing suffix in `emit.rs` shows up as 47 cases over
    # seven forms; a reader who sees only the 47 cannot tell it from 47 unrelated holes. So
    # the compiler's own complaint is normalised (every literal replaced by `<N>`) and used
    # as the grouping key -- the compiler is the one instrument here that names the KIND.
    if nichtueb:
        klassen = {}
        for e, text in nichtueb:
            m = re.search(r"(?:error|Error): (.*)", text)
            roh = m.group(1) if m else text.splitlines()[0] if text else "?"
            schluessel = re.sub(r"\d{2,}", "<N>", re.sub(r"'[^']*'", "'X'", roh)).strip()
            klassen.setdefault(schluessel, []).append(e)
        print()
        print(f"-- 2a. THE COMPILER'S OWN COMPLAINTS, GROUPED: {len(klassen)} distinct --")
        for s, ee in sorted(klassen.items(), key=lambda p: -len(p[1])):
            wo = sorted({x["form"] for x in ee})
            print(f"   {len(ee):4d}  {s[:88]}")
            print(f"         over {len(wo)} forms: {' '.join(wo)}")
    zeige("1. A THIRD ANSWER -- neither lowered nor refused by name", dritte,
          "a panic, a timeout, an unnamed exit, or a `C001` with no note")
    zeige("2. THE C DOES NOT COMPILE -- cc " + " ".join(TOR), nichtueb,
          "the emitter wrote something plausible, and the compiler is the only reader")
    zeige("3. THE NUMBER DID NOT SURVIVE -- the oracle", orakel,
          "the C compiles and carries a different value than the source named")
    zeige("4. DEBUG AND RELEASE DISAGREE", uneinig,
          "release is what `cargo install` produces; the honest answer is the one nobody ships")

    print()
    print("== BESIDE THE PROPERTY -- three nets, each with its reason ==")
    zeige("5. NOT ISO C -- the same text again with -Wpedantic", nicht_iso,
          "GCC takes it as an extension and says nothing under -Wall -Wextra -Werror")
    zeige("6. AN IDENTIFIER PAST C11 SIGNIFICANCE", namelang,
          "C11 5.2.4.1: a conforming compiler may fold everything past 63 / 31 characters")
    zeige("7. DEGENERATE CONSTANT ARITHMETIC", entart,
          "a generated expression multiplied by a literal zero cannot read its input")

    # ---- the booking -----------------------------------------------------------------
    gefunden = {}
    for kennung, liste in (("DRITTE", dritte), ("NICHT-UEBERSETZBAR", nichtueb),
                           ("ORAKEL", orakel), ("UNEINIG", uneinig),
                           ("NOT-ISO", nicht_iso), ("NAME-LEN", namelang),
                           ("ENTARTET", entart)):
        for e, _ in liste:
            gefunden[(kennung, e["form"])] = gefunden.get((kennung, e["form"]), 0) + 1

    # **A run over ONE form cannot judge the bookings of the other sixty-two.** Under `--nur`
    # every booking outside the chosen form would read as *booked and gone*, which is the
    # loudest of the four verdicts and here would be an artefact of the switch. The findings
    # are still printed; only the ledger is held back, and the line below says so.
    teillauf = bool(args.nur)
    gebucht = {k: v for k, v in GEBUCHT.items() if not teillauf or k[1] == args.nur}
    neu = sorted(k for k in gefunden if k not in gebucht)
    gestiegen = sorted(k for k in gefunden if k in gebucht and gefunden[k] > gebucht[k][0])
    verschwunden = sorted(k for k in gebucht if k not in gefunden)
    gesunken = sorted(k for k in gefunden if k in gebucht and gefunden[k] < gebucht[k][0])

    print()
    print(f"== BOOKED WHEN THIS TOOL WAS WRITTEN: {len(gebucht)} of {len(GEBUCHT)} ==")
    if teillauf:
        print(f"   `--nur {args.nur}` -- only this form's bookings are weighed; the other")
        print("   forms were not run, and an unrun form is not a repaired one.")
    for k in sorted(gebucht):
        zahl, grund = gebucht[k]
        jetzt = gefunden.get(k, 0)
        marke = "==" if jetzt == zahl else ("UP" if jetzt > zahl else "DOWN")
        print(f"   [{marke}] {k[0]:18s} {k[1]:22s} {jetzt:3d} of {zahl:3d}")
        for zeile in _umbrechen(grund, 86):
            print(f"          {zeile}")

    # ---- the denominators ------------------------------------------------------------
    print()
    print("== COVERAGE, AND WHAT IT IS A FRACTION OF ==")
    print(f"   {n:5d}  cases generated over {len(formen)} forms")
    print(f"   {len(angenommen):5d}  accepted by the checker -- the POPULATION of this "
          f"property")
    print(f"   {n - len(angenommen):5d}  refused by the checker; the emitter never sees them")
    print(f"   {len(gesenkt):5d}  lowered by the emitter "
          f"({sum(1 for e in gesenkt if e['debug'] == 'LOWER-EMPTY')} of them to a preamble "
          f"with no declaration in it)")
    print(f"   {len(abgelehnt):5d}  refused BY NAME at the emitter")
    ueb = sum(1 for e in gesenkt if e.get("uebersetzt"))
    print(f"   {ueb:5d}  of {len(gesenkt)} lowered cases compile under the gate")
    print(f"   {orakel_n:5d}  could be ORACLED -- the value is findable in the C at all")
    print(f"   {len(gesenkt) - orakel_n:5d}  lowered, compiled, and only SHAPE-checked "
          f"(1, 2, 4) -- no oracle exists for them")
    print()
    print(f"   forms whose C carries the swept NUMBER: {len(orakelbar)} of {len(formen)}")
    print(f"   forms whose C carries the swept NAME:   {len(namen_orakelbar)} of {len(formen)}")
    print("   the rest are ghost declarations, compile-time clauses, and bare types -- a")
    print("   form whose C never carried the value is out of BOTH numbers, not counted as")
    print("   a clean one (W25).")

    print()
    print("-- PER FORM: cases / accepted / lowered / refused C001 / compile / oracled --")
    for form in sorted(formen):
        je = [e for e in ergebnisse if e["form"] == form]
        ja = [e for e in je if e["angenommen"]]
        lo = [e for e in ja if e["debug"] in ("LOWER", "LOWER-EMPTY")]
        ab = [e for e in ja if e["debug"].startswith("REFUSE")]
        ok = [e for e in lo if e.get("uebersetzt")]
        orn = ("num" if form in orakelbar else "") + ("+name" if form in namen_orakelbar
                                                      else "")
        print(f"   {form:22s} {len(je):4d} {len(ja):5d} {len(lo):5d} {len(ab):5d} "
              f"{len(ok):5d}   {orn or '--'}")

    abschnitt.fertig()

    schlecht = len(neu) + len(gestiegen) + len(verschwunden)
    print()
    if neu:
        print(f"-- NOT BOOKED: {len(neu)} --")
        for k in neu:
            print(f"   {k[0]:18s} {k[1]:22s} {gefunden[k]:3d} cases")
    if gestiegen:
        print(f"-- BOOKED AND RISEN: {len(gestiegen)} --")
        for k in gestiegen:
            print(f"   {k[0]:18s} {k[1]:22s} {gefunden[k]} > {gebucht[k][0]}")
    if verschwunden:
        print(f"-- BOOKED AND GONE: {len(verschwunden)} --")
        print("   a booking is a claim about the tree, and it expires. Whoever repaired")
        print("   these takes the line out of `GEBUCHT` in the same commit -- a stale")
        print("   booking hides the next finding at the same place.")
        for k in verschwunden:
            print(f"   {k[0]:18s} {k[1]:22s} booked {gebucht[k][0]}, found 0")
    if gesunken:
        print(f"-- booked and SHRUNK (not a finding, but the number moved): {len(gesunken)} --")
        for k in gesunken:
            print(f"   {k[0]:18s} {k[1]:22s} {gefunden[k]} < {gebucht[k][0]}")

    if args.keep:
        print(f"   generated files kept in {arb}")
    summe = len(dritte) + len(nichtueb) + len(orakel) + len(uneinig)
    print()
    print(f"== {len(angenommen) - summe} of {len(angenommen)} accepted cases kept the "
          f"emitter's promise ==")
    print(f"   shapes 1-4: {summe}   nets 5-7: "
          f"{len(nicht_iso) + len(namelang) + len(entart)}   "
          f"unbooked: {len(neu)}   stale bookings: {len(verschwunden)}")
    return 1 if schlecht else 0


def _umbrechen(text, breite):
    zeilen, jetzt = [], ""
    for wort in text.split():
        if len(jetzt) + len(wort) + 1 > breite:
            zeilen.append(jetzt)
            jetzt = wort
        else:
            jetzt = f"{jetzt} {wort}".strip()
    if jetzt:
        zeilen.append(jetzt)
    return zeilen


if __name__ == "__main__":
    # `abschnitt.fahre` and not a bare `main()`: this tool has five exits ABOVE its sweep,
    # and a run that leaves at one of them has measured nothing while returning a number.
    # *A tool that measured nothing must not look like one that found something.*
    sys.exit(abschnitt.fahre(main))
