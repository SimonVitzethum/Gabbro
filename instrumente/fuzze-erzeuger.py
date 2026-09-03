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

SHAPE 3b -- THE SECOND ORACLE, AND IT NEEDS NO KNOWLEDGE OF THE TRANSFORM
--------------------------------------------------------------------------
The oracle above asks whether the source's number is IN the C, and that is the only question
a literal search can ask. **It is silent wherever the number reaches the artefact
TRANSFORMED** -- a bit range becomes a mask, an offset becomes an address, a stride becomes a
multiplier -- and on 2026-09-03 that silence covered 1 584 of 2 784 lowered cases, the larger
half. *Widening it per form would mean writing down what each form's C ought to look like,
which is a second emitter beside the emitter* (`W7`).

There is one question about a transformed value that needs no knowledge of the transform:

    TWO SOURCE PROGRAMS THAT NAME DIFFERENT NUMBERS MUST NOT PRODUCE ONE ARTEFACT.

A transform may be anything; it may not be constant. Where it is, the emitter has thrown the
value away. **It calibrates itself the same way**: a form whose C does not vary with the value
at all has one fingerprint over every rung and is out of both numbers. And cases are grouped
by their NUMBER and never by their text, so `16`, `0x10` and `0b10000` agreeing is silence.

*It rediscovers `D7` from a standing start* -- every `entry ... vector` value `konst_zahl`
cannot read collapses to the same comment -- which is the calibration that matters: an oracle
that finds nothing at all on a tree with a known live defect is measuring nothing.

    ./instrumente/fuzze-erzeuger.py --debug target/debug/gabbro --release target/release/gabbro

BEYOND THE PROPERTY -- four nets, each named, each with its reason
-------------------------------------------------------------------
The bare property misses defects that are visible in the emitted C -- and one that is
visible in no C at all, because there is none -- so four further nets run beside it and are
reported in their own section:

  5. NOT ISO C -- the same compile again with `-Wpedantic`. GCC accepts a zero-length array
     as an extension and says nothing under `-Wall -Wextra -Werror`; ISO C forbids it.
  6. AN IDENTIFIER PAST C11 SIGNIFICANCE -- C11 5.2.4.1 promises 63 significant characters
     in an internal identifier and 31 in an external one. A conforming compiler may fold
     everything past that, and then two distinct Gabbro names become one C object.
  7. DEGENERATE CONSTANT ARITHMETIC -- a generated expression multiplied by a literal zero
     computes the same value for every input, so the field it claims to read is not read.
     (`% 0` and `/ 0` need no rule here: `-Wdiv-by-zero` is on by default and shape 2 has
     them.)
  8. THE EMITTER DID NOT HALT -- added 2026-09-03. Shape 1 already names a timeout, and it
     can only see one on an input the CHECKER ACCEPTED. `command_emit` runs the whole back
     end BEFORE it reads the verdict, so a refused input drives the emitter just as far;
     `static mut A : [u64; 10^8] = 7;` is refused by `M140` and still costs 8.51 s and
     18.9 GB. **Halting is a property of the RUN and not of the C**, so no gate that reads
     the emitted text can see it -- only a deadline can. See `HALT_FORMEN` for why this
     case cannot live inside the property at all.

*These four are defects, not style.* They are separated from shapes 1-4 because the mandate
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
import hashlib
import importlib.util
import os
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
# THE FORMS THIS SWEEP OWNS -- because the EMITTER's question is not the CHECKER's
# ==========================================================================================
#
# The 63 shared templates were written to drive a slot past the CHECKER, and a template that
# does that perfectly can still put the slot somewhere the emitter never looks. **Measured:
# `aligned-n` places its swept value in a `spec fn`, which is ghost -- its whole emitted C is
# the twelve-line preamble, with no declaration in it at all.** So the shared form cannot say
# one word about how `aligned` lowers, and it never could.
#
# > *That is not a fault of the other sweep.* Its property is about acceptance, and a ghost
# > function is accepted exactly as loudly as any other. It is a fault of REUSING a table
# > across two questions, and the cure is to add the difference here rather than to move the
# > shared numbers -- `fuzze-grenzen.py` publishes `63 forms / 5778 cases`, and a form added
# > there for this question would silently restate that mark as something else.
#
# So: forms that exist because of the emitter, kept apart, counted apart, and each with the
# measurement that says why the shared one does not reach.
EIGENE_FORMEN = {
    # `aligned(p, n)` where the emitter can see it: in an `impl fn` body, which is not ghost.
    # `messung/AUDIT-2026-09-02.md` 7.7 item 2 says `aligned(p, 0)` and `aligned(p, 3)` are
    # accepted and that *"an alignment of zero lowers to a modulo by zero"* -- this form is
    # what turns that into a measurement instead of a expectation.
    "aligned-im-rumpf": """module f {{
impl fn g(a : u64) -> u64
    effects {{ pure }}
    costs   <= 4 ops
{{
    if aligned(a, {V}) {{ return 1; }}
    return 0;
}}
}}""",
    # ---- A DECLARATION NOTHING USES LOWERS TO NOTHING, and `aligned` was not alone -----
    #
    # **Measured 2026-09-03, and the measurement is the tool's own**: 27 of the 64 forms
    # produce ONE artefact over every rung they lower -- 1 495 cases whose emitted text does
    # not move when the swept number does. Some of those are compile-time slots and have no
    # C to move (`costs`, a range type, an `invariant cost`); the rest are this shape.
    #
    #     device D(basis : Pa) at mmio {{ reg X : u64 @0x8 class rw }}
    #     ->  typedef struct {{ volatile uint8_t *basis; }} D;      -- and nothing else
    #
    # Forty-four distinct offsets, one artefact. **The emitter writes an accessor for a
    # register that is READ**, and the shared template reads none -- so `@0x8` and `@0x40`
    # emit byte-identical C, and no oracle over that text can say a word.
    #
    # > *Exactly `aligned-n`'s finding, and it was never only about `aligned`.* The shared
    # > table is written for the CHECKER, where a bare declaration asks the whole question.
    # > For the EMITTER a declaration is a promise and the USE is the artefact.
    #
    # With a reader the offset lands in the C as itself:
    #
    #     return (*(volatile uint64_t *)(d->basis + 8));
    "reg-versatz-leser": """module f {{
opaque type Pa = u64;
device D(basis : Pa) at mmio {{ reg X : u64 @{V} class rw }}
impl fn g(d : ptr<mmio, rw> D) -> u64
    effects {{ reads d.X }}
    costs   <= 4 ops
{{
    return d.X;
}}
}}""",
    # **And the bit range lands there TRANSFORMED, which is why this one is worth its own
    # form and not only its own reader.** `@[3:0]` becomes `& 15u` and `@[15:0]` becomes
    # `& 65535u` -- the swept number is nowhere in the text, and the literal oracle is blind
    # to it by construction. *Shape 3b needs no knowledge of the transform*, so this is the
    # first form where the two oracles do not reach the same cases.
    "reg-bit-hi-leser": """module f {{
opaque type Pa = u64;
device D(basis : Pa) at mmio {{ reg X : u64 @0x0 class rw fields {{ A @[{V}:0] }} }}
impl fn g(d : ptr<mmio, rw> D) -> u64
    effects {{ reads d.X }}
    costs   <= 4 ops
{{
    return d.X.A;
}}
}}""",
    # **`reg-bit-hi-leser`'s own mirror, the LOW end of the same bit range.** `27-form list`,
    # 2026-09-03: `reg-bit-lo` stands beside `reg-bit-hi` in that list for the same reason --
    # a declaration nothing reads lowers to nothing that moves. `reg-bit-hi-leser` already
    # exists; this is the other end of the range, not a new construct.
    "reg-bit-lo-leser": """module f {{
opaque type Pa = u64;
device D(basis : Pa) at mmio {{ reg X : u64 @0x0 class rw fields {{ A @[63:{V}] }} }}
impl fn g(d : ptr<mmio, rw> D) -> u64
    effects {{ reads d.X }}
    costs   <= 4 ops
{{
    return d.X.A;
}}
}}""",
    # ---- A BANK REGISTER'S BIT FIELD -- one suffix past `reg-bit-hi-leser`, and it was
    # never tested there -----------------------------------------------------------------
    #
    # **Found 2026-09-03, `D19`.** `reg-bit-hi-leser` reads a bit field on a TOP-LEVEL
    # register (`d.X.A`, two suffixes past the base); a register inside a `bank` reads the
    # same field through ONE MORE suffix (`d.F[i].X.A`, the bank name, the index, the
    # register, the field). Nothing in the 64+2 forms before today combined a `bank` with a
    # `fields` block AND a reader, so this shape had never been generated:
    #
    #     pruefe:  4 items, 0 errors, 0 hints
    #     emit:    exit 0, writes `return d->F[0].X.A;`
    #     cc:      error: 'D' has no member named 'F'
    #
    # `Geraet::felder` is filled from `Device::register` only (`emit.rs`, the walk beside
    # `Geraet::bankfelder`'s own doc comment) -- a bank's OWN `RegDecl::felder` was never
    # collected, so `ort`'s bank branch (`suffixe.len() == 3`, the WHOLE register) had
    # nothing to hand a fourth suffix and fell through to the generic struct-field walk.
    # *The exact fault line `Geraet::baenke`'s comment already named, one suffix further
    # down.* Repaired: a new `Geraet::bankfelder` map and a `suffixe.len() == 4` branch in
    # `ort`, refusing by name where the lookup comes back empty rather than falling through.
    "bank-reg-bit-hi-leser": """module f {{
opaque type Pa = u64;
device D(basis : Pa) at mmio {{
    bank F at 0x0 stride 8 count 4 {{ reg X : u64 @0x0 class rw fields {{ A @[{V}:0] }} }}
}}
impl fn g(d : ptr<mmio, rw> D) -> u64
    effects {{ reads d.F[0].X }}
    costs   <= 4 ops
{{
    return d.F[0].X.A;
}}
}}""",
    # The low end of the same bank-register bit range -- `bank-reg-bit-hi-leser`'s mirror,
    # the same way `reg-bit-lo-leser` mirrors `reg-bit-hi-leser`.
    "bank-reg-bit-lo-leser": """module f {{
opaque type Pa = u64;
device D(basis : Pa) at mmio {{
    bank F at 0x0 stride 8 count 4 {{ reg X : u64 @0x0 class rw fields {{ A @[63:{V}] }} }}
}}
impl fn g(d : ptr<mmio, rw> D) -> u64
    effects {{ reads d.F[0].X }}
    costs   <= 4 ops
{{
    return d.F[0].X.A;
}}
}}""",
    # ---- `bank-regversatz` WIDENED -- the shared template's OWN stride blocks variance ---
    #
    # `bank-regversatz` (shared table) sweeps `bank F at 0x0 stride 8 count 4 { reg X : u64
    # @{V} class rw }` -- a `u64` register in an 8-byte stride, so the non-overlap check
    # (`N048`) accepts exactly ONE offset, zero, regardless of what `{V}` says. That is not
    # a ghost slot; a bank register's accessor is emitted UNCONDITIONALLY (2026-08-26's own
    # repair, `Geraet::baenke`), so the offset DOES land in the C -- `+ {V}u` -- whenever the
    # template lets more than one value through. Measured: `bank F at 0x0 stride 8 count 4
    # { reg X : u64 @0x8 class rw }` lowers to `... + i * 8u + 8u` for `X`, so widening the
    # stride is the whole fix, and it costs nothing else.
    "bank-regversatz-breit": """module f {{
opaque type Pa = u64;
device D(basis : Pa) at mmio {{
    bank F at 0x0 stride 0x1000 count 1 {{ reg X : u64 @{V} class rw }}
}}
}}""",
}
EIGENE_GUT = {
    "aligned-im-rumpf": "4",
    "reg-versatz-leser": "0x8",
    "reg-bit-hi-leser": "3",
    "reg-bit-lo-leser": "0",
    "bank-reg-bit-hi-leser": "3",
    "bank-reg-bit-lo-leser": "0",
    "bank-regversatz-breit": "0x8",
}
EIGENE_LEITER = {
    "aligned-im-rumpf": "zahl",
    "reg-versatz-leser": "zahl",
    "reg-bit-hi-leser": "zahl",
    "reg-bit-lo-leser": "zahl",
    "bank-reg-bit-hi-leser": "zahl",
    "bank-reg-bit-lo-leser": "zahl",
    "bank-regversatz-breit": "zahl",
}


# ==========================================================================================
# NET 8 -- THE EMITTER HALTS, and it needs a table of its own for a measured reason
# ==========================================================================================
#
# **The property above cannot hold this case, and that is a measurement and not a design.**
# `array-laenge` sweeps `static mut A : [u64; {V}] = 0;`, and the initialiser is a literal
# ZERO on both sides of every rung. Zero is the one value the emitter short-circuits:
#
#     let anfang = if w == 0 { "{0}".to_string() } else { ...one element at a time... };
#
# `= {0}` means *every slot zero* in C and in Gabbro alike. `= {5}` means *the first five,
# the rest zero* in C and *every slot five* in Gabbro, so the two readings part company at
# every value but zero -- and `emit.rs::feldstatisch` therefore writes the other values OUT,
# one element per element, on purpose. *A ladder whose initialiser never leaves zero measures
# one branch of two.*
#
# **So why not simply add the non-zero rung to the shared table?** Because the checker refuses
# it at EVERY rung, the known-good baseline included. `M140` (2026-09-02) reads the shape of
# a value against the shape of its slot:
#
#     [M140] static value requires `[u64; 8]`, the value has `u8 in 7 .. 7`
#            -- a number does not answer for an array
#
# and `m1.rs::gestalt_grund` lets the literal zero through and nothing else. A form whose
# baseline the checker refuses stops the whole run with *THE GENERATOR IS BROKEN* -- and
# rightly, because the property's population is what the checker ACCEPTS. **This case has an
# empty population under that property and always will.**
#
# **And the defect is live anyway, which is the whole reason this net exists.**
# `gabbro-cli/src/main.rs::command_emit` runs the back end and reads the verdict afterwards:
#
#     gabbro_check::pruefe(&baum, &mut absagen);
#     let c = gabbro_check::emit::emittiere_mit(&baum, &mut absagen, bau);   // runs anyway
#     if absagen.fehler_zahl() > 0 { ... "has errors -- no C written" }
#
# So `M140` never stands between the user and the loop; it only throws away what the loop
# produced. Measured on `ki-pc-fisch-101`, debug binary, wall clock: 0.091 s at 10^6 elements,
# 0.868 s at 10^7, **8.51 s at 10^8** -- linear, about 85 ns per element, and 18.9 GB of
# resident memory after 8 seconds. `D5` fences only past `PTRDIFF_MAX` BYTES, so
# `[u64; PTRDIFF_MAX/8]` is let through: about three thousand years, if the allocator could
# hold it.
#
# > **Halting is not a property of the emitted C**, so no gate that reads the C can see this.
# > It is a property of the RUN, and the only instrument that catches it is a deadline. That
# > is why this is a NET beside the property rather than a fifth shape inside it -- the same
# > separation nets 5 to 7 already carry, and for the same stated reason.
#
# The rungs, and each one is here because it was measured rather than guessed:
HALT_FORMEN = {
    # The non-zero initialiser, which is the branch `array-laenge` cannot reach.
    "array-nichtnull": """module f {{
static mut A : [u64; {V}] = 7;
}}""",
}
HALT_LEITER = [
    # ---- the counter-direction: three sizes that MUST come back, and do -----------------
    "8",           # the shared table's own known-good length
    "4096",        # a page of `u64` -- eight times the corpus's largest array of any kind
    "1000000",     # a million elements: 0.091 s, and the net must stay silent on it
    # ---- the two faces of the defect ---------------------------------------------------
    "100000000",   # 8.51 s: past the deadline below, and the mandate's own reproducer
    # `PTRDIFF_MAX / 8` -- the largest `[u64; n]` that `D5` still lets through. This one does
    # not hang, it PANICS: `collect::<Vec<_>>()` reserves `n` slots up front and
    # `raw_vec` answers *capacity overflow* in two milliseconds. **Two faces, one fence.**
    #
    # > **`(1 << 63) // 8` was written here first, and it is a different rung.** That is
    # > `PTRDIFF_MAX + 1` over eight, so `D5` refuses it by name and the net came back
    # > silent about a form whose defect was two lines away. *An off-by-one in a boundary
    # > rung does not look like a bug; it looks like a repair.*
    str(((1 << 63) - 1) // 8),
]

# **A deadline that is also a MEMORY budget**, and it is declared for that reason.
#
# The ordinary case of this net returns in under 50 ms; the rung that must fire needs 8.5 s.
# Three seconds sits sixty times above the first and three times below the second. It is not
# only time: the emitter takes resident memory at about 2.25 GB per second on this rung
# (18.9 GB measured at 8.4 s), so **the deadline is what bounds the cost of running this
# tool at all** -- and after the fence is in, the rung is refused in microseconds and the
# budget is never spent.
FRIST_HALT = 3


# ==========================================================================================
# READING THE ANSWER
# ==========================================================================================

# **`LC_ALL=C`, and it is not a nicety.** This tool READS what `cc` says: shape 2 keeps the
# complaint, and section 2a groups 273 cases by it. Under a German locale GCC translates
# *integer constant is too large for its type* word for word, and every pattern here would
# then be grouping the user's language rather than the compiler's verdict. Measured in this
# folder on 2026-08-25 at the linker, where `pruefe-emission.sh` searched for the English
# words, did not find them and reported an error that did not exist. *Same class as `W16`:
# a tool that measures its own locale.*
#
# (The German wording is deliberately NOT quoted here. `pruefe-englisch.py` counts German
# function words inside English comments, and a quoted foreign message would raise a ratchet
# that has nothing to do with the language this file is written in.)
UMGEBUNG = dict(os.environ, LC_ALL="C")


def lauf(argv, timeout=FRIST):
    """One subprocess. Returns (exit, panicked, stdout, stderr). NEVER raises."""
    try:
        p = subprocess.run(argv, capture_output=True, text=True, env=UMGEBUNG,
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


def kollisionen(gesenkt, formen):
    """Shape 3b: within one form, cases whose C is identical while their VALUE is not.

    Returns the same `(case, why)` pairs every other shape carries, one per colliding case,
    so that its count is comparable with shape 3a's -- both count cases and not classes.

    **The self-calibration is the third line of the loop**, and it is what keeps a
    compile-time slot out of the denominator: a form whose C never varies with the number
    has ONE fingerprint over all its rungs and is skipped whole.
    """
    aus = []
    for form in sorted(formen):
        je = [e for e in gesenkt
              if e["form"] == form and e.get("wert_zahl") is not None and e.get("c_abdruck")]
        if len({e["c_abdruck"] for e in je}) < 2:
            continue
        nach_abdruck = {}
        for e in je:
            nach_abdruck.setdefault(e["c_abdruck"], []).append(e)
        for abdruck, gruppe in sorted(nach_abdruck.items()):
            werte = sorted({e["wert_zahl"] for e in gruppe})
            if len(werte) < 2:
                continue
            erst = next(x for x in gruppe if x["wert_zahl"] == werte[0])
            for e in gruppe:
                if e["wert_zahl"] == werte[0]:
                    continue
                aus.append((e, f"the same C as `{erst['wert']}` -- {len(werte)} distinct "
                               f"values share one artefact ({abdruck})"))
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
    # ---- SHAPE 2 IS EMPTY, AND THIRTEEN BOOKINGS CAME OUT TO MAKE IT SO ---------------
    #
    # **On 2026-09-03 this section held thirteen shape-2 lines and today it holds none.** They were `D1`-`D6`, plus `D13` and `D14`, and the tool reported their
    # removal itself: eleven came back `BOOKED AND GONE` on the first run after the six
    # repairs, and three more after `messung/ERZEUGERREST.md` closed the two sinks `D3` had
    # named and missed. *The removal is therefore measured and not trusted* -- the run
    # before each deletion printed `booked N, found 0` for exactly the line deleted.
    #
    # | booking | was | who took it |
    # |---|---:|---|
    # | `walk-knoten`, `walk-levels`       | 65, 65 | `D1` -- the descent looks its field up |
    # | `forever-schranke`                 | 65     | `D2` -- a body with no `return` |
    # | `ausdruck`, `if-bedingung`, `let-wert`, `zuweisung`, `bank-at` | 6, 10, 6, 6, 6 | `D3` -- `czahl` writes the `u` |
    # | `embeds-scale`                     | 4      | `D4` -- `u64::try_from` at the multiplier |
    # | `array-laenge`                     | 12     | `D5` -- the `PTRDIFF_MAX` fence |
    # | `text-abschnitt`                   | 6      | `D6` -- a `section` name is a name |
    # | `reason-code`                      | 16     | `D13` -- an enumerator holds an `int` |
    # | `static-wert`                      | 6      | `D14` -- the eighth sink of `D3` |
    #
    # > **The stale bookings were themselves a finding, and the tool made it.** `D1`-`D6`
    # > landed on 2026-09-03 and their eleven lines stayed; this run therefore returned 1 at
    # > `master` with nothing wrong in the tree. *A ratchet whose green depends on somebody
    # > tidying up is a ratchet that will be read as noise* -- which is exactly how a real
    # > finding at the same place would then be read.
    #
    # ---- THE ORACLE ------------------------------------------------------------------
    #
    # **`D7` -- an `entry` number the emitter cannot write, and it writes the unit anyway.**
    # `messung/AUDIT-2026-09-02.md` 7.7 item 3 books it: the diagnostic says *"vector: not a
    # constant in this unit"*, and it IS a constant -- one the emitter cannot represent. The
    # honest answer is a named refusal at check time, in the `N051` family.
    ("ORAKEL", "entry-vector"): (23, "D7 -- AUDIT-2026-09-02 7.7 item 3"),
    ("ORAKEL", "entry-ist"): (23, "D7 -- the same, at the stack-table index"),
    ("ORAKEL", "entry-nested-bounded"): (23, "D7 -- the same, at the nesting bound"),
    #
    # **The SAME `D7`, seen by shape 3b, and the count is 24 and not 23.** The collision
    # oracle was built on 2026-09-03 and found `D7` from a standing start -- it knows nothing
    # about `entry`, nothing about `konst_zahl`, and it asks only whether two source numbers
    # can share one artefact. *That it landed on the one defect the literal oracle already
    # had is the calibration that matters*: an oracle that finds nothing on a tree with a
    # known live defect is measuring nothing.
    #
    # **The extra case per form is a NEGATIVE rung**, and it is a real widening rather than
    # a rounding. `-340282366920938463463374607431768211455` is a number the C carries no
    # trace of, but 3a cannot say so: its question is *does the literal appear*, and for a
    # negative value the answer is `False` for an honest lowering too. 3b compares two cases
    # against each other and needs no such assumption.
    ("KOLLISION", "entry-vector"): (24, "D7 seen a second way -- 22 values, one artefact"),
    ("KOLLISION", "entry-ist"): (24, "D7 -- the same, at the stack-table index"),
    ("KOLLISION", "entry-nested-bounded"): (24, "D7 -- the same, at the nesting bound"),
    #
    # ---- BESIDE THE PROPERTY ---------------------------------------------------------
    #
    # **`D8` -- a zero-size array. FOUND HERE, AND CLOSED THE SAME DAY.**
    #
    # `table count 0` lowered to `T_slot slots[0]`, which ISO C forbids and GCC takes as an
    # extension -- so only `-Wpedantic` saw it, three rungs at `table-count` and four more
    # through a `const` bound at `const-als-schranke`. **Asking what a `count 0` table does at
    # a USE turned it into something much larger:** `umgebung.rs` had dropped the zero out of
    # the capacity map (`.filter(|n| *n > 0)`), so `M103` had no bound and `T.slots[0].a` gave
    # `0 errors` -- an out-of-bounds read in the artefact.
    #
    # Both halves repaired 2026-09-02, no new code: the capacity is recorded as ZERO, and the
    # emitter refuses the declaration by name like every sibling zero-length array already
    # was. Probe `beispiele/gift/647`, speech test
    # `rechenwerk.rs::die_leere_tabelle_hat_eine_schranke_und_kein_erzeugnis`.
    #
    # **The two lines that stood here are deliberately gone rather than set to 0.** A booking
    # is a claim about the tree; when the tree changes the line goes, and the run that finds
    # it still there says `BOOKED AND GONE`. *That is how this ratchet reported its own
    # repair, and it is the only reason the removal is not on trust.*
    #
    # **`D9` -- a `reason` code past `INT_MAX`. GONE on 2026-09-03, and it took `D13` with
    # it, because they were one defect read by two gates.**
    #
    # The line stood at 13 and read *ISO C restricts an enumerator to the range of `int`
    # before C2X; GCC widens it silently.* `-Wpedantic` was the only reader, so it was
    # booked here, beside the property rather than inside it -- and 16 further cases at the
    # same slot were booked under shape 2 as `D3`, a missing `u`.
    #
    # **They are one cause.** C11 6.7.2.2p2 is a CONSTRAINT: an enumerator shall have a value
    # representable as an `int`. Everything past that is ill-formed, and which of the three
    # complaints `cc` prints depends only on how far past. *A suffix would have silenced the
    # loud two and left the quiet one*, which is the repair `D6` refused for the same reason.
    # `emit.rs::C_ENUM_MAX` now refuses at `INT_MAX`, and both bookings went to zero in the
    # same run. Probe `beispiele/gift/666`.
    #
    # > **The lesson is about the BOOKS and not about C.** Two lines, two shapes, two
    # > sections, one defect -- and the split made it look like a style note beside a
    # > compile error. *A finding filed under the gate that happened to see it is filed
    # > under the wrong heading.*
    #
    # **`D6` again, seen a second time by `-Wpedantic`.** 3 -> 2 on 2026-09-03: the third was
    # the trailing backslash, which the `section`-name rule stops before any C is written.
    # The two that stand are `-Woverlength-strings` -- a string past the 4095 characters
    # ISO C99 compilers are required to support -- and that is a different complaint about
    # the same slot, not a leftover of the same one.
    ("NOT-ISO", "text-abschnitt"): (2, "D6's neighbour -- `-Woverlength-strings`, not the name rule"),
    #
    # **`D10` -- an identifier past C11 5.2.4.1 significance.**
    # `messung/AUDIT-2026-09-02.md` 7.7 item 5. Four of the eight name positions reach C
    # with the user's own spelling; the other four do not, and that asymmetry is a
    # measurement rather than a repair (`name-modul`, `-parameter`, `-reg`, `-typ` all give
    # 0). The two `text-*` entries are the same rule at a STRING that becomes part of a C
    # name.
    ("NAME-LEN", "name-const"): (12, "D10 -- AUDIT-2026-09-02 7.7 item 5"),
    ("NAME-LEN", "name-fn"): (12, "D10 -- at a function name"),
    ("NAME-LEN", "name-feld"): (13, "D10 -- at a `format` field, and the prefix adds seven"),
    ("NAME-LEN", "name-tabelle"): (13, "D10 -- at a table, and the suffix adds five"),
    ("NAME-LEN", "text-abschnitt"): (4, "D10 -- a long section name is a long C token"),
    ("NAME-LEN", "text-grund"): (4, "D10 -- a long reason message is a long C token"),
    #
    # **`D11` -- `embeds ... scale 0`.** `messung/AUDIT-2026-09-02.md` 7.7 item 4: the
    # extracted frame number is multiplied by zero, so every record yields address zero.
    # Three rungs write the same zero (`0`, `0x0`, `0b0`).
    ("ENTARTET", "embeds-scale"): (3, "D11 -- AUDIT-2026-09-02 7.7 item 4"),
}


# ==========================================================================================
# ONE CASE
# ==========================================================================================

def eine_probe(auftrag):
    """Everything measured about one generated file. A pure worker -- no shared state."""
    (form, wert, quelle, pfad, dbg, rel, cc, basis_zahlen, basis_namen,
     frist_halt) = auftrag
    pfad.write_text(quelle, encoding="utf-8")
    e = {"form": form, "wert": wert, "pfad": str(pfad)}

    # **The precondition is MEASURED and not inferred.** The property speaks about inputs the
    # checker accepts; reading that off the emitter's own diagnostic would let a checker
    # refusal and an emitter refusal share one number.
    pe, pp, _, pf = lauf([dbg, "pruefe", str(pfad)])
    e["angenommen"] = (pe == 0 and not pp)
    if not e["angenommen"]:
        e["pruefer"] = "PANIC" if pp else ("TIMEOUT" if pe is None else ",".join(kodes(pf)))
        # **NET 8, and this is the only line at which it can be measured.** See the table
        # above: `command_emit` runs the whole back end BEFORE it reads the verdict, so a
        # case the checker refused still drives the emitter. Until today this `return`
        # stood two lines up and the emitter was never started on these at all.
        he, hp, _, hf = lauf([dbg, "emit", str(pfad)], timeout=frist_halt)
        e["haelt"] = he is not None
        e["halt_wie"] = ("TIMEOUT" if he is None else
                         ("PANIC" if hp else f"exit {he}"))
        # **The panic's own words and not the whole stream.** A refused case carries the
        # checker's diagnostic on the same stderr, and that is what the case is ABOUT --
        # printing it here would name `M140` where the finding is a back end that ran past
        # it. So the two lines Rust writes for a panic are lifted out by name.
        zeilen = hf.splitlines()
        e["halt_text"] = ""
        for i, z in enumerate(zeilen):
            if "panicked at" in z:
                e["halt_text"] = " / ".join(x.strip() for x in zeilen[i:i + 2])[:160]
                break
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
    # Shape 3b -- the collision oracle. The whole text is kept as a digest and never as
    # text: 2 784 lowered units are about 3 MB, and none of them is ever read back.
    e["c_abdruck"] = hashlib.sha256(c.encode("utf-8", "replace")).hexdigest()[:16]

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

    # **Shape 3b, all four directions, over cases this test builds by hand.** The oracle is
    # a grouping and not a comparison, so a wrong `<` or a wrong key would still return a
    # list -- and an empty list reads exactly like a clean tree.
    def _f(w, ab):
        return {"form": "f", "wert": str(w), "wert_zahl": w, "c_abdruck": ab}
    # It FIRES: two values, one artefact, and a third rung proving the form is not ghost.
    if len(kollisionen([_f(1, "a"), _f(2, "a"), _f(3, "b")], ["f"])) != 1:
        tot.append("the collision oracle does not see two values sharing one artefact")
    # It is SILENT on a ghost form -- one fingerprint over every rung is a compile-time slot.
    if kollisionen([_f(1, "a"), _f(2, "a"), _f(3, "a")], ["f"]):
        tot.append("the collision oracle fires on a form whose C never varies -- every "
                   "`costs` clause and every range type would be a finding")
    # It is SILENT on three spellings of ONE number, which MUST give one C.
    if kollisionen([_f(16, "a"), _f(16, "a"), _f(17, "b")], ["f"]):
        tot.append("the collision oracle fires on one value written twice -- it is grouping "
                   "by the TEXT and not by the number")
    # It is SILENT where every value has its own artefact.
    if kollisionen([_f(1, "a"), _f(2, "b"), _f(3, "c")], ["f"]):
        tot.append("the collision oracle fires where every value has its own C")

    # Net 6 and net 7, both directions.
    if max((len(n) for n in bezeichner("a" * 64 + " b;")), default=0) <= C11_INNEN:
        tot.append("net 6 does not see a 64-character identifier")
    if max((len(n) for n in bezeichner("short_name x;")), default=0) > C11_INNEN:
        tot.append("net 6 fires on an ordinary name")
    if not entartet("return (x >> 12) * 0u;"):
        tot.append("net 7 does not see a multiplication by zero")
    if entartet("return x * 4096u;") or entartet("return x * 0x10u;"):
        tot.append("net 7 fires on an ordinary multiplication")

    # **Net 8's reader is the DEADLINE, and a deadline that never expires is an ornament.**
    # Both directions over `sleep`, which is the one process whose running time this tool can
    # state rather than measure. `lauf` swallows every exception by contract, so a broken
    # timeout would come back as a clean answer and every hang would count as a halt.
    if lauf(["sleep", "10"], timeout=1)[0] is not None:
        tot.append("the deadline does not expire on a process that outlives it -- net 8 "
                   "would count every hang as a halt")
    if lauf(["sleep", "0"], timeout=10)[0] != 0:
        tot.append("the deadline fires on a process that finishes at once -- net 8 would "
                   "report a hang that is not there")
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
    print(f"   {len(EIGENE_FORMEN)} more this sweep OWNS -- a slot the shared table places "
          f"where the emitter never looks")

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
    print("   17 probes, both directions: the compile gate, `-Wpedantic`, the oracle over")
    print("   decimal / hex / signed literals, the COLLISION oracle in all four of its")
    print("   directions, net 6, net 7, and net 8's DEADLINE over a process that outlives")
    print("   it and one that does not. All spoke.")

    alle_formen = dict(g.FORMEN)
    alle_formen.update(EIGENE_FORMEN)
    gut = dict(g.GUT)
    gut.update(EIGENE_GUT)
    leiter_von = dict(g.LEITER)
    leiter_von.update(EIGENE_LEITER)
    formen = {k: v for k, v in alle_formen.items() if not args.nur or k == args.nur}
    # **The single-form switch reaches net 8's own table too.** Its forms are deliberately
    # outside the property's population (see `HALT_FORMEN`), so they are not in
    # `alle_formen` -- and a switch that named one used to come back *names no form*, which
    # is a different sentence from *found nothing* and would have been read as the second.
    #
    # (The switch is spelled out nowhere in this comment on purpose: `pruefe-englisch.py`
    # carries a closed list of German function words, one of them is a homograph of that
    # flag's name, and a ratchet raised by quoting a flag measures nothing about language.)
    if not formen and args.nur in HALT_FORMEN:
        print()
        print(f"== `--nur {args.nur}` is a NET 8 form -- the property's own sweep is empty ==")
        print("   That is not a defect of the switch: this form has no accepted population")
        print("   by construction. Only net 8 below can say anything about it.")
    elif not formen:
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
            auftraege.append((form, gut[form],
                              formen[form].format(V=gut[form]) + "\n", p,
                              args.debug, args.release, cc, set(), set(), FRIST))
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
        leiter = g.LEITERN[leiter_von.get(form, "zahl")]
        for wert in leiter:
            n += 1
            p = arb / f"{form}--{n:05d}.gab"
            auftraege.append((form, wert, formen[form].format(V=wert) + "\n", p,
                              args.debug, args.release, cc,
                              basis_zahlen.get(form, set()), basis_namen.get(form, set()),
                              FRIST))
    print(f"   {n} cases over {len(formen)} forms, {args.faeden} at a time")

    ergebnisse = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.faeden) as pool:
        for e in pool.map(eine_probe, auftraege):
            ergebnisse.append(e)

    # ---------------------------------------------------------------------------------
    # NET 8. **ONE at a time, and that is not a preference.** The rung that must fire takes
    # resident memory at about 2.25 GB per second until its deadline; sixteen of those at
    # once is not a measurement, it is an out-of-memory kill wearing the same exit code.
    # ---------------------------------------------------------------------------------
    halt_n = 0
    if not args.nur or args.nur in HALT_FORMEN:
        halt_formen = {k: v for k, v in HALT_FORMEN.items()
                       if not args.nur or k == args.nur}
        halt_auftraege = []
        for form in sorted(halt_formen):
            for wert in HALT_LEITER:
                halt_n += 1
                p = arb / f"halt-{form}--{halt_n:05d}.gab"
                halt_auftraege.append((form, wert,
                                       halt_formen[form].format(V=wert) + "\n", p,
                                       args.debug, args.release, cc, set(), set(),
                                       FRIST_HALT))
        print(f"   {halt_n} more for net 8, ONE at a time, deadline {FRIST_HALT} s")
        for auftrag in halt_auftraege:
            ergebnisse.append(eine_probe(auftrag))
    return bericht(ergebnisse, formen, n, halt_n, arb, args)


def bericht(ergebnisse, formen, n, halt_n, arb, args):
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

    # ---- SHAPE 3b -- THE COLLISION ORACLE ---------------------------------------------
    #
    # **The oracle above asks whether the source's number is IN the C, and that is the only
    # question it can ask.** It is silent wherever the number reaches the artefact
    # TRANSFORMED -- a bit range becomes a mask, an offset becomes an address, a stride
    # becomes a multiplier -- and on 2026-09-03 that silence covered **1 584 of 2 784**
    # lowered cases, the larger half. *Widening it per form would mean writing down what each
    # form's C ought to look like, which is a second emitter beside the emitter* (`W7`), and
    # a second emitter is exactly the thing that cannot be trusted to disagree.
    #
    # There is one question about a transformed value that needs no knowledge of the
    # transform at all, and it is the one the `konst_zahl` class fails:
    #
    #     TWO SOURCE PROGRAMS THAT NAME DIFFERENT NUMBERS MUST NOT PRODUCE ONE ARTEFACT.
    #
    # A transform may be anything; it may not be constant. Where it is, the emitter has
    # thrown the value away -- and the user's number is then in no C, transformed or
    # otherwise. **`entry ... vector` is the standing instance**: every value `konst_zahl`
    # cannot read collapses to the same comment, *"vector: not a constant in this unit"*, and
    # the units are byte-identical.
    #
    # **It calibrates itself the same way the literal oracle does, and for the same reason.**
    # A form whose C does not depend on the swept value AT ALL -- a `costs` clause, a range
    # type, a ghost `spec fn` -- is not a defect, it is a form whose value is compile-time.
    # Such a form has NO pair of rungs with different C, so it is out of the numerator and
    # out of the denominator both (`W25`). A form counts here only where some pair of
    # accepted rungs demonstrably differs.
    #
    # > **Spelling is not value.** The ladders sweep `16`, `0x10` and `0b10000`, which are
    # > one number in three dresses and MUST give one C. Cases are grouped by `quellwert`
    # > and never by the text, so the three agreeing is silence and not a finding.
    kollision = kollisionen(gesenkt, formen)
    # **The denominator of 3b, and it is a different one from 3a's.** A form is reachable by
    # the collision oracle where its C demonstrably varies with the number -- the same
    # self-calibration `kollisionen` applies, computed once here so the coverage block can
    # print what the fraction is OF. *The two oracles overlap and do not partition*, so the
    # union is printed as well: adding them would count a case twice.
    kollisionsfaehig = set()
    for f in formen:
        je = [e for e in gesenkt
              if e["form"] == f and e.get("wert_zahl") is not None and e.get("c_abdruck")]
        if len({e["c_abdruck"] for e in je}) >= 2:
            kollisionsfaehig.add(f)
    kollisionsfaehig_n = sum(1 for e in gesenkt if e["form"] in kollisionsfaehig
                             and e.get("wert_zahl") is not None and e.get("c_abdruck"))

    def _von_3a(e):
        return ((e["form"] in orakelbar and e.get("wert_zahl") is not None)
                or (e["form"] in namen_orakelbar and "traegt_namen" in e))

    def _von_3b(e):
        return (e["form"] in kollisionsfaehig and e.get("wert_zahl") is not None
                and e.get("c_abdruck"))

    beide_n = sum(1 for e in gesenkt if _von_3a(e) and _von_3b(e))
    keins_n = sum(1 for e in gesenkt if not _von_3a(e) and not _von_3b(e))

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

    # ---- net 8: over the cases the checker REFUSED, which is where it can be seen -----
    #
    # A case the checker ACCEPTED and that then hung is already shape 1 (`TIMEOUT`), and
    # counting it twice would make one event look like two. So this net's population is the
    # complement: every generated case the checker refused, on which `command_emit` runs the
    # back end anyway.
    nicht_gehalten = []
    halt_gemessen = [e for e in ergebnisse if not e["angenommen"] and "haelt" in e]
    for e in halt_gemessen:
        if not e["haelt"]:
            nicht_gehalten.append(
                (e, f"the checker refused it, and `gabbro emit` still ran the back end "
                    f"-- no answer within the deadline"))
        elif e.get("halt_wie") == "PANIC":
            nicht_gehalten.append(
                (e, f"the back end PANICKED on an input the checker had refused: "
                    f"{e.get('halt_text', '')}"))

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
    zeige("3a. THE NUMBER DID NOT SURVIVE -- the literal oracle", orakel,
          "the C compiles and carries a different value than the source named")
    zeige("3b. TWO SOURCE NUMBERS, ONE ARTEFACT -- the collision oracle", kollision,
          "the C compiles and does not depend on a number the source named -- and this one "
          "needs no knowledge of the transform")
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
    zeige("8. THE EMITTER DID NOT HALT -- a deadline is the only reader of this", nicht_gehalten,
          "the back end runs BEFORE `command_emit` reads the verdict, so a refused input "
          "still drives it")

    # ---- the booking -----------------------------------------------------------------
    gefunden = {}
    for kennung, liste in (("DRITTE", dritte), ("NICHT-UEBERSETZBAR", nichtueb),
                           ("ORAKEL", orakel), ("KOLLISION", kollision),
                           ("UNEINIG", uneinig),
                           ("NOT-ISO", nicht_iso), ("NAME-LEN", namelang),
                           ("ENTARTET", entart), ("NICHT-GEHALTEN", nicht_gehalten)):
        for e, _ in liste:
            gefunden[(kennung, e["form"])] = gefunden.get((kennung, e["form"]), 0) + 1

    # **A run over ONE form cannot judge the bookings of the other sixty-three.** With a
    # single form selected, every booking outside it would read as *booked and gone*, which
    # is the loudest of the four verdicts and here would be an artefact of the switch. The
    # findings are still printed; the ledger alone is held back, and the line below says so.
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
    print(f"   {halt_n:5d}  more generated for net 8 over {len(HALT_FORMEN)} forms the "
          f"property cannot hold")
    print(f"   {len(angenommen):5d}  accepted by the checker -- the POPULATION of this "
          f"property")
    print(f"   {n + halt_n - len(angenommen):5d}  refused by the checker -- and "
          f"{len(halt_gemessen)} of those were still run through the emitter under a "
          f"{FRIST_HALT} s deadline (net 8)")
    print(f"   {len(gesenkt):5d}  lowered by the emitter "
          f"({sum(1 for e in gesenkt if e['debug'] == 'LOWER-EMPTY')} of them to a preamble "
          f"with no declaration in it)")
    print(f"   {len(abgelehnt):5d}  refused BY NAME at the emitter")
    ueb = sum(1 for e in gesenkt if e.get("uebersetzt"))
    print(f"   {ueb:5d}  of {len(gesenkt)} lowered cases compile under the gate")
    print(f"   {orakel_n:5d}  could be ORACLED by 3a -- the value is findable in the C at all")
    print(f"   {kollisionsfaehig_n:5d}  could be ORACLED by 3b -- the form's C demonstrably "
          f"varies with the number")
    print(f"   {beide_n:5d}  by BOTH -- the two oracles overlap, they do not partition")
    print(f"   {len(gesenkt) - keins_n:5d}  reached by at least one oracle")
    print(f"   {keins_n:5d}  lowered, compiled, and only SHAPE-checked (1, 2, 4) -- no "
          f"oracle reaches them")
    print()
    print(f"   forms whose C carries the swept NUMBER: {len(orakelbar)} of {len(formen)}")
    print(f"   forms whose C carries the swept NAME:   {len(namen_orakelbar)} of {len(formen)}")
    print(f"   forms whose C VARIES with the number:   {len(kollisionsfaehig)} of {len(formen)}")
    print("   the rest are ghost declarations, compile-time clauses, and bare types -- a")
    print("   form whose C never carried the value is out of BOTH numbers, not counted as")
    print("   a clean one (W25).")
    # **Does 3b reach anything 3a does not? The answer is printed and not assumed.** A
    # widening that adds no case to the denominator is still a widening -- it asks a
    # different question about the same cases -- but saying so needs the set difference and
    # not the two sizes.
    nur_3b = sorted(kollisionsfaehig - orakelbar - namen_orakelbar)
    nur_3a = sorted((orakelbar | namen_orakelbar) - kollisionsfaehig)
    print(f"   reached by 3b and NOT by 3a: {' '.join(nur_3b) if nur_3b else '(none)'}")
    print(f"   reached by 3a and NOT by 3b: {' '.join(nur_3a) if nur_3a else '(none)'}")

    # ---- WHERE THE UNORACLED HALF ACTUALLY LIVES -------------------------------------
    #
    # **The two causes are different and only one of them is a limit of this tool.** A form
    # whose C never varies with the number is either (a) a compile-time slot -- a `costs`
    # clause, a range type, an `invariant cost` -- where there is nothing in ANY C to check,
    # or (b) a DECLARATION NOTHING USES, where the emitter writes no accessor and the value
    # would have reached the C in a template that read it.
    #
    # *(b) is a limit of the TEMPLATE and not of the emitter*, and it is the same finding
    # `ERZEUGERSWEEP.md` §6 made once for `aligned-n`: the shared table is written for the
    # CHECKER, where a bare declaration is enough to ask the question. **Naming the forms is
    # what turns that anecdote into a work list.**
    # **The question is asked of the C and not of the value**, so a form that sweeps NAMES
    # is judged the same way as one that sweeps numbers: does its emitted text move at all?
    stumm = []
    for f in sorted(formen):
        je = [e for e in gesenkt if e["form"] == f and e.get("c_abdruck")]
        if len(je) >= 2 and len({e["c_abdruck"] for e in je}) == 1:
            stumm.append((f, len(je), len({e["wert"] for e in je})))
    if stumm:
        print()
        print(f"-- FORMS WHOSE LOWERED C IS THE SAME FOR EVERY RUNG: {len(stumm)} --")
        print("   no oracle over the emitted text can say one word about these, because the")
        print("   text does not move. Either the slot is compile-time, or the template")
        print("   declares something nothing USES -- and only the second one is repairable.")
        for f, wieviel, verschieden in stumm:
            print(f"   {f:22s} {wieviel:4d} lowered, {verschieden:3d} distinct spellings, "
                  f"ONE artefact")

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
    summe = len(dritte) + len(nichtueb) + len(orakel) + len(kollision) + len(uneinig)
    print()
    print(f"== {len(angenommen) - summe} of {len(angenommen)} accepted cases kept the "
          f"emitter's promise ==")
    print(f"   shapes 1-4: {summe}   nets 5-8: "
          f"{len(nicht_iso) + len(namelang) + len(entart) + len(nicht_gehalten)}   "
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
