#!/usr/bin/env python3
"""**The BODY CHANNEL -- how many of the counted obligations can a prover read over a BODY?**

`gabbro pflichten --isabelle` writes the register as an Isabelle theory and refuses seventeen
obligations with one word: *"speaks about the world AFTER a body ran, and there is no
semantics of a Gabbro body."* `gabbro pflichten --lean` writes the same register against
`Gabbro.Body` -- the meaning that was missing there.

**The model lives in `programmlogik/` and not in `passlogik/`.** The latter formalises the
CHECKER; what is counted here is a statement about a PROGRAM.

**This tool adds up both columns over the corpus.** And the second is the one that matters: an
emitter that swallows fifty-eight obligations and emits four looks, in the first column,
exactly like one that REFUSES fifty-eight and emits four -- *and only the second has measured
anything.* Hence this run FAILS when `goals + refused` does not come to the total, and it
fails again when the reasons do not add up to the refusals.

    ./instrumente/zaehle-lean.py                 over `beispiele/` and `messung/`
    ./instrumente/zaehle-lean.py --je-datei      with the table, file by file

The binary is built on `ki-pc-fisch-101` (CLAUDE.md); this tool only calls an existing
`target/debug/gabbro` and builds nothing.
"""
import collections
import glob
import pathlib
import re
import subprocess
import sys

W = pathlib.Path(__file__).resolve().parent.parent
GABBRO = W / "target" / "debug" / "gabbro"

# **Every run under a deadline.** A hang looks like "still running", not like a finding --
# the same lesson `mutiere-pruefer.py` carries at the top of its file.
FRIST = 120

# The refusal reasons exactly as `lean.rs` writes them. **The list stands here in FULL** -- a
# reason the emitter knows and this tool does not shows up below as `UNBEKANNT` instead of
# quietly landing in no column at all.
#
# **`division-or-bits` is gone from this list because it is gone from the emitter.** The
# model took `Int.tdiv`/`Int.tmod` -- the C operators -- and the cases it cannot state are
# refused inside `binop` by getting STUCK, not by a refusal here. A row that always read `0`
# would say the channel still owes something it does not.
GRUENDE = [
    ("foreign-body", "an `ensures` at a foreign body -- an ASSUMPTION, not a goal"),
    ("table-invariant", "`maintains` names a table invariant: quantified over every slot"),
    ("call-site", "a precondition at a call site -- the Isabelle channel carries those"),
    ("device-promise", "a promise at hardware Gabbro does not see"),
    ("call-not-compositional", "a call -- compositional over the CONTRACT, gate not built"),
    ("loop", "a loop -- the measure is carried, the INVARIANT has no word"),
    ("concurrent-statement", "one state and one transition stop carrying here"),
    ("publish", "`publishes` -- a release store; it takes VISIBILITY"),
    ("await", "`awaits` -- the other half of the pairing"),
    ("exchange", "`exchange` -- visibility plus atomicity as a notion"),
    ("observe", "`observes` -- a view that MAY be stale"),
    ("let-else", "`let … else` -- two exits out of a call"),
    ("narrow", "`narrow` -- the range lattice under it is proved"),
    ("non-local-exit", "`leave`/`next` -- a real exit; `Outcome` has no fourth form"),
    ("compound-assignment", "`+=` and its kin -- a different overflow accounting"),
    ("match-not-option", "a `match` over something other than an `option`"),
    ("float", "a floating-point value -- this model has no float"),
    ("old-state", "`old(x)` -- a predicate over TWO states"),
    ("quantified", "a quantifier, `reaches` or a membership -- where a `spec fn` runs out"),
    ("call-in-expression", "a call inside an expression -- same gate as a call"),
    ("builtin", "a built-in about the LAYOUT, and this model has none"),
    ("lock-witness", "`Held(…)` -- carried by the lock passes, not by a prover"),
    # **`result-in-ensures` is gone from this list because it cannot reach this channel.**
    # It was measured on 2026-08-30 (W24, unchanged checker): `result` in an `ensures` of a
    # routine this channel carries produces a GOAL -- `bindLocal s'.local' "result" v` -- and
    # refuses nothing. The tag survives in `lean.rs` for the EXPORT datum, which drops such a
    # promise on purpose; that datum is not what this tool counts.
    #
    # *What did reach this channel under that name was `result` in a BODY* -- and the row read
    # "one gate away, not far" over a program error no gate will ever carry. Same move as
    # `division-or-bits`: a row that can only ever read `0` says the channel owes something it
    # does not.
    ("result-in-body", "`result` in a BODY, where it names nothing -- a program error"),
    ("other-value", "an error reason value or a function pointer"),
    ("no-term", "a form this channel has no Lean term for"),
    ("carrier-not-a-table", "the carrier of a place is not a declared `table`"),
    ("no-shape-for-field", "the declared type of a slot field has no shape here"),
    ("spec-not-an-expression", "the named `spec fn` is not a plain expression body"),
    # **The three cut out of `call-not-compositional` on 2026-08-28** (`messung/RUF-TOR.md`).
    # Seventeen refusals stood under one word and not one was a call over a contract: six
    # generated operations, six constructors, four `transition`s. *Three different prices
    # under one number, and a number that said the channel waited on a gate.*
    ("generated-op", "a generated table operation -- its contract is a SCHEMA"),
    ("device-transition", "a `transition` of a `device` -- a register write"),
    ("constructed-value", "a record, a `tagged` or a device handle -- no value form"),
]

# The kinds, as `pflichten.rs::kurz` writes them. **In FULL, for the same reason `GRUENDE`
# stands in full**: a kind this tool does not know would land in no column.
ARTEN = [
    ("V", "a precondition at a CALL SITE"),
    ("D", "a device promise at a register"),
    ("F", "a foreign duty -- there is no body"),
    ("E", "preservation of a table invariant"),
    ("S", "an invariant across the passes of a loop"),
    ("N", "a POSTCONDITION"),
    ("R", "a REFINEMENT of a specification"),
]

KOPF = re.compile(r"@duty 1  (\S+)  total (\d+)  goals (\d+)  refused (\d+)")
ZEILE = re.compile(r"^  (\S+) \((\d+)\): ")

# **The KIND of each refused obligation, off the line the emitter already writes.**
#
#     duty_1  N  lies :: ensures #1
#
# `pflichten.rs` prints one letter per kind: `V` precondition at a call site, `D` device
# promise, `F` foreign duty, `E` preservation, `S` loop invariant, `N` postcondition,
# `R` refinement. **Only `N` and `R` are ever TRANSLATED** -- `lean.rs::verdicts` refuses the
# other five by kind, in a `match p.art`, before an expression is looked at.
#
# *That distinction is the one the reason column cannot make.* A refusal booked as `loop` or
# `table-invariant` names a Gabbro construct and reads like a missing form; five sixths of
# them were never about a form at all, but about the one GOAL SHAPE this channel emits --
# "the body runs, and the postcondition holds". Measured 2026-08-30: 60 of 66.
DETAIL = re.compile(r"^    duty_\d+\s+([A-Z])\s")

# The kinds this channel ATTEMPTS. Everything else is refused by kind.
UEBERSETZT = {"N", "R"}


def lies_kopf(text):
    """`(total, goals, refused)` off the header, or `None` when there is none."""
    m = KOPF.search(text)
    return (int(m.group(2)), int(m.group(3)), int(m.group(4))) if m else None


def sprechprobe():
    """**In both directions: a lying balance must fall, an honest one must not.**

    The whole verdict of this tool rests on one arithmetic check, and *a check nobody
    has seen fail is a decoration* (R11).
    """
    gut = "        @duty 1  x.gab  total 4  goals 1  refused 3\n"
    gift = "        @duty 1  x.gab  total 4  goals 1  refused 1\n"
    stumm = "        nichts hier ueber sich selbst\n"
    a, b, c = lies_kopf(gut), lies_kopf(gift), lies_kopf(stumm)
    ok_gut = a is not None and a[1] + a[2] == a[0]
    ok_gift = b is not None and b[1] + b[2] != b[0]
    ok_stumm = c is None
    print("== Speech test ==")
    print("  an honest balance passes:  %s" % ("yes" if ok_gut else "NO"))
    print("  a lying balance falls:     %s" % ("yes" if ok_gift else "NO"))
    print("  a missing header falls:    %s" % ("yes" if ok_stumm else "NO"))
    return ok_gut and ok_gift and ok_stumm


def main() -> int:
    je_datei = "--je-datei" in sys.argv
    if not sprechprobe():
        print("== BODY CHANNEL: this guardian measures nothing ==")
        return 2
    if not GABBRO.exists():
        print(f"ABORT: {GABBRO} is missing -- it is built on ki-pc-fisch-101 (CLAUDE.md).")
        # **Every refusal in this file ends with 2, not 1** (2026-08-31). This counter joined
        # `abnahme.py` that day, so its return code is now read as a VERDICT -- and the sixth
        # requirement applies: `1` means the TREE has to change, `2` means the SETUP does.
        # Every site below says NOTHING WAS MEASURED, so every one of them is a `2`.
        return 2
    dateien = sorted(glob.glob(str(W / "beispiele" / "*.gab"))) + sorted(
        glob.glob(str(W / "messung" / "*" / "*.gab"))
    )
    gesamt = ziele = abgesagt = 0
    ohne_register = 0
    je_grund: collections.Counter = collections.Counter()
    je_art: collections.Counter = collections.Counter()
    tafel = []
    for f in dateien:
        rel = str(pathlib.Path(f).relative_to(W))
        try:
            lauf = subprocess.run(
                [str(GABBRO), "pflichten", "--lean", rel],
                cwd=W,
                capture_output=True,
                text=True,
                timeout=FRIST,
            )
        except subprocess.TimeoutExpired:
            print(f"ABORT: {rel} -- deadline {FRIST} s exceeded. A hang is not a finding.")
            return 2
        # **A unit with errors carries no register**, and that is the same rule
        # `gabbro pflichten` follows -- not a skipped file but one without an answer yet.
        if lauf.returncode != 0:
            ohne_register += 1
            continue
        kopf = lies_kopf(lauf.stdout)
        if kopf is None:
            print(f"ABORT: {rel} -- no `@duty` header. The emitter is silent about itself.")
            return 2
        g, z, a = kopf
        if z + a != g:
            print(f"ABORT: {rel} -- {z} + {a} != {g}. The balance of the emitter does not add up.")
            return 2
        gesamt += g
        ziele += z
        abgesagt += a
        hier: collections.Counter = collections.Counter()
        for zeile in lauf.stdout.splitlines():
            m = ZEILE.match(zeile)
            if m:
                hier[m.group(1)] += int(m.group(2))
        summe = sum(hier.values())
        if summe != a:
            print(f"ABORT: {rel} -- the reasons count {summe}, refused are {a}.")
            return 2
        je_grund.update(hier)
        for zeile in lauf.stdout.splitlines():
            d = DETAIL.match(zeile)
            if d:
                je_art[d.group(1)] += 1
        if z or a:
            tafel.append((rel, g, z, a))

    bekannt = {t for t, _ in GRUENDE}
    for t in je_grund:
        if t not in bekannt:
            print(f"ABORT: UNKNOWN refusal reason `{t}` -- this tool is out of date.")
            return 2

    if je_datei:
        print()
        print("-- per unit --")
        print(f"   {'unit':<42} {'all':>4} {'goal':>5} {'refus':>6}")
        for rel, g, z, a in tafel:
            print(f"   {rel:<42} {g:>4} {z:>5} {a:>6}")

    print()
    print("-- The register, as the BODY CHANNEL sees it --")
    print()
    for tag, satz in GRUENDE:
        print(f"   {tag:<24}{je_grund[tag]:>4}   {satz}")
    # **The kind letters must add up to the refusals too.** Same rule as the reasons: a
    # detail line this tool cannot parse would silently shrink a column, and a column that
    # is short by three looks exactly like a channel that refuses three fewer.
    if sum(je_art.values()) != abgesagt:
        print(f"ABORT: the kinds count {sum(je_art.values())}, refused are {abgesagt}.")
        return 2

    print()
    print("-- Refused BY KIND, before an expression is looked at --")
    print()
    nach_art = sum(je_art[k] for k in je_art if k not in UEBERSETZT)
    for tag, satz in ARTEN:
        marke = "translated" if tag in UEBERSETZT else "by kind"
        print(f"   {tag}  {je_art[tag]:>4}   {satz:<44} {marke}")
    print()
    print(
        f"   {nach_art} of {abgesagt} refusals never reached a translation. The reason beside"
    )
    print("   them names a Gabbro construct and reads like a missing form; what it really")
    print("   names is the one GOAL SHAPE this channel emits -- the body runs, and the")
    print("   postcondition holds. **The coverage over what it ATTEMPTS is the other**")
    print(f"   number: {ziele} of {ziele + abgesagt - nach_art}.")

    print()
    print(
        f"== BODY CHANNEL: {gesamt} obligations, {ziele} goals, {abgesagt} refused "
        f"({ohne_register} units with errors, no register) =="
    )
    print("   And what that does NOT mean: a goal is not a proved obligation. It means")
    print("   the obligation stands CLOSED. Whether it goes through is what `lean` says,")
    print("   and the way there is `./instrumente/pruefe-lean-beweis.sh`.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
