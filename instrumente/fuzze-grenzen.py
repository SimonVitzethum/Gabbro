#!/usr/bin/env python3
"""Push every NUMERIC field of every declaration form to its boundaries -- and hold the
checker to the property this folder lives by.

    THE CHECKER EITHER ACCEPTS, OR IT REFUSES BY NAME.

A panic is a third answer. A silent wrap that turns a refusal into `0 errors` is a fourth,
and it is the worse of the two -- a crash is at least a measurement.

**And the two build profiles must agree.** There is no `[profile.release]` in `Cargo.toml`,
so Rust's overflow checks are ON in debug and OFF in release -- and release is what
`cargo install --path crates/gabbro-cli` produces, the install `README.md` documents. On
2026-09-01 `@[u128::MAX:0]` was measured at

    debug   -> panicked at umgebung.rs:1334, exit 101
    release -> 3 items, 0 errors, 0 hints, exit 0

*The same source file, two answers, and the honest one is the one nobody ships.* That
disagreement is mechanically decidable, needs no oracle for what the right answer IS, and
catches both third answers at once. It is the property this instrument measures.

Usage:
    fuzze-grenzen.py --debug target/debug/gabbro --release target/release/gabbro
    fuzze-grenzen.py ... --keep VERZ      keep every generated file (for a probe)

Exit: 0 when every case answered the same in both builds and neither panicked, 1 otherwise.

**NO `--fail-fast`.** A run that stops at the first hit answers "does at least one fire",
and the question asked is "which fire" (CLAUDE.md).
"""

import argparse
import pathlib
import subprocess
import sys
import tempfile

# `sys.path` gets the tool's own directory, the same reason as in `pruefe-konstrukte.py`:
# this file may be LOADED rather than run, and then `sys.path[0]` is the working directory.
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import abschnitt  # noqa: E402

U8, U16, U32, U64 = 0xFF, 0xFFFF, 0xFFFF_FFFF, 0xFFFF_FFFF_FFFF_FFFF
U128 = (1 << 128) - 1

# The boundary ladder. Every rung is a value at which SOME width changes its mind:
# the type's own limit, one below it, one above it -- plus the small values where a
# `- 1` or a `+ 1` in the checker can leave the range.
LADDER = [
    0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 33, 63, 64, 65, 127, 128, 129,
    255, 256, 257, 1023, 1024, 65535, 65536, 65537,
    (1 << 31) - 1, 1 << 31, (1 << 31) + 1,
    U32 - 1, U32, U32 + 1, U32 + 2,
    (1 << 63) - 1, 1 << 63,
    U64 - 1, U64, U64 + 1,
    (1 << 127) - 1, 1 << 127,
    U128 - 1, U128,
]

# Values that are not legal integer literals at all, or that sit just past `u128`. The
# lexer owes a NAMED refusal for each; what it must not do is panic or disagree.
LEXICAL = [
    "0x", "0b", "0o", "0x_", "0xG", "0b2", "1__2", "_1", "1_",
    str(U128 + 1), str(U128 + 2), str(1 << 129), str(1 << 200),
    "0x" + "F" * 32, "0x" + "F" * 33, "0x" + "F" * 64,
    "9" * 40, "9" * 100,
    "0x1_0000_0000_0000_0000_0000_0000_0000_0000",
]

# ---------------------------------------------------------------------------------------
# The forms. Each names EVERY numeric field the grammar gives it, so that a sweep over one
# template covers one declaration form completely. `{V}` is the swept slot; the other
# numbers are small and fixed, so a finding names one field and not a combination.
#
# **Each form carries a KNOWN-GOOD value beside it, and the run checks it first.** The first
# draft of this instrument did not, and eight of its fifteen templates were not valid Gabbro
# -- `effects { }` instead of `effects { pure }`, a `walk` body with the wrong separator. The
# sweep then measured the same parse error 60 times per form and called it 595 findings.
# *A generator whose baseline does not parse has an EMPTY population, and `W17` says a green
# judgement over nothing looks exactly like a green judgement.*
# ---------------------------------------------------------------------------------------
GUT = {
    "bank-stride": "8", "bank-count": "4", "bank-at": "0x0", "bank-regversatz": "0x0",
    "reg-versatz": "0x8", "reg-bit-hi": "3", "reg-bit-lo": "0",
    "format-bit-hi": "31", "format-bit-lo": "0",
    "walk-levels": "4", "table-count": "8",
    "range-hi": "1000", "range-lo": "0",
    "ausdruck": "5", "costs": "2",
}

FORMEN = {
    # `bank` -- three numeric fields, and `N048`/`N049`/`N050` all live here.
    "bank-stride": """module f {{
opaque type Pa = u64;
device D(basis : Pa) at mmio {{
    bank F at 0x0 stride {V} count 4 {{ reg X : u64 @0x0 class rw }}
}}
}}""",
    "bank-count": """module f {{
opaque type Pa = u64;
device D(basis : Pa) at mmio {{
    bank F at 0x0 stride 8 count {V} {{ reg X : u64 @0x0 class rw }}
}}
}}""",
    "bank-at": """module f {{
opaque type Pa = u64;
device D(basis : Pa) at mmio {{
    bank F at {V} stride 8 count 4 {{ reg X : u64 @0x0 class rw }}
}}
}}""",
    "bank-regversatz": """module f {{
opaque type Pa = u64;
device D(basis : Pa) at mmio {{
    bank F at 0x0 stride 8 count 4 {{ reg X : u64 @{V} class rw }}
}}
}}""",
    # `reg` -- the offset, and the two ends of a field's bit range (`N007`, `N047`).
    "reg-versatz": """module f {{
opaque type Pa = u64;
device D(basis : Pa) at mmio {{ reg X : u64 @{V} class rw }}
}}""",
    "reg-bit-hi": """module f {{
opaque type Pa = u64;
device D(basis : Pa) at mmio {{ reg X : u64 @0x0 class rw fields {{ A @[{V}:0] }} }}
}}""",
    "reg-bit-lo": """module f {{
opaque type Pa = u64;
device D(basis : Pa) at mmio {{ reg X : u64 @0x0 class rw fields {{ A @[63:{V}] }} }}
}}""",
    # `format` -- the same bit range on the other construct that has one.
    "format-bit-hi": """module f {{
format F endian big {{ a : u32 @[{V}:0], }}
}}""",
    "format-bit-lo": """module f {{
format F endian big {{ a : u32 @[31:{V}], }}
}}""",
    # `walk levels` -- the field whose modulo-2^32 wrap certified `slack 0` on 2026-09-01.
    "walk-levels": """module f {{
format Pte endian little {{
    praesent : bool @0,
    rest     : u64 @[63:1] reserved,
}}
walk T levels {V} {{
    node : [Pte; 512],
    down : rest when it.praesent,
    leaf : it.praesent,
}}
}}""",
    # `table count` -- the bound every `index into` inherits.
    "table-count": """module f {{
table T count {V} {{ slot {{ a : u32 in 0 .. 1000, }} }}
}}""",
    # A range type's two ends: the place `M104` reads its width from.
    "range-hi": """module f {{
type R = u32 in 0 .. {V};
}}""",
    "range-lo": """module f {{
type R = u64 in {V} .. 0xFFFF_FFFF_FFFF_FFFF;
}}""",
    # An integer literal in an ordinary expression -- the plain path into `M1`.
    "ausdruck": """module f {{
impl fn g() -> u64
    effects {{ pure }}
    costs   <= 2 ops
{{
    return {V};
}}
}}""",
    # `costs <= N ops` -- a numeric field on the clause that carries the cost proof.
    "costs": """module f {{
impl fn g() -> u32
    effects {{ pure }}
    costs   <= {V} ops
{{
    return 1;
}}
}}""",
}


def lauf(binaer, datei, timeout=25):
    """One run. Returns (exit, panicked, text). NEVER raises -- a crash is a datum."""
    try:
        p = subprocess.run(
            [binaer, "check", str(datei)],
            capture_output=True, text=True, timeout=timeout, errors="replace",
        )
    except subprocess.TimeoutExpired:
        return (None, False, "<TIMEOUT>")
    text = p.stdout + p.stderr
    panik = "panicked at" in text or "RUST_BACKTRACE" in text
    return (p.returncode, panik, text)


def antwort(exit_code, panik, text):
    """The ANSWER, reduced to what the property is about.

    Not the full diagnostic text: two builds may legitimately word a message differently
    one day. What must agree is *which* of the three answers came back, and -- when it is
    a refusal -- *which code*.
    """
    if panik:
        return "PANIC"
    if exit_code is None:
        return "TIMEOUT"
    if exit_code not in (0, 1, 2):
        return f"EXIT{exit_code}"
    # The diagnostic prints its code in brackets: `error: [N050] file:3:9: ...`. Stripping
    # `[]` is not cosmetic -- without it every refusal came back `EXIT1-UNNAMED`, and the
    # instrument reported 595 "unexpected exits" over a corpus that was answering correctly.
    codes = sorted({w.strip("[]:,.`") for w in text.split()
                    if len(w.strip("[]:,.`")) == 4
                    and w.strip("[]:,.`")[0].isupper()
                    and w.strip("[]:,.`")[1:].isdigit()})
    if exit_code == 0:
        return "ACCEPT"
    return "REFUSE " + ",".join(codes) if codes else f"EXIT{exit_code}-UNNAMED"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--debug", required=True)
    ap.add_argument("--release", required=True)
    ap.add_argument("--keep")
    ap.add_argument("--nur", help="only this form")
    args = ap.parse_args()

    werte = [str(v) for v in LADDER] + LEXICAL
    formen = {k: v for k, v in FORMEN.items() if not args.nur or k == args.nur}

    arb = pathlib.Path(args.keep) if args.keep else pathlib.Path(tempfile.mkdtemp())
    arb.mkdir(parents=True, exist_ok=True)

    # **The instrument's own speech test, and it runs BEFORE the sweep.** A template whose
    # known-good value is refused is not measuring its numeric field -- it is measuring a
    # constant parse error, 60 times, and reporting it as findings.
    #
    # The counter-direction of this speech test is on the record rather than in a branch:
    # three runs of this tool over the same tree gave 7 panics, then 3, then 0, as the two
    # arithmetic repairs and the message repair landed. *A tool nobody has seen fall is an
    # ornament* (R11); this one has been seen falling twice on its way to green.
    tot = []
    for form in sorted(formen):
        f = arb / f"basis-{form}.gab"
        f.write_text(formen[form].format(V=GUT[form]) + "\n")
        a = antwort(*lauf(args.debug, f))
        if a != "ACCEPT":
            tot.append((form, GUT[form], a))
    if tot:
        print("== THE GENERATOR IS BROKEN, AND NOTHING BELOW WAS MEASURED ==")
        for form, wert, a in tot:
            print(f"   {form:18s} baseline `{wert}` -> {a}, so every value gives the same answer")
        print("   A template whose baseline does not parse has an EMPTY population (W17).")
        return 1

    panics, uneinig, sonst = [], [], []
    n = 0
    for form, schablone in sorted(formen.items()):
        for wert in werte:
            n += 1
            f = arb / f"{form}--{n:04d}.gab"
            f.write_text(schablone.format(V=wert) + "\n")
            de, dp, dt = lauf(args.debug, f)
            re_, rp, rt = lauf(args.release, f)
            a_d, a_r = antwort(de, dp, dt), antwort(re_, rp, rt)
            if a_d == "PANIC" or a_r == "PANIC":
                panics.append((form, wert, a_d, a_r, dt if dp else rt))
            elif a_d != a_r:
                uneinig.append((form, wert, a_d, a_r, ""))
            elif a_d.startswith("EXIT") or a_d == "TIMEOUT":
                sonst.append((form, wert, a_d, a_r, dt))

    print(f"== BOUNDARY SWEEP: {n} cases over {len(formen)} forms x {len(werte)} values ==")
    print(f"   {len(LADDER)} numeric rungs + {len(LEXICAL)} lexical shapes")
    print()

    def zeige(titel, liste, erklaerung):
        print(f"-- {titel}: {len(liste)} --")
        if erklaerung and liste:
            print(f"   {erklaerung}")
        for form, wert, a_d, a_r, extra in liste:
            kurz = wert if len(wert) <= 44 else wert[:41] + "..."
            print(f"   {form:18s} {kurz:46s} debug={a_d:22s} release={a_r}")
            if extra:
                for zeile in extra.splitlines():
                    if "panicked at" in zeile:
                        print(f"        {zeile.strip()}")
        print()

    zeige("PANICS -- a third answer", panics,
          "the checker neither accepted nor refused by name")
    zeige("DEBUG/RELEASE DISAGREE -- a wrap that only the shipped build makes", uneinig,
          "release is what `cargo install` produces; the honest answer is the one nobody ships")
    zeige("OTHER -- unexpected exit or timeout", sonst, "")

    schlecht = len(panics) + len(uneinig) + len(sonst)
    if args.keep:
        print(f"   generated files kept in {arb}")
    print(f"== {n - schlecht} of {n} answered the same in both builds, without a panic ==")
    return 1 if schlecht else 0


if __name__ == "__main__":
    # **`abschnitt.fahre` and not a bare `main()`.** This tool has an exit ABOVE its sweep --
    # the broken-generator branch -- and a run that leaves there has measured nothing while
    # returning the same `1` a finding returns. *A tool that measured nothing must not look
    # like one that found something.*
    sys.exit(abschnitt.fahre(main))
