#!/usr/bin/env python3
"""**The checker does in Rust what `M104` forbids in its object language.**

`M104` says: if a result range does not fit the declared width, that is a compile error and
not a wrap-around. The checker that says so is itself written with `as`, and `as` wraps in
silence. On 2026-09-01 that cost two real defects, both on numbers a USER wrote:

  * `umgebung.rs::walkschranken` -- `levels 4294967296` reached `checked_pow` through
    `e as u32`, arrived as `0`, and the leaf bound of a `walk` became `512^0 = 1`.
    `costs <= 1 ops` over a whole page-table traversal was ACCEPTED, and `gabbro costs`
    printed `computed 1 . promised 1 . slack 0` -- as a MEASUREMENT.
  * `umgebung.rs::typ_von_feld_mit` / `typ_von_reg` -- `@[u128::MAX:0]` overflowed a `+ 1`
    and killed `gabbro check` (exit 101) before any pass could speak. In a RELEASE build,
    where overflow checks are off, the same line wrapped in silence and the file passed
    with `0 errors`.

This tool counts truncating casts and holds a ratchet over them.

## What it counts, and it is NOT what clippy prints

`cargo clippy --all-targets` lints the same library once per target, so it printed **72
warnings over 36 casts** -- and the mandate that started this work quoted the warning count
as though it were the cast count. **The number here is unique `(file, line, column)` sites**,
and it is the only one with a denominator worth writing down (`W25`).

## And the `#[allow]` hole is counted, not left open

A ratchet over warnings alone is moved by `#[allow(clippy::cast_possible_truncation)]`
without a single cast going away. So the mark is over

    truncating cast sites  +  suppressions of that lint

A suppression removes a site and adds a suppression: **the sum does not move.** Silencing is
free of merit here, which is the whole point.

An INNER suppression (`#![allow(...)]`, crate- or module-wide) hides an unknown number of
sites, so this tool refuses to produce a number at all rather than a wrong one. An outer
`#[allow]` on a `fn` or `impl` covering several casts is a real remaining hole and it is not
detected -- *named here because a limit that is not written down is a limit nobody sees.*

## WHAT THIS MARK DOES NOT MEASURE, and the evidence is the census that built it

**Neither defect above would have moved this number.** Both casts were present, counted and
green on the day they were written; what made them defects was that a user-controlled value
reached them unbounded. The census that found them ran once, by hand, over 36 sites: 33 were
provably in range -- byte offsets under a `Span` that is `u32` by design, a shift guarded to
`0..127`, an `f64 as f32` that is a deliberate round-trip test -- and 3 were bugs.

    This tool measures HOW MANY casts exist. The risk is WHETHER A USER-CONTROLLED VALUE
    REACHES ONE UNBOUNDED. Those are different questions, and on this tree they came apart.

*So the mark is a ratchet against drift, not a proof of safety*, and it is written down that
way for the same reason `pruefe-zitate.py` writes down that it cannot read.

## A missing clippy is a missing measurement, never a green one (`W1`)

The first run of this investigation was
`cargo clippy --all-targets -- -W clippy::pedantic` on `ki-pc-fisch-101`, and it printed
`'cargo-clippy' is not installed for the toolchain` -- **and the wrapper reported exit 0.**
Zero warnings, zero findings, zero measurement. This tool exits 2 in that case.

## Where it belongs

It runs `cargo clippy`, so by `CLAUDE.md` it belongs on `ki-pc-fisch-101`, next to
`cargo build` and `pruefe-luecken.py`:

    ssh ki-pc-fisch-101 'cd gabbro-t && export PATH=$HOME/.cargo/bin:$PATH \\
                         && ./instrumente/pruefe-umwandlungen.py'

    ./instrumente/pruefe-umwandlungen.py              checks
    ./instrumente/pruefe-umwandlungen.py --liste      every site with its types
    ./instrumente/pruefe-umwandlungen.py --sprechprobe  only the two-way speech test
"""
import json
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile

W = pathlib.Path(__file__).resolve().parent.parent
FRIST = 600  # seconds; this tool builds, and a cold cache is the slow case.

LINT = "cast_possible_truncation"

# **The mark, measured 2026-09-01 on the repaired tree.** It stood at 36 before the three
# repairs in `umgebung.rs` (walk exponent, and the two bit-range widths); those removed three
# casts and no suppression was added, so the number fell by exactly three.
#
#   33 sites  =  16 lex.rs  +  8 emit.rs  +  5 span.rs  +  2 main.rs  +  1 typen.rs
#                +  1 umgebung.rs
#
# **It may FALL and not rise.** And it is a ratchet against drift, not a safety proof -- the
# section above says why, and the two defects it would not have caught are named there.
MARKE = 33

# An outer suppression of the lint: it removes a warning, so it is added back in here.
ERLAUBNIS = re.compile(r"#\s*\[\s*(?:allow|expect)\s*\(\s*clippy::" + LINT)
# An INNER one covers a whole module or crate. It is not countable, so it is refused.
ERLAUBNIS_INNEN = re.compile(r"#!\s*\[\s*(?:allow|expect)\s*\(\s*clippy::" + LINT)


def quellen(wurzel):
    return sorted(wurzel.glob("crates/*/src/*.rs"))


def clippy_da():
    return shutil.which("cargo-clippy") is not None


def erhebe(wurzel, ziel_leer=True):
    """Unique truncating-cast sites under `crates/*/src/`, as (datei, zeile, spalte, text)."""
    ruf = [
        "cargo", "clippy", "--all-targets", "--message-format=json",
        "--", "-W", "clippy::" + LINT,
    ]
    if ziel_leer:
        # Without this, a warm cache replays nothing for unchanged crates and the count
        # silently reads 0. **A cache that hides the finding is the same class as `W16`.**
        for lib in wurzel.glob("crates/*/src/lib.rs"):
            lib.touch()
    r = subprocess.run(ruf, cwd=wurzel, capture_output=True, text=True, timeout=FRIST)
    stellen = {}
    for zeile in r.stdout.splitlines():
        zeile = zeile.strip()
        if not zeile.startswith("{"):
            continue
        try:
            o = json.loads(zeile)
        except json.JSONDecodeError:
            continue
        if o.get("reason") != "compiler-message":
            continue
        m = o.get("message") or {}
        if LINT not in ((m.get("code") or {}).get("code") or ""):
            continue
        for s in m.get("spans", []):
            if not s.get("is_primary"):
                continue
            d = s["file_name"]
            if not (d.startswith("crates/") and "/src/" in d):
                continue
            text = (s.get("text") or [{}])[0].get("text", "").strip()
            stellen[(d, s["line_start"], s["column_start"])] = (m.get("message", ""), text)
    return stellen, r


def erlaubnisse(wurzel):
    """(countable outer suppressions, files carrying an UNcountable inner one)."""
    aussen, innen = 0, []
    for d in quellen(wurzel):
        t = d.read_text(encoding="utf-8")
        if ERLAUBNIS_INNEN.search(t):
            innen.append(d.name)
        aussen += len(ERLAUBNIS.findall(t)) - len(ERLAUBNIS_INNEN.findall(t))
    return aussen, innen


SPRECHPROBE_CRATE = {
    "Cargo.toml": (
        '[package]\nname = "sprechprobe"\nversion = "0.0.0"\nedition = "2021"\n'
        "[workspace]\n[lib]\npath = \"crates/p/src/lib.rs\"\n"
    ),
    # One truncating cast, and nothing else that this lint fires on.
    "crates/p/src/lib.rs": (
        "pub fn f(x: u64) -> u32 {\n    x as u32\n}\n"
    ),
}


def sprechprobe():
    """**Both directions, and the second is the one that carries the claim.**

    1. a truncating cast must be COUNTED -- otherwise the tool is blind and reads 0;
    2. the same cast under `#[allow]` must NOT lower the number -- otherwise the ratchet
       is moved by silencing, which is exactly the hole this tool is built around.
    """
    with tempfile.TemporaryDirectory() as td:
        b = pathlib.Path(td)
        for p, inhalt in SPRECHPROBE_CRATE.items():
            (b / p).parent.mkdir(parents=True, exist_ok=True)
            (b / p).write_text(inhalt, encoding="utf-8")

        stellen, r = erhebe(b)
        aussen, innen = erlaubnisse(b)
        if len(stellen) + aussen != 1:
            print("  SPEECH TEST 1 FAILED: one truncating cast, counted %d + %d allowed."
                  % (len(stellen), aussen))
            print("     cargo said: " + (r.stderr.strip().splitlines() or ["(nothing)"])[-1])
            return False

        lib = b / "crates/p/src/lib.rs"
        lib.write_text(
            "pub fn f(x: u64) -> u32 {\n"
            "    #[allow(clippy::cast_possible_truncation)]\n"
            "    let y = x as u32;\n    y\n}\n",
            encoding="utf-8",
        )
        stellen2, _ = erhebe(b)
        aussen2, _ = erlaubnisse(b)
        if len(stellen2) != 0 or aussen2 != 1 or len(stellen2) + aussen2 != 1:
            print("  SPEECH TEST 2 FAILED: under `#[allow]` the SUM must stay 1 -- "
                  "measured %d sites + %d allowed." % (len(stellen2), aussen2))
            return False
    print("  speech test: a cast is counted (1), and `#[allow]` does not lower it (0+1). OK")
    return True


def main():
    if not clippy_da():
        print("ABORT: `cargo-clippy` is not installed -- NOTHING was measured.")
        print("       `rustup component add clippy`. A missing clippy reads exactly like a")
        print("       clean tree, and on 2026-09-01 it did: the run printed no warning and")
        print("       the wrapper reported exit 0. **W1: a missing measurement is never a")
        print("       green one.**")
        return 2

    if not sprechprobe():
        return 2

    stellen, r = erhebe(W)
    if r.returncode not in (0, 101) and not stellen:
        print("ABORT: `cargo clippy` failed and produced no message -- NOTHING was measured.")
        print("       " + "\n       ".join(r.stderr.strip().splitlines()[-4:]))
        return 2

    aussen, innen = erlaubnisse(W)
    if innen:
        print("ABORT: an INNER `#![allow(clippy::%s)]` in %s." % (LINT, ", ".join(innen)))
        print("       It hides an unknown number of sites, so there is no number to give.")
        print("       Use an outer `#[allow]` at the cast -- that one is counted.")
        return 2

    summe = len(stellen) + aussen
    je_datei = {}
    for d, _, _ in stellen:
        n = d.split("/")[-1]
        je_datei[n] = je_datei.get(n, 0) + 1

    print("\n== Truncating casts in `crates/*/src/`: %d sites + %d suppressed = %d =="
          % (len(stellen), aussen, summe))
    if je_datei:
        print("   " + ", ".join("%s %d" % (a, b)
                                for a, b in sorted(je_datei.items(), key=lambda x: -x[1])))
    print("   Counted as unique (file, line, column). `cargo clippy --all-targets` lints the")
    print("   same library once per target -- on 2026-09-01 that was 66 warnings over these")
    print("   33 sites, and the warning count is NOT the cast count (`W25`).")

    if "--liste" in sys.argv:
        print("\n== Every site ==")
        for (d, z, s), (msg, text) in sorted(stellen.items()):
            print("  %s:%d:%d  %s" % (d, z, s, msg))
            print("      %s" % text[:96])

    print("\n== And what this does NOT mean ==")
    print("  It measures HOW MANY casts exist, not whether a USER-CONTROLLED value reaches")
    print("  one unbounded. **Neither defect that caused this tool to be written would have")
    print("  moved the number** -- `levels 4294967296` wrapping to a certified `slack 0`, and")
    print("  `@[u128::MAX:0]` killing the checker before any pass spoke. Both casts were")
    print("  present, counted and green on the day they were written. A ratchet against")
    print("  drift, not a proof of safety.")

    schlecht = 0
    if summe > MARKE:
        print("\n  RATCHET BROKEN: %d sites+suppressions, %d booked." % (summe, MARKE))
        print("  A new truncating cast needs the argument WHY the value cannot exceed the")
        print("  target, at the cast -- or a bound before it. `#[allow]` does not move this.")
        schlecht = 1
    elif summe < MARKE:
        print("\n  The mark may be lowered: %d measured, %d booked." % (summe, MARKE))

    print("\n== Work done: %d files, %d sites, %d suppressions, 2 probes ==" %
          (len(quellen(W)), len(stellen), aussen))
    return schlecht


if __name__ == "__main__":
    sys.exit(main())
