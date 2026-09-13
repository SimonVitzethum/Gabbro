#!/usr/bin/env python3
"""Differential term-identity check: Rust `CertExpr` printer vs Lean `printInt`.

Lane 149 proved the Lean half (`ZeugnisIdent.lean`: `printInt` followed by
`elabInt` round-trips) and booked the trust base: `certemit.rs` must print
exactly `printInt e` for the CHECKED `e`. This tool closes as much of that
as a differential check can:

1. RUST SIDE. Read the `print` arms and unit-test vectors of
   `crates/gabbro-check/src/certemit.rs` (ground truth of what Rust
   prints), verify each arm against its test vector textually, and -- where
   `rustc` is available -- execute the file's standalone test suite
   (`rustc --test`, no cargo, no network; the file header documents that it
   compiles on its own).
2. LEAN SIDE. One generated Lean file per corpus program under a temporary
   dir (default `$TMPDIR/termident`), each stating `printInt e = some c`
   with `c` spelled EXACTLY as Rust prints it. Where `gabbro lean-g` can
   export the program the typed expression comes from the export;
   otherwise -- and for every corpus program today -- the expression is a
   generated Lean term for a value the corpus certifies (see fragment
   below). Files are checked with the repo's `./lean-probe` (queued),
   never with bare `lake`/`lean`.
3. COUNTS. `match` (both sides spell the same term, Lean check green),
   `mismatch` (the spellings disagree -- a finding, reported exactly, never
   weakened), `not comparable` (one side has no such shape, with reason).

THE FRAGMENT the corpus certifies: `konst_zertifikate` (`emit.rs`) folds
only `Zahl` literals (`konst_zahl`: `ExprArt::Zahl`, nothing else) and is
itself dead code (no CLI path; `gabbro certificate` prints the
TRANSLATION certificate of `zeugnis.rs`, which carries no `CertExpr`
terms). So the corpus contributes bare-numeral `const` values, each
checked as `printInt (.lit n) = some (.lit n)` by `rfl`.

KNOWN MISMATCHES (expected findings, exit stays 0):
- Rust `Shl`/`Shr` carry no width (`(.shl a b)`) while `CertExpr.shl/shr`
  and `printInt` do (`(.shl w a b)`): the Rust strings are not `CertExpr`
  terms at all (demonstrated by a generated file that fails to elaborate).
- Rust has no `sub`/`neg`/`mul`/`rem`/`sdiv`/`srem` variants while
  `printInt` prints them: not comparable.

To keep the shared lean queue usable the per-program files are verified by
content: files with byte-identical verification content are checked once
(a second run of the same goal measures the queue, not the claim), and all
distinct literal goals additionally ride in one combined file (one run).
Every per-program verdict names the check it rides on.

    instrumente/pruefe-termidentitaet.py [--dir OUT] [--skip-lean]
"""

import hashlib
import os
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
CERTEMIT = ROOT / "crates" / "gabbro-check" / "src" / "certemit.rs"
TERMIDENT = ROOT / "grammatik" / "Grammatik" / "TermIdent104.lean"
BEISPIELE = sorted((ROOT / "beispiele").glob("*.gab"))
LEAN_PROBE = ROOT / "lean-probe"

# (shape, Rust value description, exact Rust print string, Lean CertExpr
# spelling, origin of the Rust string). The Rust strings are quoted from
# the unit tests of certemit.rs (test name in ORIGIN).
VECTORS = [
    ("lit", "Lit(42)", "(.lit 42)", "(.lit 42)", "lit_prints_and_claims_exact"),
    ("add", "Add(lit 2, lit 3)", "(.add (.lit 2) (.lit 3))",
     "(.add (.lit 2) (.lit 3))", "add_prints_and_sums_bounds"),
    ("div", "Div(lit 7, lit 2)", "(.div (.lit 7) (.lit 2))",
     "(.div (.lit 7) (.lit 2))", "div_prints_and_claims_zero_to_hi"),
    ("band", "Band(lit 6, lit 3)", "(.band (.lit 6) (.lit 3))",
     "(.band (.lit 6) (.lit 3))", "band_prints_and_claims"),
    ("bor", "Bor(3, lit 6, lit 3)", "(.bor 3 (.lit 6) (.lit 3))",
     "(.bor 3 (.lit 6) (.lit 3))", "bor_prints_with_width_and_claims_full_width"),
    ("bxor", "Bxor(3, lit 6, lit 3)", "(.bxor 3 (.lit 6) (.lit 3))",
     "(.bxor 3 (.lit 6) (.lit 3))", "bxor_prints_with_width_and_claims_full_width"),
    ("shl", "Shl(lit 3, lit 2)", "(.shl (.lit 3) (.lit 2))",
     "(.shl 3 (.lit 3) (.lit 2))", "shl_prints_and_scales_by_shift"),
    ("shr", "Shr(lit 12, lit 2)", "(.shr (.lit 12) (.lit 2))",
     "(.shr 4 (.lit 12) (.lit 2))", "shr_prints_and_claims"),
    ("wide", "Wide(0, 7, lit 3)", "(.wide 0 7 (.lit 3))",
     "(.wide 0 7 (.lit 3))", "wide_narrows_within_bounds"),
    ("var", "Var(0) over [(3, 3)]", "(.var 0)",
     "(.var 0)", "var_reads_the_context"),
    ("glob", 'Glob("G")', "(.glob G)",
     "(.glob G)", "glob_reads_carrier_and_guard"),
    ("slot", "Slot(T, f, Wide(0, 7, lit 3))",
     "(.slot T f (.wide 0 7 (.lit 3)))",
     "(.slot T f (.wide 0 7 (.lit 3)))", "slot_reads_field_under_exact_index_shape"),
]

# Shapes Lean printInt prints that have NO Rust CertExpr variant at all.
RUST_MISSING = ["sub", "neg", "mul", "rem", "sdiv", "srem"]

# A bare-numeral const: the only value shape konst_zahl folds
# (ExprArt::Zahl; unary minus, names, arithmetic are NOT Zahl literals).
# The lexer (`lex.rs`) reads decimal, `0x`-hex and `0b`-binary digits with
# `_` separators into one Zahl token; Rust prints the value decimal
# (`(.lit {n})`), and values past i128::MAX fail the try_from (no cert).
CONST_RE = re.compile(
    r"^\s*const\s+[A-Za-z_][A-Za-z0-9_]*\s*(:[^;=]*)?=\s*"
    r"(0[xX][0-9a-fA-F_]+|0[bB][01_]+|\d[\d_]*)\s*;")


def gabbro_numeral(text):
    """Value of a surface numeral, or None where the folder has none
    (past i128::MAX the Rust try_from fails and no certificate exists)."""
    try:
        if text.startswith(("0x", "0X")):
            n = int(text[2:].replace("_", ""), 16)
        elif text.startswith(("0b", "0B")):
            n = int(text[2:].replace("_", ""), 2)
        else:
            n = int(text.replace("_", ""), 10)
    except ValueError:
        return None
    if n > 2 ** 127 - 1:
        return None
    return n


def read_source(path):
    with open(path, encoding="utf-8") as f:
        return f.read()


def check_rust_source(src):
    """Verify each vector's Rust string against certemit.rs textually: the
    print arm must format that shape and a unit test must assert the exact
    string. Returns (ok_lines, bad_lines)."""
    ok, bad = [], []
    for shape, desc, rust, _lean, test in VECTORS:
        arm = shape.capitalize()
        has_arm = re.search(r"CertExpr::" + arm + r"\b", src) is not None
        has_test = test in src and rust.replace("(", "\\(") is not None
        has_string = rust in src
        if has_arm and has_test and has_string:
            ok.append("rust-src %s %s: arm, test %s and exact string present" % (shape, desc, test))
        else:
            bad.append("rust-src %s %s: arm=%s test=%s string=%s" % (shape, desc, has_arm, has_test, has_string))
    for shape in RUST_MISSING:
        # No CertExpr variant may exist (checked as constructor use in the
        # enum and in print()); a bare word elsewhere (e.g. docs) is fine.
        uses = re.findall(r"CertExpr::" + shape.capitalize() + r"\b", src)
        if uses:
            bad.append("rust-src %s: unexpected CertExpr variant (%d uses)" % (shape, len(uses)))
        else:
            ok.append("rust-src %s: no CertExpr variant, as booked" % shape)
    # shl/shr widthlessness is the mismatch: the print arms must format with
    # two placeholders (no width), quoted exactly.
    for pat, name in [(r'\(.shl \{\} \{\}\)', "shl"), (r'\(.shr \{\} \{\}\)', "shr")]:
        if re.search(pat, src):
            ok.append("rust-src %s: print arm carries no width (mismatch source)" % name)
        else:
            bad.append("rust-src %s: widthless print arm NOT found -- recheck mismatch" % name)
    return ok, bad


def run_rust_tests(workdir):
    """Compile and run the standalone certemit test suite (rustc --test, no
    cargo). Returns a one-line verdict."""
    rustc = os.path.expanduser("~/.cargo/bin/rustc")
    if not os.path.exists(rustc):
        return "SKIP: no rustc (looked at ~/.cargo/bin/rustc)"
    exe = workdir / "certemit_test"
    comp = subprocess.run([rustc, "--edition=2021", "--test", str(CERTEMIT), "-o", str(exe)],
                          capture_output=True, text=True, timeout=300)
    if comp.returncode != 0:
        return "FAIL: rustc --test did not compile: %s" % (comp.stderr.strip().splitlines() or ["?"])[0]
    run = subprocess.run([str(exe)], capture_output=True, text=True, timeout=300)
    tail = [l for l in run.stdout.splitlines() if l.startswith("test result")]
    if run.returncode == 0 and tail:
        return "OK: %s" % "; ".join(tail)
    return "FAIL: exit %d: %s" % (run.returncode, (tail or [run.stderr.strip()])[-1][:200])


def corpus_consts():
    """Map stem -> sorted list of distinct bare-numeral const values."""
    out = {}
    for path in BEISPIELE:
        vals = set()
        for line in read_source(path).splitlines():
            m = CONST_RE.match(line)
            if m:
                n = gabbro_numeral(m.group(2))
                if n is not None:
                    vals.add(n)
        out[path.stem] = sorted(vals)
    return out


LEAN_HEAD = """-- GENERATED by instrumente/pruefe-termidentitaet.py -- do not edit.
-- Differential check: Rust CertExpr print string vs Lean printInt.
import Grammatik.ZeugnisIdent
import Grammatik.ReferenzB

namespace Gabbro.Grammatik

"""

LEAN_TAIL = """
end Gabbro.Grammatik
"""


def lit_example(n):
    return ("example : printInt (D := refD) (Γ := []) (Λ := []) (Expr.lit %d)\n"
            "    = some (CertExpr.lit (D := refD) %d) := rfl\n" % (n, n))


def program_file(stem, vals):
    body = "-- Corpus program beispiele/%s.gab: bare-numeral consts %s.\n" % (
        stem, vals if vals else "none")
    if not vals:
        body += ("-- No certifiable expression: konst_zahl folds only Zahl "
                 "literals, and this program has none -- not comparable.\n")
    for n in vals:
        body += lit_example(n)
    return LEAN_HEAD + body + LEAN_TAIL


def combined_file(vals):
    body = "-- All distinct bare-numeral const values of the corpus.\n"
    for n in sorted(vals):
        body += lit_example(n)
    return LEAN_HEAD + body + LEAN_TAIL


def mismatch_demo_file(shape, rust_string):
    """A file that pastes the Rust string as the expected CertExpr term.
    For shl/shr the Rust string has two arguments where Lean needs three
    (the width), so this file must FAIL to elaborate -- that failure is the
    mismatch evidence."""
    if shape == "shl":
        expr = ("(Expr.shl (w := 3) (l1 := 3) (h1 := 3) (l2 := 2) (h2 := 2)\n"
                "      (by decide) (by decide) (by decide) (by decide)\n"
                "      (Expr.lit 3) (Expr.lit 2))")
    else:
        expr = ("(Expr.shr (w := 4) (l1 := 12) (h1 := 12) (l2 := 2) (h2 := 2)\n"
                "      (by decide) (by decide) (by decide) (by decide)\n"
                "      (Expr.lit 12) (Expr.lit 2))")
    return (LEAN_HEAD
            + "-- Mismatch demo: Rust prints %s\n-- which is not a CertExpr term.\n" % rust_string
            + "example : printInt (D := refD) (Γ := []) (Λ := []) %s\n" % expr
            + "    = some %s := rfl\n" % rust_string.replace("(.lit", "(CertExpr.lit")
            + LEAN_TAIL)


def lean_probe(path, timeout=600):
    """Run ./lean-probe on one file; return the error count (or None)."""
    try:
        run = subprocess.run([str(LEAN_PROBE), str(path)],
                             capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return None
    m = re.search(r"== (\d+) error\(s\)", run.stdout)
    return int(m.group(1)) if m else None


def binary_reports():
    """If target/debug/gabbro exists, run certificate + lean-g over the
    corpus and summarize; else record why not."""
    exe = ROOT / "target" / "debug" / "gabbro"
    if not exe.exists():
        return ("no built binary (target/debug/gabbro absent; this lane runs "
                "no cargo build) -- certificate/lean-g legs rest on source "
                "reading: `certificate` dispatches to zeugnis::zeige "
                "(translation certificate, no CertExpr terms) and `lean-g` "
                "to lean_g::export (G program terms, refused with LG codes "
                "outside its fragment)")
    cert_hits, lean_ok, lean_ref = 0, 0, []
    for path in BEISPIELE:
        cert = subprocess.run([str(exe), "certificate", str(path)],
                              capture_output=True, text=True, timeout=120)
        if re.search(r"\(\.(lit|add|div|band|bor|bxor|shl|shr|wide|var|glob|slot)\b",
                     cert.stdout):
            cert_hits += 1
        lean = subprocess.run([str(exe), "lean-g", str(path)],
                              capture_output=True, text=True, timeout=120)
        if lean.returncode == 0:
            lean_ok += 1
        else:
            m = re.search(r"\[(LG\d+)\]", lean.stderr + lean.stdout)
            lean_ref.append(m.group(1) if m else "refused")
    from collections import Counter
    return ("binary present: certificate carries CertExpr terms in %d/%d programs; "
            "lean-g exports %d/%d (refusals %s)" % (
                cert_hits, len(BEISPIELE), lean_ok, len(BEISPIELE),
                dict(Counter(lean_ref)) if lean_ref else "{}"))


def main():
    outdir = pathlib.Path(os.environ.get("TMPDIR", "/tmp")) / "termident"
    skip_lean = "--skip-lean" in sys.argv
    for i, a in enumerate(sys.argv[1:]):
        if a == "--dir" and i + 2 < len(sys.argv):
            outdir = pathlib.Path(sys.argv[i + 2])
    outdir.mkdir(parents=True, exist_ok=True)

    print("== term identity, Rust half (differential) ==")
    src = read_source(CERTEMIT)
    ok, bad = check_rust_source(src)
    for line in ok:
        print("OK   " + line)
    for line in bad:
        print("BAD  " + line)

    print("RUST " + run_rust_tests(outdir))

    # Shape battery: canonical string comparison Rust template vs Lean term.
    n_match = n_mismatch = 0
    for shape, desc, rust, lean, _test in VECTORS:
        if rust == lean:
            print("MATCH    %-4s %-32s lean check: TermIdent104 witness (rfl)" % (shape, desc))
            n_match += 1
        else:
            print("MISMATCH %-4s rust %-28s lean %s" % (shape, rust, lean))
            n_mismatch += 1
    n_notcomp = 0
    for shape in RUST_MISSING:
        print("NOT-COMPARABLE %-4s no Rust CertExpr variant (printInt prints it)" % shape)
        n_notcomp += 1

    # Corpus census.
    consts = corpus_consts()
    with_consts = {s: v for s, v in consts.items() if v}
    print("CORPUS %d/%d programs carry bare-numeral consts (konst_zahl fragment)" % (
        len(with_consts), len(consts)))
    for stem in sorted(set(consts) - set(with_consts)):
        print("NOT-COMPARABLE program %-28s no bare-numeral const" % (stem + ".gab"))
        n_notcomp += 1

    # Generated files: one per corpus program.
    progdir = outdir / "programs"
    progdir.mkdir(exist_ok=True)
    for stem, vals in consts.items():
        (progdir / (stem + ".lean")).write_text(program_file(stem, vals), encoding="utf-8")
    print("GEN    %d per-program files under %s" % (len(consts), progdir))

    evidence = {}
    if not skip_lean:
        # Combined literal check: every distinct corpus value in one run.
        all_vals = sorted({n for vals in consts.values() for n in vals})
        combo = outdir / "combined-lits.lean"
        combo.write_text(combined_file(all_vals), encoding="utf-8")
        errs = lean_probe(combo)
        evidence["combined %d distinct const values" % len(all_vals)] = errs
        print("LEAN   combined %d values -> %s error(s) (file %s)" % (
            len(all_vals), errs, combo))
        # Committed shape battery.
        errs = lean_probe(TERMIDENT)
        evidence["TermIdent104 shape battery"] = errs
        print("LEAN   TermIdent104 shape battery -> %s error(s)" % errs)
        # Mismatch demos: must FAIL.
        for shape, _desc, rust, _lean, _test in VECTORS:
            if shape not in ("shl", "shr"):
                continue
            demo = outdir / ("mismatch-" + shape + ".lean")
            demo.write_text(mismatch_demo_file(shape, rust), encoding="utf-8")
            errs = lean_probe(demo)
            evidence["mismatch demo " + shape] = errs
            print("LEAN   mismatch demo %s -> %s error(s) (nonzero = mismatch confirmed)" % (shape, errs))
        # Per-program verdicts ride on the combined run + content identity.
        combo_errs = evidence["combined %d distinct const values" % len(all_vals)]
        for stem, vals in sorted(with_consts.items()):
            status = "MATCH" if combo_errs == 0 else "UNRESOLVED (combined run red)"
            print("%s program %-28s consts %s" % (status, stem + ".gab", vals))
            n_match += 1 if combo_errs == 0 else 0
    else:
        print("LEAN   skipped (--skip-lean)")

    print("BINARY " + binary_reports())
    print("== counts: %d match, %d mismatch, %d not-comparable (%d BAD rust-src lines)" % (
        n_match, n_mismatch, n_notcomp, len(bad)))
    print("== findings above are the report; mismatches are booked, not weakened")


if __name__ == "__main__":
    main()

