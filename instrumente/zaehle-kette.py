#!/usr/bin/env python3
"""**The chain count** -- how many corpus programs pass the WHOLE translation-validation
chain, not one pillar of it.

    ./instrumente/zaehle-kette.py [--binary PATH] [--allow-stale] [--lean]

WHAT IT DOES
------------
PLAN-UEBERSETZUNGSVALIDIERUNG.md section 3 (revised 2026-09-13): coverage is
MULTIPLICATIVE -- the closing theorem holds only for programs that pass every sieve --
so the state is measured by closed chains, not by per-pillar percentages. This script
prints, per corpus program in `beispiele/*.gab`, which sieve it passes:

  (a) Lean parse -- the Lean parser in `grammatik/Grammatik/Parser/`, and ONLY where a
      generated pin exists (today: `beispiele/104-referenz.gab`, pinned by the `u104*`
      theorems in `Parser/Uebersetze.lean` over the pasted export in `Export104.lean`).
      Everywhere else the column reads "not measured". With `--lean` the pin file is
      re-checked through `./lean-probe`; without it a pin reads "pin present, Lean not
      re-run" -- which counts as NOT passed, because an unchecked pin is not a check.
  (b) `gabbro lean-g` export succeeds (exit 0, nonempty output).
  (c) `gabbro certificate` prints every body: exit 0 and no `REFUSED` line (a `CSnnn`
      refusal is the statement printer saying the body is outside its fragment).
  (d) every emitted C form is in state lemma or named assumption -- the three states of
      `pruefe-cformen.py`, imported from that file (single source of truth). A program
      the emitter refuses has no emitted C, so the column reads "not measured".
  (e) a correspondence certificate exists AND Lean checked it. Today neither half
      exists: `gabbro` prints no per-program `corrcert` sidecar (no CLI surface), and
      T2 -- the Lean rechecker plus rulings for the open C forms -- does not exist
      (`Erhaltung.lean` holds the `CorrCert` SHAPE, not the rechecker). The column
      reads 0 for every program, honestly, never guessed.

The headline "chain count" is the number of programs passing ALL columns. A column that
was not measured counts as not passed -- an unmeasured sieve is not a passed one. On
2026-09-13 the count is 0 (column (e) alone guarantees it); the per-column numbers are
the diagnostics the count replaces as a headline, not as information.

EXIT CODES -- a counter, not a guard: 0 once it measured (even when the chain count is
0 -- zero closed chains is the measurement, not a defect of the tree), 2 (ABBRUCH) when
it measured nothing: no binary, a stale binary without `--allow-stale`, or an empty
population. Every `gabbro` call runs under FRIST; a hang reads as a failed column, not
as a missing program.
"""
import argparse
import importlib.util
import pathlib
import re
import subprocess
import sys

W = pathlib.Path(__file__).resolve().parent.parent
GRAMMATIK = W / "grammatik" / "Grammatik"

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import korpus  # noqa: E402

_PC_SPEC = importlib.util.spec_from_file_location(
    "pruefe_cformen", W / "instrumente" / "pruefe-cformen.py")
_PC = importlib.util.module_from_spec(_PC_SPEC)
_PC_SPEC.loader.exec_module(_PC)

# A hang looks like "still running", not like a finding.
FRIST = 120

# The generated Lean pins, per program: files whose pasted export / parse theorems the
# Lean kernel re-checks. `Export104.lean` names its source (`beispiele/104-referenz.gab`)
# in its header; a program is pinned exactly when a pin file names it.
PIN_DATEIEN = [GRAMMATIK / "Export104.lean", GRAMMATIK / "Parser" / "Uebersetze.lean"]


def umgebung():
    import os
    env = dict(os.environ)
    env["LC_ALL"] = "C"
    return env


def rufe(binary, args):
    """Run `[binary] + args`, under FRIST. Returns `(ok, stdout)`; a timeout or an
    unreadable launch reads as failure, never as a silent pass."""
    try:
        r = subprocess.run([str(binary)] + args, capture_output=True, text=True,
                           cwd=W, timeout=FRIST, env=umgebung())
    except (OSError, subprocess.TimeoutExpired):
        return False, ""
    return r.returncode == 0, r.stdout


def pin_fuer(datei):
    """The pin files naming `datei` (by its file name), or [] -- "not measured"."""
    try:
        name = datei.name
    except AttributeError:
        name = str(datei)
    gefunden = []
    for pin in PIN_DATEIEN:
        try:
            if name in pin.read_text(encoding="utf-8", errors="replace"):
                gefunden.append(pin)
        except OSError:
            continue
    return gefunden


def t2_vorhanden(binary):
    """Does T2 exist as a per-program check: a CLI surface printing a correspondence
    certificate AND a Lean rechecker consuming it? Both halves are probed, neither is
    guessed: the CLI half by asking the binary, the Lean half by grep over grammatik."""
    cli_ok, cli_out = rufe(binary, ["--help"])
    cli_ok = cli_ok and bool(re.search(r"corr.?cert", cli_out, re.I))
    try:
        lean = "\n".join(p.read_text(encoding="utf-8", errors="replace")
                         for p in GRAMMATIK.glob("*.lean"))
    except OSError:
        lean = ""
    # `Erhaltung.lean` defines the `CorrCert` SHAPE (`structure CorrCert`, `corrClosed`
    # over a `ruled` predicate) -- data, not a rechecker. A rechecker would be a
    # per-certificate decision procedure the kernel runs; that name does not exist yet.
    lean_ok = bool(re.search(r"^(?:def|theorem)\s+corr(?:cert)?_(?:pruef|check|entscheide)",
                             lean, re.M))
    return cli_ok and lean_ok


def selbsttest():
    """**The speech test, in both directions: what must pass passes, what must fall
    falls.** A sieve nobody has seen fail is a decoration: the planted statements below
    must land in their forms and states, the planted garbage must stay unclassified, and
    the assumption-name check must accept a binder and refuse an absent name.
    """
    unit = _PC.Unit("")
    faelle = [
        ("__asm__ __volatile__(", "stmt:asm", "assumption"),
        ("(*(volatile uint32_t *)(d->basis + 24)) = (uint32_t)x;", "stmt:reg-store",
         "assumption"),
        ("uint32_t _s = (*(volatile uint32_t *)(d->basis + 28));", "stmt:reg-load",
         "assumption"),
        ("Platz * tz = SPEICHER;", "stmt:decl-ptr", "uncovered"),
    ]
    ok = True
    print("== Speech test ==")
    for text, form, zustand in faelle:
        gefunden = _PC.classify_stmt(text, unit, False, None)
        gut = gefunden == form and _PC.form_state(gefunden) == zustand
        ok = ok and gut
        print(f"  {text[:50]:52s} -> {gefunden} / {zustand}: {'yes' if gut else 'NO'}")
    muell = _PC.classify_stmt("??? kein Satz ???;", unit, False, None)
    ok_mu = muell is None
    ok = ok and ok_mu
    print(f"  planted garbage stays unclassified: {'yes' if ok_mu else 'NO'}")
    ok_bind = _PC.assumption_exists("hdev", "(hdev : cWrap w x = y)")
    ok_weg = not _PC.assumption_exists("hdev", "nothing here names it")
    ok = ok and ok_bind and ok_weg
    print(f"  a binder occurrence verifies: {'yes' if ok_bind else 'NO'}")
    print(f"  an absent name falls: {'yes' if ok_weg else 'NO'}")
    return ok


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--binary", default=str(W / "target" / "debug" / "gabbro"))
    ap.add_argument("--allow-stale", action="store_true")
    ap.add_argument("--lean", action="store_true",
                    help="re-check the generated pin files through ./lean-probe")
    args = ap.parse_args()

    if not selbsttest():
        print("ABBRUCH: the speech test fell -- this run measures nothing")
        return 2

    binary = pathlib.Path(args.binary)
    if not binary.exists():
        print(f"ABBRUCH: no binary at {binary} -- build it or pass --binary")
        return 2
    stand = binary.stat().st_mtime
    neuer = sorted(q for q in W.glob("crates/*/src/*.rs") if q.stat().st_mtime > stand)
    if neuer and not args.allow_stale:
        print(f"ABBRUCH: the binary is OLDER than {len(neuer)} source file(s) under "
              f"crates/ (first: {neuer[0].relative_to(W)}) -- it measures another emitter")
        print("  (build it, or pass --allow-stale to measure that binary anyway)")
        return 2
    if neuer:
        print(f"  CAVEAT: binary older than {len(neuer)} crates/ source file(s)")

    dateien = sorted(p for p in (W / "beispiele").glob("*.gab") if korpus.verfolgt(p, W))
    if not dateien:
        print("ABBRUCH: empty population -- no tracked beispiele/*.gab")
        return 2

    # Column (e), once for the whole run: T2 does not exist, so no program passes it.
    t2 = t2_vorhanden(binary)

    # Column (a) with --lean: check each pin file once, not once per program.
    pin_gruen = {}
    if args.lean:
        for pin in PIN_DATEIEN:
            r = subprocess.run([str(W / "lean-probe"), str(pin)],
                               capture_output=True, text=True, cwd=W,
                               timeout=900, env=umgebung())
            pin_gruen[pin] = ("== 0 error(s)" in r.stdout)

    zeilen = []
    for f in dateien:
        # (a) Lean parse: a pin, and (with --lean) a green re-check of the pin file.
        pins = pin_fuer(f)
        if not pins:
            a = ("-", "not measured (no generated pin)")
        elif not args.lean:
            a = ("-", f"pin present ({', '.join(p.name for p in pins)}), "
                      "Lean not re-run (needs --lean)")
        elif all(pin_gruen.get(p, False) for p in pins):
            a = ("pass", f"pin {', '.join(p.name for p in pins)} re-checked green")
        else:
            a = ("FAIL", "pin re-check red")

        # (b) lean-g export.
        ok_g, aus_g = rufe(binary, ["lean-g", str(f)])
        if ok_g and aus_g.strip():
            b = ("pass", "export printed")
        else:
            b = ("FAIL", "export failed")

        # (c) certificate: every body printed means no REFUSED line.
        ok_z, aus_z = rufe(binary, ["certificate", str(f)])
        if not ok_z:
            c = ("FAIL", "certificate failed (checker errors?)")
        else:
            zurueck = aus_z.count("REFUSED")
            ruempfe = aus_z.count(" term:\n")
            if zurueck:
                c = ("FAIL", f"{zurueck} refused bodie(s), {ruempfe} printed")
            else:
                c = ("pass", f"{ruempfe} bodie(s) printed, none refused")

        # (d) C-form states over the emitted C.
        ok_e, aus_e = rufe(binary, ["emit", str(f)])
        if not ok_e or not aus_e.strip():
            d = ("-", "not measured (emitter refused)")
        else:
            src = _PC.strip_comments(aus_e)
            unit = _PC.Unit(src)
            formen = set()
            unklass = 0
            for _fname, kanal, zeilen_c in unit.bodies:
                zellen = set()
                prev = None
                for ln in zeilen_c:
                    for s in _PC.split_statements(ln):
                        form = _PC.classify_stmt(s, unit, kanal, prev)
                        prev = form
                        if form is None:
                            unklass += 1
                            continue
                        if form != "brace":
                            formen.add(form)
                        if form == "stmt:decl-cell":
                            m = re.match(r"^\S+ (" + _PC.IDENT + r");$", s)
                            if m:
                                zellen.add(m.group(1))
                        for ex in set(_PC.classify_exprs(
                                _PC.expression_part(s, form), unit, zellen, form)):
                            formen.add(ex)
            dritt = sorted(f_ for f_ in formen if _PC.form_state(f_) == "uncovered")
            if unklass or dritt:
                d = ("FAIL", f"{unklass} unclassified, "
                              f"without semantics: {', '.join(dritt) or 'none'}")
            else:
                n_asm = sorted(f_ for f_ in formen if _PC.form_state(f_) == "assumption")
                d = ("pass", f"{len(formen)} forms lemma/assumption"
                              + (f" (assumption: {', '.join(n_asm)})" if n_asm else ""))

        # (e) correspondence: 0 for every program until T2 exists.
        e = ("pass", "certificate checked") if t2 else ("0", "T2 does not exist")

        zeilen.append((f.name, a, b, c, d, e))

    print(f"zaehle-kette: {len(zeilen)} tracked programs in beispiele/*.gab, binary {binary}")
    print("  sieve: (a) Lean parse [pin]  (b) lean-g  (c) certificate  (d) C forms  (e) corrcert")
    for name, a, b, c, d, e in zeilen:
        marken = []
        for col in (a, b, c, d, e):
            marken.append({"pass": "Y", "FAIL": "F", "-": ".", "0": "0"}[col[0]])
        print(f"  [{''.join(marken)}] {name}")
        for tag, col in zip("abcde", (a, b, c, d, e)):
            if col[0] != "pass":
                print(f"        ({tag}) {col[0]}: {col[1]}")
    n_b = sum(1 for z in zeilen if z[2][0] == "pass")
    n_c = sum(1 for z in zeilen if z[3][0] == "pass")
    n_d = sum(1 for z in zeilen if z[4][0] == "pass")
    n_a = sum(1 for z in zeilen if z[1][0] == "pass")
    n_e = sum(1 for z in zeilen if z[5][0] == "pass")
    kette = sum(1 for z in zeilen if all(col[0] == "pass" for col in z[1:]))
    print(f"\n  sieve totals: (a) {n_a}  (b) {n_b}  (c) {n_c}  (d) {n_d}  (e) {n_e} "
          f"of {len(zeilen)}")
    print(f"== CHAIN COUNT: {kette} of {len(zeilen)} programs pass every checked sieve "
          f"(unmeasured counts as not passed) ==")
    return 0


if __name__ == "__main__":
    sys.exit(main())
