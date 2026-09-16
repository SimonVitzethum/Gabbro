#!/usr/bin/env python3
# `pruefe-akzeptiert-diff.py` -- DIFFERENTIAL TEST: the Rust checker computes
# the whole Lean checker Bool (`Akzeptiert`, `grammatik/Grammatik/Zielsatz/
# Akzeptiert.lean`, decided exactly by `akzeptiert_iff`).
#
# For every corpus program `gabbro lean-g` exports, the script compares:
# * the Rust verdict -- ACCEPT iff none of the Akzeptiert-rules fires
#   (`N290`-`N294` footprint, `N300`-`N304` race+starts, `N310`-`N314` answers,
#   `N315`-`N319` the transfer-2 additions), read from `gabbro pruefe`; and
# * the Lean Bool -- `Akzeptiert gP gS gFs gLs gCs gWs` on the EXPORTED
#   program, decided (`by decide`) component by component in a generated
#   Lean file run through `./lean-probe`.
#
# Every disagreement is a FINDING: the script reports it and exits 1 -- it
# never papers it over. Agreement table at the end.
#
# What the comparison covers, and what it does not:
# * Only exported programs are compared. A file the checker refuses (any
#   error) or the export refuses (`LG001`-`LG007`) never reaches the Lean
#   side -- it stands in the SKIP column with its reason, counted, not
#   hidden. The comparison therefore measures ONE direction: Rust accepts
#   ==> Lean accepts. The other direction (Rust refuses ==> Lean refuses)
#   is pinned by the gift probes of each code, not by this script.
# * Starts (`gWs`) are the `concurrent` members of the unit. `entry`/`boot`
#   roots count as starts on the Rust side (`startexklusiv.rs`); a file
#   using them is marked PARTIAL and excluded from the agreement count --
#   the export drops them ("not a G notion"), so the Lean side cannot see
#   them. Today no exportable file uses them.
#
# Exit codes: 0 every compared program agrees; 1 at least one disagreement
# (a finding); 2 infrastructure abort (red, never silent).
#
# Usage:
#   ./instrumente/pruefe-akzeptiert-diff.py [--binaer PATH] [--frist SEC]
#   ./instrumente/pruefe-akzeptiert-diff.py --selbsttest   # two-way speech test
#
# Measured cost: ~12 exported programs, one `lean-probe` run each (seconds
# per file, imports from olean cache).

import argparse
import os
import re
import subprocess
import sys
import tempfile

W = os.path.dirname(os.path.dirname(os.path.realpath(__file__)))
sys.path.insert(0, os.path.join(W, "instrumente"))

# The nine components of `Akzeptiert` (Akzeptiert.lean §3), each with the
# Rust rule that decides it. `None` = decided by construction / vacuous on
# the export fragment (named in the report, never silently dropped).
# Vacuity mechanisms, verified by lane 208 (MUSE-REPORT-208.md):
# * `abg`: `reachB` runs `fs.length` rounds of `erreichSchritt`, which is the
#   fixpoint over `ruftB` -- the same relation `rufM` closes over -- so every
#   computed graph is closed on every export, with no Rust rule involved.
# * `stufen`: `resolve_floors` (`lean_g.rs`, which this lane must not touch)
#   writes each floor as the minimum rank taken anywhere in the function's
#   reachable set, so `mE (bodenM f)` holds per body by construction. `N294`
#   decides a DIFFERENT property (no take at/below a signature-held lock,
#   the `H006` shape, also enforced at export time by `tr_locks`/`LG004`).
# * `sperrOrte`: `S.orte` and `D.braucht`/`D.gbraucht` are built from the one
#   `LockModel.guards` set (`read_lock`), so the implication holds per
#   carrier by construction; unknown `protects` entries refuse at export
#   (`LG005`).
# * `antworten`: no answer site exports -- axioms write `Ax := Empty` and
#   register accesses have no `Reg` form (both `LG...` refusals) -- so the
#   component is `true` on every export; `N310`-`N316` pin the refuse
#   direction, measured by gift probes, not by this script.
KOMPONENTEN = [
    # (short, lean-bool-template, rust-codes)
    ("frag", "programmImFragmentG {P} {fs}",
     ["LG004"]),  # export refuses untranslatable bodies; N293 the indirect leg
    ("abg", "abgAlleB {P} {fs}", None),  # vacuous: fixpoint, see above
    ("fuss", "fussWB {P} {S} {fs} {ws}",
     ["N290", "N291", "N292", "N293", "N294"]),
    ("stufen", "stufenB {P} {fs}", ["N294"]),  # N294 is the held-take rule;
    # stufenB proper is vacuous (minimum-floor construction, see above)
    ("sperrOrte", "sperrOrteB {S} {ls}", None),  # vacuous: one source, see above
    ("wurzeln", "wurzelnB {ws}", ["N302", "N303"]),
    ("einzeln", "einzelnB {ws}", ["N304", "N315"]),
    ("renn", "rennB {P} {fs} {cs} {ws}", ["N300", "N301"]),
    ("antworten", "antwortenB {P} {fs}",
     ["N310", "N311", "N312", "N313", "N314", "N316"]),
    # vacuous on the export (no Ax/Reg sites); refuse direction by gifts
]

# The Rust verdict: ACCEPT iff none of these fires (all are ERROR severity).
# `N317`-`N319` are PHANTOM codes (lane 208): reserved as transfer-2
# additions, implemented nowhere, firing on nothing. They stay in the set
# so the day a rule takes one, the verdict reads it with no script change;
# until then they change no verdict.
AKZEPTIERT_CODES = frozenset([
    "N290", "N291", "N292", "N293", "N294",
    "N300", "N301", "N302", "N303", "N304",
    "N310", "N311", "N312", "N313", "N314",
    "N315", "N316", "N317", "N318", "N319",
])

# Corpus roots walked for exportable programs (the clean half of the
# 870-file corpus of lane 194; gift files carry expected errors and never
# export, so they are not walked).
WURZELN = [
    ("beispiele", "*.gab", False),
    ("messung/proben", "*.gab", False),
    ("messung/fragmente", "*.gab", False),
    ("messung/tor-proben", "*.gab", False),
]


def binaer(pfad=None):
    # One register (zaehle-absagen.py): the binary with the staleness latch.
    # Returns argv (a list); callers append the subcommand.
    if pfad:
        return [pfad]
    import importlib
    befehl = importlib.import_module("zaehle-absagen").binaer()
    if befehl is None:
        print("ABBRUCH: no current gabbro binary (staleness latch)")
        sys.exit(2)
    return befehl


def korpus_dateien():
    import glob
    out = []
    for rel, muster, rekursiv in WURZELN:
        d = os.path.join(W, rel)
        if not os.path.isdir(d):
            continue
        out.extend(sorted(glob.glob(os.path.join(d, muster))))
    return out


def kommentarlos(quelle):
    # Strip `--` line comments so the start regex never reads prose.
    return "\n".join(
        l.split("--")[0] if "--" in l else l for l in quelle.splitlines())


def startet_aus(quelle):
    """Declared starts from the source: `concurrent` members (short names).

    Returns (starts, partial): partial is True where the file uses `entry`
    or `boot` roots, which the export cannot carry.
    """
    text = kommentarlos(quelle)
    starts = []
    for m in re.finditer(r"concurrent\s*\{([^}]*)\}", text):
        for teil in m.group(1).split(","):
            teil = teil.strip()
            if not teil:
                continue
            starts.append(teil.split("::")[-1])
    partial = bool(re.search(r"(?m)^\s*(entry|boot)\b", text))
    return starts, partial


def exportiere(gabbro, datei):
    p = subprocess.run(gabbro + ["lean-g", datei],
                       capture_output=True, text=True, timeout=120)
    return p.returncode, p.stdout, p.stderr


def pruefe_codes(gabbro, datei):
    p = subprocess.run(gabbro + ["pruefe", datei],
                       capture_output=True, text=True, timeout=120)
    codes = set(re.findall(r"(?m)^(error|hint): \[([A-Z0-9]+)\]", p.stdout))
    fehler = {c for (stufe, c) in codes if stufe == "error"}
    return fehler, p.stdout + p.stderr


def parse_export(text):
    """Tables, locks, functions and the namespace out of an export."""
    ns = None
    for m in re.finditer(r"(?m)^namespace (\w+)\s*$", text):
        if m.group(1) != "Gabbro":
            ns = m.group(1)
    def ctors(variant):
        m = re.search(
            r"inductive %s where\n((?:  \| \w+\n)+)" % variant, text)
        if m:
            return re.findall(r"\| (\w+)", m.group(1))
        if re.search(r"abbrev %s := Empty" % variant, text):
            return []
        return None
    tabellen = ctors("GTab")
    sperren = ctors("GLock")
    funktionen = ctors("GFn")
    if ns is None or tabellen is None or sperren is None or funktionen is None:
        return None
    return {"ns": ns, "tabellen": tabellen, "sperren": sperren,
            "funktionen": funktionen}


def sonde(ns, exp, starts):
    """The probe: the export plus one `decide` per component and the whole."""
    q = "Gabbro.Grammatik.%s" % ns
    P, S, fs = "%s.gP" % q, "%s.gS" % q, "%s.gFs" % q
    # Parenthesised throughout: `f [...] : T [...]` would parse the
    # ascription loose and apply the next argument to the ascribed term.
    if exp["sperren"]:
        ls = "([" + ", ".join("%s.GLock.%s" % (q, l) for l in exp["sperren"]) + "])"
    else:
        ls = "([] : List %s.gD.Lock)" % q
    if exp["tabellen"]:
        cs = ("(([" + ", ".join(".inl %s.GTab.%s" % (q, t)
                                for t in exp["tabellen"]) + "])"
              " : List (%s.gD.Tab ⊕ %s.gD.Glob))" % (q, q))
    else:
        cs = "([] : List (%s.gD.Tab ⊕ %s.gD.Glob))" % (q, q)
    if starts:
        ws = "([" + ", ".join("%s.g_%s" % (q, s) for s in starts) + "])"
    else:
        ws = "([] : List %s.gD.Fn)" % q
    env = {"P": P, "S": S, "fs": fs, "ls": ls, "cs": cs, "ws": ws,
           "G": "Gabbro.Grammatik"}
    zeilen = []
    for kurz, schablone, _ in KOMPONENTEN:
        zeilen.append("example : ({G}.%s) = true := by decide -- COMP:%s"
                      % (schablone.format(**env), kurz))
    zeilen.append(
        "example : ({G}.Akzeptiert %s %s %s %s %s %s) = true := by decide -- COMP:gesamt"
        % (P, S, fs, ls, cs, ws))
    return ("\n".join(zeilen) + "\n").format(**env)


def umgebung():
    """`lake` lives in `~/.elan/bin` and is not on a non-interactive PATH --
    the same repair `zaehle-kette.py` carries since 2026-09-15."""
    env = dict(os.environ)
    env["LC_ALL"] = "C"
    zusatz = [os.path.expanduser("~/.elan/bin"), os.path.expanduser("~/.cargo/bin")]
    pfad = env.get("PATH", "")
    env["PATH"] = os.pathsep.join([d for d in zusatz if os.path.isdir(d)] +
                                  ([pfad] if pfad else []))
    return env


def lean_lauf(sondentext, exporttext, frist):
    """Run one probe through `./lean-probe`; return (ok, failing_comps, raw).

    ok=True means Lean evaluated every check to `true` (exit 0, no errors).
    """
    import shutil
    tmp = tempfile.mkdtemp(prefix="akz-diff-")
    try:
        # The export carries its own imports; the Akzeptiert import joins them.
        imp = [l for l in exporttext.splitlines() if l.startswith("import ")]
        if not any("Zielsatz/Akzeptiert" in l for l in imp):
            imp.append("import Grammatik.Zielsatz.Akzeptiert")
        rest = [l for l in exporttext.splitlines()
                if not l.startswith("import ")]
        text = "\n".join(imp) + "\n" + "\n".join(rest) + "\n" + sondentext
        datei = os.path.join(tmp, "sonde.lean")
        with open(datei, "w") as f:
            f.write(text)
        # **`./lean-probe` exists only inside a LANE CLONE** (`neu-agent3` writes
        # it). In master it is absent, and the old code then found neither an
        # error line nor the success line and returned "Lean refuses, component
        # unknown" for EVERY program -- 16 findings with an empty component on
        # 2026-09-15, including `beispiele/104`, whose checker Bool is decided
        # `true` in `GenOblig104.lean`. *A measurement that cannot tell "refused"
        # from "never ran" is the failure class this tree books again and again.*
        # So: use the wrapper where it exists, `lake env lean` otherwise, and if
        # NEITHER can produce a verdict, say NOT MEASURED instead of refusing.
        probe = os.path.join(W, "lean-probe")
        if os.path.exists(probe):
            ruf, cwd = ["bash", probe, datei], W
        else:
            ruf, cwd = ["lake", "env", "lean", datei], os.path.join(W, "grammatik")
        try:
            p = subprocess.run(ruf, capture_output=True, text=True, timeout=frist,
                               cwd=cwd, env=umgebung())
        except subprocess.TimeoutExpired:
            return None, [], "FRIST: the Lean run exceeded %ss" % frist
        except OSError as e:
            return None, [], "NICHT GEMESSEN: %s could not be launched (%s)" % (ruf[0], e)
        fehler = [l for l in (p.stdout + p.stderr).splitlines()
                  if re.search(r"\.lean:\d+:\d+: error", l)]
        # A verdict needs EVIDENCE: either the wrapper's exit line, or a real
        # process exit code from `lake env lean`. Anything else is not a verdict.
        wrapper = "== lean exit code: 0" in p.stdout
        direkt = (os.path.basename(ruf[0]) == "lake")
        if not fehler and not wrapper and not direkt:
            return None, [], "NICHT GEMESSEN: no verdict line\n" + p.stdout + p.stderr
        if not fehler and (wrapper or (direkt and p.returncode == 0)):
            return True, [], p.stdout
        # Map each error line back to its COMP marker.
        comp_zeilen = {}
        for i, l in enumerate(text.splitlines(), start=1):
            m = re.search(r"-- COMP:(\w+)", l)
            if m:
                comp_zeilen[i] = m.group(1)
        gefallen = set()
        for l in fehler:
            m = re.search(r"sonde\.lean:(\d+):", l)
            if m and int(m.group(1)) in comp_zeilen:
                gefallen.add(comp_zeilen[int(m.group(1))])
        return False, sorted(gefallen), p.stdout + p.stderr
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--binaer", default=None)
    ap.add_argument("--frist", type=int, default=600)
    ap.add_argument("--selbsttest", action="store_true")
    args = ap.parse_args()
    gabbro = binaer(args.binaer)

    if args.selbsttest:
        return selbsttest(gabbro, args.frist)

    dateien = korpus_dateien()
    zeilen, befunde, partial, skip = [], [], [], []
    nicht_gemessen = []
    # Coverage denominator (lane 208): per compared program, the static
    # facts that decide whether a component was NON-TRIVIALLY exercised.
    # `wurzeln` needs >= 1 start; `einzeln`, `renn` and the thread legs of
    # `fuss` need >= 2 starts (their Bools are vacuous over fewer);
    # `stufen`/`sperrOrte` need >= 1 lock; `renn` needs >= 1 table.
    # `abg`/`antworten` are vacuous on every export (see KOMPONENTEN).
    deckung = []
    for datei in dateien:
        rel = os.path.relpath(datei, W)
        quelle = open(datei, encoding="utf-8").read()
        rc, export, err = exportiere(gabbro, datei)
        if rc != 0:
            grund = "LG" if "[LG" in err else "checker-error"
            skip.append((rel, grund))
            continue
        parsed = parse_export(export)
        if parsed is None:
            print("ABBRUCH: export of %s parses not" % rel)
            return 2
        starts, is_partial = startet_aus(quelle)
        # Starts must name exported functions; else the comparison is blind.
        unbekannt = [s for s in starts
                     if s not in parsed["funktionen"]]
        if unbekannt:
            print("ABBRUCH: %s starts %s not in export" % (rel, unbekannt))
            return 2
        fehler, _ = pruefe_codes(gabbro, datei)
        rust_ok = not (fehler & AKZEPTIERT_CODES)
        ok, gefallen, raw = lean_lauf(sonde(parsed["ns"], parsed, starts),
                                     export, args.frist)
        if ok is None:
            # **An abort on the first unmeasurable file hides the rest.** Book it,
            # keep going, and let the run end RED with every number it does have
            # (the `zaehle-kette.py` repair of 2026-09-15, same class).
            nicht_gemessen.append((rel, raw.splitlines()[0] if raw else "(no reason)"))
            continue
        if is_partial:
            partial.append(rel)
            status = "PARTIAL"
        elif rust_ok == ok:
            status = "agree"
        else:
            status = "FINDING"
            befunde.append((rel, rust_ok, gefallen))
        zeilen.append((rel, "rust=%s" % ("accept" if rust_ok else "refuse"),
                       "lean=%s" % ("accept" if ok else
                                    ("refuse@" + ",".join(gefallen)
                                     if gefallen else "refuse")),
                       status))
        if not is_partial:
            deckung.append((rel, len(starts), len(parsed["sperren"]),
                            len(parsed["tabellen"]), len(parsed["funktionen"])))
    print("| file | Rust | Lean | verdict |")
    print("|---|---|---|---|")
    for rel, r, l, s in zeilen:
        print("| %s | %s | %s | %s |" % (rel, r, l, s))
    print("compared=%d skip=%d partial=%d findings=%d not-measured=%d"
          % (len(zeilen), len(skip), len(partial), len(befunde), len(nicht_gemessen)))
    # The coverage table: how many compared programs exercise each
    # component NON-TRIVIALLY. A "0 findings" over a denominator that never
    # reaches a component measures nothing about it -- this table says
    # which components the denominator reaches. (PARTIAL files excluded:
    # their Lean side drops the entry/boot roots, so no component verdict
    # on them is comparable.)
    n = len(deckung)
    mit_start = sum(1 for (_, s, _, _, _) in deckung if s >= 1)
    mit_paar = sum(1 for (_, s, _, _, _) in deckung if s >= 2)
    mit_sperre = sum(1 for (_, _, l, _, _) in deckung if l >= 1)
    mit_tabelle = sum(1 for (_, _, _, t, _) in deckung if t >= 1)
    print("coverage: of %d comparable programs," % n)
    print("coverage: wurzeln(>=1 start): %d | einzeln/renn/fuss-thread-legs(>=2 starts): %d | "
          "stufen/sperrOrte(>=1 lock): %d | renn(>=1 table): %d"
          % (mit_start, mit_paar, mit_sperre, mit_tabelle))
    print("coverage: abg/antworten vacuous on every export (fixpoint / no Ax-Reg sites); "
          "their refuse direction is pinned by gift probes, not here")
    for rel, s, l, t, f in deckung:
        print("deckt: %s (starts=%d locks=%d tables=%d fns=%d)" % (rel, s, l, t, f))
    for rel, grund in skip:
        print("skip: %s (%s)" % (rel, grund))
    for rel in partial:
        print("partial (entry/boot roots): %s" % rel)
    for rel, rust_ok, gefallen in befunde:
        print("FINDING: %s rust=%s lean-refuses@%s -- report it, never paper it over"
              % (rel, "accept" if rust_ok else "refuse", ",".join(gefallen)))
    for rel, grund in nicht_gemessen:
        print("BEFUND: %s was NOT measured -- %s" % (rel, grund))
    if nicht_gemessen:
        print("== RED: %d program(s) could not be measured -- a run that cannot tell "
              "'refused' from 'never ran' measures nothing about them ==" % len(nicht_gemessen))
        return 2
    return 1 if befunde else 0


def selbsttest(gabbro, frist):
    """Two-way speech test: 104 must agree (positive); a doubled start must
    refuse at `einzeln` (negative) -- the error-to-component map is read."""
    datei = os.path.join(W, "beispiele/104-referenz.gab")
    rc, export, err = exportiere(gabbro, datei)
    assert rc == 0, "104 must export: %s" % err
    parsed = parse_export(export)
    assert parsed, "104 export parses"
    ok, gefallen, raw = lean_lauf(sonde(parsed["ns"], parsed, []),
                                 export, frist)
    assert ok, "104 must agree: %s" % raw[-2000:]
    print("selbsttest positiv: 104 agree")
    # Negative: every function as its own double -- `einzelnB` must fall.
    fns = parsed["funktionen"]
    starts = [fns[0], fns[0]] if fns else []
    ok2, gefallen2, raw2 = lean_lauf(sonde(parsed["ns"], parsed, starts),
                                    export, frist)
    assert not ok2 and "einzeln" in gefallen2, \
        "doubled start must refuse at einzeln: %s / %s" % (gefallen2,
                                                           raw2[-2000:])
    print("selbsttest negativ: doubled start refuses at einzeln")
    print("SELBSTTEST: ok (both directions)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
