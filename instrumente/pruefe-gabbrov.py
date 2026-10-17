#!/usr/bin/env python3
"""Guardian 4 of 4 -- GabbroV (source -> Lean `Body` model, duty channel, `programmlogik/`).

    ./instrumente/pruefe-gabbrov.py

Stages:
  1. `lake build` in `programmlogik/`: the body model, the bridge, the coverage theorem and the
     duty libraries build, and no theorem depends on `sorryAx`.
  2. The person's proofs (`programmlogik/Proofs/`) and the GabbroV files (`programmlogik/gabbrov/`)
     carry no `sorry`, `admit`, `native_decide` and no `axiom`.
  3. `gabbro prove` over every unit that has a proof file: GREEN means every generated duty
     statement is closed by the generator or proved by a person, and Lean really checked it.
  4. `cargo test -p gabbro-cli --test beweismessung`: `prove` can never say GREEN without Lean
     having checked something.

Exit 0 green, 1 red, 2 nothing measured. `bruecke/` is NOT measured here: its manifest is
broken (`lake build` there fails on the missing `mathlib` entry), see `TODO.md`."""
import os, pathlib, re, subprocess, sys

W = pathlib.Path(__file__).resolve().parent.parent
P = W / "programmlogik"
ENV = {**os.environ, "LC_ALL": "C"}
ENV.pop("ELAN_TOOLCHAIN", None)
# proof file -> the unit it is held against
EINHEITEN = {
    "DutyProbeTaggedWirdGebaut": "messung/proben/probe-tagged-wird-gebaut.gab",
    "Duty120TaggedConstruction": "beispiele/120-tagged-construction.gab",
    "Duty124TwoThreadsPrivate": "beispiele/124-two-threads-private.gab",
    "Duty151WordPoolDiscipline": "beispiele/151-word-pool-discipline.gab",
}
VERBOTEN = re.compile(r"\b(sorry|admit|native_decide|sorryAx|axiom)\b")


def ohne_kommentare(t):
    out, i, tiefe = [], 0, 0
    while i < len(t):
        if t.startswith("/-", i): tiefe += 1; i += 2
        elif tiefe and t.startswith("-/", i): tiefe -= 1; i += 2
        elif tiefe: i += 1
        elif t.startswith("--", i):
            j = t.find("\n", i); i = len(t) if j < 0 else j
        else: out.append(t[i]); i += 1
    return "".join(out)


def stufe_bau():
    p = subprocess.run(["lake", "build"], cwd=P, env=ENV, capture_output=True, text=True, timeout=3600)
    jobs = re.findall(r"Build completed successfully \((\d+) jobs\)", p.stdout + p.stderr)
    sorry_ax = len(re.findall(r"depends on axioms:[^\n]*sorryAx", p.stdout + p.stderr))
    ok = p.returncode == 0 and bool(jobs) and sorry_ax == 0
    print(f"  1 bau:      {'ok' if ok else 'ROT'} ({jobs[-1] + ' Jobs' if jobs else 'kein Abschluss'}, {sorry_ax} Saetze mit sorryAx)")
    return ok


def stufe_sorry():
    dateien = [f for d in ("Proofs", "gabbrov") for f in sorted((P / d).glob("*.lean"))]
    bad = [f"{f.relative_to(W)}: {m.group(1)}" for f in dateien
           for m in VERBOTEN.finditer(ohne_kommentare(f.read_text(encoding="utf-8")))]
    ok = bool(dateien) and not bad
    print(f"  2 sorry:    {'ok' if ok else 'ROT'} ({len(dateien)} Dateien, {len(bad)} Verstoesse)")
    for b in bad[:10]: print("     ", b)
    return ok


def stufe_prove():
    g = W / "target/debug/gabbro"
    if not g.is_file(): print("  3 prove:    NICHT GEMESSEN (target/debug/gabbro fehlt)"); return None
    gruen = 0
    for name, einheit in EINHEITEN.items():
        p = subprocess.run([str(g), "prove", einheit], cwd=W, env=ENV, capture_output=True, text=True, timeout=1500)
        ok = p.returncode == 0 and re.search(r"GREEN\s+" + re.escape(name), p.stdout) is not None
        gruen += ok
        if not ok: print(f"     {einheit}: rc={p.returncode}\n{p.stdout[-500:]}")
    ok = gruen == len(EINHEITEN)
    print(f"  3 prove:    {'ok' if ok else 'ROT'} ({gruen} von {len(EINHEITEN)} Einheiten GREEN)")
    return ok


def stufe_tor():
    p = subprocess.run(["cargo", "test", "-q", "-p", "gabbro-cli", "--test", "beweismessung", "--no-fail-fast"],
                       cwd=W, env=ENV, capture_output=True, text=True, timeout=1500)
    m = re.findall(r"test result: \w+\. (\d+) passed; (\d+) failed", p.stdout)
    n = sum(int(a) for a, _ in m); rot = sum(int(b) for _, b in m)
    ok = p.returncode == 0 and n > 0 and rot == 0
    print(f"  4 tor:      {'ok' if ok else 'ROT'} ({n} Tests, {rot} gefallen)")
    return ok


def main():
    if not P.is_dir(): print("ABBRUCH: programmlogik/ fehlt -- nichts gemessen"); return 2
    print("== Wächter 4: GabbroV ==")
    erg = [stufe_bau(), stufe_sorry(), stufe_prove(), stufe_tor()]
    if False in erg: print("== GABBROV: ROT =="); return 1
    if None in erg: print("== GABBROV: TEILMESSUNG =="); return 2
    print("== GABBROV: GRUEN =="); return 0


if __name__ == "__main__":
    sys.exit(main())
