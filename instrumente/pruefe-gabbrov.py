#!/usr/bin/env python3
"""Guardian 2 of 2 -- GabbroV (the model's certificate of the unit Stage 0 compiles, `programmlogik/`).

    ./instrumente/pruefe-gabbrov.py

Stages:
  1. `lake build` in `programmlogik/passlogik/` (the pass logic) is green.
  2. No Lean file under `programmlogik/` carries `sorry`, `admit`, `native_decide` or `axiom`.
  3. GabbroV (`programmlogik/bruecke/`: the certificate theorems and the generator `gabbrov`): `lake build`
     there is green, and every `#print axioms` of a theorem there names exactly `propext`,
     `Classical.choice`, `Quot.sound`.

Exit 0 green, 1 red, 2 nothing measured."""
import os, pathlib, re, subprocess, sys

W = pathlib.Path(__file__).resolve().parent.parent
P = W / "programmlogik"
B = P / "bruecke"
L = P / "passlogik"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
ENV = {**os.environ, "LC_ALL": "C"}
ENV.pop("ELAN_TOOLCHAIN", None)
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


def stufe_passlogik():
    if not L.is_dir():
        print("  1 passlogik: NICHT GEMESSEN (programmlogik/passlogik/ fehlt)"); return None
    p = subprocess.run(["lake", "build"], cwd=L, env=ENV, capture_output=True, text=True, timeout=3600)
    jobs = re.findall(r"Build completed successfully \((\d+) jobs\)", p.stdout + p.stderr)
    ok = p.returncode == 0 and bool(jobs)
    print(f"  1 passlogik: {'ok' if ok else 'ROT'} ({jobs[-1] + ' Jobs' if jobs else 'kein Abschluss'})")
    return ok


def stufe_sorry():
    dateien = [f for f in sorted(P.rglob("*.lean")) if ".lake" not in f.parts]
    bad = [f"{f.relative_to(W)}: {m.group(1)}" for f in dateien
           for m in VERBOTEN.finditer(ohne_kommentare(f.read_text(encoding="utf-8")))]
    ok = bool(dateien) and not bad
    print(f"  2 sorry:     {'ok' if ok else 'ROT'} ({len(dateien)} Dateien, {len(bad)} Verstoesse)")
    for b in bad[:10]: print("     ", b)
    return ok


def stufe_gabbrov():
    if not B.is_dir():
        print("  3 gabbrov:   NICHT GEMESSEN (programmlogik/bruecke/ fehlt)"); return None
    p = subprocess.run(["lake", "build"], cwd=B, env=ENV, capture_output=True, text=True, timeout=3600)
    aus = p.stdout + p.stderr
    jobs = re.findall(r"Build completed successfully \((\d+) jobs\)", aus)
    saetze = re.findall(r"Bruecke/\S+: '([^']+)' depends on axioms: \[([^\]]*)\]", aus)
    fremd = [n for n, ax in saetze if set(a.strip() for a in ax.split(",")) != STANDARD]
    ok = p.returncode == 0 and bool(jobs) and bool(saetze) and not fremd
    print(f"  3 gabbrov:   {'ok' if ok else 'ROT'} ({jobs[-1] + ' Jobs' if jobs else 'kein Abschluss'}, "
          f"{len(saetze)} Saetze geprueft, {len(fremd)} mit anderen Axiomen)")
    for x in fremd[:10]: print("     ", x)
    return ok


def main():
    if not P.is_dir(): print("ABBRUCH: programmlogik/ fehlt -- nichts gemessen"); return 2
    print("== Wächter 2: GabbroV ==")
    erg = [stufe_passlogik(), stufe_sorry(), stufe_gabbrov()]
    if False in erg: print("== GABBROV: ROT =="); return 1
    if None in erg: print("== GABBROV: TEILMESSUNG =="); return 2
    print("== GABBROV: GRUEN =="); return 0


if __name__ == "__main__":
    sys.exit(main())
