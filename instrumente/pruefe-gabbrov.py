#!/usr/bin/env python3
"""Guardian 2 of 2 -- GabbroV (source -> Lean `Body` model, duty channel, `programmlogik/`).

    ./instrumente/pruefe-gabbrov.py

Stages:
  1. `lake build` in `programmlogik/`: the body model, the bridge, the coverage theorem and the
     duty libraries build, and no theorem depends on `sorryAx`.
  2. The person's proofs (`programmlogik/Proofs/`) and the GabbroV files (`programmlogik/gabbrov/`)
     carry no `sorry`, `admit`, `native_decide` and no `axiom`.
  3. The bridge (`bruecke/`): the tracked duty files its `Duty` library imports exist, `lake build`
     there is green, and every `#print axioms` of a bridge theorem names exactly `propext`,
     `Classical.choice`, `Quot.sound`.

The duty files under `programmlogik/Duty/` were printed by the removed Rust tool; they are tracked
inputs now. A verified generator in Lean is owed (TODO.md).

Exit 0 green, 1 red, 2 nothing measured."""
import os, pathlib, re, subprocess, sys

W = pathlib.Path(__file__).resolve().parent.parent
P = W / "programmlogik"
B = W / "bruecke"
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


def stufe_bruecke():
    if not B.is_dir():
        print("  3 bruecke:  NICHT GEMESSEN (bruecke/ fehlt)"); return None
    wurzeln = re.findall(r'"Duty\.(\w+)"', (B / "lakefile.toml").read_text(encoding="utf-8"))
    fehlend = [n for n in wurzeln if not (P / "Duty" / f"{n}.lean").is_file()]
    p = subprocess.run(["lake", "build"], cwd=B, env=ENV, capture_output=True, text=True, timeout=3600)
    aus = p.stdout + p.stderr
    jobs = re.findall(r"Build completed successfully \((\d+) jobs\)", aus)
    saetze = re.findall(r"Bruecke/\S+: '([^']+)' depends on axioms: \[([^\]]*)\]", aus)
    fremd = [n for n, ax in saetze if set(a.strip() for a in ax.split(",")) != STANDARD]
    ok = p.returncode == 0 and bool(jobs) and bool(saetze) and not fremd and bool(wurzeln) and not fehlend
    print(f"  3 bruecke:  {'ok' if ok else 'ROT'} ({jobs[-1] + ' Jobs' if jobs else 'kein Abschluss'}, "
          f"{len(saetze)} Saetze geprueft, {len(fremd)} mit anderen Axiomen, "
          f"{len(wurzeln) - len(fehlend)} von {len(wurzeln)} Duty-Dateien vorhanden)")
    for x in (fremd + fehlend)[:10]: print("     ", x)
    return ok


def main():
    if not P.is_dir(): print("ABBRUCH: programmlogik/ fehlt -- nichts gemessen"); return 2
    print("== Wächter 2: GabbroV ==")
    erg = [stufe_bau(), stufe_sorry(), stufe_bruecke()]
    if False in erg: print("== GABBROV: ROT =="); return 1
    if None in erg: print("== GABBROV: TEILMESSUNG =="); return 2
    print("== GABBROV: GRUEN =="); return 0


if __name__ == "__main__":
    sys.exit(main())
