#!/usr/bin/env python3
"""Guardian 1 of 4 -- the Lean model (`grammatik/`).

    ./instrumente/pruefe-lean.py [--ohne-bau]

Stages (each prints what it measured; a stage that cannot run is NOT a pass):
  1. `lake build` of `grammatik/` -- every module builds.
  2. `NachpruefungZiel.lean` -- `gabbro_ziel` (and its siblings) depend on exactly
     `propext`, `Classical.choice`, `Quot.sound`.
  3. No `sorry`, `admit`, `native_decide`, `sorryAx`, `unsafe` in Lean code (comments
     stripped) and no `axiom` outside `teile/kein-sorry-allowlist.txt`.
  4. Layout: no folder holds more than 20 entries (`teile/lean-layout.py --check`).
  5. Certificates, generated on demand (never stored): `cargo test --test zertifikate` writes one
     certificate per exported corpus program to `target/zertifikate/`; each is elaborated with
     `lake env lean` against the built model, so the Lean Bool `Akzeptiert` deciding the exported
     unit and `gabbro_ziel` instantiated on it are checked for every certified program.
  6. Coverage of the register by the program generator (`Gen/Abdeckung/`): `lake build gen-abdeckung`, then the
     native driver generates every program of the family up to the reference bounds and fails (exit 1) on a
     register member that no valid and no single-fault program contains and that is not a declared known gap
     (`bekannteLuecken`), or on a declared gap that is covered (the list is exact).

Exit 0 green, 1 red, 2 nothing measured. `--ohne-bau` skips stage 1 (the other stages read
the existing build state)."""
import os, pathlib, re, subprocess, sys

W = pathlib.Path(__file__).resolve().parent.parent
G = W / "grammatik"
ENV = {**os.environ, "LC_ALL": "C"}
ENV.pop("ELAN_TOOLCHAIN", None)
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
VERBOTEN = re.compile(r"\b(sorry|admit|native_decide|sorryAx|unsafe)\b")
AXIOM = re.compile(r"^\s*axiom\s+([A-Za-z0-9_.']+)", re.M)


def lauf(cmd, cwd, frist):
    try:
        p = subprocess.run(cmd, cwd=cwd, env=ENV, capture_output=True, text=True, timeout=frist)
        return p.returncode, p.stdout + p.stderr
    except subprocess.TimeoutExpired:
        return 124, f"Frist {frist} s ueberschritten"


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
    rc, out = lauf(["lake", "build"], G, 3600)
    jobs = re.findall(r"Build completed successfully \((\d+) jobs\)", out)
    ok = rc == 0 and bool(jobs)
    print(f"  1 bau:     {'ok' if ok else 'ROT'} ({jobs[-1] + ' Jobs' if jobs else out.strip().splitlines()[-1:]})")
    return ok


def stufe_axiome():
    rc, out = lauf(["lake", "env", "lean", "NachpruefungZiel.lean"], G, 900)
    zeilen = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", out)
    ziel = [z for z in zeilen if z[0].endswith(".gabbro_ziel")]
    schlecht = [n for n, a in zeilen if not {x.strip() for x in a.split(",") if x.strip()} <= STANDARD]
    ok = rc == 0 and bool(ziel) and not schlecht
    print(f"  2 axiome:  {'ok' if ok else 'ROT'} ({len(zeilen)} Saetze, gabbro_ziel {'gefunden' if ziel else 'FEHLT'}, "
          f"{len(schlecht)} mit fremden Axiomen{': ' + ', '.join(schlecht) if schlecht else ''})")
    return ok


def stufe_sorry():
    erlaubt = {l.split()[1] for l in (W / "instrumente/teile/kein-sorry-allowlist.txt").read_text().splitlines()
               if l.strip() and not l.startswith("#")}
    n, befunde = 0, []
    for f in sorted(G.rglob("*.lean")):
        if ".lake" in f.parts: continue
        code = ohne_kommentare(f.read_text(encoding="utf-8"))
        n += 1
        for m in VERBOTEN.finditer(code):
            befunde.append(f"{f.relative_to(W)}: {m.group(1)}")
        for m in AXIOM.finditer(code):
            if m.group(1) not in erlaubt: befunde.append(f"{f.relative_to(W)}: axiom {m.group(1)}")
    print(f"  3 sorry:   {'ok' if n and not befunde else 'ROT'} ({n} Dateien, {len(befunde)} Verstoesse)")
    for b in befunde[:10]: print("     ", b)
    return n > 0 and not befunde


def stufe_layout():
    rc, out = lauf([sys.executable, str(W / "instrumente/teile/lean-layout.py"), "--check"], W, 300)
    print(f"  4 layout:  {'ok' if rc == 0 else 'ROT'} ({out.strip().splitlines()[-1] if out.strip() else ''})")
    return rc == 0


def stufe_zertifikate():
    p = subprocess.run(["cargo", "test", "-q", "--test", "zertifikate"], cwd=W, env=ENV,
                       capture_output=True, text=True, timeout=1800)
    if p.returncode != 0:
        print("  5 zertif.: ROT (the generator test failed)\n", (p.stdout + p.stderr)[-800:])
        return False
    dateien = sorted(f for f in (W / "target" / "zertifikate").glob("*.lean"))
    schlecht = []
    for f in dateien:
        rc, out = lauf(["lake", "env", "lean", str(f)], G, 900)
        if rc != 0 or re.search(r"error", out):
            schlecht.append(f"{f.name}: {out.strip().splitlines()[:2]}")
    ok = bool(dateien) and not schlecht
    print(f"  5 zertif.: {'ok' if ok else 'ROT'} ({len(dateien)} Zertifikate elaboriert, {len(schlecht)} gefallen)")
    for b in schlecht[:6]: print("     ", b)
    return ok


ABDECKUNG_GRENZEN = ["7", "7", "5", "7:6:6:4"]   # bodies/skeletons up to 7, one change up to 5; member 7 (registers only): 6/6/4


def stufe_abdeckung():
    rc, out = lauf(["lake", "build", "gen-abdeckung"], G, 3600)
    exe = G / ".lake/build/bin/gen-abdeckung"
    if rc != 0 or not exe.exists():
        print("  6 abdeckung: ROT (the driver does not build)\n", out[-600:])
        return False
    rc, out = lauf([str(exe), str(W / "dokumente/llvm-modelldeckung.tsv"), *ABDECKUNG_GRENZEN], G, 3600)
    zeilen = [z for z in out.splitlines() if z.startswith(("register members", "valid programs", "cells"))]
    print(f"  6 abdeckung: {'ok' if rc == 0 else 'ROT'} ({'; '.join(zeilen)})")
    if rc != 0:
        for z in out.splitlines()[-3:]: print("     ", z[:400])
    return rc == 0


def main():
    if not G.is_dir(): print("ABBRUCH: grammatik/ fehlt -- nichts gemessen"); return 2
    print("== Wächter 1: Lean-Modell ==")
    stufen = ([] if "--ohne-bau" in sys.argv else [stufe_bau]) + [stufe_axiome, stufe_sorry, stufe_layout, stufe_zertifikate, stufe_abdeckung]
    erg = [s() for s in stufen]
    print("== LEAN:", "GRUEN" if all(erg) else "ROT", "==")
    return 0 if all(erg) else 1


if __name__ == "__main__":
    sys.exit(main())
