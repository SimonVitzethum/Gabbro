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
  5. The bridge (`bruecke/`): every duty file its `Duty` library imports equals what
     `gabbro pflichten --lean` prints for its unit, `lake build` there is green, and every
     `#print axioms` of a bridge theorem names exactly `propext`, `Classical.choice`, `Quot.sound`.

Exit 0 green, 1 red, 2 nothing measured."""
import os, pathlib, re, subprocess, sys

W = pathlib.Path(__file__).resolve().parent.parent
P = W / "programmlogik"
B = W / "bruecke"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
ENV = {**os.environ, "LC_ALL": "C"}
ENV.pop("ELAN_TOOLCHAIN", None)
# proof file -> the unit it is held against
EINHEITEN = {
    "Duty0120TaggedConstruction": "beispiele/0120-tagged-construction.gab",
    "Duty0124TwoThreadsPrivate": "beispiele/0124-two-threads-private.gab",
    "Duty0151WordPoolDiscipline": "beispiele/0151-word-pool-discipline.gab",
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


def duty_name(datei):
    """`crate::lean::module_name`: `Duty` and the file stem in upper camel case."""
    s, gross = "Duty", True
    for ch in pathlib.Path(datei).stem:
        if ch.isascii() and ch.isalnum():
            s += ch.upper() if gross else ch; gross = False
        else:
            gross = True
    return s


def stufe_bruecke():
    g = W / "target/debug/gabbro"
    if not B.is_dir() or not g.is_file():
        print("  5 bruecke:  NICHT GEMESSEN (bruecke/ oder target/debug/gabbro fehlt)"); return None
    wurzeln = re.findall(r'"Duty\.(\w+)"', (B / "lakefile.toml").read_text(encoding="utf-8"))
    einheiten = {duty_name(f.name): f"beispiele/{f.name}" for f in (W / "beispiele").glob("*.gab")}
    abweichend = []
    for name in wurzeln:
        datei = P / "Duty" / f"{name}.lean"
        q = subprocess.run([str(g), "pflichten", "--lean", einheiten.get(name, "?")], cwd=W, env=ENV,
                           capture_output=True, text=True, timeout=600)
        if q.returncode != 0 or not datei.is_file() or datei.read_text(encoding="utf-8") != q.stdout:
            abweichend.append(name)
    p = subprocess.run(["lake", "build"], cwd=B, env=ENV, capture_output=True, text=True, timeout=3600)
    aus = p.stdout + p.stderr
    jobs = re.findall(r"Build completed successfully \((\d+) jobs\)", aus)
    saetze = re.findall(r"Bruecke/\S+: '([^']+)' depends on axioms: \[([^\]]*)\]", aus)
    fremd = [n for n, ax in saetze if set(a.strip() for a in ax.split(",")) != STANDARD]
    ok = p.returncode == 0 and bool(jobs) and bool(saetze) and not fremd and bool(wurzeln) and not abweichend
    print(f"  5 bruecke:  {'ok' if ok else 'ROT'} ({jobs[-1] + ' Jobs' if jobs else 'kein Abschluss'}, "
          f"{len(saetze)} Saetze geprueft, {len(fremd)} mit anderen Axiomen, "
          f"{len(wurzeln) - len(abweichend)} von {len(wurzeln)} Duty-Dateien gleich dem Drucker)")
    for x in (fremd + abweichend)[:10]: print("     ", x)
    return ok


def main():
    if not P.is_dir(): print("ABBRUCH: programmlogik/ fehlt -- nichts gemessen"); return 2
    print("== Wächter 4: GabbroV ==")
    erg = [stufe_bau(), stufe_sorry(), stufe_prove(), stufe_tor(), stufe_bruecke()]
    if False in erg: print("== GABBROV: ROT =="); return 1
    if None in erg: print("== GABBROV: TEILMESSUNG =="); return 2
    print("== GABBROV: GRUEN =="); return 0


if __name__ == "__main__":
    sys.exit(main())
