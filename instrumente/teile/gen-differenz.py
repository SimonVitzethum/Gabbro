#!/usr/bin/env python3
"""Generated-program differential (a stage of `pruefe-llvm.py`, not a guardian of its own).

    instrumente/teile/gen-differenz.py [--n 3] [--seed 1] [--ziel 5] [--versuche 150] [--out DIR] [--keep]

The generator (`grammatik/Grammatik/Gen/`, run with `lake env lean --run`) builds programs the Lean model
ACCEPTS and writes each with the value the model's semantics gives `main` (`gNNN.gab`, `gNNN.exp`; nothing
is committed, the files live under `.tmp/gen-differenz` or `--out`). For each program this stage asks:

  1. the Rust checker (`gabbro check`) must ACCEPT it -- a refusal is a checker INCOMPLETENESS
     (model accepts, checker refuses);
  2. `gabbro llvm --target=x86_64|aarch64` must lower it -- a `Y1xx` refusal is a coverage gap;
  3. the binary, run natively (x86_64) and under qemu (aarch64), must return `expected mod 256` --
     anything else is a COMPILER BUG (highest priority).

Outcome classes: ok, checker-refusal (with codes), compiler-refusal (with codes), mismatch.
A checker refusal and a refusal by the compiler are reported with a SHRUNK example (statement lines are
deleted while the same first code remains). Exit 0 when no mismatch and the tools ran, 1 on a mismatch,
2 when something could not be measured. Mismatches and counts are printed; findings are not failures
of the stage except a mismatch."""
import argparse, collections, os, pathlib, re, shutil, subprocess, sys

W = pathlib.Path(__file__).resolve().parent.parent.parent
GABBRO = W / "target/debug/gabbro"
ENV = {**os.environ, "LC_ALL": "C"}
CODE = re.compile(r"(?:error|hint)?:?\s*\[([A-Z]\d{3})\]")


def sh(cmd, timeout=300, cwd=None):
    return subprocess.run(cmd, capture_output=True, text=True, timeout=timeout, cwd=cwd, env=ENV)


def erzeuge(out, seed, n, ziel, versuche):
    env = {k: v for k, v in ENV.items() if k != "ELAN_TOOLCHAIN"}
    # the generator is interpreted from the built modules: bring them up to date first (a no-op when current)
    b = subprocess.run(["lake", "build", "Grammatik.Gen.Bau"], cwd=W / "grammatik", env=env,
                       capture_output=True, text=True, timeout=7200)
    if b.returncode != 0:
        return b
    p = subprocess.run(["lake", "env", "lean", "--run", "Grammatik/Gen/Main.lean", str(out), str(seed),
                        str(n), str(ziel), str(versuche)], cwd=W / "grammatik", env=env,
                       capture_output=True, text=True, timeout=7200)
    return p


def pruefer(datei):
    """None when accepted, else the sorted list of error codes."""
    p = sh([str(GABBRO), "check", str(datei)])
    if p.returncode == 0:
        return None
    return sorted(set(re.findall(r"error: \[([A-Z]\d{3})\]", p.stderr + p.stdout))) or ["?"]


def uebersetze(datei, ziel, tls):
    """(None, rc) when the binary ran; (code, None) when the compiler refused or a tool failed."""
    name = pathlib.Path(datei).stem
    ll, bc, o, exe = (tls / f"{name}-{ziel}{s}" for s in (".ll", ".bc", ".o", ""))
    p = sh([str(GABBRO), "llvm", f"--target={ziel}", str(datei)])
    if p.returncode != 0:
        m = re.findall(r"\[(Y\d{3})\]", p.stderr)
        return (m[0] if m else "llvm:" + p.stderr.strip()[:60]), None
    ll.write_text(p.stdout)
    triple = f"{ziel}-unknown-linux-gnu"
    for cmd in (["opt", "-O3", str(ll), "-o", str(bc)],
                ["llc", "-O3", f"-mtriple={triple}", "-filetype=obj", str(bc), "-o", str(o)],
                ["ld.lld", "-static", "-e", "_start", "-o", str(exe), str(o)]):
        q = sh(cmd)
        if q.returncode != 0:
            return f"{cmd[0]}:" + q.stderr.strip()[:60], None
    lauf = [str(exe)] if ziel == "x86_64" else ["qemu-aarch64", str(exe)]
    try:
        r = sh(lauf, timeout=60)
    except subprocess.TimeoutExpired:
        return "timeout", None
    return None, r.returncode


TYPEN = {"Expr", "Stmt", "Block", "Endblock", "Arms", "GrundArms", "Args", "Ty", "ErgExpr", "NutzlastExpr"}


def abdeckung(texte):
    """Coverage keyed by the model-coverage register (`dokumente/llvm-modelldeckung.tsv`): which constructor
    members of the term types appear in the G terms the exporter writes for the generated programs
    (`gabbro lean-g`). A member is matched by its `.name` token, so a name two types share (`ret`, `bind`,
    `cons`) counts for each of them: the figure is an upper bound for those."""
    zeilen = (W / "dokumente/llvm-modelldeckung.tsv").read_text().splitlines()
    mitglieder = [z.split("\t") for z in zeilen if z and not z.startswith("#")]
    mitglieder = [(m[0], m[1]) for m in mitglieder if m[0].split(".")[0] in TYPEN]
    text = "".join(texte)
    def da(m):
        t, n = m.split(".")
        return re.search(r"(?<![A-Za-z0-9_])\." + re.escape(n) + r"\b|\b" + t + r"\." + re.escape(n) + r"\b", text)
    erreicht = [m for m, _ in mitglieder if da(m)]
    return mitglieder, erreicht


def schrumpfe(text, hat_befund):
    """Delete statement lines (the generator puts one per line) while `hat_befund` stays true."""
    zeilen = text.split("\n")
    if len(zeilen) < 6:
        return text
    kopf, rumpf, fuss = zeilen[:1], zeilen[1:-4], zeilen[-4:]
    wieder = True
    while wieder and rumpf:
        wieder = False
        for i in range(len(rumpf)):
            versuch = rumpf[:i] + rumpf[i + 1:]
            if hat_befund("\n".join(kopf + versuch + fuss)):
                rumpf, wieder = versuch, True
                break
    return "\n".join(kopf + rumpf + fuss)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=3)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--ziel", type=int, default=5)
    ap.add_argument("--versuche", type=int, default=150)
    ap.add_argument("--out", default=str(W / ".tmp/gen-differenz"))
    ap.add_argument("--keep", action="store_true", help="reuse the files already in --out")
    a = ap.parse_args()
    out = pathlib.Path(a.out).resolve()
    fehlt = [t for t in ("opt", "llc", "ld.lld", "qemu-aarch64", "lake") if not shutil.which(t)]
    if fehlt or not GABBRO.is_file():
        print(f"  gen: NICHT GEMESSEN (fehlt: {fehlt or ''} {'' if GABBRO.is_file() else 'target/debug/gabbro'})")
        return 2
    if not a.keep:
        shutil.rmtree(out, ignore_errors=True)
        p = erzeuge(out, a.seed, a.n, a.ziel, a.versuche)
        if p.returncode != 0:
            print("  gen: NICHT GEMESSEN (Erzeuger:", (p.stderr or p.stdout)[-300:], ")")
            return 2
        (out / "erzeuger.txt").write_text(p.stdout)
        print("\n".join(l for l in p.stdout.splitlines() if l.startswith(("programs", "constructors in no"))))
    tls = out / "bin"
    tls.mkdir(parents=True, exist_ok=True)
    klassen = collections.Counter()
    pcodes, ycodes = collections.Counter(), collections.Counter()
    beispiele, abweichungen, gtexte = {}, [], []
    lcodes = collections.Counter()
    dateien = sorted(out.glob("g*.gab"))
    for datei in dateien:
        soll = int(datei.with_suffix(".exp").read_text().strip()) % 256
        codes = pruefer(datei)
        if codes:
            klassen["checker-refusal"] += 1
            pcodes.update(codes)
            def noch(t, c=codes[0]):
                tmp = tls / "schrumpf.gab"
                tmp.write_text(t)
                return pruefer(tmp) and pruefer(tmp)[0] == c
            beispiele.setdefault(("P", codes[0]), schrumpfe(datei.read_text(), noch))
            continue
        lg = sh([str(GABBRO), "lean-g", str(datei)])
        if lg.returncode == 0:
            gtexte.append(lg.stdout)
        else:
            klassen["exporter-refusal"] += 1
            lc = re.findall(r"\[(LG\d+)\]", lg.stderr) or ["?"]
            lcodes.update(lc)

            def lnoch(t, c=lc[0]):
                tmp = tls / "schrumpf.gab"
                tmp.write_text(t)
                q = sh([str(GABBRO), "lean-g", str(tmp)])
                return q.returncode != 0 and f"[{c}]" in q.stderr
            beispiele.setdefault(("LG", lc[0]), schrumpfe(datei.read_text(), lnoch))
        ergebnis = {}
        for ziel in ("x86_64", "aarch64"):
            ergebnis[ziel] = uebersetze(datei, ziel, tls)
        refus = [(z, c) for z, (c, _) in ergebnis.items() if c]
        if refus:
            klassen["compiler-refusal"] += 1
            for z, c in refus:
                ycodes[c] += 1
                beispiele.setdefault(("Y", c), datei.read_text())
            continue
        rcs = {z: r for z, (_, r) in ergebnis.items()}
        if all(r == soll for r in rcs.values()):
            klassen["ok"] += 1
        else:
            klassen["mismatch"] += 1
            abweichungen.append((datei.name, soll, rcs))
    print(f"  gen: {len(dateien)} Programme; " + ", ".join(f"{k}={v}" for k, v in sorted(klassen.items())))
    if pcodes:
        print("  gen: Pruefer-Absagen (Unvollstaendigkeit):", dict(pcodes))
    if lcodes:
        print("  gen: Exporter-Absagen (`gabbro lean-g` verweigert ein vom Pruefer angenommenes Programm):", dict(lcodes))
    if ycodes:
        print("  gen: Erzeuger-Absagen (Abdeckungsluecke):", dict(ycodes))
    if dateien:
        mitglieder, erreicht = abdeckung(gtexte)
        offen = [m for m, _ in mitglieder if m not in erreicht]
        print(f"  gen: Registerglieder (Expr/Stmt/Block/Endblock/Arms/Args/Ty) in erzeugten G-Termen erreicht: "
              f"{len(erreicht)} von {len(mitglieder)}")
        if offen:
            print("  gen: nicht erreicht:", ", ".join(offen))
    for (art, code), text in beispiele.items():
        print(f"  --- kleinstes Beispiel {art}/{code} ---\n" + text.rstrip())
    for name, soll, rcs in abweichungen:
        print(f"  gen: ABWEICHUNG {name}: Modell {soll}, Binaerdatei {rcs}")
    return 1 if abweichungen else 0


if __name__ == "__main__":
    sys.exit(main())
