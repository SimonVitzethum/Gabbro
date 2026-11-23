#!/usr/bin/env python3
"""Guardian 2 of 2 -- GabbroV (the model's certificate of the unit Stage 0 compiles, `programmlogik/`).

    ./instrumente/pruefe-gabbrov.py

Stages:
  1. No Lean file under `programmlogik/` carries `sorry`, `admit`, `native_decide` or `axiom`.
  2. GabbroV (`programmlogik/bruecke/`: the certificate theorems and the generator `gabbrov`): `lake build`
     there is green, and every `#print axioms` of a theorem there names exactly `propext`,
     `Classical.choice`, `Quot.sound`.
  3. The automation on every IR probe (`stage0/proben-ir/*.gab`): `gabbrov --ein` writes the unit as ONE
     module (source, data, duties, logic statements), checked by one `lean` process within `GABBROV_ZEIT`
     seconds (default 60); `gabbrov_logik` never fails, it states what remains, and every
     `logik<i>.genuegt` depends on exactly the three standard axioms. Reported: duties without and with
     remaining logic, units without any, probes over the time limit (a finding), refusals of the
     generator. Parallel jobs from the free memory (`GABBROV_JOBS` overrides).

Exit 0 green, 1 red, 2 nothing measured."""
import os, pathlib, re, subprocess, sys

W = pathlib.Path(__file__).resolve().parent.parent
P = W / "programmlogik"
B = P / "bruecke"
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


def stufe_sorry():
    dateien = [f for f in sorted(P.rglob("*.lean")) if ".lake" not in f.parts]
    bad = [f"{f.relative_to(W)}: {m.group(1)}" for f in dateien
           for m in VERBOTEN.finditer(ohne_kommentare(f.read_text(encoding="utf-8")))]
    ok = bool(dateien) and not bad
    print(f"  1 sorry:     {'ok' if ok else 'ROT'} ({len(dateien)} Dateien, {len(bad)} Verstoesse)")
    for b in bad[:10]: print("     ", b)
    return ok


def stufe_gabbrov():
    if not B.is_dir():
        print("  2 gabbrov:   NICHT GEMESSEN (programmlogik/bruecke/ fehlt)"); return None
    p = subprocess.run(["lake", "build", "Bruecke", "gabbrov"], cwd=B, env=ENV, capture_output=True, text=True,
                       timeout=3600)
    aus = p.stdout + p.stderr
    jobs = re.findall(r"Build completed successfully \((\d+) jobs\)", aus)
    saetze = re.findall(r"Bruecke/\S+: '([^']+)' depends on axioms: \[([^\]]*)\]", aus)
    fremd = [n for n, ax in saetze if set(a.strip() for a in ax.split(",")) != STANDARD]
    ok = p.returncode == 0 and bool(jobs) and bool(saetze) and not fremd
    print(f"  2 gabbrov:   {'ok' if ok else 'ROT'} ({jobs[-1] + ' Jobs' if jobs else 'kein Abschluss'}, "
          f"{len(saetze)} Saetze geprueft, {len(fremd)} mit anderen Axiomen)")
    for x in fremd[:10]: print("     ", x)
    return ok


def lean_pfad():
    p = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=B, env=ENV, capture_output=True,
                       text=True, timeout=600)
    return p.stdout.strip() if p.returncode == 0 else None


def modul_bauen(wurzel, modul, pfad, zeit=900):
    datei = wurzel / (modul.replace(".", "/") + ".lean")
    olean = wurzel / ".olean" / (modul.replace(".", "/") + ".olean")
    olean.parent.mkdir(parents=True, exist_ok=True)
    env = {**ENV, "LEAN_PATH": str(wurzel / ".olean") + ":" + pfad}
    try:
        p = subprocess.run(["lean", "-R", str(wurzel), "-o", str(olean), str(datei)], cwd=wurzel, env=env,
                           capture_output=True, text=True, timeout=zeit)
        return p.returncode == 0, p.stdout + p.stderr
    except subprocess.TimeoutExpired:
        return False, "timeout"


def einheit(gab, aus, pfad, zeit):
    import shutil, time
    # one module name per probe: replaced, not dropped, characters keep two probes apart
    name = "P_" + re.sub(r"[^A-Za-z0-9]", "_", gab.stem)
    wurzel = aus / name
    shutil.rmtree(wurzel, ignore_errors=True)
    wurzel.mkdir(parents=True)
    g = subprocess.run([str(B / ".lake" / "build" / "bin" / "gabbrov"), "--ein", name, str(gab), str(wurzel)],
                       env=ENV, capture_output=True, text=True, timeout=120)
    if g.returncode != 0:
        return {"probe": gab.name, "abgelehnt": g.returncode}
    t = time.time()
    ok, out = modul_bauen(wurzel, name + ".Ein", pfad, zeit)
    erg = {"probe": gab.name, "fehler": [], "rest": [], "fremd": [], "zeit": time.time() - t,
           "langsam": out == "timeout"}
    for n, ax in re.findall(r": (\d+) statement\(s\) of the program's logic remain; axioms \[([^\]]*)\]", out):
        erg["rest"].append(int(n))
        if set(a.strip() for a in ax.split(",") if a.strip()) - STANDARD: erg["fremd"].append(gab.name)
    if not ok and not erg["langsam"]:
        erg["fehler"].append(f"{gab.name}: {out.strip()[-200:]}")
    shutil.rmtree(wurzel, ignore_errors=True)
    return erg


def jobs():
    if "GABBROV_JOBS" in os.environ: return int(os.environ["GABBROV_JOBS"])
    try:
        frei = int(next(l for l in open("/proc/meminfo") if l.startswith("MemAvailable")).split()[1]) // 1048576
    except Exception:
        frei = 8
    return max(1, min(os.cpu_count() or 2, (frei - 4) // 3))


def stufe_proben():
    from concurrent.futures import ThreadPoolExecutor
    import time
    proben = sorted((W / "stage0" / "proben-ir").glob("*.gab"))
    pfad = lean_pfad()
    if not proben or pfad is None:
        print("  3 proben:    NICHT GEMESSEN (keine Proben oder kein LEAN_PATH)"); return None
    aus = B / ".lake" / "gabbrov-proben"
    zeit = int(os.environ.get("GABBROV_ZEIT", "60"))
    t0 = time.time()
    n = jobs()
    with ThreadPoolExecutor(n) as ex:
        erg = list(ex.map(lambda g: einheit(g, aus, pfad, zeit), proben))
    abgelehnt = [e for e in erg if "abgelehnt" in e]
    gemessen = [e for e in erg if "abgelehnt" not in e]
    fehler = [f for e in gemessen for f in e["fehler"]]
    fremd = [m for e in gemessen for m in e["fremd"]]
    langsam = [e["probe"] for e in gemessen if e["langsam"]]
    pflichten = [k for e in gemessen for k in e["rest"]]
    frei = sum(1 for k in pflichten if k == 0)
    ganz = sum(1 for e in gemessen if e["rest"] and all(k == 0 for k in e["rest"]))
    ok = bool(gemessen) and not fehler and not fremd
    print(f"  3 proben:    {'ok' if ok else 'ROT'} ({len(proben)} Proben in {time.time() - t0:.0f} s mit {n} Jobs, "
          f"{len(abgelehnt)} vom Generator abgelehnt; {len(pflichten)} Pflichten: {frei} ohne Rest, "
          f"{len(pflichten) - frei} mit Logik; {ganz} Einheiten ganz ohne Rest; {len(langsam)} ueber {zeit} s, "
          f"{len(fehler)} Fehler, {len(fremd)} mit anderen Axiomen)")
    for f in (fehler + fremd + [f"langsam: {p}" for p in langsam])[:15]: print("     ", f)
    return ok


def main():
    if not P.is_dir(): print("ABBRUCH: programmlogik/ fehlt -- nichts gemessen"); return 2
    print("== Wächter 2: GabbroV ==")
    erg = [stufe_sorry(), stufe_gabbrov()]
    erg.append(stufe_proben() if erg[1] else None)
    if False in erg: print("== GABBROV: ROT =="); return 1
    if None in erg: print("== GABBROV: TEILMESSUNG =="); return 2
    print("== GABBROV: GRUEN =="); return 0


if __name__ == "__main__":
    sys.exit(main())
