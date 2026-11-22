#!/usr/bin/env python3
"""Guardian 2 of 2 -- GabbroV (the model's certificate of the unit Stage 0 compiles, `programmlogik/`).

    ./instrumente/pruefe-gabbrov.py

Stages:
  1. `lake build` in `programmlogik/passlogik/` (the pass logic) is green.
  2. No Lean file under `programmlogik/` carries `sorry`, `admit`, `native_decide` or `axiom`.
  3. GabbroV (`programmlogik/bruecke/`: the certificate theorems and the generator `gabbrov`): `lake build`
     there is green, and every `#print axioms` of a theorem there names exactly `propext`,
     `Classical.choice`, `Quot.sound`.
  4. The automation on every IR probe (`stage0/proben-ir/*.gab`): `gabbrov` writes the unit; its
     modules up to `Logik/F<i>` compile (`gabbrov_logik` never fails, it states what remains), and every
     `logik<i>.genuegt` depends on exactly the three standard axioms. Where nothing remains for any
     function, the whole unit (`nutzerBild`) compiles too. Reported: duties without remaining logic,
     duties with remaining logic, units with `nutzerBild` proved; refusals of the generator are counted.
     Parallel jobs: `GABBROV_JOBS` (default 4).

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


def einheit(gab, aus, pfad):
    import shutil
    name = "P" + re.sub(r"[^A-Za-z0-9]", "", gab.stem)
    wurzel = aus / name
    shutil.rmtree(wurzel, ignore_errors=True)
    wurzel.mkdir(parents=True)
    g = subprocess.run([str(B / ".lake" / "build" / "bin" / "gabbrov"), name, str(gab), str(wurzel)],
                       env=ENV, capture_output=True, text=True, timeout=600)
    if g.returncode != 0:
        return {"probe": gab.name, "abgelehnt": g.returncode}
    module = sorted(str(f.relative_to(wurzel))[:-5].replace("/", ".") for f in wurzel.rglob("*.lean"))
    rang = lambda m: (0 if ".Quelle" in m else 1 if ".Daten." in m else 2 if m.endswith(".Daten") else
                      3 if ".Pflicht." in m else 4 if ".Logik." in m else 5 if ".Beweis." in m else
                      6 if ".Sammlung." in m else 8 if m.endswith(".Pruefung") else 7)
    module.sort(key=rang)
    erg = {"probe": gab.name, "fehler": [], "rest": [], "fremd": [], "bild": False}
    for m in module:
        if rang(m) >= 5: break
        ok, out = modul_bauen(wurzel, m, pfad)
        if not ok:
            erg["fehler"].append(f"{m}: {out.strip()[-200:]}"); return erg
        for n, ax in re.findall(r": (\d+) statement\(s\) of the program's logic remain; axioms \[([^\]]*)\]", out):
            erg["rest"].append(int(n))
            if set(a.strip() for a in ax.split(",") if a.strip()) - STANDARD: erg["fremd"].append(m)
    if erg["rest"] and all(n == 0 for n in erg["rest"]):
        alle = True
        for m in module:
            if rang(m) in (5, 6, 7):
                ok, out = modul_bauen(wurzel, m, pfad)
                if not ok: alle = False; erg["fehler"].append(f"{m}: {out.strip()[-200:]}"); break
        erg["bild"] = alle
    return erg


def stufe_proben():
    from concurrent.futures import ThreadPoolExecutor
    proben = sorted((W / "stage0" / "proben-ir").glob("*.gab"))
    pfad = lean_pfad()
    if not proben or pfad is None:
        print("  4 proben:    NICHT GEMESSEN (keine Proben oder kein LEAN_PATH)"); return None
    aus = B / ".lake" / "gabbrov-proben"
    with ThreadPoolExecutor(int(os.environ.get("GABBROV_JOBS", "4"))) as ex:
        erg = list(ex.map(lambda g: einheit(g, aus, pfad), proben))
    abgelehnt = [e for e in erg if "abgelehnt" in e]
    gemessen = [e for e in erg if "abgelehnt" not in e]
    fehler = [f for e in gemessen for f in e["fehler"]]
    fremd = [m for e in gemessen for m in e["fremd"]]
    pflichten = [n for e in gemessen for n in e["rest"]]
    frei = sum(1 for n in pflichten if n == 0)
    bild = sum(1 for e in gemessen if e["bild"])
    ok = bool(gemessen) and not fehler and not fremd
    print(f"  4 proben:    {'ok' if ok else 'ROT'} ({len(proben)} Proben, {len(abgelehnt)} vom Generator abgelehnt; "
          f"{len(pflichten)} Pflichten: {frei} ohne Rest, {len(pflichten) - frei} mit Logik; "
          f"nutzerBild bewiesen in {bild} Einheiten; {len(fehler)} Fehler, {len(fremd)} mit anderen Axiomen)")
    for f in (fehler + fremd)[:10]: print("     ", f)
    return ok


def main():
    if not P.is_dir(): print("ABBRUCH: programmlogik/ fehlt -- nichts gemessen"); return 2
    print("== Wächter 2: GabbroV ==")
    erg = [stufe_passlogik(), stufe_sorry(), stufe_gabbrov()]
    erg.append(stufe_proben() if erg[2] else None)
    if False in erg: print("== GABBROV: ROT =="); return 1
    if None in erg: print("== GABBROV: TEILMESSUNG =="); return 2
    print("== GABBROV: GRUEN =="); return 0


if __name__ == "__main__":
    sys.exit(main())
