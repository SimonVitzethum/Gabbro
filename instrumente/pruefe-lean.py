#!/usr/bin/env python3
"""Guardian 1 of 4 -- the Lean model (`grammatik/`), the stage-0 compiler (`stage0/`) and the runner (`runner/`).

    ./instrumente/pruefe-lean.py [--stufe N[,M...]] [--seriell | --parallel] [--ohne-bau]

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
  7. Stage 0 (`stage0/`, PLAN-SELF-HOSTING.md §2): `lake build` of the package (library and the executable
     `stage0`); stage 3 covers its Lean files too. Then every probe `stage0/proben/NAME.gab` runs through the
     compiler to IR, then through the assembly runner on `NAME.ein` (written after `NAME.warte` seconds when
     that file exists); the runner must print exactly `NAME.aus` with exit code 0.
     `stage0/Nachpruefung.lean`: the lowering's theorems (`bild_ok_u`, `lowS_ok`, ...) depend on exactly the three
     standard axioms. Every probe `stage0/proben-ir/NAME.gab` is lowered by `stage0 --ir` to an `S0IR` image, which
     the runner binary (written by `lake exe runner`) runs; its exit code must be `NAME.code`.
  8. The verified x86-64 runner (`runner/`, PLAN-SELF-HOSTING.md §2.2): `lake build` of the package;
     `Nachpruefung.lean` -- `runner_tso`, `runner_sc`, `runner_mt`, the memory models, the file facts, the witness and `decode_enc`
     depend on exactly the three standard axioms; then `teile/runner-cpu.py` on this processor: the runner binary runs the probe images with
     the IR semantics' output and exit code, the differential tests of the x86-64 model (every instruction form,
     every flag the model defines) show no difference, and every instruction the model says faults ends its
     program with the named signal. Stage 3 covers the package's Lean files too.
  6. Coverage of the register by the program generator (`Gen/Abdeckung/`): `lake build gen-abdeckung`, then the
     native driver generates every program of the family up to the reference bounds and fails (exit 1) on a
     register member that no valid and no single-fault program contains and that is not a declared known gap
     (`bekannteLuecken`), or on a declared gap that is covered (the list is exact).

Exit 0 green, 1 red, 2 nothing or not everything measured (a stage that could not run, was killed for lack of
memory or did not get its memory in time; a run restricted by `--stufe` is also a 2 when everything it ran is
green, because the other stages were not measured). `--ohne-bau` skips stage 1 (the other stages read the existing
build state). `--stufe 7,8` runs only the named stages.

Memory (AGENTS.md, "RAM discipline"): every process that can use real memory runs in a no-swap `systemd-run`
scope, and a heavy step waits until 8 GiB are available. Lake has no job limit, so there are two modes:
  serial (default when under 24 GiB are available at the start, or `--seriell`): Lake's `lean` is
    `teile/lean-seriell.py` (fake sysroot, `LAKE_OVERRIDE_LEAN=1`), which lets ONE `lean -j1 -DElab.async=false
    -M4608` run at a time on one of the two shared slot locks (`~/.cache/gabbro-stage0-build.slot-N.lock`, 5 GiB
    scope), module by module in Lake's dependency order -- exactly the module set `lake build` builds (the
    lakefile roots, here `Stage0` and `Stage0.Haupt`, with their import closure), traces and the executables
    stay Lake's. The grammar stages (1, 2, 5, 6) hold BOTH slots and use `MemAvailable - 2 GiB` as the scope,
    with `(available - 2 GiB) / 6 GiB` parallel `lean` processes in the grammar build.
  parallel (`--parallel`): Lake as before, inside one scope of `MemAvailable - 2 GiB`."""
import contextlib, fcntl, os, pathlib, re, shutil, signal, subprocess, sys, time

W = pathlib.Path(__file__).resolve().parent.parent
G = W / "grammatik"
S0 = W / "stage0"
RN = W / "runner"
ENV = {**os.environ, "LC_ALL": "C"}
ENV.pop("ELAN_TOOLCHAIN", None)
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
VERBOTEN = re.compile(r"\b(sorry|admit|native_decide|sorryAx|unsafe)\b")
AXIOM = re.compile(r"^\s*axiom\s+([A-Za-z0-9_.']+)", re.M)


GIB = 1024 ** 3
WARTE_GIB = 8                      # a heavy step starts with at least this much MemAvailable (AGENTS.md)
SERIELL_UNTER_GIB = 24             # serial mode by default when less than this is available at the start
SLOT_DATEIEN = [pathlib.Path.home() / ".cache" / f"gabbro-stage0-build.slot-{n}.lock" for n in (1, 2)]
WACHE = W / "arbeitsprotokoll" / "lean-wache"      # scratch of this guardian (not committed)
LEAN_SERIELL = W / "instrumente" / "teile" / "lean-seriell.py"
# What a killed or memory-starved run prints: a lack of memory is not a finding (AGENTS.md), the stage is NOT MEASURED.
SPEICHERZEICHEN = ("excessive memory consumption", "out of memory", "cannot allocate memory",
                   "exited with code 137", "exited with code 143", "exited with code 75", "lean-seriell: ")
SERIELL = False


class NichtGemessen(Exception):
    """A step that could not be measured (memory, locks): exit code 2, never a green and never a red."""


def verfuegbar_gib():
    for z in pathlib.Path("/proc/meminfo").read_text().splitlines():
        if z.startswith("MemAvailable:"):
            return int(z.split()[1]) * 1024 / GIB
    return 0.0


def warte_speicher(frist=14400):
    ende = time.time() + frist
    gemeldet = False
    while verfuegbar_gib() < WARTE_GIB:
        if not gemeldet:
            print(f"     waiting for {WARTE_GIB} GiB available memory ({verfuegbar_gib():.1f} now)", flush=True)
            gemeldet = True
        if time.time() > ende:
            raise NichtGemessen(f"under {WARTE_GIB} GiB available for {frist} s")
        time.sleep(10)


def budget_gib():
    """Scope size of a grammar-wide step: MemAvailable - 2 GiB (owner, 2026-11-01), measured right before."""
    warte_speicher()
    return max(2, int(verfuegbar_gib() - 2))


def scope(mx, hoch=None):
    return ["systemd-run", "--user", "--scope", "-q", "-p", f"MemoryHigh={hoch or max(1, mx - 1)}G",
            "-p", f"MemoryMax={mx}G", "-p", "MemorySwapMax=0"]


def sc(cmd, mx=4):
    """`cmd` in a no-swap scope (the stage-0 compiler and the runner binary run many short processes)."""
    return scope(mx) + cmd


class _FristAbgelaufen(Exception):
    pass


def _alarm(signum, frame):
    raise _FristAbgelaufen()


@contextlib.contextmanager
def beide_slots(frist=14400):
    """Hold both global Lean slots (grammar-wide steps may use all memory minus 2 GiB, so nobody else runs).
    Blocking `flock` queues fairly behind the workers already waiting (polling would starve against them)."""
    fds = []
    alt = signal.signal(signal.SIGALRM, _alarm)
    try:
        for d in SLOT_DATEIEN:
            fd = os.open(d, os.O_RDWR | os.O_CREAT, 0o666)
            fds.append(fd)
            print(f"     taking slot lock {d.name}", flush=True)
            signal.alarm(frist)
            try:
                fcntl.flock(fd, fcntl.LOCK_EX)
            except _FristAbgelaufen:
                raise NichtGemessen(f"slot lock {d.name} not free for {frist} s")
            finally:
                signal.alarm(0)
        yield
    finally:
        signal.signal(signal.SIGALRM, alt)
        for fd in fds:
            os.close(fd)


def lauf(cmd, cwd, frist, mx=None, env=None):
    """Run `cmd` (in a no-swap scope of `mx` GiB when given); a run killed for lack of memory raises NichtGemessen."""
    if mx:
        warte_speicher()
        cmd = scope(mx) + cmd
    try:
        p = subprocess.run(cmd, cwd=cwd, env=env or ENV, capture_output=True, text=True, timeout=frist)
    except subprocess.TimeoutExpired:
        return 124, f"Frist {frist} s ueberschritten"
    out = p.stdout + p.stderr
    if p.returncode in (137, 143, -9, -15) or (p.returncode != 0 and any(z in out.lower() for z in SPEICHERZEICHEN)):
        raise NichtGemessen(f"killed or out of memory (rc {p.returncode}): {out.strip()[-200:]!r}")
    return p.returncode, out


def lean_umgebung(cwd, slots, parallel=1, mx=5, hoch=4, args="streng"):
    """Environment that makes Lake (as its `lean`) and `lake env` use `lean-seriell.py`; also the fake sysroot."""
    WACHE.mkdir(parents=True, exist_ok=True)
    rc, out = lauf(["lake", "env", "printenv", "LEAN_SYSROOT"], cwd, 300)
    echt = next((z for z in reversed(out.splitlines()) if z.startswith("/")), "") if rc == 0 else ""
    if not echt or not (pathlib.Path(echt) / "bin" / "lean").exists():
        raise NichtGemessen(f"no Lean sysroot found in {cwd}: {out.strip()[-200:]!r}")
    fake = WACHE / "sysroot"
    shutil.rmtree(fake, ignore_errors=True)
    (fake / "bin").mkdir(parents=True)
    for e in pathlib.Path(echt).iterdir():
        if e.name != "bin": (fake / e.name).symlink_to(e)
    for e in (pathlib.Path(echt) / "bin").iterdir():
        (fake / "bin" / e.name).symlink_to(LEAN_SERIELL if e.name == "lean" else e)
    privat = []
    for i in range(parallel):
        f = WACHE / f"privat-{i}.lock"
        f.touch()
        privat.append(str(f))
    return {**ENV, "LAKE_OVERRIDE_LEAN": "1", "LEAN_SYSROOT": str(fake),
            "GABBRO_LEAN_ECHT": str(pathlib.Path(echt) / "bin" / "lean"),
            "GABBRO_LEAN_PRIVAT": ":".join(privat),
            "GABBRO_LEAN_SLOTS": ":".join(str(d) for d in slots),
            "GABBRO_LEAN_MAX": str(mx), "GABBRO_LEAN_HOCH": str(hoch), "GABBRO_LEAN_ARGS": args}


def lake_bau(argv, cwd, frist, grammatik=False):
    """`lake <argv>` of one package under the memory rules. Serial: Lake's `lean` is lean-seriell.py (one `lean`
    at a time on a shared slot for stage 0/runner; `(available - 2 GiB) / 6 GiB` at a time for the grammar, whose
    modules keep Lake's own arguments); parallel: Lake as before in a scope of `MemAvailable - 2 GiB`."""
    if grammatik:
        mx = budget_gib()
        if not SERIELL:
            return lauf(["lake", *argv], cwd, frist, mx=mx)
        n = max(1, mx // 6)
        env = lean_umgebung(cwd, [], parallel=n, mx=max(2, mx // n), hoch=max(1, mx // n - 1), args="lake")
        env["GABBRO_LEAN_MIN"] = "2"
        return lauf(["lake", *argv], cwd, frist, mx=4, env=env)
    if not SERIELL:
        return lauf(["lake", *argv], cwd, frist, mx=budget_gib())
    env = lean_umgebung(cwd, SLOT_DATEIEN)
    return lauf(["lake", *argv], cwd, frist, mx=4, env=env)


def lean_datei(datei, cwd, frist, grammatik=False):
    """`lake env lean FILE`: the grammar's checks run with both slots held by the caller and a scope of
    `MemAvailable - 2 GiB`; stage 0 and the runner run `lean -j1 -DElab.async=false -M4608` on one shared slot."""
    if grammatik:
        mx = budget_gib()
        env = lean_umgebung(cwd, [], mx=mx, hoch=max(1, mx - 1), args="lake")
        env["GABBRO_LEAN_MIN"] = "2"
    else:
        env = lean_umgebung(cwd, SLOT_DATEIEN)
    return lauf(["lake", "env", str(LEAN_SERIELL), str(datei)], cwd, frist, env=env)


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
    with beide_slots():
        rc, out = lake_bau(["build"], G, 14400, grammatik=True)
    jobs = re.findall(r"Build completed successfully \((\d+) jobs\)", out)
    ok = rc == 0 and bool(jobs)
    print(f"  1 bau:     {'ok' if ok else 'ROT'} ({jobs[-1] + ' Jobs' if jobs else out.strip().splitlines()[-1:]})")
    return ok


def stufe_axiome():
    with beide_slots():
        rc, out = lean_datei("NachpruefungZiel.lean", G, 3600, grammatik=True)
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
    for f in sorted(list(G.rglob("*.lean")) + list(S0.rglob("*.lean")) + list(RN.rglob("*.lean"))):
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
    with beide_slots():
        mx = budget_gib()
        rc, out = lauf(["cargo", "test", "-q", "--test", "zertifikate"], W, 7200, mx=mx,
                       env={**ENV, "CARGO_BUILD_JOBS": str(max(1, min(8, mx // 2)))})
        if rc != 0:
            print("  5 zertif.: ROT (the generator test failed)\n", out[-800:])
            return False
        dateien = sorted(f for f in (W / "target" / "zertifikate").glob("*.lean"))
        schlecht = []
        for f in dateien:
            rc, out = lean_datei(f, G, 3600, grammatik=True)
            if rc != 0 or re.search(r"error", out):
                schlecht.append(f"{f.name}: {out.strip().splitlines()[:2]}")
    ok = bool(dateien) and not schlecht
    print(f"  5 zertif.: {'ok' if ok else 'ROT'} ({len(dateien)} Zertifikate elaboriert, {len(schlecht)} gefallen)")
    for b in schlecht[:6]: print("     ", b)
    return ok


ABDECKUNG_GRENZEN = ["7", "7", "5", "7:6:6:4"]   # bodies/skeletons up to 7, one change up to 5; member 7 (registers only): 6/6/4


def stufe_abdeckung():
    with beide_slots():
        rc, out = lake_bau(["build", "gen-abdeckung"], G, 14400, grammatik=True)
        exe = G / ".lake/build/bin/gen-abdeckung"
        if rc != 0 or not exe.exists():
            print("  6 abdeckung: ROT (the driver does not build)\n", out[-600:])
            return False
        rc, out = lauf([str(exe), str(W / "dokumente/llvm-modelldeckung.tsv"), *ABDECKUNG_GRENZEN], G, 3600,
                       mx=budget_gib())
    zeilen = [z for z in out.splitlines() if z.startswith(("register members", "valid programs", "cells"))]
    print(f"  6 abdeckung: {'ok' if rc == 0 else 'ROT'} ({'; '.join(zeilen)})")
    if rc != 0:
        for z in out.splitlines()[-3:]: print("     ", z[:400])
    return rc == 0


def stufe_stage0():
    if not S0.is_dir():
        print("  7 stage0:  ROT (stage0/ fehlt)")
        return False
    # `lake build` builds the closure of the lakefile roots `Stage0` and `Stage0.Haupt`; `Nachpruefung.lean` imports
    # modules outside it (`Stage0.Bindung.Proben`), which `lake env lean` cannot elaborate unbuilt: build them too.
    extra = [f"+{m}" for m in re.findall(r"^import\s+(Stage0\.[A-Za-z0-9_.]+)", (S0 / "Nachpruefung.lean").read_text(), re.M)]
    rc, out = lake_bau(["build", "Stage0", "stage0", *extra], S0, 14400)
    jobs = re.findall(r"Build completed successfully \((\d+) jobs\)", out)
    ok = rc == 0 and bool(jobs)
    print(f"  7 stage0:  {'ok' if ok else 'ROT'} ({jobs[-1] + ' Jobs' if jobs else out.strip().splitlines()[-1:]})")
    if not ok:
        return False
    exe = S0 / ".lake/build/bin/stage0"
    proben = sorted((S0 / "proben").glob("*.gab"))
    falsch = []
    rc, out = lean_datei("Nachpruefung.lean", S0, 3600)
    zeilen = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", out)
    schlecht = [n for n, a in zeilen if not {x.strip() for x in a.split(",") if x.strip()} <= STANDARD]
    satz = any(n.endswith(".bild_ok_u") for n, _ in zeilen)
    ok_ax = rc == 0 and satz and len(zeilen) >= 13 and not schlecht
    print(f"  7 senke:   {'ok' if ok_ax else 'ROT'} ({len(zeilen)} Saetze, bild_ok_u "
          f"{'gefunden' if satz else 'FEHLT'}, {len(schlecht)} mit fremden Axiomen)")
    kratz = S0 / ".lake" / "ir"
    kratz.mkdir(parents=True, exist_ok=True)
    rc, out = lake_bau(["exe", "runner", str(kratz)], RN, 14400)
    runner = kratz / "runner"
    irproben = sorted((S0 / "proben-ir").glob("*.gab"))
    irfalsch = []
    if rc != 0 or not runner.exists():
        irfalsch.append(f"runner binary not written: {out.strip()[-200:]}")
    else:
        runner.chmod(0o755)
        for gab in proben:
            img = kratz / ("io-" + gab.stem + ".img")
            q = subprocess.run(sc([str(exe), "--ir", str(gab), str(img)]), cwd=S0, env=ENV,
                               capture_output=True, timeout=600)
            if q.returncode != 0:
                falsch.append(f"{gab.name}: compilation failed: {(q.stdout + q.stderr)[:200]!r}")
                continue
            ein = gab.with_suffix(".ein").read_bytes()
            warte = gab.with_suffix(".warte")
            p = subprocess.Popen(sc([str(runner), str(img)]), cwd=kratz, env=ENV,
                                 stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            try:
                if warte.exists():
                    try:
                        p.wait(timeout=float(warte.read_text()))
                    except subprocess.TimeoutExpired:
                        pass
                aus, err = p.communicate(ein, timeout=600)
            except subprocess.TimeoutExpired:
                p.kill()
                aus, err = p.communicate()
            if p.returncode != 0 or aus != gab.with_suffix(".aus").read_bytes():
                falsch.append(f"{gab.name} (rc {p.returncode}: {(aus + err)[:200]!r})")
        for gab in irproben:
            img = kratz / (gab.stem + ".img")
            q = subprocess.run(sc([str(exe), "--ir", str(gab), str(img)]), cwd=S0, env=ENV, capture_output=True, timeout=600)
            refusal = gab.with_suffix(".error")
            if refusal.exists():
                expected = refusal.read_bytes().strip()
                if q.returncode != 1 or expected not in q.stderr:
                    irfalsch.append(f"{gab.name}: expected compiler refusal {expected!r}, "
                                    f"got rc {q.returncode}: {(q.stdout + q.stderr)[:200]!r}")
                continue
            if q.returncode != 0:
                irfalsch.append(f"{gab.name}: stage0 --ir rc {q.returncode}: {(q.stdout + q.stderr)[:200]!r}")
                continue
            r = subprocess.run(sc([str(runner), str(img)]), cwd=kratz, env=ENV, capture_output=True, timeout=600)
            soll = int(gab.with_suffix(".code").read_text())
            if r.returncode != soll:
                irfalsch.append(f"{gab.name}: exit {r.returncode}, expected {soll}")
    print(f"  7 proben:  {'ok' if proben and not falsch else 'ROT'} ({len(proben) - len(falsch)} of {len(proben)})")
    for f in falsch: print("     ", f)
    print(f"  7 ir:      {'ok' if irproben and not irfalsch else 'ROT'} ({len(irproben) - len(irfalsch)} of {len(irproben)})")
    for f in irfalsch: print("     ", f)
    return bool(proben) and not falsch and ok_ax and bool(irproben) and not irfalsch


RUNNER_FAELLE = "20000"


def stufe_runner():
    if not RN.is_dir():
        print("  8 runner:  ROT (runner/ fehlt)")
        return False
    rc, out = lake_bau(["build"], RN, 14400)
    jobs = re.findall(r"Build completed successfully \((\d+) jobs\)", out)
    if rc != 0 or not jobs:
        print(f"  8 runner:  ROT (build: {out.strip().splitlines()[-1:]})")
        return False
    rc, out = lean_datei("Nachpruefung.lean", RN, 3600)
    zeilen = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", out)
    schlecht = [n for n, a in zeilen if not {x.strip() for x in a.split(",") if x.strip()} <= STANDARD]
    satz = any(n.endswith(".runner_tso") for n, _ in zeilen)
    ok_ax = rc == 0 and satz and len(zeilen) >= 10 and not schlecht
    print(f"  8 runner:  {'ok' if ok_ax else 'ROT'} ({jobs[-1]} Jobs, {len(zeilen)} Saetze, runner_tso "
          f"{'gefunden' if satz else 'FEHLT'}, {len(schlecht)} mit fremden Axiomen)")
    kratz = RN / ".lake" / "cpu"
    rc, out = lauf([sys.executable, str(W / "instrumente/teile/runner-cpu.py"), str(RN / ".lake/build/bin/runner"),
                    str(kratz), RUNNER_FAELLE], RN, 7200, mx=6)
    letzte = [z for z in out.splitlines() if z.startswith("runner-cpu:")]
    print(f"  8 cpu:     {'ok' if rc == 0 else 'ROT'} ({letzte[-1] if letzte else out.strip()[-200:]})")
    if rc != 0:
        for z in letzte[:10]: print("     ", z[:300])
    return ok_ax and rc == 0


STUFEN = {1: stufe_bau, 2: stufe_axiome, 3: stufe_sorry, 4: stufe_layout, 5: stufe_zertifikate,
          6: stufe_abdeckung, 7: stufe_stage0, 8: stufe_runner}


def waehle(argv):
    """The stages to run and whether the run is complete; None on a malformed command line."""
    wahl, ohne_bau, i = None, False, 0
    while i < len(argv):
        a = argv[i]
        if a == "--ohne-bau": ohne_bau = True
        elif a in ("--seriell", "--parallel"): pass
        elif a == "--stufe" and i + 1 < len(argv): wahl = argv[i + 1]; i += 1
        elif a.startswith("--stufe="): wahl = a.split("=", 1)[1]
        else: return None
        i += 1
    if wahl is None:
        return [n for n in STUFEN if not (ohne_bau and n == 1)], True
    try:
        nummern = sorted({int(x) for x in wahl.split(",")})
    except ValueError:
        return None
    if not nummern or any(n not in STUFEN for n in nummern): return None
    return nummern, False


def main():
    global SERIELL
    w = waehle(sys.argv[1:])
    if w is None:
        print(__doc__.split("Stages")[0]); print("ABBRUCH: malformed command line -- nothing measured"); return 2
    nummern, vollstaendig = w
    if not G.is_dir(): print("ABBRUCH: grammatik/ fehlt -- nichts gemessen"); return 2
    SERIELL = "--seriell" in sys.argv or ("--parallel" not in sys.argv and verfuegbar_gib() < SERIELL_UNTER_GIB)
    print(f"== Wächter 1: Lean-Modell == (stages {','.join(map(str, nummern))}; "
          f"{'serial' if SERIELL else 'parallel'} mode, {verfuegbar_gib():.1f} GiB available)")
    erg = {}
    for n in nummern:
        try:
            erg[n] = STUFEN[n]()
        except NichtGemessen as e:
            print(f"  {n} NOT MEASURED: {e}")
            erg[n] = None
    rot = [n for n, r in erg.items() if r is False]
    offen = [n for n, r in erg.items() if r is None]
    if rot:
        print(f"== LEAN: ROT (stage {','.join(map(str, rot))}"
              f"{'; not measured: ' + ','.join(map(str, offen)) if offen else ''}) ==")
        return 1
    if offen or not vollstaendig:
        print(f"== LEAN: NOT FULLY MEASURED ({'not measured: ' + ','.join(map(str, offen)) if offen else 'only stages ' + ','.join(map(str, nummern)) + ', all green'}) ==")
        return 2
    print("== LEAN: GRUEN ==")
    return 0


if __name__ == "__main__":
    sys.exit(main())
