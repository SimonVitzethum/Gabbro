#!/usr/bin/env python3
"""Guardian 2 of 4 -- the LLVM compiler (`crates/gabbro-check/src/llvm.rs`, `llvm/`).

    ./instrumente/pruefe-llvm.py

Stages (a stage that cannot run is reported NICHT GEMESSEN and the run is not green):
  1. `cargo test --test llvm`: IR tests, refusals by name (Y101..Y106), model-coverage register
     (`teile/llvm-modelldeckung.py`), noalias rule, and the Lean certificate elaborating with
     plain `lean`.
  2. End to end (`teile/baue-llvm.sh`): checker, IR, `opt -O3`, `llc`, `ld.lld`, static binary
     without INTERP/NEEDED, run on x86_64 natively and on aarch64 under qemu; both targets must
     return the SAME code, and it must be the expected one.

Exit 0 green, 1 red, 2 a stage could not run."""
import os, pathlib, re, shutil, subprocess, sys

W = pathlib.Path(__file__).resolve().parent.parent
ENV = {**os.environ, "LC_ALL": "C"}
# program -> expected exit code (the same on both targets)
PROGRAMME = {
    "messung/llvm/summe.gab": 25,
    "beispiele/1160-halde-mit-abtastung.gab": 42,
    "beispiele/1161-platz-freigeben.gab": 100,
    "beispiele/1162-echte-faeden.gab": 64,
}


def stufe_tests():
    p = subprocess.run(["cargo", "test", "-q", "-p", "gabbro-check", "--test", "llvm", "--no-fail-fast"],
                       cwd=W, env=ENV, capture_output=True, text=True, timeout=3000)
    m = re.findall(r"test result: (\w+)\. (\d+) passed; (\d+) failed", p.stdout)
    gesamt = sum(int(a[1]) for a in m); rot = sum(int(a[2]) for a in m)
    ok = p.returncode == 0 and gesamt > 0 and rot == 0
    print(f"  1 tests:   {'ok' if ok else 'ROT'} ({gesamt} Tests, {rot} gefallen)")
    if not ok: print(p.stdout[-1500:], p.stderr[-800:])
    return ok


def stufe_ende_zu_ende():
    fehlt = [t for t in ("opt", "llc", "ld.lld", "readelf", "qemu-aarch64") if not shutil.which(t)]
    if fehlt:
        print(f"  2 binaer:  NICHT GEMESSEN (fehlt: {', '.join(fehlt)})")
        return None
    if not (W / "target/debug/gabbro").is_file():
        print("  2 binaer:  NICHT GEMESSEN (target/debug/gabbro fehlt: cargo build)")
        return None
    tls = W / ".tmp" / "llvm-waechter"; tls.mkdir(parents=True, exist_ok=True)
    gut = 0
    for datei, soll in PROGRAMME.items():
        p = subprocess.run(["bash", str(W / "instrumente/teile/baue-llvm.sh"), datei],
                           cwd=W, env={**ENV, "TLS": str(tls)}, capture_output=True, text=True, timeout=600)
        rcs = re.findall(r"\[(x86_64|aarch64)\] rc=(\d+)", p.stdout)
        ok = len(rcs) == 2 and all(int(r) == soll for _, r in rcs) and "5b. x86_64 und aarch64 stimmen" in p.stdout \
            and "FUND" not in p.stdout and "ROT" not in p.stdout
        gut += ok
        if not ok: print(f"     {datei}: erwartet rc={soll}, erhalten {rcs}\n{p.stdout[-600:]}")
    ok = gut == len(PROGRAMME)
    print(f"  2 binaer:  {'ok' if ok else 'ROT'} ({gut} von {len(PROGRAMME)} Programmen, x86_64 und aarch64 gleich)")
    return ok


def main():
    print("== Wächter 2: LLVM-Compiler ==")
    erg = [stufe_tests(), stufe_ende_zu_ende()]
    if False in erg: print("== LLVM: ROT =="); return 1
    if None in erg: print("== LLVM: TEILMESSUNG (nicht alles gemessen) =="); return 2
    print("== LLVM: GRUEN =="); return 0


if __name__ == "__main__":
    sys.exit(main())
