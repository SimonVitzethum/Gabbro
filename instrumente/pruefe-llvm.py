#!/usr/bin/env python3
"""Guardian 2 of 4 -- the LLVM compiler (`crates/gabbro-check/src/llvm.rs`, `llvm/`).

    ./instrumente/pruefe-llvm.py

Stages (a stage that cannot run is reported NICHT GEMESSEN and the run is not green):
  1. `cargo test --test llvm`: IR tests, refusals by name (Y101..Y106), model-coverage register
     (`teile/llvm-modelldeckung.py`), noalias rule, and the Lean certificate elaborating with
     plain `lean`.
  3. Instruction text (`stufe_befehle`): hardware-only forms (`asm` bodies with `outb`/`invlpg`, the port
     space's `in`/`out`) cannot run in user space, so `llc -filetype=obj` + `llvm-objdump -d` must show
     the intended instructions. 4. The aarch64 exception entries RUN under `qemu-system-aarch64 -M virt`
     (`teile/eintritt-a64-qemu.sh`: two `svc`, the generated stub, `eret`).
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
    "messung/llvm/sperre.gab": 3,
    "messung/llvm/kind.gab": 42,
    "messung/llvm/nachricht.gab": 42,
    "messung/llvm/leserschreiber.gab": 42,
    "beispiele/1160-halde-mit-abtastung.gab": 42,
    "beispiele/1161-platz-freigeben.gab": 100,
    "beispiele/1162-echte-faeden.gab": 64,
    "messung/llvm/assembler.gab": 42,
}

# hardware-only forms: (file, target, [(objdump pattern, what)]) -- the TEXT is checked, never the effect at a device
BEFEHLE = [
    ("beispiele/36-asm.gab", "x86_64", [(r"\boutb\s+%al, %dx", "outb"), (r"\bsyscall\b", "syscall")]),
    ("beispiele/67-befehlsebene.gab", "x86_64", [(r"\binvlpg\b", "invlpg"), (r"\bsfence\b", "sfence"), (r"\bmfence\b", "mfence")]),
    ("beispiele/65-port-space.gab", "x86_64", [(r"\binb\s+%dx, %al", "inb"), (r"\boutb\s+%al, %dx", "outb")]),
    ("beispiele/60-annahme-mit-maschine.gab", "x86_64", [(r"\bmfence\b", "mfence")]),
]


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
    # the binary the end-to-end stage drives must match the sources (a stale binary measured the old compiler)
    subprocess.run(["cargo", "build", "-q", "-p", "gabbro-cli"], cwd=W, env=ENV, capture_output=True, timeout=3000)
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
    return ok and stufe_halde_frei(tls)


def stufe_halde_frei(tls):
    """A heap is free unless used: the unbounded-heap binary must never map more than 1 GiB read/write at once
    (reservations are PROT_NONE; payload and metadata become accessible chunk by chunk)."""
    if not shutil.which("strace"):
        print("  2b halde:  NICHT GEMESSEN (strace fehlt)")
        return None
    exe = tls / "1160-halde-mit-abtastung-x86_64"
    p = subprocess.run(["strace", "-f", "-e", "trace=mmap", str(exe)], capture_output=True, text=True, timeout=120)
    gross = [m for m in re.findall(r"mmap\(NULL, (\d+), ([A-Z_|]+),", p.stderr)
             if "PROT_WRITE" in m[1] and int(m[0]) > 2**30]
    ok = not gross
    print(f"  2b halde:  {'ok' if ok else 'ROT'} (keine Lese/Schreib-Abbildung über 1 GiB{'' if ok else ': ' + str(gross)})")
    return ok


def stufe_befehle():
    fehlt = [t for t in ("opt", "llc", "llvm-objdump") if not shutil.which(t)]
    if fehlt:
        print(f"  3 befehle: NICHT GEMESSEN (fehlt: {', '.join(fehlt)})")
        return None
    tls = W / ".tmp" / "llvm-waechter"; tls.mkdir(parents=True, exist_ok=True)
    gut = 0
    for datei, ziel, muster in BEFEHLE:
        name = pathlib.Path(datei).stem
        ll, o = tls / f"{name}-{ziel}.befehle.ll", tls / f"{name}-{ziel}.befehle.o"
        ok = False
        p = subprocess.run([str(W / "target/debug/gabbro"), "llvm", f"--target={ziel}", datei], cwd=W, env=ENV, capture_output=True, text=True)
        if p.returncode == 0:
            ll.write_text(p.stdout)
            a = subprocess.run(["opt", "-O3", str(ll), "-S", "-o", str(ll)], capture_output=True, text=True)
            b = subprocess.run(["llc", "-O3", "-filetype=obj", str(ll), "-o", str(o)], capture_output=True, text=True)
            if a.returncode == 0 and b.returncode == 0:
                text = subprocess.run(["llvm-objdump", "-d", "--no-show-raw-insn", str(o)], capture_output=True, text=True).stdout
                fehlend = [w for m, w in muster if not re.search(m, text)]
                ok = not fehlend
                if not ok: print(f"     {datei} [{ziel}]: im Objekt fehlt: {fehlend}")
            else:
                print(f"     {datei} [{ziel}]: opt/llc: {(a.stderr + b.stderr)[:300]}")
        else:
            print(f"     {datei} [{ziel}]: Erzeuger: {p.stderr[-300:]}")
        gut += ok
    ok = gut == len(BEFEHLE)
    print(f"  3 befehle: {'ok' if ok else 'ROT'} ({gut} von {len(BEFEHLE)} Dateien: die Befehle stehen im Objekt; Wirkung am Gerät NICHT ausgeführt)")
    return ok


def stufe_eintritt_a64():
    p = subprocess.run(["bash", str(W / "instrumente/teile/eintritt-a64-qemu.sh")], cwd=W, env=ENV, capture_output=True, text=True, timeout=600)
    if p.returncode == 2:
        print(f"  4 eintritt: NICHT GEMESSEN ({p.stderr.strip()[:120]})")
        return None
    ok = p.returncode == 0
    print(f"  4 eintritt: {'ok' if ok else 'ROT'} (aarch64-Ausnahmen unter qemu-system-aarch64 -M virt, EL1)")
    if not ok: print(p.stdout[-800:], p.stderr[-400:])
    return ok


def main():
    print("== Wächter 2: LLVM-Compiler ==")
    erg = [stufe_tests(), stufe_ende_zu_ende(), stufe_befehle(), stufe_eintritt_a64()]
    if False in erg: print("== LLVM: ROT =="); return 1
    if None in erg: print("== LLVM: TEILMESSUNG (nicht alles gemessen) =="); return 2
    print("== LLVM: GRUEN =="); return 0


if __name__ == "__main__":
    sys.exit(main())
