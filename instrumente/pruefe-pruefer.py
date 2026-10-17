#!/usr/bin/env python3
"""Guardian 3 of 4 -- the checker (`crates/gabbro-check`, `gabbro-syntax`, `gabbro-cli`).

    ./instrumente/pruefe-pruefer.py

Stages:
  1. `cargo test --workspace --no-fail-fast`: every rule has its poison probe (`beispiele/gift/`
     must fall with exactly the booked code), every example checks clean, the tutorial, the
     grammar and reserved-word tables, the doc code blocks and the certificates agree.
  2. Sentence register (`teile/saetze.py`): every issued code has a sentence at most as often as
     the booked ratchet, and no sentence describes a rule that does not exist.
  3. Issued-code uniqueness (`teile/kennungen.py`): no code is issued from two places unless
     booked with a reason.

Exit 0 green, 1 red, 2 nothing measured."""
import os, pathlib, re, subprocess, sys

W = pathlib.Path(__file__).resolve().parent.parent
ENV = {**os.environ, "LC_ALL": "C"}


def stufe_tests():
    p = subprocess.run(["cargo", "test", "-q", "--workspace", "--no-fail-fast"], cwd=W, env=ENV,
                       capture_output=True, text=True, timeout=3500)
    m = re.findall(r"test result: \w+\. (\d+) passed; (\d+) failed", p.stdout)
    gesamt = sum(int(a) for a, _ in m); rot = sum(int(b) for _, b in m)
    ok = p.returncode == 0 and gesamt > 0 and rot == 0
    print(f"  1 tests:    {'ok' if ok else 'ROT'} ({gesamt} Tests in {len(m)} Sammlungen, {rot} gefallen)")
    if not ok:
        for z in re.findall(r"^---- (\S+) stdout ----", p.stdout, re.M)[:15]: print("     gefallen:", z)
    return gesamt > 0 and ok


def teil(name, label):
    p = subprocess.run([sys.executable, str(W / "instrumente/teile" / name)], cwd=W, env=ENV,
                       capture_output=True, text=True, timeout=900)
    ok = p.returncode == 0
    letzte = (p.stdout.strip().splitlines() or [""])[-1][:150]
    print(f"  {label}: {'ok' if ok else 'ROT'} ({letzte})")
    if not ok: print(p.stdout[-1200:], p.stderr[-400:])
    return ok


def main():
    if not (W / "crates").is_dir(): print("ABBRUCH: crates/ fehlt -- nichts gemessen"); return 2
    print("== Wächter 3: Prüfer ==")
    subprocess.run(["cargo", "build", "-q"], cwd=W, env=ENV, capture_output=True)
    erg = [stufe_tests(), teil("saetze.py", "2 saetze:  "), teil("kennungen.py", "3 kennungen:")]
    print("== PRUEFER:", "GRUEN" if all(erg) else "ROT", "==")
    return 0 if all(erg) else 1


if __name__ == "__main__":
    sys.exit(main())
