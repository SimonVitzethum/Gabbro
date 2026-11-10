#!/usr/bin/env python3
"""Acceptance: the two guardians, one after the other (one heavy run at a time).

    ./instrumente/abnahme.py [--lean|--gabbrov]

  pruefe-lean.py     the Lean model     (lake build, gabbro_ziel axioms, no sorry, layout)
  pruefe-gabbrov.py  GabbroV            (programmlogik build, proofs, the bridge)

Exit 0 only when both are green. A guardian that could not measure (exit 2) is not green,
and `abnahme` says so; what stands behind an abort was NOT measured."""
import pathlib, subprocess, sys, time

W = pathlib.Path(__file__).resolve().parent
WAECHTER = {"--lean": "pruefe-lean.py", "--gabbrov": "pruefe-gabbrov.py"}


def main():
    wahl = [v for k, v in WAECHTER.items() if k in sys.argv] or list(WAECHTER.values())
    erg = {}
    for w in wahl:
        t = time.time()
        rc = subprocess.call([sys.executable, str(W / w)])
        erg[w] = (rc, time.time() - t)
    print("\n== Abnahme ==")
    for w, (rc, s) in erg.items():
        print(f"  {'GRUEN' if rc == 0 else 'ROT' if rc == 1 else 'NICHT GEMESSEN':<15} {w:<20} {s:6.1f} s")
    gruen = sum(rc == 0 for rc, _ in erg.values())
    print(f"== {gruen} von {len(erg)} Waechtern gruen ==")
    return 0 if gruen == len(erg) else 1


if __name__ == "__main__":
    sys.exit(main())
