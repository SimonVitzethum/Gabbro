#!/usr/bin/env python3
"""The runner on the processor (called by the Lean guardian, stage 8; PLAN-SELF-HOSTING.md section 2.2).

    runner-cpu.py BIN DIR [CASES]

BIN is the `runner` executable of the Lean package `runner/`; DIR a scratch directory. Three checks:

1. The runner binary written by Lean runs every probe image with the output and exit code the IR semantics
   computes (`hello`, `probe`).
2. Differential tests of the x86-64 model: CASES random cases of the 22 instruction forms run on this processor;
   registers, data area and every flag the model defines must equal the model's `exec`.
3. Fault programs: every instruction the model says faults ends the program with the named signal, and the model
   does say fault for it.

Exit 0 all green, 1 a difference (printed), 2 nothing or not everything measured.
"""
import os
import subprocess
import sys

KINDS = 19  # Runner.Test.KINDS


def main():
    if len(sys.argv) < 3:
        print(__doc__)
        return 2
    exe, d = sys.argv[1], sys.argv[2]
    cases = sys.argv[3] if len(sys.argv) > 3 else "20000"
    os.makedirs(d, exist_ok=True)
    bad = 0
    measured = 0

    # 1. probes
    r = subprocess.run([exe, d], capture_output=True, text=True)
    if r.returncode != 0:
        print("runner-cpu: writing the runner failed:", r.stderr)
        return 2
    os.chmod(os.path.join(d, "runner"), 0o755)
    for p in ["hello", "probe"]:
        want = open(os.path.join(d, p + ".out"), "rb").read()
        code = int(open(os.path.join(d, p + ".code")).read())
        q = subprocess.run([os.path.join(d, "runner"), os.path.join(d, p + ".img")], capture_output=True)
        measured += 1
        if q.stdout != want or q.returncode != code:
            bad += 1
            print(f"runner-cpu: probe {p}: exit {q.returncode} (IR {code}), output equal: {q.stdout == want}")
    # 2. differential tests
    r = subprocess.run([exe, "difftest", d, cases], capture_output=True, text=True)
    if r.returncode != 0:
        print("runner-cpu: generating the tests failed:", r.stderr)
        return 2
    xt = os.path.join(d, "xtest")
    os.chmod(xt, 0o755)
    q = subprocess.run([xt], capture_output=True)
    exp = open(xt + ".expect", "rb").read()
    pairs = [l.split() for l in open(xt + ".mask").read().splitlines() if l.strip()]
    masks = [int(m) for m, _ in pairs]
    kinds = {}
    for _, k in pairs:
        kinds[int(k)] = kinds.get(int(k), 0) + 1
    blk = 1024
    if q.returncode != 0 or len(q.stdout) != len(exp) or len(exp) != blk * len(masks):
        print(f"runner-cpu: xtest exit {q.returncode}, {len(q.stdout)} bytes, expected {len(exp)}")
        return 1
    for i, m in enumerate(masks):
        a = q.stdout[i * blk:(i + 1) * blk]
        e = exp[i * blk:(i + 1) * blk]
        measured += 1
        same = a[:640] == e[:640]
        fa = int.from_bytes(a[640:648], "little")
        fe = int.from_bytes(e[640:648], "little")
        if not same or (fa & m) != fe:
            bad += 1
            if bad <= 10:
                regs = [(j, int.from_bytes(a[512 + 8 * j:520 + 8 * j], "little"),
                         int.from_bytes(e[512 + 8 * j:520 + 8 * j], "little")) for j in range(16)]
                diff = [(j, hex(x), hex(y)) for j, x, y in regs if x != y]
                print(f"runner-cpu: case {i}: regs {diff}, data equal {a[136:392] == e[136:392]}, "
                      f"flags {fa & m:#x} vs {fe:#x} (mask {m:#x})")
    missing = [k for k in range(KINDS) if kinds.get(k, 0) == 0]
    print("runner-cpu: cases per kind", [kinds.get(k, 0) for k in range(KINDS)])
    # 3. faults
    for line in open(os.path.join(d, "faults.txt")).read().splitlines():
        name, sig, model = line.split()
        f = os.path.join(d, "fault-" + name)
        os.chmod(f, 0o755)
        q = subprocess.run([f], capture_output=True)
        measured += 1
        if q.returncode != -int(sig) or model != "true":
            bad += 1
            print(f"runner-cpu: fault {name}: ended {q.returncode}, expected signal {sig}, model says fault: {model}")
    print(f"runner-cpu: {measured} checks, {bad} differences")
    if measured == 0 or missing:
        print("runner-cpu: kinds not measured:", missing)
        return 2
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
