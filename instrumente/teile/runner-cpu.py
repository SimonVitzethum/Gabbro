#!/usr/bin/env python3
"""The runner on the processor (called by the Lean guardian, stage 8; PLAN-SELF-HOSTING.md section 2.2).

    runner-cpu.py BIN DIR [CASES]

BIN is the `runner` executable of the Lean package `runner/`; DIR a scratch directory. Three checks:

1. The runner binary written by Lean runs every probe image with the output and exit code fixed in
   `runner/proben/NAME.aus` and `NAME.code` (no Lean program runs the IR); `objdump` decodes the runner's code to the
   instructions of the listing `runner.s`.
2. Differential tests of the x86-64 model: CASES random cases of the 22 instruction forms run on this processor;
   registers, data area and every flag the model defines must equal the model's `exec`.
3. Fault programs: every instruction the model says faults ends the program with the named signal, and the model
   does say fault for it.
4. Litmus tests of x86-TSO (the memory model of the multi-thread theorem), run by the runner on real threads:
   20000 synchronised rounds each; the outcomes TSO forbids must not occur (SB with locked stores (0,0),
   MP (1,0), LB (1,1)); the count of SB's allowed (0,0) is printed (the store buffer at work).

Exit 0 all green, 1 a difference (printed), 2 nothing or not everything measured.
"""
import os
import subprocess
import sys

KINDS = 19  # Runner.Test.KINDS


def listing_matches(binary, listing):
    """objdump's mnemonics at every address of the listing equal the listing's (operands are not compared:
    the two syntaxes differ in detail; the bytes themselves are checked by the proofs)."""
    want = {}
    for line in open(listing):
        line = line.strip()
        if line.startswith("0x") and ":" in line:
            a, ins = line.split(":", 1)
            want[int(a, 16)] = ins.split()[0] if ins.split()[0] != "lock" else "lock"
    try:
        out = subprocess.run(["objdump", "-D", "-b", "binary", "-m", "i386:x86-64", "-M", "intel",
                                  "--adjust-vma=0x400000", "--start-address=0x400100", binary],
                             capture_output=True, text=True).stdout
    except FileNotFoundError:
        print("runner-cpu: objdump missing")
        return False
    got = {}
    for line in out.splitlines():
        parts = line.split("\t")
        if len(parts) >= 3 and parts[0].strip().endswith(":"):
            try:
                words = [w for w in parts[2].split() if not w.startswith("rex")]
                got[int(parts[0].strip()[:-1], 16)] = words[0]
            except ValueError:
                pass
    bad = [hex(a) for a, m in want.items() if got.get(a) != m]
    if bad:
        print(f"runner-cpu: listing and objdump differ at {len(bad)} of {len(want)} addresses, e.g. {bad[:5]}",
              [(a, want[int(a, 16)], got.get(int(a, 16))) for a in bad[:5]])
    return not bad and len(want) > 0


def main():
    if len(sys.argv) < 3:
        print(__doc__)
        return 2
    exe, d = os.path.abspath(sys.argv[1]), os.path.abspath(sys.argv[2])
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
    proben = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "runner", "proben")
    for p in ["hello", "probe", "threads", "io"]:
        want = open(os.path.join(proben, p + ".aus"), "rb").read()
        code = int(open(os.path.join(proben, p + ".code")).read())
        q = subprocess.run([os.path.join(d, "runner"), os.path.join(d, p + ".img")], capture_output=True, cwd=d)
        measured += 1
        if q.stdout != want or q.returncode != code:
            bad += 1
            print(f"runner-cpu: probe {p}: exit {q.returncode} (IR {code}), output equal: {q.stdout == want}")
    measured += 1
    committed = os.path.join(proben, "..", "runner.s")
    if open(committed).read() != open(os.path.join(d, "runner.s")).read():
        bad += 1
        print("runner-cpu: runner/runner.s is not the listing of the current runner (write it with lake exe runner)")
    measured += 1
    if not listing_matches(os.path.join(d, "runner"), os.path.join(d, "runner.s")):
        bad += 1
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
    # 4. litmus tests
    forbidden = {"lit-sbcas": (0, 0), "lit-mp": (1, 0), "lit-lb": (1, 1)}
    counts = {}
    for t in ["lit-sb", "lit-sbcas", "lit-mp", "lit-lb"]:
        q = subprocess.run([os.path.join(d, "runner"), os.path.join(d, t + ".img")], capture_output=True,
                           cwd=d, timeout=600)
        measured += 1
        out = q.stdout
        if q.returncode != 0 or len(out) != 16 * 20000:
            bad += 1
            print(f"runner-cpu: {t}: exit {q.returncode}, {len(out)} bytes")
            continue
        c = {}
        for k in range(len(out) // 16):
            key = (int.from_bytes(out[16 * k:16 * k + 8], "little"), int.from_bytes(out[16 * k + 8:16 * k + 16], "little"))
            c[key] = c.get(key, 0) + 1
        counts[t] = c
        if t in forbidden and c.get(forbidden[t], 0):
            bad += 1
            print(f"runner-cpu: {t}: the outcome {forbidden[t]} TSO forbids occurred {c[forbidden[t]]} times")
    print("runner-cpu: litmus", {t: {f"{a}{b}": n for (a, b), n in sorted(c.items())} for t, c in counts.items()})
    print(f"runner-cpu: {measured} checks, {bad} differences")
    if measured == 0 or missing:
        print("runner-cpu: kinds not measured:", missing)
        return 2
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
