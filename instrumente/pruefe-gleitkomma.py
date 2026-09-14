#!/usr/bin/env python3
"""Differential check: the Gleitkomma.lean model against C arithmetic.

Compares the kernel-computable IEEE-754 model (grammatik/Grammatik/
Gleitkomma.lean, executed through an embedded driver via
`lake env lean --run`) with C `double`/`float` results compiled with the
manifest flags (`-std=c11 -ffp-contract=off -O2`) on random plus
edge-case inputs (a few thousand vectors per width and op).

Mismatch classes, decided per vector from the bit patterns:

* both sides NaN -- match (payloads and quiet bits are
  implementation-defined, IEEE 754 leaves them open);
* exact bit equality -- match;
* anything else -- a finding, exit 1. Signed zeros are compared bit for
  bit: the model follows IEEE 754-2019 section 6.3 (`-0 + -0 = -0`,
  `x - x = +0`, xor signs for `*` and `/`). Until the lane after 166 a
  zero-sign difference was a tolerated "known cut" class; that class is
  gone, and the population carries every signed-zero pairing explicitly
  (`zero_pairs`), so a regression falls instead of hiding.

Comparisons (`lt`, `le`: C `<`, `<=`, model `flt`/`fle`) run on the same
pairs and are compared as 0/1 (NaN unordered on both sides).

Usage: python3 instrumente/pruefe-gleitkomma.py [--n N] [--seed S]
Requires built oleans (run ./lean-bau first) and `lake`/`cc`.
"""

import argparse
import os
import random
import shutil
import struct
import subprocess
import sys
import tempfile

DRIVER_SRC = r"""import Grammatik.Gleitkomma

open Gabbro.Grammatik.Gleitkomma

/-- Bit pattern as a value (inverse of `zuBits` on well-formed input). -/
def ausBits (F : Format) (n : Nat) : GBits F :=
  ⟨(n / 2 ^ (F.ebits + F.fracBits)) % 2 == 1,
    (n / 2 ^ F.fracBits) % 2 ^ F.ebits, n % 2 ^ F.fracBits⟩

def parseInt (s : String) : Int :=
  if s.startsWith "-" then -((s.drop 1).toNat! : Int)
  else ((s.toNat!) : Int)

def runLine (w : List String) : String :=
  match w with
  | [op, fmt, sa, sb] =>
    let F := if fmt == "32" then f32 else f64
    if op == "cvt" then toString (zuBits F (ofInt F (parseInt sa)))
    else
      let a := ausBits F sa.toNat!
      let b := ausBits F sb.toNat!
      if op == "lt" then (if flt F a b then "1" else "0")
      else if op == "le" then (if fle F a b then "1" else "0")
      else
      let r := if op == "add" then add F a b
        else if op == "sub" then sub F a b
        else if op == "mul" then mul F a b
        else div F a b
      toString (zuBits F r)
  | _ => "ERR"

def main (args : List String) : IO UInt32 := do
  match args with
  | [] => IO.eprintln "usage: treiber <vektoren>"; return 1
  | path :: _ =>
    let text <- IO.FS.readFile path
    for line in text.splitToList (· == '\n') do
      if line.trimAscii.isEmpty then continue
      IO.println (runLine (line.splitToList (· == ' ')))
    return 0
"""

C_SRC = r"""/* Differential counterpart: one line per vector, bits out. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <inttypes.h>

int main(int argc, char **argv) {
  FILE *f = fopen(argv[1], "r");
  if (!f) { fprintf(stderr, "cannot open %s\n", argv[1]); return 2; }
  char op[8], fmt[8], sa[64], sb[64];
  while (fscanf(f, "%7s %7s %63s %63s", op, fmt, sa, sb) == 4) {
    if (!strcmp(fmt, "64")) {
      if (!strcmp(op, "cvt")) {
        volatile int64_t n = (int64_t)strtoll(sa, 0, 10);
        volatile double r = (double)n;
        uint64_t u; memcpy(&u, &r, 8);
        printf("%" PRIu64 "\n", u);
      } else {
        uint64_t ua = strtoull(sa, 0, 10), ub = strtoull(sb, 0, 10);
        volatile double a, b;
        memcpy(&a, &ua, 8); memcpy(&b, &ub, 8);
        volatile double r = 0;
        if (!strcmp(op, "lt")) { printf("%d\n", a < b); continue; }
        if (!strcmp(op, "le")) { printf("%d\n", a <= b); continue; }
        if (!strcmp(op, "add")) r = a + b;
        else if (!strcmp(op, "sub")) r = a - b;
        else if (!strcmp(op, "mul")) r = a * b;
        else r = a / b;
        uint64_t u; memcpy(&u, &r, 8);
        printf("%" PRIu64 "\n", u);
      }
    } else {
      if (!strcmp(op, "cvt")) {
        volatile int64_t n = (int64_t)strtoll(sa, 0, 10);
        volatile float r = (float)n;
        uint32_t u; memcpy(&u, &r, 4);
        printf("%" PRIu32 "\n", u);
      } else {
        uint32_t ua = (uint32_t)strtoul(sa, 0, 10);
        uint32_t ub = (uint32_t)strtoul(sb, 0, 10);
        volatile float a, b;
        memcpy(&a, &ua, 4); memcpy(&b, &ub, 4);
        volatile float r = 0;
        if (!strcmp(op, "lt")) { printf("%d\n", a < b); continue; }
        if (!strcmp(op, "le")) { printf("%d\n", a <= b); continue; }
        if (!strcmp(op, "add")) r = a + b;
        else if (!strcmp(op, "sub")) r = a - b;
        else if (!strcmp(op, "mul")) r = a * b;
        else r = a / b;
        uint32_t u; memcpy(&u, &r, 4);
        printf("%" PRIu32 "\n", u);
      }
    }
  }
  fclose(f);
  return 0;
}
"""

WIDTHS = {32: (8, 23), 64: (11, 52)}

# Declared deadline for every executed step (the static half of FRIST).
FRIST = 900

# Pinned locale for every foreign tool call (GEBIETSSCHEMA).
GEBIET = {"LC_ALL": "C"}


def pat(fmt, s, bexp, frac):
    ebits, fbits = WIDTHS[fmt]
    return (s << (ebits + fbits)) | (bexp << fbits) | frac


def edges(fmt):
    ebits, fbits = WIDTHS[fmt]
    E = (1 << ebits) - 1
    FMAX = (1 << fbits) - 1
    out = [
        pat(fmt, 0, 0, 0), pat(fmt, 1, 0, 0),
        pat(fmt, 0, 0, 1), pat(fmt, 1, 0, 1),
        pat(fmt, 0, 0, 1 << (fbits - 1)), pat(fmt, 0, 0, FMAX),
        pat(fmt, 0, 1, 0), pat(fmt, 0, 1, 1),
        pat(fmt, 0, E - 1, 0), pat(fmt, 0, E - 1, 1),
        pat(fmt, 0, E - 1, FMAX), pat(fmt, 1, E - 1, FMAX),
        pat(fmt, 0, E, 0), pat(fmt, 1, E, 0),
        pat(fmt, 0, E, 1), pat(fmt, 1, E, 1),
        pat(fmt, 0, E, 1 << (fbits - 1)), pat(fmt, 0, E, FMAX),
        pat(fmt, 0, E, 1 << (fbits - 2)),
    ]
    if fmt == 64:
        for x in (1.0, -1.0, 2.0, 0.5, 0.1, 0.2, 0.3, 1.0 / 3.0,
                  2.0 ** -53, 1.0 + 2.0 ** -53, 2.0 ** 53 - 1, 2.0 ** 53,
                  2.0 ** 53 + 1, 2.0 ** 53 + 2, 2.0 ** -1022, 2.0 ** -1021,
                  2.0 ** -1074, 2.0 ** -1073, 2.0 ** 1023,
                  (2.0 ** 53 - 1) * 2.0 ** 971):
            out.append(struct.unpack("<Q", struct.pack("<d", x))[0])
    else:
        for x in (1.0, -1.0, 2.0, 0.5, 0.1, 1.0 / 3.0,
                  2.0 ** -24, 2.0 ** 24, 2.0 ** -126, 2.0 ** -149,
                  2.0 ** 127 * (2 - 2.0 ** -23)):
            out.append(struct.unpack("<I", struct.pack("<f", x))[0])
    mask = (1 << (ebits + fbits)) - 1
    return sorted({v & mask for v in out})


def rand_bits(rng, fmt):
    ebits, fbits = WIDTHS[fmt]
    return rng.getrandbits(ebits + fbits)


def rand_normal(rng, fmt):
    ebits, fbits = WIDTHS[fmt]
    E = (1 << ebits) - 1
    s = rng.getrandbits(1)
    bexp = rng.randint(1, E - 2)
    frac = rng.getrandbits(fbits)
    return pat(fmt, s, bexp, frac)


def zero_pairs(fmt):
    """Every pairing of the signed zeros with themselves and with a small
    set of signed partners (min subnormal, one, max finite, infinity, and
    the operand's own negation), so the section-6.3 rule is measured on
    every op, not left to the random draw."""
    ebits, fbits = WIDTHS[fmt]
    E = (1 << ebits) - 1
    FMAX = (1 << fbits) - 1
    one = pat(fmt, 0, (1 << (ebits - 1)) - 1, 0)
    base = [pat(fmt, 0, 0, 0), pat(fmt, 0, 0, 1), one,
            pat(fmt, 0, E - 1, FMAX), pat(fmt, 0, E, 0),
            pat(fmt, 0, 0x3F if fmt == 32 else 0x3FB, 0x1234)]
    sign = 1 << (ebits + fbits)
    vals = base + [v | sign for v in base]
    out = [(a, b) for a in vals for b in vals]
    return out


def build_vectors(n, seed):
    vecs = []
    for fmt in (32, 64):
        rng = random.Random("%d/%d" % (seed, fmt))
        ed = edges(fmt)
        pairs = []
        for i in range(n):
            r = rng.random()
            if r < 0.45:
                pairs.append((rand_bits(rng, fmt), rand_bits(rng, fmt)))
            elif r < 0.75:
                pairs.append((rand_normal(rng, fmt), rand_normal(rng, fmt)))
            elif r < 0.85:
                pairs.append((ed[i % len(ed)], rand_normal(rng, fmt)))
            elif r < 0.95:
                pairs.append((rand_normal(rng, fmt), ed[i % len(ed)]))
            else:
                pairs.append((ed[i % len(ed)], ed[(i * 7 + 1) % len(ed)]))
        pairs.extend(zero_pairs(fmt))
        ebits, fbits = WIDTHS[fmt]
        for _ in range(50):
            x = rand_normal(rng, fmt)
            pairs.append((x, x))
            pairs.append((x, x ^ (1 << (ebits + fbits))))
        for (a, b) in pairs:
            for op in ("add", "sub", "mul", "div", "lt", "le"):
                vecs.append((op, fmt, a, b))
        ints = [0, 1, -1, 2, -2, 2**24 - 1, 2**24, 2**24 + 1,
                -(2**24 - 1), 2**53 - 1, 2**53, 2**53 + 1, 2**53 + 2,
                -(2**53 - 1), 2**63 - 1, -(2**63 - 1), 2**62,
                2**32 - 1, 2**32, -(2**32)]
        for _ in range(80):
            ints.append(rng.randint(-(2**63 - 1), 2**63 - 1))
        for z in ints:
            vecs.append(("cvt", fmt, z, 0))
    return vecs

def is_nan(bits, fmt):
    ebits, fbits = WIDTHS[fmt]
    return ((bits >> fbits) & ((1 << ebits) - 1)) == (1 << ebits) - 1 \
        and (bits & ((1 << fbits) - 1)) != 0


def find_lake():
    p = shutil.which("lake")
    if p:
        return p
    cand = os.path.expanduser("~/.elan/bin/lake")
    if os.path.exists(cand):
        return cand
    print("ABBRUCH: lake not found (PATH or ~/.elan/bin/lake)")
    sys.exit(2)


def vergleiche(vecs, lout, cout):
    """Compare bit patterns. Returns (exact, both_nan, bad, broken).

    `bad` are findings (the tree has to change); `broken` are unparsable
    driver lines (the setup has to change -- exit 2, never a finding).
    """
    nok = nnan = 0
    bad, broken = [], []
    for i, (op, fmt, a, b) in enumerate(vecs):
        try:
            m, c = int(lout[i]), int(cout[i])
        except (ValueError, IndexError):
            broken.append((i, op, fmt, a, b,
                           lout[i] if i < len(lout) else "?",
                           cout[i] if i < len(cout) else "?"))
            continue
        if m == c:
            nok += 1
        elif op not in ("lt", "le") and is_nan(m, fmt) and is_nan(c, fmt):
            nnan += 1
        else:
            bad.append((i, op, fmt, a, b, m, c))
    return nok, nnan, bad, broken


def selbsttest():
    """Speech test in both directions: good data passes, corrupted data
    falls. Exits 0 only if both hold (a blind comparator would fail the
    second leg)."""
    vecs = [("add", 64, 4607182418800017408, 4607182418800017408),
            ("mul", 32, 1065353216, 1073741824),
            ("div", 64, 4607182418800017408, 4607182418800017408),
            ("cvt", 64, -7, 0)]
    good_lean = ["4607182418800017409", "1084227584", "4607182418800017408",
                 "13835058055282163712"]
    good_c = list(good_lean)
    nok, _, bad, broken = vergleiche(vecs, good_lean, good_c)
    if bad or broken or nok != len(vecs):
        print("Selbsttest GESCHEITERT: gute Daten fallen")
        return 1
    corrupt = list(good_lean)
    corrupt[0] = str(int(corrupt[0]) ^ 1)
    _, _, bad2, _ = vergleiche(vecs, corrupt, good_c)
    if len(bad2) != 1:
        print("Selbsttest GESCHEITERT: kaputte Daten fallen nicht")
        return 1
    # The retired signed-zero class must not come back: `-0` against `+0`
    # is a finding now.
    zvecs = [("add", 64, 1 << 63, 1 << 63)]
    _, _, bad3, _ = vergleiche(zvecs, [str(0)], [str(1 << 63)])
    if len(bad3) != 1:
        print("Selbsttest GESCHEITERT: Nullvorzeichen faellt nicht")
        return 1
    print("Selbsttest ok (gut faellt nicht, kaputt faellt)")
    return 0


def umgebung():
    env = dict(os.environ)
    env.update(GEBIET)
    return env


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=1500)
    ap.add_argument("--seed", type=int, default=166)
    ap.add_argument("--selbsttest", action="store_true")
    args = ap.parse_args()
    if args.selbsttest:
        sys.exit(selbsttest())
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    olean = os.path.join(root, "grammatik", ".lake", "build", "lib",
                         "lean", "Grammatik", "Gleitkomma.olean")
    if not os.path.exists(olean):
        print("ABBRUCH: Gleitkomma.olean missing -- run ./lean-bau first")
        sys.exit(2)
    vecs = build_vectors(args.n, args.seed)
    tmp = tempfile.mkdtemp(prefix="gleitkomma-")
    vpath = os.path.join(tmp, "vektoren.txt")
    with open(vpath, "w") as f:
        for (op, fmt, a, b) in vecs:
            f.write("%s %d %d %d\n" % (op, fmt, a, b))
    cpath = os.path.join(tmp, "dif.c")
    with open(cpath, "w") as f:
        f.write(C_SRC)
    cbin = os.path.join(tmp, "dif")
    try:
        r = subprocess.run(["cc", "-std=c11", "-ffp-contract=off", "-O2",
                            "-Wall", "-Wextra", "-o", cbin, cpath],
                           capture_output=True, text=True, timeout=FRIST,
                           env=umgebung())
    except subprocess.TimeoutExpired:
        print("ABBRUCH: cc reached the deadline")
        sys.exit(2)
    if r.returncode != 0:
        print("ABBRUCH: cc failed:\n" + r.stderr)
        sys.exit(2)
    dpath = os.path.join(tmp, "treiber.lean")
    with open(dpath, "w") as f:
        f.write(DRIVER_SRC)
    lake = find_lake()
    try:
        r = subprocess.run([cbin, vpath], capture_output=True, text=True,
                           timeout=FRIST, env=umgebung())
    except subprocess.TimeoutExpired:
        print("ABBRUCH: C driver reached the deadline")
        sys.exit(2)
    if r.returncode != 0:
        print("ABBRUCH: C driver failed:\n" + r.stderr)
        sys.exit(2)
    cout = r.stdout.split()
    try:
        r = subprocess.run([lake, "env", "lean", "--run", dpath, vpath],
                           capture_output=True, text=True, timeout=FRIST,
                           env=umgebung(),
                           cwd=os.path.join(root, "grammatik"))
    except subprocess.TimeoutExpired:
        print("ABBRUCH: Lean driver reached the deadline")
        sys.exit(2)
    if r.returncode != 0:
        print("ABBRUCH: Lean driver failed:\n" + r.stderr[-3000:])
        sys.exit(2)
    lout = r.stdout.split()
    if len(cout) != len(vecs) or len(lout) != len(vecs):
        print("ABBRUCH: line count mismatch (truncated population): "
              "%d vectors, %d C, %d Lean" % (len(vecs), len(cout), len(lout)))
        print("evidence kept in " + tmp)
        sys.exit(2)
    nok, nnan, bad, broken = vergleiche(vecs, lout, cout)
    if broken:
        print("ABBRUCH: %d unparsable driver lines, first: %s"
              % (len(broken), broken[0]))
        print("evidence kept in " + tmp)
        sys.exit(2)
    print("vectors: %d  exact: %d  both-NaN: %d  MISMATCH: %d"
          % (len(vecs), nok, nnan, len(bad)))
    for (i, op, fmt, a, b, m, c) in bad[:20]:
        print("  MISMATCH #%d: %s f%d a=%d b=%d lean=%d c=%d"
              % (i, op, fmt, a, b, m, c))
    if bad:
        print("evidence kept in " + tmp)
        sys.exit(1)
    shutil.rmtree(tmp, ignore_errors=True)
    print("ok -- no finding (signed zeros compared bit for bit)")


if __name__ == "__main__":
    main()
