#!/usr/bin/env python3
"""Rewrite the LINUX syscall declarations of a Gabbro source from x86_64 to aarch64.

usage: to_aarch64.py IN.gab OUT.gab

Only the Linux gates change (a literal `abi linux arch x86_64 number N ...` gate, or a
`target linux_x86_64 abi linux arch x86_64 { ... }` block); `abi metal` blocks and every
other x86_64 sentence stay. This is a measurement aid, not a tool of the compiler: it maps
the x86_64 call numbers the corpus uses onto the AArch64 numbers of the agreed ABI and the
x86 argument registers onto x0-x5.
"""
import re
import sys

NUM = {0: 63, 1: 64, 2: 56, 3: 57, 9: 222, 10: 226, 11: 215, 28: 233, 39: 172, 56: 220,
       60: 93, 202: 98, 24: 124, 228: 113, 231: 94, 1000: 1000}
REG = {"rdi": "x0", "rsi": "x1", "rdx": "x2", "r10": "x3", "r8": "x4", "r9": "x5", "rax": "x0"}


def gate(seg: str) -> str:
    seg = seg.replace("arch x86_64", "arch aarch64")
    seg = re.sub(r"number (\d+)", lambda m: "number %d" % NUM[int(m.group(1))], seg)
    seg = re.sub(r"\b(rdi|rsi|rdx|r10|r8|r9|rax)\b", lambda m: REG[m.group(1)], seg)
    seg = re.sub(r"clobbers \{[^}]*\}", "clobbers { }", seg)
    return seg


def main() -> None:
    src = open(sys.argv[1]).read()
    out = []
    pos = 0
    # target blocks of the linux ABI
    pat = re.compile(r"target linux_x86_64 abi linux arch x86_64 \{.*?\n\}", re.S)
    for m in pat.finditer(src):
        out.append(src[pos:m.start()])
        out.append(gate(m.group(0)).replace("target linux_x86_64", "target linux_aarch64"))
        pos = m.end()
    out.append(src[pos:])
    src = "".join(out)
    src = src.replace("target linux_x86_64;", "target linux_aarch64;")
    # literal gates: `abi linux arch x86_64 number N` through the `assume ... ;` that ends them
    lit = re.compile(r"abi linux arch x86_64 number \d+.*?;", re.S)
    src = lit.sub(lambda m: gate(m.group(0)), src)
    open(sys.argv[2], "w").write(src)


main()
