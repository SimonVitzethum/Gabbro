#!/usr/bin/env python3
"""Derive bibliothek/linux/linux-aarch64.gab from bibliothek/linux/linux.gab (run once; the
result is committed and hand-reviewed, this script is the record of what differs).

usage: mk_linux_aarch64.py linux.gab linux-aarch64.gab
"""
import re
import sys

src = open(sys.argv[1]).read()

NUM = {9: 222, 10: 226, 1: 64, 231: 94, 28: 233, 24: 124, 56: 220, 60: 93, 202: 98}
NAME = {9: "mmap", 10: "mprotect", 1: "write", 231: "exit_group", 28: "madvise",
        24: "sched_yield", 56: "clone", 60: "exit", 202: "futex"}
REG = {"rdi": "x0", "rsi": "x1", "rdx": "x2", "r10": "x3", "r8": "x4", "r9": "x5", "rax": "x0"}

# 1. the gates
def gate(m):
    seg = m.group(0)
    nr = int(re.search(r"number (\d+)", seg).group(1))
    seg = seg.replace("arch x86_64", "arch aarch64")
    seg = re.sub(r"number \d+", "number %d" % NUM[nr], seg)
    if nr == 56:
        # AArch64 raw clone(flags, stack, parent_tid, tls, child_tid): the child's tid word
        # travels in x4, not in the fourth register (x86_64 has it in r10, tls in r8).
        seg = seg.replace("regs in { rdi = flaggen, rsi = spitze, rdx = eltern, r10 = kind }",
                          "regs in { x0 = flaggen, x1 = spitze, x2 = eltern, x4 = kind }")
        seg = seg.replace("stack rsi", "stack x1")
    seg = re.sub(r"\b(rdi|rsi|rdx|r10|r8|r9|rax)\b", lambda k: REG[k.group(1)], seg)
    seg = re.sub(r"clobbers \{[^}]*\}", "clobbers { }", seg)
    return seg

src = re.sub(r"abi linux arch x86_64 number \d+.*?;", gate, src, flags=re.S)

# 2. the assumptions' sentences
def assume(m):
    seg = m.group(0)
    nr = re.search(r"\(number (\d+)\)", seg)
    if nr:
        n = int(nr.group(1))
        seg = seg.replace("Linux x86_64", "Linux AArch64")
        seg = seg.replace("(number %d)" % n, "(number %d)" % NUM[n])
    seg = seg.replace("it destroys only rcx and r11", "it destroys no register but x0")
    seg = seg.replace("and destroys only rcx and r11", "and destroys no register but x0")
    seg = seg.replace("whose rsp is the address", "whose sp is the address")
    seg = seg.replace("the caller's except rax", "the caller's except x0")
    # the probes: a probe for the x86_64 claim does not falsify this one
    seg = re.sub(r"falsifier (sonde_os_\w+)", r"falsifier \1_a64", seg)
    return seg

src = re.sub(r"assume \w+\n    \"[^\"]*\"\n    falsifier \w+;", assume, src)
src = re.sub(r"assume (linux_os_\w+) falsifier (sonde_os_\w+);",
             r"assume \1 falsifier \2_a64;", src)
open(sys.argv[2], "w").write(src)
