#!/usr/bin/env python3
"""instrumente/zaehle-c.py -- HOW MUCH HANDWRITTEN C/ASM ENDS UP IN A FINISHED GABBRO BINARY,
per target, as one number each (C-free lane, C0; the rule is AGENTS.md section 3, 2026-09-30:
"no handwritten C in a finished Gabbro binary, as far as possible").

WHAT IS COUNTED. For every scenario of a target, `gabbro build --c-liste <manifest>` lists the
handwritten files the build puts into that product -- read out of the SAME lists the build
compiles from (`bau.rs::handgeschrieben`: the unit's own `.c`/`.h`, the `kmod` and `metal`
runtime sources, the hosted runtime a generated driver is linked against), never a guess of
this script. Lines are counted once per file per target (a file that stands in three
scenarios is one file). The emitted C and the generated drivers are Gabbro's output and are
not counted.

HOSTED ONLY, the second number: with `--baue` every hosted scenario is built and the
undefined symbols of the linked program (or of the object and its foreign objects, for an
`object` unit) are listed with `nm -u` -- the libc names the finished thing still imports.
The toolchain's own names (`__cxa_finalize`, `_GLOBAL_OFFSET_TABLE_`, ...) are subtracted.
Kernel-module and bare-metal scenarios build only under `--baue --alle` (they need the
kernel build tree and take longer); their C count is the listing, which needs neither.

SPRECHPROBE (`--sprech`, both ways). A planted extra `.c` file is added to the first scenario
of every target: the target's number MUST rise by exactly its line count; the unplanted run
MUST give the base number back. A counter that cannot see a planted file has measured
nothing, and one that keeps seeing it after removal counted a stale list.

    instrumente/zaehle-c.py [--baue [--alle]] [--sprech] [--json]

Exit 0: the run measured. It does NOT say the numbers are zero -- that is what the
acceptance points of the lane ask for, read off the report.
"""
import os
import re
import subprocess
import sys
import tempfile

W = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
GABBRO = os.path.join(W, "target", "release", "gabbro")
ARBEIT = os.environ.get(
    "C0_ARBEIT", os.path.join(os.path.dirname(W), "gabbro-lane-c", "scratch", "c0"))

TOOLCHAIN = {
    "__cxa_finalize", "__gmon_start__", "_ITM_deregisterTMCloneTable",
    "_ITM_registerTMCloneTable", "__libc_start_main", "_GLOBAL_OFFSET_TABLE_",
    "__stack_chk_fail", "__TMC_END__", "_init", "_fini", "__dso_handle",
}

# Scenario tables. Each is (name, manifest body). `{W}` is this tree, `{OUT}` the build dir.
# The kernel build tree is named by the environment, never baked in.
KBUILD = os.environ.get("KBUILD", "/lib/modules/%s/build" % os.uname().release)
BINDUNG_LINUX = "  {W}/bibliothek/linux/linux.gab\n"
BINDUNG_KMOD = "  {W}/bibliothek/linux-kmod/linux-kmod.gab\n  {W}/bibliothek/linux-kmod/linux-kmod.c\n"
CC = "compiler cc -std=c11 -O0 -Wall -Wextra -Werror\nout {OUT}\n"

NOLIBC = ("compiler cc -std=c11 -O0 -ffreestanding -fno-stack-protector -fno-pie -Wall -Wextra -Werror\n"
          "out {OUT}\nnolibc\n")

SZENARIEN = {
    "hosted": [
        ("druckt", CC + "unit hallo program\n  {W}/beispiele/63-druckt.gab\n", "hallo"),
        ("puffer", CC + "unit puffer program\n  {W}/beispiele/64-writes-a-whole-buffer.gab\n", "puffer"),
        ("prozess172", NOLIBC + "unit prozess program\n  {W}/beispiele/172-prozess-ohne-libc.gab\n", "prozess"),
        ("abbruch173", NOLIBC + "unit abbruch program\n  {W}/beispiele/173-abbruch-ohne-libc.gab\n", "abbruch"),
        ("osprobe", CC.replace("-Werror", "-Werror -I {W}/laufzeit") +
         "unit osprobe object\n  {W}/messung/proben/os-bindung/os-probe.gab\n" + BINDUNG_LINUX +
         "  {W}/messung/proben/os-bindung/melde.c\n", "osprobe"),
    ],
    "kmod": [
        ("halde", CC + "kmod {W}/laufzeit/kmodul " + KBUILD + "\nunit gabbro_halde module laden entladen\n"
         "  {W}/messung/proben/kmodul/halde-treiber.gab\n  {W}/messung/proben/kmodul/melde.c\n" + BINDUNG_KMOD,
         "gabbro_halde"),
        ("takt", CC + "kmod {W}/laufzeit/kmodul " + KBUILD + "\nunit gabbro_takt module laden entladen\n"
         "  {W}/messung/proben/kmodul/sperre-takt.gab\n  {W}/messung/proben/kmodul/takt.c\n" + BINDUNG_KMOD,
         "gabbro_takt"),
    ],
    "metal": [
        ("pool157", CC + "metal {W}/laufzeit/metall\nunit einheit object\n  {W}/beispiele/157-worker-pool.gab\n",
         "einheit"),
        ("eintritt59", CC + "metal {W}/laufzeit/metall\nunit einheit object\n"
         "  {W}/beispiele/59-eintritt-nimmt-maskierte-sperre.gab\n", "einheit"),
    ],
}


def manifest_schreiben(ziel, szen, extra=None):
    name, text, _ = szen
    out = os.path.join(ARBEIT, ziel, name, "out")
    os.makedirs(out, exist_ok=True)
    body = text.replace("{W}", W).replace("{OUT}", out)
    if extra:
        body = body.rstrip("\n") + "\n  " + extra + "\n"
    pfad = os.path.join(ARBEIT, ziel, name, "bau")
    with open(pfad, "w") as f:
        f.write(body)
    return pfad, out


def liste(pfad):
    """The `c-file` lines of `gabbro build --c-liste`, as {path: lines}."""
    r = subprocess.run([GABBRO, "build", "--c-liste", pfad], capture_output=True, text=True, cwd=W)
    if r.returncode != 0:
        sys.exit("zaehle-c: `gabbro build --c-liste %s` failed:\n%s%s" % (pfad, r.stdout, r.stderr))
    dateien = {}
    for z in r.stdout.splitlines():
        m = re.match(r"c-file (\S+) (\S+) (\d+) (.*)$", z)
        if m:
            dateien[os.path.normpath(os.path.join(W, m.group(4)))] = (int(m.group(3)), m.group(2))
    return dateien


def zahl(ziel, extra_fuer_erstes=None):
    alle = {}
    for i, s in enumerate(SZENARIEN[ziel]):
        pfad, _ = manifest_schreiben(ziel, s, extra_fuer_erstes if i == 0 else None)
        alle.update(liste(pfad))
    return alle


def nm_liste(pfad, was):
    r = subprocess.run(["nm", "--format=posix", was, pfad], capture_output=True, text=True)
    return {z.split()[0].split("@")[0] for z in r.stdout.splitlines() if z.split()}


def nm_u(pfade):
    """What the linked union of `pfade` still needs from outside: undefined minus defined."""
    fehlt, da = set(), set()
    for p in pfade:
        fehlt |= nm_liste(p, "-u")
        da |= nm_liste(p, "--defined-only")
    return {n for n in fehlt - da if n and n not in TOOLCHAIN}


def laufzeit_objekte(einheit, out, dateien):
    """The objects of the generated driver and the hosted runtime the build does not compile
    itself -- what a user links by hand, per the driver's own header comment."""
    objs = []
    treiber = os.path.join(out, einheit + ".treiber.c")
    if os.path.isfile(treiber):
        o = os.path.join(out, einheit + ".treiber.o")
        r = subprocess.run(["cc", "-std=c11", "-I", os.path.join(W, "laufzeit"), "-I", out,
                            '-DEINHEIT_INCLUDE="%s.c"' % einheit, "-c", "-o", o, treiber],
                           capture_output=True, text=True)
        if r.returncode == 0:
            objs.append(o)
        else:
            print("  (driver did not compile: %s)" % r.stderr[-300:])
    for p, (_, h) in dateien.items():
        if h == "hosted-runtime" and p.endswith(".c"):
            o = os.path.join(out, os.path.basename(p) + ".o")
            r = subprocess.run(["cc", "-std=c11", "-I", os.path.join(W, "laufzeit"), "-c", "-o", o, p],
                               capture_output=True, text=True)
            if r.returncode == 0:
                objs.append(o)
    return objs


def baue(ziel, szen):
    pfad, out = manifest_schreiben(ziel, szen)
    r = subprocess.run([GABBRO, "build", pfad], capture_output=True, text=True, cwd=W)
    return r.returncode == 0, out, (r.stdout + r.stderr)


def main():
    a = sys.argv[1:]
    if not os.path.exists(GABBRO):
        sys.exit("zaehle-c: NOT RUN -- no release binary at %s (cargo build --release)" % GABBRO)
    os.makedirs(ARBEIT, exist_ok=True)
    gesamt = {}
    print("== C0: handwritten C/asm per finished product, by target ==")
    for ziel in SZENARIEN:
        d = zahl(ziel)
        gesamt[ziel] = sum(z for z, _ in d.values())
        print("  %-7s %5d lines in %2d file(s)" % (ziel, gesamt[ziel], len(d)))
        for p, (z, h) in sorted(d.items(), key=lambda kv: -kv[1][0]):
            print("            %5d  %-14s %s" % (z, h, os.path.relpath(p, W)))
    if "--baue" in a:
        print("== hosted imports (nm -u over the built products, toolchain names removed) ==")
        libc = set()
        for s in SZENARIEN["hosted"]:
            ok, out, log = baue("hosted", s)
            if not ok:
                print("  %-8s BUILD FAILED\n%s" % (s[0], log[-600:]))
                continue
            name = s[2]
            kandidaten = [os.path.join(out, name)] if os.path.isfile(os.path.join(out, name)) else \
                [os.path.join(out, f) for f in sorted(os.listdir(out)) if f.endswith(".o")]
            pfad_m = os.path.join(ARBEIT, "hosted", s[0], "bau")
            kandidaten += laufzeit_objekte(name, out, liste(pfad_m))
            n = nm_u(kandidaten)
            libc |= n
            print("  %-8s %2d import(s): %s" % (s[0], len(n), " ".join(sorted(n)) or "-"))
        print("  hosted libc imports, distinct over all scenarios: %d" % len(libc))
        if "--alle" in a:
            for ziel in ("kmod", "metal"):
                for s in SZENARIEN[ziel]:
                    ok, out, log = baue(ziel, s)
                    print("  %-6s %-11s %s" % (ziel, s[0], "built" if ok else "BUILD FAILED\n" + log[-400:]))
    if "--sprech" in a:
        print("== Sprechprobe: plant a C file, then take it away ==")
        gut = True
        with tempfile.TemporaryDirectory(dir=ARBEIT) as td:
            plant = os.path.join(td, "geplant.c")
            with open(plant, "w") as f:
                f.write("int geplant(void)\n{\n    return 7;\n}\n")
            for ziel in SZENARIEN:
                mit = sum(z for z, _ in zahl(ziel, plant).values())
                ohne = sum(z for z, _ in zahl(ziel).values())
                # A metal/kmod scenario lists the planted file only as a unit file; hosted too.
                ok = (mit - gesamt[ziel] == 4) and ohne == gesamt[ziel]
                gut &= ok
                print("  %-7s base %d, planted %d (+%d, want +4), removed %d  %s" % (
                    ziel, gesamt[ziel], mit, mit - gesamt[ziel], ohne, "ok" if ok else "FAILS"))
        if not gut:
            print("SPRECHPROBE FAILS -- the counter does not see what it should")
            sys.exit(1)
        print("  Sprechprobe: ok (planted file seen in every target, gone when removed)")
    print("== C0 total: " + ", ".join("%s %d" % (k, v) for k, v in gesamt.items()) + " ==")


if __name__ == "__main__":
    main()
