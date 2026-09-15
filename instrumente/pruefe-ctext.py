#!/usr/bin/env python3
"""**The pinned emitted C text IS what the emitter writes -- byte for byte.**

    ./instrumente/pruefe-ctext.py [--binary PATH] [--allow-stale] [--probe]

WHY THIS EXISTS
---------------
`grammatik/Grammatik/CText104.lean` and `CText108.lean` pin the emitted C of a chain
program as Lean data and prove, by kernel reduction, that the Lean C parser reads it as
the very unit the correspondence certificate elaborates to (assumption A2 of
`dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md` §6.4, discharged). That proof is about the
PINNED TEXT. If the emitter changes and the pin does not, the theorem stays true and stops
being about this tree -- *a stale paste is a different program*, the same failure
`zaehle-kette.py` guards against on the Gabbro side (the source literal `src104real`).

So this guardian re-emits every pinned program with the built binary and compares the
bytes. It is the only reader that closes the loop between `emit.rs` and the Lean pin.

WHAT IT READS
-------------
A file under `grammatik/Grammatik/` carries, in its header,

    CTEXT-PIN <program>.gab <name>

and, around the definition of `<name>`, the two block markers

    -- CTEXT-BEGIN <name>
    def <name> : List (List Char) := [ "…".toList, "…".toList, … ]
    -- CTEXT-END <name>

The text is the concatenation of the string literals in the block, in order. The text is
a LIST OF LINES and not one literal for a measured reason (the kernel cost note in
`Grammatik/CParser/CLexer.lean`); the guardian does not care how it is cut, only what the
bytes are.

THE VERDICT, AND THE THREE EXITS
--------------------------------
    0   green -- every pin is the emitter's output, byte for byte
    1   a finding -- a pin differs, and the first differing byte is printed
    2   ABBRUCH -- nothing was measured: no binary, a stale binary, no pin at all,
        or an `emit` that did not answer inside the deadline

The work count stands beside the verdict (`N pins, M bytes`), so a green run over nothing
is not a green run (`pruefe-waechter.py` requirement 4).
"""
import argparse
import os
import pathlib
import re
import subprocess
import sys

W = pathlib.Path(__file__).resolve().parent.parent
GRAMMATIK = W / "grammatik" / "Grammatik"

# A hang looks like "still running", not like a finding: every `emit` runs under FRIST.
FRIST = 120

MARKE = re.compile(r"CTEXT-PIN\s+(\S+\.gab)\s+(\w+)")
LITERAL = re.compile(r'"((?:[^"\\]|\\.)*)"\.toList')

ESCAPE = {"n": "\n", "t": "\t", "r": "\r", "\\": "\\", '"': '"', "'": "'"}


def umgebung():
    """`LC_ALL=C`: a tool that measures its own locale looks plausible doing it."""
    env = dict(os.environ)
    env["LC_ALL"] = "C"
    return env


def lean_unescape(body):
    """The value of a Lean string literal's body. An escape this reader does not know is
    refused (`None`) -- never guessed into a character."""
    out = []
    i = 0
    while i < len(body):
        c = body[i]
        if c != "\\":
            out.append(c)
            i += 1
            continue
        i += 1
        if i >= len(body):
            return None
        e = body[i]
        if e in ESCAPE:
            out.append(ESCAPE[e])
            i += 1
        elif e == "x" and i + 2 < len(body):
            out.append(chr(int(body[i + 1:i + 3], 16)))
            i += 3
        elif e == "u" and i + 4 < len(body):
            out.append(chr(int(body[i + 1:i + 5], 16)))
            i += 5
        else:
            return None
    return "".join(out)


def block_text(quelle, name):
    """The pinned text of `name` in the Lean source `quelle`, or `None`."""
    m = re.search(r"-- CTEXT-BEGIN " + re.escape(name) + r"\n(.*?)-- CTEXT-END "
                  + re.escape(name), quelle, re.S)
    if not m:
        return None
    stuecke = []
    for lit in LITERAL.findall(m.group(1)):
        s = lean_unescape(lit)
        if s is None:
            return None
        stuecke.append(s)
    return "".join(stuecke)


def pins():
    """`[(lean file, program, name)]` for every pin in the tree."""
    aus = []
    for p in sorted(GRAMMATIK.rglob("*.lean")):
        t = p.read_text(encoding="utf-8", errors="replace")
        for prog, name in MARKE.findall(t):
            aus.append((p, prog, name))
    return aus


def sprechprobe():
    """**The speech test, in both directions, on a planted block** -- a guardian that
    cannot go red measures nothing (`pruefe-waechter.py` requirement 2).

    Direction one: a block whose literals spell the text is read as that text. Direction
    two: the same block with ONE byte changed is read as a different text, and the
    comparison below says so. Both over an invented source, so the probe does not measure
    how well this tree fits this reader.
    """
    gut = ('-- CTEXT-BEGIN zeilenX\ndef zeilenX : List (List Char) :=\n'
           '  ["static void f(void) {\\n".toList,\n   "    return;\\n".toList,\n'
           '   "}\\n".toList]\n-- CTEXT-END zeilenX\n')
    schlecht = gut.replace("return;", "return ;")
    echt = "static void f(void) {\n    return;\n}\n"
    return [
        ("a pinned block is read as its bytes", block_text(gut, "zeilenX") == echt),
        ("one byte changed is a DIFFERENT text", block_text(schlecht, "zeilenX") != echt),
        ("an unknown escape is refused, not guessed", lean_unescape("a\\q") is None),
        ("a missing block is no text", block_text(gut, "zeilenY") is None),
    ]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--binary", default=str(W / "target" / "debug" / "gabbro"))
    ap.add_argument("--allow-stale", action="store_true")
    ap.add_argument("--probe", action="store_true", help="only the speech test")
    args = ap.parse_args()

    probe = sprechprobe()
    for was, ok in probe:
        print(f"  probe: {'ok  ' if ok else 'FAIL'} {was}")
    if not all(ok for _, ok in probe):
        print("ABBRUCH: the speech test of this guardian failed -- it measured nothing")
        return 2
    if args.probe:
        print(f"pruefe-ctext: speech test only, {len(probe)} of {len(probe)} directions ok")
        return 0

    binary = pathlib.Path(args.binary)
    if not binary.exists():
        print(f"ABBRUCH: no binary at {binary} -- build it (on ki-pc-fisch-101) "
              f"or pass --binary")
        return 2
    stand = binary.stat().st_mtime
    neuer = sorted(q for q in W.glob("crates/*/src/*.rs") if q.stat().st_mtime > stand)
    if neuer and not args.allow_stale:
        print(f"ABBRUCH: the binary is OLDER than {len(neuer)} source file(s) under crates/ "
              f"(first: {neuer[0].relative_to(W)}) -- it measures another emitter")
        print("  (build it, or pass --allow-stale to measure that binary anyway)")
        return 2

    marken = pins()
    if not marken:
        print("ABBRUCH: no CTEXT-PIN marker under grammatik/Grammatik -- nothing to measure")
        return 2

    befunde = 0
    bytes_geprueft = 0
    for quelle, prog, name in marken:
        text = block_text(quelle.read_text(encoding="utf-8", errors="replace"), name)
        if text is None:
            print(f"  {name}: BEFUND -- no readable CTEXT block in "
                  f"{quelle.relative_to(W)}")
            befunde += 1
            continue
        pfad = W / prog
        if not pfad.exists():
            print(f"  {name}: BEFUND -- the program {prog} does not exist")
            befunde += 1
            continue
        try:
            r = subprocess.run([str(binary), "emit", str(pfad)], capture_output=True,
                               text=True, cwd=W, timeout=FRIST, env=umgebung())
        except (OSError, subprocess.TimeoutExpired):
            print(f"ABBRUCH: `gabbro emit {prog}` did not answer inside {FRIST} s")
            return 2
        if r.returncode != 0 or not r.stdout:
            print(f"  {name}: BEFUND -- the emitter refused {prog} (exit {r.returncode})")
            befunde += 1
            continue
        bytes_geprueft += len(text)
        if r.stdout == text:
            print(f"  {name}: ok -- {len(text)} bytes, byte-identical to "
                  f"`gabbro emit {prog}`")
            continue
        befunde += 1
        stelle = next((i for i, (a, b) in enumerate(zip(text, r.stdout)) if a != b),
                      min(len(text), len(r.stdout)))
        print(f"  {name}: BEFUND -- the pin in {quelle.relative_to(W)} is NOT what the "
              f"emitter writes for {prog}")
        print(f"      pin {len(text)} bytes, emitted {len(r.stdout)} bytes, "
              f"first difference at byte {stelle}")
        print(f"      pin     …{text[max(0, stelle - 40):stelle + 20]!r}")
        print(f"      emitted …{r.stdout[max(0, stelle - 40):stelle + 20]!r}")

    print(f"pruefe-ctext: {len(marken) - befunde} of {len(marken)} pins byte-identical, "
          f"{bytes_geprueft} bytes compared, binary {binary}")
    print("== CTEXT: " + ("GRUEN" if befunde == 0 else f"{befunde} BEFUNDE") + " ==")
    return 1 if befunde else 0


if __name__ == "__main__":
    sys.exit(main())
