#!/usr/bin/env python3
"""Proof lines per line of user code, for every unit that has a `programmlogik/Proofs/<Unit>.lean`
(GabbroV lane, 2026-09-29).  Writes the table `messung/GABBROV-PROOF-RATIO.md` reads from.

THE COUNTING RULE (written down because a ratio without one is a number without a meaning):

  code line   a line of the unit's `.gab` file that is neither empty nor a `--` comment line.
              A trailing `-- …` comment does not make a line a comment line.  `module … {`
              and `}` count: they are lines of the program.
  proof line  a line of `Proofs/<Unit>.lean` that is neither empty, nor a comment line (`--`,
              or inside a `/- … -/` block, doc comments included), nor a header line
              (`import`, `open`, `set_option`, `namespace`, `end`).
  library     the proof lines BEFORE the first theorem named `*_done`: definitions and lemmas
              that are not one duty's proof (the semantic layer of the firewall).  A unit
              without a library has 0.
  duty proof  the proof lines from the first `*_done` theorem on: the argument for each
              `_statement` the generator left to a person.

  ratio       (library + duty proof) / code -- the number the NLnet proposal quotes -- and,
              beside it, duty proof / code: what a user pays who does not need the library.

What is NOT counted: the generated `Duty/<Unit>.lean` (the generator writes it, the person
does not read it as an obligation to write), the model `Gabbro/Body.lean`, and every tactic
of it.  What IS counted although a person did not type it by hand: nothing.
"""
import glob, os, re, sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))

def code_lines(path):
    n = 0
    for l in open(path, encoding="utf-8"):
        s = l.strip()
        if s and not s.startswith("--"):
            n += 1
    return n

def proof_lines(path):
    """(library, duty) proof line counts."""
    lib = duty = 0
    in_block = 0
    in_duty = False
    for l in open(path, encoding="utf-8"):
        s = l.strip()
        # block comments (they nest in Lean; the files here do not nest, but count anyway)
        if in_block:
            in_block += s.count("/-") - s.count("-/")
            continue
        if s.startswith("/-"):
            in_block = 1 + s[2:].count("/-") - s.count("-/")
            if in_block < 0:
                in_block = 0
            continue
        if not s or s.startswith("--"):
            continue
        if re.match(r"(import|open|set_option|namespace|end)\b", s):
            continue
        if re.match(r"theorem \w+_done\b", s):
            in_duty = True
        if in_duty:
            duty += 1
        else:
            lib += 1
    return lib, duty

def unit_source(name):
    """The `.gab` a `Duty<Name>` module was made from: the module name is `module_name(path)`;
    look the file up by walking the corpus and matching the generated Duty file's own header."""
    duty = os.path.join(ROOT, "programmlogik", "Duty", name + ".lean")
    if not os.path.isfile(duty):
        return None
    m = re.search(r"@duty \d+\s+(\S+\.gab)", open(duty, encoding="utf-8").read())
    return os.path.join(ROOT, m.group(1)) if m else None

def main():
    rows = []
    for p in sorted(glob.glob(os.path.join(ROOT, "programmlogik", "Proofs", "*.lean"))):
        name = os.path.basename(p)[:-5]
        src = unit_source(name)
        if src is None or not os.path.isfile(src):
            print(f"# {name}: no source found (run `gabbro prove` on the unit first)", file=sys.stderr)
            continue
        lib, duty = proof_lines(p)
        code = code_lines(src)
        rows.append((name, os.path.relpath(src, ROOT), code, lib, duty))
    print("| unit | source | code | library | duty proof | ratio (all/code) | ratio (duty/code) |")
    print("|---|---|--:|--:|--:|--:|--:|")
    tc = tl = td = 0
    for name, src, code, lib, duty in rows:
        tc += code; tl += lib; td += duty
        print(f"| `{name}` | `{src}` | {code} | {lib} | {duty} | {(lib + duty) / code:.2f} | {duty / code:.2f} |")
    if rows:
        print(f"| **total** | | {tc} | {tl} | {td} | {(tl + td) / tc:.2f} | {td / tc:.2f} |")

if __name__ == "__main__":
    main()
