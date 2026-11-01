#!/usr/bin/env python3
"""Lean module system migration and check (owner rule, 2026-11-01: every Lean source file is a `module`).

    lean-module.py --check [PATH...]     list the tracked Lean files that are not modules; exit 1 when there is one
    lean-module.py --meta-imports [PATH...]  add `meta import X` for every import of a module that has `#eval`/`run_cmd`
    lean-module.py --apply [PATH...]     migrate the given files / folders in place (default: every tracked Lean file)
        --private-imports                keep `import` instead of turning it into `public import`
        --no-expose                      open `public section` without `@[expose]`

A file is migrated to the form

    <leading comments>
    module
    public import A
    public import B
    @[expose] public section
    <the file, unchanged>

`public import` keeps the transitive import closure every file saw before (so nothing that compiled stops
compiling); `@[expose] public section` keeps every definition unfoldable for `decide`/`rfl`/`simp`/`unfold` in the
importing files. Theorem proofs are never exposed, so an edit that only changes proofs leaves the public `.olean`
unchanged and Lake does not rebuild the dependents. Narrowing (`lake shake --fix` for the imports, dropping `@[expose]`
where no dependent unfolds a definition) is a separate step after a green build.

The header is read with a tokenizer for Lean comments (`--` and nested `/- -/`), never with a line regex over the
whole file, so an `import` inside a comment is not touched. UTF-8 throughout; files are written back byte-for-byte
except the inserted lines."""
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
# Lake's own configuration files are Lean but not modules.
NOT_MODULES = {"lakefile.lean"}
IMPORT = re.compile(r"[ \t]*import[ \t]+([^\s]+)[ \t]*([^\n]*)")


def skip_trivia(t, i):
    """Index after whitespace and comments starting at `i` (stops at a `/-!` or `/--` doc comment: those are commands)."""
    n = len(t)
    while i < n:
        c = t[i]
        if c in " \t\r\n":
            i += 1
        elif t.startswith("--", i):
            j = t.find("\n", i)
            i = n if j < 0 else j
        elif t.startswith("/-", i) and not t.startswith(("/-!", "/--"), i):
            depth, i = 1, i + 2
            while i < n and depth:
                if t.startswith("/-", i): depth += 1; i += 2
                elif t.startswith("-/", i): depth -= 1; i += 2
                else: i += 1
        else:
            break
    return i


def header(t):
    """(index of `module` insertion, [(start, end, name, rest)] of the import lines, index after the last import)."""
    i = skip_trivia(t, 0)
    first = i
    imports, after = [], i
    if t.startswith("module", i) and not t[i + 6:i + 7].isalnum():
        return None
    while True:
        m = IMPORT.match(t, i)
        if not m or not (i == 0 or t[i - 1] == "\n" or t[i - 1] in " \t"):
            break
        end = m.end()
        imports.append((i, end, m.group(1), m.group(2)))
        after = end
        i = skip_trivia(t, end)
    return first, imports, after


def migrate(t, public=True, expose=True):
    h = header(t)
    if h is None:
        return None
    first, imports, after = h
    body = t[first:after]
    for s, e, name, rest in reversed(imports):
        body = body[:s - first] + ("public " if public else "") + body[s - first:]
    attr = "@[expose] public section" if expose else "public section"
    tail = t[after:]
    return t[:first] + "module\n" + body + "\n" + attr + "\n" + (tail if tail.startswith("\n") else "\n" + tail)


SECTION = re.compile(r"^(@\[expose\] )?public section[ \t]*$", re.M)
EVAL = re.compile(r"^[ \t]*(#eval|run_cmd|run_elab|run_meta)\b", re.M)


def add_meta_imports(t):
    """A module that evaluates code of an imported module at compile time (`#eval`, `run_cmd`, ...) needs that module
    as a `meta import` too ("`f` is not accessible here; consider adding `public meta import`"). The lines go in front
    of the `public section` line. Returns the new text, or None when nothing is to be done."""
    m = SECTION.search(t)
    if m is None or not is_module(t) or not EVAL.search(t):
        return None
    head = t[:m.start()]
    have = set(re.findall(r"^meta import[ \t]+(\S+)", head, re.M))
    names = [n for n in re.findall(r"^(?:public )?import[ \t]+(\S+)", head, re.M) if n not in have]
    if not names:
        return None
    return head + "".join(f"meta import {n}\n" for n in names) + t[m.start():]


def tracked_lean():
    names = subprocess.check_output(["git", "ls-files", "*.lean"], cwd=ROOT, text=True).split("\n")
    return [ROOT / n for n in names if n and Path(n).name not in NOT_MODULES]


def is_module(t):
    i = skip_trivia(t, 0)
    return t.startswith("module", i) and not t[i + 6:i + 7].isalnum()


def expand(paths):
    if not paths:
        return tracked_lean()
    fs = []
    for p in map(Path, paths):
        p = p if p.is_absolute() else Path.cwd() / p
        fs += sorted(f for f in p.rglob("*.lean") if ".lake" not in f.parts and f.name not in NOT_MODULES) if p.is_dir() else [p]
    return fs


def main(argv):
    mode = next((m for m in ("--check", "--apply", "--meta-imports") if m in argv), None)
    paths = [a for a in argv if not a.startswith("--")]
    if mode is None:
        print(__doc__)
        return 2
    files = expand(paths)
    schlecht, n = [], 0
    for f in files:
        t = f.read_text(encoding="utf-8")
        if mode == "--meta-imports":
            r = add_meta_imports(t) if is_module(t) else None
            if r is not None:
                f.write_text(r, encoding="utf-8")
                n += 1
            continue
        if is_module(t):
            continue
        if mode == "--check":
            schlecht.append(f)
            continue
        r = migrate(t, public="--private-imports" not in argv, expose="--no-expose" not in argv)
        if r is None:
            continue
        f.write_text(r, encoding="utf-8")
        n += 1
    if mode == "--meta-imports":
        print(f"lean-module: added meta imports to {n} of {len(files)} files")
        return 0
    if mode == "--check":
        for f in schlecht[:20]:
            print(f"not a module: {f.relative_to(ROOT)}")
        if len(schlecht) > 20:
            print(f"... and {len(schlecht) - 20} more")
        print(f"lean-module: {len(files) - len(schlecht)} of {len(files)} Lean files are modules")
        return 1 if schlecht else 0
    print(f"lean-module: migrated {n} of {len(files)} files")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
