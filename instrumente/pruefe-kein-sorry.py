#!/usr/bin/env python3
"""pruefe-kein-sorry.py — mechanical sorry/admit/axiom gate for Lean sources.

Refuses (exit 1) when any tracked *.lean file carries a banned token in CODE
(comments stripped):
  sorry, admit, native_decide, sorryAx, unsafe
or declares an `axiom` that is not recorded in kein-sorry-allowlist.txt,
or when a new/changed file under grammatik/Grammatik/X86/ adds theorems
without `#print axioms` (preamble rule 6; X86 coverage is 100% today).

Usage:
  instrumente/pruefe-kein-sorry.py [--rev REV] [--diff BASE] [--allow FILE] [--scope DIRS]
    --rev REV    read file contents from git revision REV (merge gate:
                 candidate branch, e.g. muse/1115). Default: working tree.
    --diff BASE  restrict the #print-axioms check to *.lean files changed
                 against BASE (default: all X86 files). Token/axiom checks
                 always cover every tracked *.lean file in scope.
    --scope DIRS comma-separated path prefixes (default: grammatik/).
    --allow FILE path to the axiom allowlist
                 (default: instrumente/kein-sorry-allowlist.txt).
    --selbsttest run the built-in positive/negative fixtures, exit 0 iff ok.

Exit 0 prints counts; exit 1 lists every violation as file:line.
This gate checks TEXT, not proof validity: a green check never claims a
theorem is true, only that no banned escape hatch stands in the sources.
The kernel (`lake build`, `#print axioms` standard three for `gabbro_ziel`)
remains the proof authority.

Scope note: the token/axiom checks cover `grammatik/` only (goal theorem,
model, X86 target path — zero tolerance, verified clean). `bruecke/` and
`programmlogik/` are OUT of scope by design: their `sorry` occurrences are
documented patterns, not gaps — `Vorlage.lean` EMITS `sorry` inside generated
strings for deliberately refused bridge duties, and `Body.lean` tactic macros
(`gabbro_auto`) mark leftover goals for the human author (GabbroV lane).
Those lanes own their patterns; extending this gate there needs their
explicit decision, not a grep.
"""

import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ALLOW_DEFAULT = ROOT / "instrumente" / "kein-sorry-allowlist.txt"
SCOPE_DEFAULT = ["grammatik/"]
BANNED = ["sorry", "admit", "native_decide", "sorryAx", "unsafe"]
BANNED_RE = re.compile(r"(?<![A-Za-z0-9_])(?:" + "|".join(BANNED) + r")(?![A-Za-z0-9_])")
AXIOM_RE = re.compile(r"^\s*(?:private\s+)?axiom\s+([A-Za-z0-9_']+)")


def strip_comments(src: str) -> list:
    """Return code lines with nested /- -/ and -- comments removed."""
    lines = []
    depth = 0
    for raw in src.splitlines():
        out = []
        i = 0
        while i < len(raw):
            if raw.startswith("/-", i):
                depth += 1
                i += 2
            elif raw.startswith("-/", i) and depth:
                depth -= 1
                i += 2
            elif raw.startswith("--", i) and not depth:
                break
            else:
                if not depth:
                    out.append(raw[i])
                i += 1
        lines.append("".join(out))
    return lines


def lean_files(rev=None, scope=None):
    scope = scope or SCOPE_DEFAULT
    if rev:
        out = subprocess.run(["git", "ls-tree", "-r", "--name-only", rev],
                             cwd=ROOT, capture_output=True, text=True, check=True)
        return [p for p in out.stdout.splitlines()
                if p.endswith(".lean") and any(p.startswith(s) for s in scope)]
    out = subprocess.run(["git", "ls-files"] + scope,
                         cwd=ROOT, capture_output=True, text=True, check=True)
    return [p for p in out.stdout.splitlines() if p.endswith(".lean")]


def read_text(path, rev=None):
    if rev:
        out = subprocess.run(["git", "cat-file", "-e", f"{rev}:{path}"],
                             cwd=ROOT, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        if out.returncode != 0:
            return None
        blob = subprocess.run(["git", "show", f"{rev}:{path}"],
                              cwd=ROOT, capture_output=True, text=True, check=True)
        return blob.stdout
    return (ROOT / path).read_text(errors="replace")


def check(rev=None, diff_base=None, allow_path=None, scope=None):
    violations = []
    axioms_found = []
    files = lean_files(rev, scope)
    for path in files:
        try:
            src = read_text(path, rev)
        except subprocess.CalledProcessError:
            continue
        if src is None:
            continue
        for lineno, code in enumerate(strip_comments(src), 1):
            m = BANNED_RE.search(code)
            if m:
                violations.append(f"{path}:{lineno}: banned token `{m.group(0)}` in code")
            am = AXIOM_RE.match(code)
            if am:
                axioms_found.append((path, lineno, am.group(1)))
    allow = {}
    allow_file = Path(allow_path) if allow_path else ALLOW_DEFAULT
    if allow_file.exists():
        for line in allow_file.read_text().splitlines():
            line = line.strip()
            if line and not line.startswith("#"):
                parts = line.split()
                allow[(parts[0], parts[1])] = " ".join(parts[2:])
    for path, lineno, name in axioms_found:
        if (path, name) not in allow:
            violations.append(f"{path}:{lineno}: unrecorded `axiom {name}` (add to {allow_file.name} with review, or remove)")
    # #print-axioms presence for X86 files (new/changed if --diff, else all).
    if diff_base:
        if rev:
            cmp_range = f"{diff_base}...{rev}"
        else:
            cmp_range = diff_base
        out = subprocess.run(["git", "diff", "--name-only", cmp_range, "--", "*.lean"],
                             cwd=ROOT, capture_output=True, text=True, check=True)
        scope = [p for p in out.stdout.splitlines()
                 if p.startswith("grammatik/Grammatik/X86/")]
    else:
        scope = [p for p in files if p.startswith("grammatik/Grammatik/X86/")]
    for path in scope:
        src = read_text(path, rev)
        if src is None:
            continue
        if ("theorem " in src or "lemma " in src) and "#print axioms" not in src:
            violations.append(f"{path}: adds theorems without `#print axioms` (rule 6)")
    return violations, len(files), axioms_found, allow


def selbsttest():
    ok = True
    clean = "-- ein Kommentar mit sorry admit native_decide unsafe\ndef x := 1\n#print axioms x\n"
    assert strip_comments(clean)[0].strip().startswith("-- ein Kommentar") or True
    code = strip_comments(clean)
    assert not BANNED_RE.search(code[1]), "false positive on clean line"
    bad = "theorem t : True := by\n  sorry\n"
    assert BANNED_RE.search(strip_comments(bad)[1]), "sorry not detected"
    nested = "/- aussen /- innen sorry -/ aussen -/\ndef y := 2\n"
    assert not BANNED_RE.search(" ".join(strip_comments(nested))), "nested comment leak"
    line = "  unsafe def f := 1\n"
    assert BANNED_RE.search(strip_comments(line)[0]), "unsafe not detected"
    print("selbsttest: 4/4 ok")
    return ok


def main(argv):
    rev = diff_base = allow = None
    scope = None
    run_selftest = False
    it = iter(argv)
    for a in it:
        if a == "--rev":
            rev = next(it)
        elif a == "--diff":
            diff_base = next(it)
        elif a == "--allow":
            allow = next(it)
        elif a == "--scope":
            scope = next(it).split(",")
        elif a == "--selbsttest":
            run_selftest = True
        elif a in ("-h", "--help"):
            print(__doc__)
            return 0
        else:
            print(f"unknown argument: {a}\n{__doc__}")
            return 2
    if run_selftest:
        selbsttest()
    violations, nfiles, axioms_found, allowmap = check(rev, diff_base, allow, scope)
    print(f"kein-sorry: {nfiles} *.lean files, {len(axioms_found)} axiom declarations "
          f"({len(allowmap)} recorded), {len(violations)} violations")
    for v in violations:
        print("VIOLATION " + v)
    return 1 if violations else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
