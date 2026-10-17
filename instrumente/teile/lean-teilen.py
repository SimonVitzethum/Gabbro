#!/usr/bin/env python3
"""Split one big Lean file into parts of about --ziel lines (default 450) at top-level boundaries.

    python3 instrumente/teile/lean-teilen.py grammatik/Grammatik/Logik/Ruf/RufAdaequatRufG.lean [--ziel 450]

`X.lean` becomes an umbrella that only imports `X/T1.lean` ... `X/Tn.lean`, so every module that imported `X` keeps
working. Boundaries: between top-level declarations; a `section ... end` block and a `mutual ... end` block are never
cut. Each part reopens the `namespace`s and repeats the persistent top-level `open`/`variable`/`universe`/`set_option`
lines seen so far. Part 1 keeps the header (doc comment and imports); part k imports part k-1. The Lean build decides
whether a split is sound (`private` names and `local` notation do not cross a part boundary: fix those by hand)."""
import re, sys, pathlib

def main():
    src = pathlib.Path(sys.argv[1]); ziel = 450
    if "--ziel" in sys.argv: ziel = int(sys.argv[sys.argv.index("--ziel") + 1])
    L = src.read_text(encoding="utf-8").split("\n")
    # header = up to the line before the first namespace
    first_ns = next(i for i, l in enumerate(L) if re.match(r"namespace\b", l))
    # opening block: consecutive top-level namespace lines (and blank/comment lines between) at the start of the body
    ns_lines = []; i = first_ns
    while i < len(L) and (re.match(r"namespace\b", L[i]) or L[i].strip() == ""):
        if L[i].strip(): ns_lines.append(L[i])
        i += 1
    body_start = first_ns
    # closing: the matching trailing `end X` lines
    last = len(L) - 1
    while last > 0 and L[last].strip() == "": last -= 1
    closers = []; j = last
    while j >= 0 and re.match(r"end\b", L[j]) and len(closers) < len(ns_lines):
        closers.append(L[j]); j -= 1
    closers.reverse()
    body = L[body_start + len(ns_lines):j + 1] if False else L[first_ns:j + 1]
    # strip the namespace opening lines from the body
    k = 0; cnt = 0
    while cnt < len(ns_lines):
        if re.match(r"namespace\b", body[k]): cnt += 1
        k += 1
    body = body[k:]
    # units: split into top-level units at depth 0
    depth = 0; units = []; cur = []; pre_idx = []
    PERSIST = re.compile(r"^(open\b(?!.*\bin\s*$)|variable\b|universe\b|set_option\b(?!.*\bin\s*$)|attribute \[|noncomputable section)")
    def flush():
        if cur and any(x.strip() for x in cur): units.append(list(cur))
        cur.clear()
    START = re.compile(r"^(/--|/-!|@\[|theorem|lemma|def|instance|structure|inductive|abbrev|class|opaque|axiom|example|private|protected|noncomputable|set_option|open|variable|universe|section|mutual|namespace|attribute|#print|#eval|#check|macro|syntax|notation|local|scoped)\b|^/-")
    prev_blank = True
    for idx, l in enumerate(body):
        top = depth == 0
        if top and prev_blank and START.match(l) and cur and not re.match(r"^(def|theorem|lemma|instance|structure|inductive|abbrev|class|private|protected|noncomputable|@\[)", l) is None or (top and prev_blank and START.match(l) and cur and re.match(r"^(/--|/-!|section|mutual|namespace|set_option|open|variable|universe|attribute)", l)):
            flush()
        # after a doc comment the declaration belongs to it: do not split between `/-- ... -/` and the decl
        cur.append(l)
        if re.match(r"^(namespace|section|mutual)\b", l) or re.match(r"^noncomputable section\b", l): depth += 1
        elif re.match(r"^end\b", l): depth -= 1
        prev_blank = (l.strip() == "") or (top and depth == 0 and re.match(r"^end\b", l) is not None)
        if depth == 0 and re.match(r"^end\b", l): flush()
    flush()
    # a doc comment unit directly followed by its declaration must stay together: merge units that are only a comment
    merged = []
    for u in units:
        txt = "\n".join(u).strip()
        if merged and re.fullmatch(r"/--.*?-/", "\n".join(merged[-1]).strip(), re.S) :
            merged[-1] = merged[-1] + u
        else: merged.append(u)
    units = merged
    # chunk
    parts = []; cur_lines = []; size = 0
    for u in units:
        if cur_lines and size + len(u) > ziel and size >= ziel * 0.4:
            parts.append(cur_lines); cur_lines = []; size = 0
        cur_lines = cur_lines + u; size += len(u)
    if cur_lines: parts.append(cur_lines)
    if len(parts) < 2: print("nothing to split:", src, "(%d lines)" % len(L)); return 1
    modbase = ".".join(src.with_suffix("").parts[src.parts.index("grammatik") + 1:]) if "grammatik" in src.parts else None
    outdir = src.with_suffix("")
    outdir.mkdir(exist_ok=True)
    header = L[:first_ns]
    persist = []
    names = []
    for n, p in enumerate(parts, 1):
        name = f"T{n}"; names.append(name)
        out = []
        if n == 1: out += header
        else:
            out += [f"/- Part {n} of {len(parts)} of `{src.stem}` (split by instrumente/teile/lean-teilen.py; the umbrella `{src.stem}.lean` imports all parts). -/",
                    f"import {modbase}.T{n-1}", ""]
        out += ns_lines + [""] + persist + ([""] if persist else [])
        out += p
        out += [""] + closers + [""]
        (outdir / f"{name}.lean").write_text("\n".join(out), encoding="utf-8")
        # persistent top-level commands of this part carry on
        depth = 0
        for ix, l in enumerate(p):
            if depth == 0 and PERSIST.match(l) and not l.startswith("noncomputable section"):
                stmt = [l]; q = ix + 1
                while q < len(p) and p[q][:1] in (" ", "\t"):   # continuation lines belong to the command
                    stmt.append(p[q]); q += 1
                persist.append("\n".join(stmt))
            if re.match(r"^(namespace|section|mutual)\b", l): depth += 1
            elif re.match(r"^end\b", l): depth -= 1
    umb = header + [f"import {modbase}.{n}" for n in names] + [""]
    # keep the original doc header; drop the original imports from the umbrella (the parts carry them)
    uh = [l for l in header if not l.startswith("import ")]
    src.write_text("\n".join(uh + [f"import {modbase}.{n}" for n in names] + [""]), encoding="utf-8")
    print(f"{src}: {len(L)} lines -> {len(parts)} parts", [len(p) for p in parts])
    return 0

if __name__ == "__main__":
    sys.exit(main())
