#!/usr/bin/env python3
"""Premise-necessity probe for Lean goal theorems.

An auditor asked whether the goal chain DERIVES or merely FORWARDS its
premises: a theorem that restates a premise under a new name looks like
progress and measures like none. This instrument answers per premise, by
rebuilding a stripped variant in a scratch copy (never in the tree) and
reading what breaks.

Three probe kinds, one verdict scale:

  hyp probe   THM:prem   -- premise type replaced by True, call-site
                          arguments at the premise position replaced by
                          `trivial`. Variant A strips prem itself, variant B
                          strips every OTHER explicit premise instead.
  field probe STRUCT.f   -- structure field removed, constructor literals
                          repaired by deleting the `f := ...` segment,
                          projections left to fail.
  gate probe  THM:@Word  -- conclusion arrows whose segment mentions Word
                          are deleted, matching `intro` binders dropped,
                          body uses left to fail.

Verdicts:

  DERIVED    a downstream proof fails that is not the forwarding theorem
             itself (hyp: A shows prem necessary, B shows the rest
             necessary too -- joint derivation; field/gate: a proved
             declaration breaks on the stripped content).
  FORWARDED  only the theorem restating the premise breaks (hyp: A shows
             prem necessary, B builds with prem alone -- prem carries the
             whole conclusion; field: only the structure and constructor
             defs break; gate: the stripped conclusion builds).
  UNUSED     the stripped cone builds unchanged -- the premise is dead
             weight end to end.
  INCONCLUSIVE  the patch did not apply cleanly (ambiguous call site,
             shared binder group, missing pattern) -- a site list is
             printed, nothing is claimed.

Precedent is `mutiere-pruefer.py --anker` for checker passes: cheap text
work first, expensive rebuilds only where they decide, and a speech test
in both directions so the instrument proves it can say each word.

Usage:

    instrumente/pruefe-praemisse.py --sprechprobe
    instrumente/pruefe-praemisse.py [--fisch] [--keep] THM[:prem] ... STRUCT.f ... THM:@Word ...

Builds run on ki-pc-fisch-101 under /tmp/praemisse-r02 (own scratch lane,
never a shared tree) unless --local is given. The speech test is
hermetic: small Lean files through `lean` on this host, no lake
project, no network.

Two extensions over the per-theorem verdict:

  conjunct probe  THM:prem^c splits a conjunction conclusion into one
                  tripwire copy per conjunct (same binders, narrowed
                  conclusion, proof closer isolated -- see
                  parse_conjunct_proof) and builds them all in ONE
                  variant: NEEDS (copy red) vs FREE (copy green).
                  Mixed copies read SPLIT, all-red UNIFORM, all-green
                  DETACHED. STRUCT.field@TARGET does the same against
                  a removed structure field (no strength dual: dropping
                  every other field changes the representation itself).
  strength probe  for each NEEDS conjunct a second variant weakens
                  every OTHER premise instead: green reads ALONE (the
                  premise alone carries the conjunct -- restatement
                  shape, weak) and red reads JOINT (real joint use,
                  strong). FREE conjuncts have no strength question.
"""
import os
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile

HERE = pathlib.Path(__file__).resolve().parent
TREE = HERE.parent
GRAMMATIK = TREE / "grammatik"
LEAN = os.environ.get("LEANBIN", os.path.expanduser("~/.elan/bin/lean"))
LAKE = os.environ.get("LAKE", os.path.expanduser("~/.elan/bin/lake"))
FISCH = "ki-pc-fisch-101"
REMOTE_ROOT = "/tmp/praemisse-r02"
LOCAL_ROOT = "/tmp/praemisse-r02-local"
BUILD_TIMEOUT = 900

DECLKIND = r"(?:theorem|def|abbrev|structure|example|instance|opaque|class|inductive)"
DECLRE = re.compile(r"^((?:noncomputable\s+|private\s+)?" + DECLKIND +
                    r")\s+(\S+)")
ERRORRE = re.compile(r"^error: (.+\.lean):(\d+):(\d+): (.*)$")
HERMERRORRE = re.compile(r"^(.+\.lean):(\d+):(\d+): error: (.*)$")
ARROW = "\u2192"


def find_decl_source(name):
    """Locate files holding `theorem|def|structure name` under grammatik/."""
    hits = []
    for path in sorted((GRAMMATIK / "Grammatik").glob("*.lean")):
        text = path.read_text(encoding="utf-8")
        if re.search(r"^((?:noncomputable\s+|private\s+)?" + DECLKIND +
                     r")\s+" + re.escape(name) + r"\b", text, re.M):
            hits.append(path)
    return hits


def decl_table_text(text):
    """Map each declaration in source text to (keyword, start, end) lines."""
    lines = text.splitlines()
    starts = []
    for i, line in enumerate(lines):
        m = DECLRE.match(line)
        if m:
            kind = m.group(1).split()[-1]
            name = m.group(2)
            if kind == "example":
                # `example` carries no name; synthesize a stable key so
                # error attribution does not read the first binder.
                name = "example@%d" % (i + 1)
            starts.append((i + 1, kind, name))
    table = {}
    for k, (start, kind, name) in enumerate(starts):
        end = starts[k + 1][0] - 1 if k + 1 < len(starts) else len(lines)
        table[name] = (kind, start, end)
    return table


def decl_table(path):
    """Map each declaration in a file to (keyword, start, end) lines."""
    return decl_table_text(path.read_text(encoding="utf-8"))


def find_matching(text, open_pos, open_ch="(", close_ch=")"):
    """Index just past the bracket matching text[open_pos]."""
    depth = 0
    i = open_pos
    in_str = False
    while i < len(text):
        ch = text[i]
        if ch == '"' and (i == 0 or text[i - 1] != "\\"):
            in_str = not in_str
        if not in_str:
            if ch == open_ch:
                depth += 1
            elif ch == close_ch:
                depth -= 1
                if depth == 0:
                    return i + 1
        i += 1
    return -1


def split_top_spans(text):
    """Split text at top-level commas; return (segment, start, end)."""
    opens = "([{⟨‹«"
    closes = ")]}⟩›»"
    segs, depth, cur, start = [], 0, [], 0
    in_str = False
    for i, ch in enumerate(text):
        if ch == '"' and (i == 0 or text[i - 1] != "\\"):
            in_str = not in_str
        if not in_str:
            if ch in opens:
                depth += 1
            elif ch in closes:
                depth -= 1
            elif ch == "," and depth == 0:
                segs.append(("".join(cur), start, i))
                cur, start = [], i + 1
                continue
        cur.append(ch)
    segs.append(("".join(cur), start, len(text)))
    return segs


def split_top_commas(text):
    """Split text at top-level commas; return segment strings."""
    return [s for s, _a, _b in split_top_spans(text)]


def blank_span(text, start, end):
    """Blank a span keeping newlines: line numbers never shift."""
    return "".join("\n" if ch == "\n" else " " for ch in text[start:end])


def parse_signature(sig):
    """Parse binder groups into (names, explicit, has_type) entries."""
    binders = []
    i, n = 0, len(sig)
    while i < n:
        while i < n and sig[i] in " \t\n":
            i += 1
        if i >= n:
            break
        if sig[i] in "([{":
            open_ch = sig[i]
            close_ch = {"(": ")", "[": "]", "{": "}"}[open_ch]
            end = find_matching(sig, i, open_ch, close_ch)
            if end < 0:
                break
            inner = sig[i + 1:end - 1]
            depth, colon = 0, -1
            for k, ch in enumerate(inner):
                if ch in "([{":
                    depth += 1
                elif ch in ")]}":
                    depth -= 1
                elif ch == ":" and depth == 0:
                    if k + 1 < len(inner) and inner[k + 1] == "=":
                        continue
                    colon = k
                    break
            if colon >= 0:
                binders.append((inner[:colon].split(), open_ch == "(", True))
            else:
                binders.append((inner.split(), open_ch == "(", False))
            i = end
        else:
            while i < n and sig[i] not in " \t\n([{":
                i += 1
    return binders


def theorem_signature(text, name):
    """Return the signature text of a theorem/def (up to top-level :=)."""
    m = re.search(r"^((?:noncomputable\s+|private\s+)?" + DECLKIND + r")\s+" +
                  re.escape(name) + r"\b", text, re.M)
    if not m:
        return None
    i = m.end()
    depth = 0
    while i < len(text):
        ch = text[i]
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif depth == 0 and text.startswith(":=", i):
            return text[m.end():i]
        i += 1
    return None


def group_spans(decl_text, thm):
    """Binder groups of a signature with absolute type spans.

    Returns (entries, error) where each entry is (names, explicit,
    has_type, type_start, type_end). Positions are explicit argument
    indices per name in signature order.
    """
    sig = theorem_signature(decl_text, thm)
    if sig is None:
        return None, "signature of %s not parsed" % thm
    base = decl_text.index(sig)
    entries, i, pos = [], 0, 0
    while True:
        # Only the leading binder prefix counts: the return type with
        # its own foralls is not a premise. Stop at the first char
        # that opens neither whitespace nor a group.
        while i < len(sig) and sig[i] in " \t\n":
            i += 1
        if i >= len(sig) or sig[i] not in "([{":
            break
        open_ch = sig[i]
        close_ch = {"(": ")", "[": "]", "{": "}"}[open_ch]
        end = find_matching(sig, i, open_ch, close_ch)
        if end < 0:
            return None, "unbalanced group in signature"
        inner = sig[i + 1:end - 1]
        depth, colon = 0, -1
        for k, ch in enumerate(inner):
            if ch in "([{":
                depth += 1
            elif ch in ")]}":
                depth -= 1
            elif ch == ":" and depth == 0:
                if k + 1 < len(inner) and inner[k + 1] == "=":
                    continue
                colon = k
                break
        explicit = open_ch == "("
        if colon >= 0:
            names = inner[:colon].split()
            estart = base + i + 1 + colon + 1
            eend = base + end - 1
        else:
            names = inner.split()
            estart = eend = -1
        positions = {}
        for nm in names:
            positions[nm] = pos if explicit else -1
            if explicit:
                pos += 1
        entries.append((names, explicit, colon >= 0, estart, eend, positions))
        i = end
    return entries, None


def weaken_span(text, start, end):
    """Replace a type span with True, keeping every newline in place.

    Error line numbers must still match the tree after the patch, so a
    multi-line type becomes `True` followed by its own newline count --
    whitespace inside a binder group parses fine.
    """
    return text[:start] + " True " + "\n" * text[start:end].count("\n") + text[end:]


def apply_weaken_to_text(decl_text, thm, prem):
    """Replace the type of premise `prem` with True; return (text, error)."""
    entries, err = group_spans(decl_text, thm)
    if err:
        return None, err
    for names, _exp, has_type, estart, eend, _pos in entries:
        if prem in names:
            if not has_type:
                return None, "bare binder without type"
            if len(names) > 1:
                return None, "shared binder group " + " ".join(names)
            return weaken_span(decl_text, estart, eend), None
    return None, "premise %s not found in signature" % prem


def explicit_position(decl_text, thm, prem):
    """Explicit argument index of premise `prem`; -1 when implicit."""
    sig = theorem_signature(decl_text, thm)
    if sig is None:
        return None
    pos = 0
    for names, explicit, _has in parse_signature(sig):
        if prem in names:
            return pos if explicit else -1
        if explicit:
            pos += len(names)
    return None


def structure_fields(text, name):
    """Return (field_name, span_start, span_end) entries for a structure."""
    m = re.search(r"^structure\s+" + re.escape(name) + r"\b[^\n]*\n", text, re.M)
    if not m:
        return None
    fields = []
    for fm in re.finditer(r"^  ([A-Za-z_][A-Za-z_0-9']*)\s*:",
                          text[m.end():], re.M):
        abs_start = m.end() + fm.start()
        # Stop at the declaration following the structure: anything
        # after it cannot be a field of this structure.
        tail = text[abs_start:]
        stop = re.search(r"^(?:theorem|def|abbrev|structure|example|"
                         r"instance|end)\b", tail, re.M)
        limit = abs_start + stop.start() if stop else len(text)
        if abs_start >= limit and fields:
            continue
        fname = fm.group(1)
        type_start = m.end() + fm.end()
        # A field ends at the first newline at depth zero that is
        # followed by a line no deeper than the field itself.
        depth, i = 0, type_start
        end = limit
        while i < limit:
            ch = text[i]
            if ch in "([{":
                depth += 1
            elif ch in ")]}":
                depth -= 1
            elif ch == "\n" and depth == 0:
                j = i + 1
                while j < limit and text[j] == " ":
                    j += 1
                indent = j - (i + 1)
                rest = text[j:j + 40]
                if indent <= 2 or re.match(r"(?:theorem|def|abbrev|structure|"
                                           r"example|instance|end)\b", rest):
                    end = i
                    break
            i += 1
        if abs_start < limit:
            fields.append((fname, abs_start, end))
    # Keep only the leading run: entries before the first stop line.
    trimmed = []
    for fname, start, end in fields:
        before = text[m.end():start]
        if re.search(r"^(?:theorem|def|abbrev|structure|example|"
                     r"instance|end)\b", before, re.M):
            break
        trimmed.append((fname, start, end))
    return trimmed


ATOMRE = re.compile(r"[^\s(){}\[\],;→]+")

# Tactic and term keywords terminate an application: a bare mention
# (`exact thm` at end of line, `have h := thm`) is not a call, and the
# word after the name is not an argument. Proof TERMS that double as
# arguments (`rfl`, `trivial`) are deliberately absent: the example in
# `Geteilt.lean` passes `rfl` positionally.
STOPWORDS = frozenset("by have exact apply intro refine rw simp show calc match "
                      "with if then else fun do return where let in theorem def "
                      "abbrev structure example instance end section namespace open "
                      "import variable sorry admit obtain suffices congr simp_all aesop "
                      "assumption omega decide done next case".split())


def patch_application(text, call_end, prem, position):
    """Patch one application: named `(prem := e)` wins, else positional.

    Returns the patched full text, or None when the site is not a plain
    full application of the target.
    """
    k, explicit = call_end, 0
    while True:
        while k < len(text) and text[k] in " \t\n":
            k += 1
        if k >= len(text):
            return None
        ch = text[k]
        if ch == "(":
            e = find_matching(text, k, "(", ")")
            if e < 0:
                return None
            inner = text[k + 1:e - 1]
            cm = re.match(r"\s*" + re.escape(prem) + r"\s*:=", inner)
            if cm:
                return text[:k + 1 + cm.end()] + " trivial " + text[e - 1:]
            if explicit == position:
                return text[:k] + "trivial" + text[e:]
            explicit += 1
            k = e
        elif ch in "{[":
            close_ch = {"{": "}", "[": "]"}[ch]
            e = find_matching(text, k, ch, close_ch)
            if e < 0:
                return None
            k = e  # implicit argument: skipped, not counted
        elif ch not in ")]}:,;→|":
            r = ATOMRE.match(text, k)
            atom = r.group(0)
            if re.search(r"=>|:=", atom) or atom in STOPWORDS:
                return None
            if explicit == position:
                return text[:k] + "trivial" + text[r.end():]
            explicit += 1
            k = r.end()
        else:
            return None


def comment_spans(text):
    """Spans of line and (nesting-aware) block comments in Lean source."""
    spans = []
    i, n = 0, len(text)
    while i < n:
        if text.startswith("--", i):
            j = text.find("\n", i)
            spans.append((i, n if j < 0 else j))
            i = n if j < 0 else j
        elif text.startswith("/-", i):
            depth, j = 0, i
            while j < n:
                if text.startswith("/-", j):
                    depth += 1
                    j += 2
                elif text.startswith("-/", j):
                    depth -= 1
                    j += 2
                    if depth == 0:
                        break
                else:
                    j += 1
            spans.append((i, j))
            i = j
        elif text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            i = j + 1
        else:
            i += 1
    return spans


def in_spans(spans, pos):
    for a, b in spans:
        if a <= pos < b:
            return True
    return False


def patch_call_sites(files_text, thm, prem, position):
    """Patch applications of thm: named argument first, else positional.

    Returns (patched_files, unpatched_sites, ignored). `#print axioms`
    lines, comments and the declaration itself are ignored; anything
    else that is not a full application is reported unpatched.
    """
    patched, unpatched = {}, []
    ignored = 0
    site_re = re.compile(r"(?<!\.)\b" + re.escape(thm) + r"\b")
    decl_re = re.compile(r"^((?:noncomputable\s+|private\s+)?" + DECLKIND +
                         r")\s+" + re.escape(thm) + r"\b")
    for fname, original in files_text.items():
        cur, cursor, changed = original, 0, False
        while True:
            # Spans are recomputed round by round: each patch shifts
            # the text, and stale spans would misattribute sites.
            spans = comment_spans(cur)
            m = site_re.search(cur, cursor)
            if not m:
                break
            if in_spans(spans, m.start()):
                cursor = m.end()
                ignored += 1
                continue
            line_start = cur.rfind("\n", 0, m.start()) + 1
            line_end = cur.find("\n", m.start())
            line = cur[line_start:line_end if line_end >= 0 else len(cur)]
            stripped = line.lstrip()
            if ("print axioms" in line or decl_re.match(stripped)):
                cursor = m.end()
                ignored += 1
                continue
            new_cur = patch_application(cur, m.end(), prem, position)
            if new_cur is None:
                unpatched.append("%s: %s" % (fname, line.strip()[:100]))
                cursor = m.end()
                continue
            # The replaced argument stays one atom, so scanning can
            # continue right after the inserted `trivial`.
            inserted = new_cur.find("trivial", m.start())
            cur = new_cur
            cursor = inserted + len("trivial")
            changed = True
        if changed:
            patched[fname] = cur
    return patched, unpatched, ignored


def classify_build(log, cone, target_thm):
    """Attribute lean errors to enclosing declarations.

    `unknown constant target` is cascade fallout of the stripped
    theorem itself and is folded back onto the target.
    """
    failed = {}
    for line in log.splitlines():
        m = ERRORRE.match(line.strip())
        if not m:
            continue
        rel, lineno, msg = m.group(1), int(m.group(2)), m.group(4)
        fname = pathlib.Path(rel).name
        owner = None
        for cand, table in cone.items():
            if pathlib.Path(cand).name == fname or cand.endswith(rel):
                for decl, (_kind, start, end) in table.items():
                    if start <= lineno <= end:
                        owner = "%s:%s" % (pathlib.Path(cand).name, decl)
                        break
            if owner:
                break
        if owner is None:
            owner = "%s:<top>" % fname
        if (("unknown constant" in msg or "Unknown identifier" in msg) and
                target_thm in msg):
            owner = "CASCADE:" + target_thm
        if owner not in failed:
            failed[owner] = msg[:160]
    return failed


def run(cmd, timeout=BUILD_TIMEOUT):
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
        return proc.returncode, proc.stdout + proc.stderr
    except subprocess.TimeoutExpired:
        return 124, "TIMEOUT after %ds" % timeout


class Lane:
    """Where scratch copies live and variant builds run."""

    def __init__(self, remote):
        self.remote = remote
        self.root = REMOTE_ROOT if remote else LOCAL_ROOT

    def setup(self):
        if self.remote:
            code, out = run(["ssh", "-o", "ConnectTimeout=10", FISCH,
                             "mkdir -p %s/work && rm -rf %s/work/grammatik && "
                             "cp -r ~/gabbro-r02/grammatik %s/work/grammatik && "
                             "du -sh %s/work/grammatik | cut -f1"
                             % (self.root, self.root, self.root, self.root)])
            return code == 0, out[-500:]
        work = pathlib.Path(self.root) / "work" / "grammatik"
        shutil.rmtree(work, ignore_errors=True)
        shutil.copytree(GRAMMATIK, work, ignore=shutil.ignore_patterns(".lake"))
        return True, "local scratch ready"

    def push_files(self, changed):
        """Write {project-relpath: text} into the scratch lane."""
        if self.remote:
            for rel, text in changed.items():
                with tempfile.NamedTemporaryFile("w", suffix=".lean",
                                                 delete=False,
                                                 encoding="utf-8") as tmp:
                    tmp.write(text)
                    tmpname = tmp.name
                code, out = run(["rsync", "-rlpgoD", tmpname,
                                 "%s:%s/work/grammatik/%s" % (FISCH, self.root, rel)])
                os.unlink(tmpname)
                if code != 0:
                    return False, out[-500:]
            return True, "pushed %d files" % len(changed)
        for rel, text in changed.items():
            (pathlib.Path(self.root) / "work" / "grammatik" / rel).write_text(
                text, encoding="utf-8")
        return True, "wrote %d files" % len(changed)

    def restore(self, rels):
        """Restore pristine sources from the tree (read, never written).

        rels are project-relative (Grammatik/...) and map back under
        grammatik/ for tree reads.
        """
        return self.push_files({rel: (TREE / ("grammatik/" + rel)).read_text(
            encoding="utf-8") for rel in rels})

    def build(self):
        if self.remote:
            code, out = run(["ssh", "-o", "ConnectTimeout=10", FISCH,
                             "cd %s/work/grammatik && export PATH=$HOME/.elan/bin:$PATH && "
                             "lake build > /tmp/praemisse-r02-last.log 2>&1; "
                              "echo EXIT=$?; echo ERRORS=$(grep -c '^error: ' "
                              "/tmp/praemisse-r02-last.log); "
                              "grep '^error: ' /tmp/praemisse-r02-last.log | head -n 120"
                             % self.root], timeout=BUILD_TIMEOUT + 120)
            ok = "EXIT=0" in out
            return ok, out
        work = pathlib.Path(self.root) / "work" / "grammatik"
        code, out = run(["bash", "-lc", "cd '%s' && '%s' build > /tmp/praemisse-r02-local.log 2>&1; "
                         "echo EXIT=$?; echo ERRORS=$(grep -c '^error: ' "
                         "/tmp/praemisse-r02-local.log); "
                         "grep '^error: ' /tmp/praemisse-r02-local.log | head -n 120" %
                         (work, LAKE)], timeout=BUILD_TIMEOUT + 60)
        ok = "EXIT=0" in out
        return ok, out


def cone_tables():
    tables = {}
    for path in sorted((GRAMMATIK / "Grammatik").glob("*.lean")):
        tables["Grammatik/" + path.name] = decl_table(path)
    return tables


def lane_texts():
    return {("Grammatik/" + p.name): p.read_text(encoding="utf-8")
            for p in sorted((GRAMMATIK / "Grammatik").glob("*.lean"))}


def probe_hyp(lane, thm, prem, keep):
    """Variants A (strip prem) and B (strip the rest) for THM:prem."""
    hits = find_decl_source(thm)
    if len(hits) != 1:
        return {"verdict": "INCONCLUSIVE",
                "note": "declaration %s found in %d files" % (thm, len(hits))}
    src = hits[0]
    proj_rel = "Grammatik/" + src.name
    proj_rel = "Grammatik/" + src.name
    text = src.read_text(encoding="utf-8")
    patched, err = apply_weaken_to_text(text, thm, prem)
    if err:
        return {"verdict": "INCONCLUSIVE", "note": "A unpatchable: " + err}
    pos = explicit_position(text, thm, prem)
    if pos is None or pos < 0:
        return {"verdict": "INCONCLUSIVE", "note": "premise position unknown"}
    sig = theorem_signature(text, thm)
    others = [nm for names, exp, _h in parse_signature(sig)
              for nm in names if exp and nm != prem]
    report = {"position": pos, "others": others}
    # ---- Variant A ----
    lane.restore([proj_rel])
    files_text = lane_texts()
    files_text[proj_rel] = patched
    call_patched, unpatched, _ = patch_call_sites(files_text, thm, prem, pos)
    if unpatched:
        if not keep:
            lane.restore([proj_rel])
        return {"verdict": "INCONCLUSIVE", "note": "A call sites ambiguous",
                "sites": unpatched}
    changed = {proj_rel: patched}
    changed.update(call_patched)
    push = dict(changed)
    ok, msg = lane.push_files(push)
    if not ok:
        return {"verdict": "INCONCLUSIVE", "note": "push failed: " + msg}
    ok_a, log_a = lane.build()
    cone = cone_tables()
    failed_a = classify_build(log_a, cone, thm)
    real_a = {k: v for k, v in failed_a.items() if not k.startswith("CASCADE")}
    report["A_builds"] = ok_a
    report["A_failed"] = real_a
    if ok_a:
        if not keep:
            lane.restore([proj_rel])
        report.update({"verdict": "UNUSED",
                       "note": "cone builds with premise at True"})
        return report
    target_key = src.name + ":" + thm
    if target_key not in real_a:
        if not keep:
            lane.restore([proj_rel])
        report.update({"verdict": "INCONCLUSIVE",
                       "note": "theorem holds but downstream fails"})
        return report
    # ---- Variant B: weaken every explicit group but the target's.
    # Shared groups (Pre Post) weaken as one bundle: all their names
    # are stripped at consecutive positions.
    entries, err_e = group_spans(text, thm)
    if err_e:
        if not keep:
            lane.restore([proj_rel])
        return {"verdict": "INCONCLUSIVE", "note": "B: " + err_e}
    strip = []
    for names, explicit, has_type, _s, _e, positions in entries:
        if prem in names or not explicit or not has_type:
            continue
        for nm in names:
            strip.append((nm, positions[nm]))
    second = text
    while True:
        entries, err_e = group_spans(second, thm)
        if err_e:
            if not keep:
                lane.restore([proj_rel])
            return {"verdict": "INCONCLUSIVE", "note": "B: " + err_e}
        todo = [(names, estart, eend) for names, explicit, has_type,
                estart, eend, _p in entries
                if prem not in names and explicit and has_type
                and second[estart:eend].strip() != "True"]
        if not todo:
            break
        _names, estart, eend = todo[0]
        second = weaken_span(second, estart, eend)
    # Positions survive weakening: binder order is kept.
    entries, _ = group_spans(second, thm)
    pos_of = {}
    for names, _e2, _h, _s, _x, positions in entries:
        pos_of.update(positions)
    files_b = lane_texts()
    files_b[proj_rel] = second
    changed_b = {proj_rel: second}
    for other, _pos_o in strip:
        pos_o = pos_of.get(other)
        if pos_o is None or pos_o < 0:
            if not keep:
                lane.restore([proj_rel])
            return {"verdict": "INCONCLUSIVE",
                    "note": "B position unknown for " + other}
        # Each replaced argument stays one explicit atom, so indices
        # stay valid round by round.
        cp, unp, _ = patch_call_sites(files_b, thm, other, pos_o)
        if unp:
            if not keep:
                lane.restore([proj_rel])
            return {"verdict": "INCONCLUSIVE",
                    "note": "B call sites ambiguous at " + other, "sites": unp}
        files_b.update(cp)
        changed_b.update(cp)
    ok, msg = lane.push_files(dict(changed_b))
    if not ok:
        return {"verdict": "INCONCLUSIVE", "note": "push failed"}
    ok_b, log_b = lane.build()
    failed_b = classify_build(log_b, cone, thm)
    real_b = {k: v for k, v in failed_b.items() if not k.startswith("CASCADE")}
    report["B_builds"] = ok_b
    report["B_failed"] = real_b
    if not keep:
        lane.restore([proj_rel])
    if ok_b:
        report.update({"verdict": "FORWARDED",
                       "note": "premise alone carries the conclusion"})
    else:
        report.update({"verdict": "DERIVED",
                       "note": "joint derivation -- necessary, not sufficient"})
    return report


def strip_structure_field(text, struct, field):
    """Blank STRUCT.field and repair constructor literals.

    Returns (patched_text, error): blanking keeps every newline, so
    error line numbers still match the tree.
    """
    fields = structure_fields(text, struct)
    if not fields or field not in [f[0] for f in fields]:
        return None, "field not found"
    span = [f for f in fields if f[0] == field][0]
    # Blank the field instead of deleting it: a multi-line field would
    # shift every error line below it and misattribute the breakage.
    stripped = (text[:span[1]] + blank_span(text, span[1], span[2]) +
                text[span[2]:])
    # Repair constructor literals: blank the top-level `field := expr`
    # segment plus one adjacent comma in brace literals that also assign
    # a sibling field. Blanking keeps every newline, so error line
    # numbers still match the tree.
    siblings = [f[0] for f in fields if f[0] != field]
    sib_re = "(?:" + "|".join(re.escape(s) for s in siblings) + ")"
    chars = list(stripped)
    for m in re.finditer(r"\{", stripped):
        depth_end = find_matching(stripped, m.start(), "{", "}")
        if depth_end < 0:
            continue
        segs = split_top_spans(stripped[m.start() + 1:depth_end - 1])
        idx = None
        has_sib = False
        for k, (seg, _a, _b) in enumerate(segs):
            if re.match(r"\s*" + re.escape(field) + r"\s*:=", seg):
                idx = k
            if re.match(r"\s*" + sib_re + r"\s*:=", seg):
                has_sib = True
        if idx is None or not has_sib:
            continue
        base = m.start() + 1
        if idx + 1 < len(segs):
            bstart = base + segs[idx][1]
            bend = base + segs[idx + 1][1]
        else:
            bstart = base + segs[idx - 1][2]
            bend = base + segs[idx][2]
        blanked = blank_span(stripped, bstart, bend)
        for j, ch in enumerate(blanked):
            chars[bstart + j] = ch
    return "".join(chars), None


def probe_field(lane, struct, field, keep):
    """Remove STRUCT.field and rebuild the cone."""
    hits = find_decl_source(struct)
    if len(hits) != 1:
        return {"verdict": "INCONCLUSIVE", "note": "structure not unique"}
    src = hits[0]
    proj_rel = "Grammatik/" + src.name
    text = src.read_text(encoding="utf-8")
    repaired, err = strip_structure_field(text, struct, field)
    if err:
        return {"verdict": "INCONCLUSIVE", "note": err}
    lane.restore([proj_rel])
    ok, msg = lane.push_files({proj_rel: repaired})
    if not ok:
        return {"verdict": "INCONCLUSIVE", "note": "push failed"}
    ok_b, log = lane.build()
    cone = cone_tables()
    failed = classify_build(log, cone, struct)
    real = {k: v for k, v in failed.items() if not k.startswith("CASCADE")}
    if not keep:
        lane.restore([proj_rel])
    if ok_b:
        return {"verdict": "UNUSED", "failed": real,
                "note": "cone builds with the field removed"}
    proved = []
    for key in real:
        fname, _, decl = key.partition(":")
        for cand, table in cone.items():
            if pathlib.Path(cand).name == fname and decl in table:
                if table[decl][0] in ("theorem", "example"):
                    proved.append(key)
    if proved:
        return {"verdict": "DERIVED", "failed": real,
                "note": "%d proved declarations break" % len(proved)}
    if real:
        return {"verdict": "FORWARDED", "failed": real,
                "note": "only the structure and constructor defs break"}
    return {"verdict": "INCONCLUSIVE", "failed": real,
            "note": "build failed without file errors"}


def split_arrows(conclusion):
    """Split a proposition at top-level arrows (unicode or ASCII)."""
    parts, depth, cur = [], 0, []
    i = 0
    while i < len(conclusion):
        ch = conclusion[i]
        if ch in "([{":
            depth += 1
            cur.append(ch)
        elif ch in ")]}":
            depth -= 1
            cur.append(ch)
        elif depth == 0 and ch == ARROW:
            parts.append("".join(cur))
            cur = []
        elif depth == 0 and conclusion.startswith("->", i):
            parts.append("".join(cur))
            cur = []
            i += 1
        else:
            cur.append(ch)
        i += 1
    parts.append("".join(cur))
    return parts


def probe_gates(lane, thm, word, keep):
    """Delete conclusion arrows mentioning Word; drop matching intros."""
    hits = find_decl_source(thm)
    if len(hits) != 1:
        return {"verdict": "INCONCLUSIVE", "note": "theorem not unique"}
    src = hits[0]
    proj_rel = "Grammatik/" + src.name
    text = src.read_text(encoding="utf-8")
    sig = theorem_signature(text, thm)
    if sig is None:
        return {"verdict": "INCONCLUSIVE", "note": "signature not parsed"}
    # The conclusion starts after the leading binder prefix: walk
    # groups from position zero, stopping at the first non-group char.
    pos = 0
    while True:
        while pos < len(sig) and sig[pos] in " \t\n":
            pos += 1
        if pos < len(sig) and sig[pos] in "([{":
            end = find_matching(sig, pos, sig[pos],
                                {"(": ")", "[": "]", "{": "}"}[sig[pos]])
            if end < 0:
                return {"verdict": "INCONCLUSIVE",
                        "note": "unbalanced binder group"}
            pos = end
        else:
            break
    conclusion = sig[pos:]
    parts = split_arrows(conclusion)
    gate_idx = [k for k, p in enumerate(parts[:-1]) if word in p]
    if not gate_idx:
        return {"verdict": "INCONCLUSIVE",
                "note": "no conclusion arrow mentions " + word}
    # Deleted parts take their following arrow with them; the lost
    # newlines are compensated at the end of the conclusion so body
    # lines below never shift.
    deleted_nl = sum(parts[k].count("\n") for k in gate_idx)
    kept = [p for k, p in enumerate(parts) if k not in gate_idx]
    new_conclusion = ARROW.join(kept) + "\n" * deleted_nl
    abs_conc = text.index(conclusion)
    patched = text[:abs_conc] + new_conclusion + text[abs_conc + len(conclusion):]
    # Gate binders live in the proof's `intro`, not in the conclusion:
    # each conclusion part before the last binds names positionally (one
    # per arrow, plus the forall-bound names inside the part), and the
    # intro line consumes them in order. Deleted arrows map to intro
    # positions by cumulative count.
    counts = []
    for part in parts[:-1]:
        n_forall = 0
        for fm in re.finditer(r"∀", part):
            # Every binder group up to the comma belongs to this forall.
            gpos = fm.end()
            while True:
                while gpos < len(part) and part[gpos] in " \t\n":
                    gpos += 1
                if gpos < len(part) and part[gpos] in "([{":
                    gend = find_matching(part, gpos, part[gpos],
                                         {"(": ")", "[": "]",
                                          "{": "}"}[part[gpos]])
                    inner = part[gpos + 1:gend - 1]
                    colon = inner.find(":")
                    if colon >= 0:
                        n_forall += len(inner[:colon].split())
                    gpos = gend
                else:
                    break
        counts.append(n_forall + 1)
    decl_m = re.search(r"^((?:noncomputable\s+|private\s+)?" + DECLKIND +
                       r")\s+" + re.escape(thm) + r"\b", patched, re.M)
    body = patched[patched.index(":=", decl_m.end()):]
    im = re.search(r"^(\s*)intro\s+([^\n]*)$", body, re.M)
    if not im:
        return {"verdict": "INCONCLUSIVE", "note": "intro line not found"}
    intro_names = im.group(2).split()
    if len(intro_names) != sum(counts):
        return {"verdict": "INCONCLUSIVE",
                "note": "intro/binder count mismatch %d vs %d" %
                        (len(intro_names), sum(counts))}
    drop = set()
    pos = 0
    for k, cnt in enumerate(counts):
        if k in gate_idx:
            drop.update(intro_names[pos:pos + cnt])
        pos += cnt
    if not drop:
        return {"verdict": "INCONCLUSIVE", "note": "gate binders not isolated"}
    gate_names = sorted(drop)
    for gname in gate_names:
        patched = re.sub(r"(intro[^\n]*?)\s+\b" + re.escape(gname) + r"\b",
                         r"\1", patched)
    lane.restore([proj_rel])
    ok, msg = lane.push_files({proj_rel: patched})
    if not ok:
        return {"verdict": "INCONCLUSIVE", "note": "push failed"}
    ok_b, log = lane.build()
    cone = cone_tables()
    failed = classify_build(log, cone, thm)
    real = {k: v for k, v in failed.items() if not k.startswith("CASCADE")}
    if not keep:
        lane.restore([proj_rel])
    if ok_b:
        return {"verdict": "FORWARDED", "failed": real,
                "note": "conclusion holds without the gates -- decorative"}
    gate_used = any(word in v or any(g in v for g in gate_names)
                    for v in real.values())
    if gate_used:
        return {"verdict": "DERIVED", "failed": real,
                "note": "proof body consumes the gates"}
    return {"verdict": "INCONCLUSIVE", "failed": real,
            "note": "failure mentions no gate -- inspect log"}


def split_conjuncts(ty):
    """Split a proposition at top-level conjunctions; return conjuncts.

    Separators are the unicode `∧` and the ASCII `/\\` at bracket depth
    zero. Anything else (including a bare proposition) returns as one
    conjunct. Conjunctions under binders (after a `∀`) are NOT split:
    the caller passes the whole conclusion, and a leading `∀ ... ,`
    body keeps its depth-zero `∧` -- splitting there would claim one
    theorem where the binders belong to both sides. Callers that want
    the top arrow/forall spine intact check `split_top_spans` first;
    here depth counts only brackets, so `∀ x, P x ∧ Q x` splits into
    `∀ x, P x` and `Q x`, which is wrong -- such conclusions are
    rejected by parse_conjunct_proof unless every `∧` sits before any
    top-level `∀`/`,` binder tail. In practice the tree targets carry
    closed conjuncts (`(∀ f j, ...) ∧ ...`), which split cleanly.
    """
    parts, depth, cur = [], 0, []
    i = 0
    in_str = False
    while i < len(ty):
        ch = ty[i]
        if ch == '"' and (i == 0 or ty[i - 1] != "\\"):
            in_str = not in_str
            cur.append(ch)
            i += 1
            continue
        if in_str:
            cur.append(ch)
            i += 1
            continue
        if ch in "([{" or ch in "⟨‹«":
            depth += 1
            cur.append(ch)
        elif ch in ")]}" or ch in "⟩›»":
            depth -= 1
            cur.append(ch)
        elif depth == 0 and ch == "∧":
            parts.append("".join(cur))
            cur = []
        elif depth == 0 and ty.startswith("/\\", i):
            parts.append("".join(cur))
            cur = []
            i += 1
        else:
            cur.append(ch)
        i += 1
    parts.append("".join(cur))
    return parts


def sig_conclusion(sig):
    """Split a signature into (binder prefix, conclusion).

    The binder prefix is the leading run of groups; the conclusion is
    everything after it. Returns (None, None) when no group leads.
    """
    pos = 0
    while True:
        while pos < len(sig) and sig[pos] in " \t\n":
            pos += 1
        if pos < len(sig) and sig[pos] in "([{":
            end = find_matching(sig, pos, sig[pos],
                                {"(": ")", "[": "]", "{": "}"}[sig[pos]])
            if end < 0:
                return None, None
            pos = end
        else:
            break
    if pos == 0:
        return None, None
    conclusion = sig[pos:].strip()
    # The `:` separating binders from the conclusion belongs to
    # neither side: strip one leading colon.
    if conclusion.startswith(":"):
        conclusion = conclusion[1:].strip()
    return sig[:pos], conclusion


def explicit_binder_names(text, thm):
    """Explicit binder names of the signature prefix (never the conclusion).

    parse_signature over the whole signature would also read parenthesized
    groups inside the conclusion as binders; the prefix walk stops where
    the binders stop.
    """
    sig = theorem_signature(text, thm)
    if sig is None:
        return None
    prefix, _conc = sig_conclusion(sig)
    if prefix is None:
        return None
    return [nm for names, exp, _h in parse_signature(prefix)
            for nm in names if exp]


def weaken_names_in_sig(sig, targets):
    """Weaken several binder types to True; return (prefix, error).

    Runs through a synthetic mini-declaration so the existing
    single-premise patch applies unchanged. Groups weaken as one
    bundle: every name in a touched group must be a target, else the
    group cannot split and the probe reports INCONCLUSIVE (same rule
    as the per-theorem variant A).
    """
    remaining = set(targets)
    cur = "theorem __tmp" + sig + " := sorry"
    while remaining:
        entries, err = group_spans(cur, "__tmp")
        if err:
            return None, err
        todo = None
        for names, explicit, has_type, estart, eend, _pos in entries:
            if not explicit or not has_type:
                continue
            if cur[estart:eend].strip() == "True":
                remaining.difference_update(names)
                continue
            touch = [nm for nm in names if nm in remaining]
            if not touch:
                continue
            if len(touch) != len(names):
                return None, "shared binder group " + " ".join(names)
            todo = (estart, eend, names)
            break
        if todo is None:
            if remaining:
                return None, "premise %s not found in signature" % sorted(
                    remaining)[0]
            break
        estart, eend, names = todo
        cur = weaken_span(cur, estart, eend)
        remaining.difference_update(names)
    back = theorem_signature(cur, "__tmp")
    if back is None:
        return None, "weakened signature not parsed"
    prefix, _conc = sig_conclusion(back)
    if prefix is None:
        return None, "weakened binders not parsed"
    return prefix, None


def parse_conjunct_proof(text, thm):
    """Split a conjunction theorem into prefix + per-conjunct closers.

    Handles two proof shapes, both with a shared tactic prefix (obtain/
    have lines) before a tuple closer:

      exact shape   `exact ⟨c1, ..., cN⟩` -- closer i is `exact ci`.
      refine shape  `refine ⟨s1, ..., sN⟩` with one `·` bullet block per
                    `?_` hole in order -- closer i is the dedented bullet
                    block for a hole, `exact si` for a term.

    Returns (prefix_sig, conjuncts, closers, error): prefix_sig is the
    (unweakened) binder prefix, conjuncts the conclusion parts, closers
    the per-conjunct proof bodies. Anything else (no conjunction,
    other closer, component/conjunct count mismatch, missing bullet)
    returns an error and the caller reports INCONCLUSIVE -- the shape
    vocabulary stays closed rather than guessing.
    """
    sig = theorem_signature(text, thm)
    if sig is None:
        return None, None, None, "signature of %s not parsed" % thm
    prefix_sig, conclusion = sig_conclusion(sig)
    if conclusion is None:
        return None, None, None, "no binder prefix in signature"
    # A top-level forall spine owns the conjunction: `∀ x, P x ∧ Q x`
    # would split into a binder fragment and a bare tail. Reject when
    # the conclusion opens with a forall before any conjunction part.
    stripped = conclusion.strip()
    if stripped.startswith("∀") or re.match(r"forall\b", stripped):
        return None, None, None, "conclusion is forall-quantified"
    conjuncts = split_conjuncts(conclusion)
    if len(conjuncts) < 2:
        return None, None, None, "conclusion is not a conjunction"
    table = decl_table_text(text)
    if thm not in table:
        return None, None, None, "declaration lines not found"
    _kind, start, end = table[thm]
    lines = text.splitlines()
    body_lines = lines[start - 1:end]
    body = "\n".join(body_lines)
    # The proof opens after the declaration-level `:=`: a plain find
    # would stop at binder defaults like `(D := D)` in the signature.
    # Walk from the declaration match at depth zero instead.
    dm = re.search(r"^((?:noncomputable\s+|private\s+)?" + DECLKIND +
                   r")\s+" + re.escape(thm) + r"\b", text, re.M)
    if dm is None:
        return None, None, None, "declaration head not found"
    di, depth = dm.end(), 0
    assign = -1
    while di < len(text):
        ch = text[di]
        if ch in "([{" or ch in "⟨‹«":
            depth += 1
        elif ch in ")]}" or ch in "⟩›»":
            depth -= 1
        elif depth == 0 and text.startswith(":=", di):
            assign = di - (len("\n".join(lines[:start - 1])) +
                           (1 if start > 1 else 0))
            break
        di += 1
    if assign < 0 or assign >= len(body):
        return None, None, None, "proof body not found"
    tactics = body[assign + 2:]
    m = None
    for cm in re.finditer(r"^([ \t]*)(exact|refine)\s+⟨", tactics, re.M):
        m = cm
    if m is None:
        return None, None, None, "no exact/refine tuple closer"
    open_pos = tactics.find("⟨", m.start())
    body_open = assign + 2 + open_pos
    close_end = find_matching(body, body_open, "⟨", "⟩")
    if close_end < 0:
        return None, None, None, "unbalanced tuple closer"
    inner = body[body_open + 1:close_end - 1]
    components = split_top_commas(inner)
    if len(components) != len(conjuncts):
        return None, None, None, \
            "component/conjunct count mismatch %d vs %d" % \
            (len(components), len(conjuncts))
    after = tactics[m.end():]
    bullets = []
    cur_block, in_block = [], False
    for ln in after.splitlines()[1:]:
        if re.match(r"^[ \t]*·", ln):
            if cur_block:
                bullets.append(cur_block)
            cur_block = [ln]
            in_block = True
        elif in_block:
            if ln.strip() == "":
                cur_block.append(ln)
            elif re.match(r"^[ \t]*·", ln):
                bullets.append(cur_block)
                cur_block = [ln]
            else:
                # Continuation while indented past the bullet; a new
                # declaration or dedented tactic ends the block run.
                indent = len(ln) - len(ln.lstrip())
                if indent >= 2 and ln.strip() != "":
                    cur_block.append(ln)
                else:
                    break
    if cur_block:
        bullets.append(cur_block)
    holes = [c for c in components if c.strip() == "?_"]
    if len(holes) > len(bullets):
        return None, None, None, "fewer bullet blocks than holes"
    # The shared prefix is everything between `by` and the closer line.
    closer_line_start = tactics[:m.start()].count("\n")
    prelim = tactics.splitlines()[:closer_line_start]
    # tactics opens with the rest of the `:= by` line: a lone `by` is
    # the opening, not a prefix step.
    if prelim and prelim[0].strip() == "by":
        prelim = prelim[1:]
    prefix = "\n".join(prelim)
    if not prefix.endswith("\n") and prefix.strip() != "":
        prefix += "\n"
    closers = []
    bullet_idx = 0
    for comp in components:
        if comp.strip() == "?_":
            block = bullets[bullet_idx]
            bullet_idx += 1
            # Content column of the bullet line (`  · tac` -> tac at 4):
            # continuations dedent by the same width, or the tactic
            # column staggers and the block dies for grammar reasons.
            mfirst = re.match(r"^[ \t]*·\s?", block[0])
            base_col = len(mfirst.group(0)) if mfirst else 0
            first = block[0][base_col:]
            rest = [ln[base_col:] if ln.strip() and len(ln) >= base_col
                    and ln[:base_col].strip() == "" else ln
                    for ln in block[1:]]
            closers.append(first + "\n" + "\n".join(rest))
        else:
            closers.append("exact " + comp.strip())
    return prefix_sig, conjuncts, (prefix, closers), None


def build_conjunct_copies(text, thm, weaken_targets, drop_res):
    """Insert one tripwire copy per conjunct; return (new_text, error).

    Each copy `THM__c{i}` keeps the (weakened) binders, narrows the
    conclusion to conjunct i, and runs the shared prefix minus dropped
    lines plus its own closer. weaken_targets are binder names set to
    True; drop_res are regexes for prefix lines that cannot survive
    the strip (obtain lines off a weakened premise). Copies go right
    after the target declaration -- still inside its namespace -- and
    the original is untouched, so no call site needs patching.
    """
    if re.search(r"\b" + re.escape(thm) + r"__c\d+\b", text):
        return None, "tripwire names already present"
    parsed = parse_conjunct_proof(text, thm)
    prefix_sig, conjuncts, proof, err = parsed
    if err:
        return None, err
    weakened, err = weaken_names_in_sig(prefix_sig, weaken_targets)
    if err:
        return None, err
    prefix, closers = proof
    kept = []
    for ln in prefix.splitlines(keepends=True):
        if any(rx.search(ln) for rx in drop_res):
            continue
        kept.append(ln)
    kept_prefix = "".join(kept)
    copies = []
    for i, (conj, closer) in enumerate(zip(conjuncts, closers), start=1):
        # Generated closer lines take two spaces: a tactic at column
        # zero after `by` parses as a command and the copy dies for
        # grammar reasons instead of premise reasons. Prefix lines
        # keep their tree indentation.
        indented = "\n".join(("  " + ln) if ln.strip() else ln
                             for ln in closer.splitlines())
        copies.append("theorem %s__c%d%s : %s := by\n%s%s\n" %
                     (thm, i, weakened, conj.strip(), kept_prefix, indented))
    table = decl_table_text(text)
    _kind, _start, end = table[thm]
    off = len("\n".join(text.splitlines()[:end]))
    # Trailing non-declaration commands (`#print axioms`, `end`) are
    # not declarations: table end can sit past the namespace close,
    # which would strand the copies outside it. Cap the insertion at
    # the first `end` line after the declaration head.
    for i, ln in enumerate(text.splitlines()):
        if i + 1 >= _start and re.match(r"^end(\s|$)", ln):
            off = min(off, len("\n".join(text.splitlines()[:i])))
            break
    return text[:off] + "\n" + "\n".join(copies) + "\n" + text[off:], None


def check_conjunct_variant(src, thm, prem, idx, weaken_rest=False):
    """Append narrowed tripwire copies, check copy idx with lean.

    Returns (verdict_word, log): NEEDS/FREE for the need question
    (weaken prem), ALONE/JOINT for the strength question (weaken every
    other explicit premise). None plus a note when the text patch
    itself fails -- the fixture is out of shape vocabulary.
    """
    sig = theorem_signature(src, thm)
    if sig is None:
        return None, "signature not parsed"
    if weaken_rest:
        bound = explicit_binder_names(src, thm)
        if bound is None:
            return None, "binder prefix not parsed"
        targets = [nm for nm in bound if nm != prem]
        drops = [re.compile(r"\b" + re.escape(nm) + r"\b")
                 for nm in targets]
    else:
        targets, drops = [prem], [re.compile(r"\b" + re.escape(prem) +
                                             r"\b")]
    variant, err = build_conjunct_copies(src, thm, targets, drops)
    if err:
        return None, err
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False,
                                     encoding="utf-8") as tmp:
        tmp.write(variant)
        tmpname = tmp.name
    try:
        code, out = run([LEAN, tmpname], timeout=180)
    finally:
        os.unlink(tmpname)
    table = decl_table_text(variant)
    copy = "%s__c%d" % (thm, idx)
    red = False
    for line in out.splitlines():
        # Hermetic `lean` prints `file:line:col: error:` (lake build
        # prints the mirrored `error: file:line:col:` that ERRORRE
        # reads -- lane attribution is untouched).
        m = HERMERRORRE.match(line.strip())
        if not m:
            continue
        lineno = int(m.group(2))
        if copy in table and table[copy][1] <= lineno <= table[copy][2]:
            red = True
            break
    if weaken_rest:
        return ("JOINT" if red else "ALONE"), out[-800:]
    return ("NEEDS" if red else "FREE"), out[-800:]


def copies_failed(log, patched_tables, target_thm, proj_rel, count):
    """Per-copy red/green from a tripwire build log.

    Tables are recomputed from the patched text (copies live past EOF,
    so tree tables cannot see them). Returns (need_list, failed_map)
    with NEEDS/FREE per conjunct index.
    """
    cone = dict(patched_tables)
    failed = classify_build(log, cone, target_thm)
    real = {k: v for k, v in failed.items()
            if not k.startswith("CASCADE")}
    need = []
    for i in range(1, count + 1):
        hit = [k for k in real if k.endswith(":%s__c%d" % (target_thm, i))]
        need.append("NEEDS" if hit else "FREE")
    return need, real


def rollup_conjuncts(need):
    if all(w == "NEEDS" for w in need):
        return "UNIFORM"
    if all(w == "FREE" for w in need):
        return "DETACHED"
    return "SPLIT"


def probe_hyp_conjuncts(lane, thm, prem, keep):
    """Per-conjunct need plus per-conjunct strength for THM:prem.

    Two lane builds: need (copies with prem weakened, prem-mentioning
    prefix lines dropped) and strength (copies with every other
    explicit premise weakened instead, for NEEDS conjuncts only).
    """
    hits = find_decl_source(thm)
    if len(hits) != 1:
        return {"verdict": "INCONCLUSIVE",
                "note": "declaration %s found in %d files" % (thm, len(hits))}
    src = hits[0]
    proj_rel = "Grammatik/" + src.name
    text = src.read_text(encoding="utf-8")
    parsed = parse_conjunct_proof(text, thm)
    _sig, conjuncts, _proof, err = parsed
    if err:
        return {"verdict": "INCONCLUSIVE", "note": err}
    count = len(conjuncts)
    sig = theorem_signature(text, thm)
    pos = explicit_position(text, thm, prem)
    if pos is None or pos < 0:
        return {"verdict": "INCONCLUSIVE", "note": "premise position unknown"}
    bound = explicit_binder_names(text, thm)
    if bound is None or prem not in bound:
        return {"verdict": "INCONCLUSIVE", "note": "binder prefix not parsed"}
    others = [nm for nm in bound if nm != prem]
    report = {"conjuncts": count, "others": others}
    # ---- Need variant: weaken prem, drop prem-mentioning prefix lines.
    need_text, err = build_conjunct_copies(
        text, thm, [prem], [re.compile(r"\b" + re.escape(prem) + r"\b")])
    if err:
        return {"verdict": "INCONCLUSIVE", "note": "need copies: " + err}
    lane.restore([proj_rel])
    ok, msg = lane.push_files({proj_rel: need_text})
    if not ok:
        return {"verdict": "INCONCLUSIVE", "note": "push failed: " + msg}
    _ok_n, log_n = lane.build()
    base = cone_tables()
    patched = dict(base)
    patched[proj_rel] = decl_table_text(need_text)
    need, real_n = copies_failed(log_n, patched, thm, proj_rel, count)
    report["need"] = need
    report["need_failed"] = real_n
    verdict = rollup_conjuncts(need)
    # ---- Strength variant: weaken the rest, for NEEDS conjuncts only.
    strength = ["n/a"] * count
    if any(w == "NEEDS" for w in need) and others:
        drops = [re.compile(r"\b" + re.escape(nm) + r"\b")
                 for nm in others]
        str_text, err = build_conjunct_copies(text, thm, others, drops)
        if err:
            report["strength_note"] = "strength copies: " + err
        else:
            ok, msg = lane.push_files({proj_rel: str_text})
            if not ok:
                report["strength_note"] = "push failed"
            else:
                _ok_s, log_s = lane.build()
                patched_s = dict(base)
                patched_s[proj_rel] = decl_table_text(str_text)
                _need_s, real_s = copies_failed(log_s, patched_s, thm,
                                                proj_rel, count)
                report["strength_failed"] = real_s
                for i in range(count):
                    if need[i] == "NEEDS":
                        hit = [k for k in real_s
                               if k.endswith(":%s__c%d" % (thm, i + 1))]
                        strength[i] = "JOINT" if hit else "ALONE"
    if not keep:
        lane.restore([proj_rel])
    report["strength"] = strength
    if any(s == "ALONE" for s in strength):
        note = "conjunct follows from the premise alone -- restatement shape"
    elif any(s == "JOINT" for s in strength):
        note = "needy conjuncts need the rest too -- joint use"
    elif verdict == "SPLIT":
        note = "premise feeds only some conjuncts"
    elif verdict == "UNIFORM":
        note = "every conjunct needs the premise"
    else:
        note = "no conjunct needs the premise"
    report.update({"verdict": verdict, "note": note})
    return report


def probe_field_conjuncts(lane, struct, field, target, keep):
    """Per-conjunct need of TARGET against a removed STRUCT.field.

    One lane build: the structure patch plus one tripwire copy per
    conjunct of the target. No strength dual (weakening every other
    field changes the representation itself, not the premise).
    """
    shits = find_decl_source(struct)
    thits = find_decl_source(target)
    if len(shits) != 1 or len(thits) != 1:
        return {"verdict": "INCONCLUSIVE", "note": "declaration not unique"}
    ssrc, tsrc = shits[0], thits[0]
    srel, trel = "Grammatik/" + ssrc.name, "Grammatik/" + tsrc.name
    stext = ssrc.read_text(encoding="utf-8")
    ttext = tsrc.read_text(encoding="utf-8")
    stripped, err = strip_structure_field(stext, struct, field)
    if err:
        return {"verdict": "INCONCLUSIVE", "note": err}
    base = stripped if srel == trel else ttext
    parsed = parse_conjunct_proof(base, target)
    _sig, conjuncts, _proof, perr = parsed
    if perr:
        return {"verdict": "INCONCLUSIVE", "note": perr}
    count = len(conjuncts)
    # Prefix lines off the stripped field cannot survive: an obtain
    # line over M.hEin breaks as a whole even for conjuncts that never
    # touch it. The closer itself stays intact -- its own redness is
    # the signal.
    copies, err = build_conjunct_copies(
        base, target, [], [re.compile(r"\b" + re.escape(field) + r"\b")])
    if err:
        return {"verdict": "INCONCLUSIVE", "note": "copies: " + err}
    changed = {srel: stripped}
    if srel == trel:
        # Copies were built on the stripped text: both patches compose
        # in the one file.
        changed = {srel: copies}
    else:
        changed[trel] = copies
    lane.restore([srel] if srel == trel else [srel, trel])
    ok, msg = lane.push_files(changed)
    if not ok:
        return {"verdict": "INCONCLUSIVE", "note": "push failed: " + msg}
    _ok_n, log_n = lane.build()
    base_tables = cone_tables()
    patched = dict(base_tables)
    for rel, txt in changed.items():
        patched[rel] = decl_table_text(txt)
    need, real_n = copies_failed(log_n, patched, target, trel, count)
    if not keep:
        lane.restore([srel] if srel == trel else [srel, trel])
    verdict = rollup_conjuncts(need)
    report = {"verdict": verdict, "conjuncts": count, "need": need,
              "need_failed": real_n,
              "note": "field feeds only some conjuncts" if verdict == "SPLIT"
              else "every conjunct needs the field" if verdict == "UNIFORM"
              else "no conjunct needs the field"}
    return report


SPEECH_SPLIT = """-- Speech fixture SPLIT: w1w2w4 shape -- conjunct 1 from h,
-- conjunct 2 from k. Per-conjunct need must read [NEEDS, FREE].
theorem mid (h : 0 < 1) (k : 2 < 3) : 0 < 1 ∧ 2 < 3 := by
  exact ⟨h, k⟩
"""

SPEECH_UNIFORM = """-- Speech fixture UNIFORM: both conjuncts from h alone.
-- Per-conjunct need must read [NEEDS, NEEDS].
theorem mid (h : 0 < 1) : 0 < 1 ∧ 0 < 2 := by
  exact ⟨h, Nat.lt_trans h (by decide)⟩
"""

SPEECH_WEAK = """-- Speech fixture WEAK: restatement shape -- conjunct 1 IS h.
-- Need reads NEEDS, strength reads ALONE (k weakened, copy green).
theorem mid (h : 0 < 1) (k : 2 < 3) : 0 < 1 ∧ 0 < 1 := by
  exact ⟨h, h⟩
"""

SPEECH_STRONG = """-- Speech fixture STRONG: joint-use shape -- conjunct 1 needs
-- h AND k together. Need reads NEEDS, strength reads JOINT.
theorem mid (h : 0 < 1) (k : 1 < 2) : 0 < 2 ∧ 0 < 1 := by
  exact ⟨Nat.lt_trans h k, h⟩
"""

SPEECH_DERIVED = """-- Speech fixture DERIVED: joint-use pattern quoted from
-- `ungeteilt_aus_lauf` (Geteilt.lean): the stripped premise is one
-- ingredient among several in the proof term.
theorem mid (h : 0 < 1) (k : 2 < 3) : 0 < 1 ∧ 2 < 3 := ⟨h, k⟩
theorem down : 0 < 1 ∧ 2 < 3 := mid (by decide) (by decide)
"""

SPEECH_FORWARDED = """-- Speech fixture FORWARDED: restatement pattern quoted from
-- `ziel_l5_schranke` (Ziel.lean): the premise alone is the conclusion.
theorem mid (h : 0 < 1) (k : 2 < 3) : 0 < 1 := h
theorem down : 0 < 1 := mid (by decide) (by decide)
"""


def check_single_variant(src, thm, prem, weaken_all_but=None):
    """Weaken premises in src, patch the call, check with lean.

    Returns (builds, log). weaken_all_but=None weakens prem itself
    (variant A); otherwise weakens every explicit premise but prem
    (variant B).
    """
    sig = theorem_signature(src, thm)
    names = [nm for group, exp, _h in parse_signature(sig)
             for nm in group if exp]
    if weaken_all_but is None:
        targets = [prem]
    else:
        targets = [nm for nm in names if nm != prem]
    cur = src
    for target in targets:
        cur, err = apply_weaken_to_text(cur, thm, target)
        if err:
            return None, "patch failed at " + target + ": " + err
    files = {"probe.lean": cur}
    for target in targets:
        pos = explicit_position(src, thm, target)
        if pos is None or pos < 0:
            return None, "position unknown for " + target
        cp, unp, _ = patch_call_sites(files, thm, target, pos)
        if unp:
            return None, "call site ambiguous: %s" % unp[0][:100]
        files.update(cp)
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False,
                                     encoding="utf-8") as tmp:
        tmp.write(files["probe.lean"])
        tmpname = tmp.name
    try:
        code, out = run([LEAN, tmpname], timeout=180)
    finally:
        os.unlink(tmpname)
    return code == 0, out[-1500:]


def speech_probe():
    """All directions, hermetic: lean over scratch files, no lake."""
    cases = [("derived", SPEECH_DERIVED, "mid", "h", "DERIVED"),
             ("forwarded", SPEECH_FORWARDED, "mid", "h", "FORWARDED")]
    results = []
    for tag, src, thm, prem, want in cases:
        with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False,
                                         encoding="utf-8") as tmp:
            tmp.write(src)
            tmpname = tmp.name
        try:
            code, out = run([LEAN, tmpname], timeout=180)
        finally:
            os.unlink(tmpname)
        if code != 0:
            print("  speech %s: FIXTURE RED (not a probe result)" % tag)
            print(out[-1500:])
            return False
        builds_a, log_a = check_single_variant(src, thm, prem)
        if builds_a is None:
            print("  speech %s: variant A error: %s" % (tag, log_a))
            return False
        if builds_a:
            got, note = "UNUSED", "variant A builds"
        else:
            builds_b, log_b = check_single_variant(src, thm, prem,
                                                   weaken_all_but=True)
            if builds_b is None:
                print("  speech %s: variant B error: %s" % (tag, log_b))
                return False
            got = "FORWARDED" if builds_b else "DERIVED"
            note = "A red, B %s" % ("green" if builds_b else "red")
        ok = got == want
        print("  speech %-9s reads %-9s (want %-9s) -- %s (%s)" %
              (tag, got, want, "PASS" if ok else "FAIL", note))
        results.append(ok)
    # Per-conjunct need: SPLIT says [NEEDS, FREE], UNIFORM [NEEDS, NEEDS].
    conj_cases = [("split", SPEECH_SPLIT, "mid", "h",
                   ["NEEDS", "FREE"], "SPLIT"),
                  ("uniform", SPEECH_UNIFORM, "mid", "h",
                   ["NEEDS", "NEEDS"], "UNIFORM")]
    for tag, src, thm, prem, want_need, want in conj_cases:
        if not speech_conjunct_basis(tag, src):
            return False
        need = []
        for idx in (1, 2):
            got_w, log = check_conjunct_variant(src, thm, prem, idx)
            if got_w is None:
                print("  speech %s: need variant error at c%d: %s" %
                      (tag, idx, log[-400:]))
                return False
            need.append(got_w)
        got = ("SPLIT" if "NEEDS" in need and "FREE" in need
               else "UNIFORM" if all(w == "NEEDS" for w in need)
               else "DETACHED")
        ok = need == want_need and got == want
        print("  speech %-9s reads %-9s %-16s (want %-9s %-16s) -- %s" %
              (tag, got, need, want, want_need,
               "PASS" if ok else "FAIL"))
        results.append(ok)
    # Strength per conjunct: WEAK reads ALONE, STRONG reads JOINT.
    strength_cases = [("weak", SPEECH_WEAK, "mid", "h", 1,
                       "NEEDS", "ALONE"),
                      ("strong", SPEECH_STRONG, "mid", "h", 1,
                       "NEEDS", "JOINT")]
    for tag, src, thm, prem, idx, want_need, want in strength_cases:
        if not speech_conjunct_basis(tag, src):
            return False
        got_need, log = check_conjunct_variant(src, thm, prem, idx)
        if got_need is None:
            print("  speech %s: need variant error: %s" % (tag, log[-400:]))
            return False
        got_str, log = check_conjunct_variant(src, thm, prem, idx,
                                              weaken_rest=True)
        if got_str is None:
            print("  speech %s: strength variant error: %s" %
                  (tag, log[-400:]))
            return False
        ok = got_need == want_need and got_str == want
        print("  speech %-9s reads need %-5s strength %-5s "
              "(want need %-5s strength %-5s) -- %s" %
              (tag, got_need, got_str, want_need, want,
               "PASS" if ok else "FAIL"))
        results.append(ok)
    return all(results)


def speech_conjunct_basis(tag, src):
    """Green-basis gate for a conjunct fixture; False prints and fails."""
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False,
                                     encoding="utf-8") as tmp:
        tmp.write(src)
        tmpname = tmp.name
    try:
        code, out = run([LEAN, tmpname], timeout=180)
    finally:
        os.unlink(tmpname)
    if code != 0:
        print("  speech %s: FIXTURE RED (not a probe result)" % tag)
        print(out[-1500:])
        return False
    return True


USAGE = ("usage: pruefe-praemisse.py [--local] [--keep] --sprechprobe | "
          "THM[:prem[^c]] ... STRUCT.field[@TARGET] ... THM:@Word ...")


def main(argv):
    remote, keep, args = True, False, []
    for a in argv[1:]:
        if a == "--local":
            remote = False
        elif a == "--fisch":
            remote = True
        elif a == "--keep":
            keep = True
        elif a == "--sprechprobe":
            print("== premise probe: speech test (all directions) ==")
            sys.exit(0 if speech_probe() else 2)
        else:
            args.append(a)
    if not args:
        print(USAGE)
        return 2
    lane = Lane(remote)
    print("== premise probe: scratch lane %s ==" % lane.root)
    ok, msg = lane.setup()
    print("  setup: %s" % msg)
    if not ok:
        return 2
    print("  basis build (green required, else no verdict):")
    ok_b, log_b = lane.build()
    print("  basis: %s" % ("GREEN" if ok_b else "RED"))
    if not ok_b:
        print(log_b[-3000:])
        return 2
    rows = []
    for spec in args:
        if ":" in spec:
            thm, _, prem = spec.partition(":")
            if prem.startswith("@"):
                rows.append((spec, "gate", probe_gates(lane, thm, prem[1:], keep)))
            elif prem.endswith("^c"):
                rows.append((spec, "conj",
                             probe_hyp_conjuncts(lane, thm, prem[:-2], keep)))
            else:
                hits = find_decl_source(thm)
                is_struct = bool(hits) and bool(re.search(
                    r"^structure\s+" + re.escape(thm) + r"\b",
                    hits[0].read_text(encoding="utf-8"), re.M))
                if is_struct:
                    rows.append((spec, "field", probe_field(lane, thm, prem, keep)))
                else:
                    rows.append((spec, "hyp", probe_hyp(lane, thm, prem, keep)))
        elif "." in spec:
            struct, _, field = spec.partition(".")
            if "@" in field:
                field, _, target = field.partition("@")
                rows.append((spec, "conj",
                             probe_field_conjuncts(lane, struct, field,
                                                   target, keep)))
            else:
                rows.append((spec, "field",
                             probe_field(lane, struct, field, keep)))
        else:
            hits = find_decl_source(spec)
            if len(hits) != 1:
                rows.append((spec, "hyp", {"verdict": "INCONCLUSIVE",
                                           "note": "theorem not unique"}))
                continue
            text0 = hits[0].read_text(encoding="utf-8")
            sig = theorem_signature(text0, spec)
            prems = [nm for group, exp, _h in parse_signature(sig)
                     for nm in group if exp and re.match(r"h[A-Za-z]", nm)]
            if not prems:
                rows.append((spec, "hyp", {"verdict": "INCONCLUSIVE",
                                           "note": "no h-premises found"}))
                continue
            for prem in prems:
                rows.append(("%s:%s" % (spec, prem), "hyp",
                             probe_hyp(lane, spec, prem, keep)))
    print("\n== verdict table ==")
    print("  %-52s %-6s %-12s %s" % ("probe", "kind", "verdict", "note"))
    for spec, kind, rep in rows:
        print("  %-52s %-6s %-12s %s" % (spec, kind, rep.get("verdict"),
                                         rep.get("note", "")[:70]))
        if rep.get("need") is not None:
            print("      need %-24s strength %s" %
                  (rep.get("need"), rep.get("strength")))
        for key in ("A_failed", "B_failed", "failed", "need_failed",
                    "strength_failed"):
            for site, msg in list(rep.get(key, {}).items())[:6]:
                print("      %-48s %s" % (site, msg[:90]))
        for site in rep.get("sites", [])[:6]:
            print("      UNPATCHED %s" % site)
    counts = {}
    for _s, _k, rep in rows:
        counts[rep.get("verdict")] = counts.get(rep.get("verdict"), 0) + 1
    print("  " + " / ".join("%s %d" % (k, v) for k, v in sorted(counts.items())))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
