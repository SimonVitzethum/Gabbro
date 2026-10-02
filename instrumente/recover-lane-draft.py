#!/usr/bin/env python3
"""Recover one draft file from a recorded lane log (lane 642). Stdlib only.

Replays exact-target file write/edit events from a recorded OpenCode log
without executing any recorded shell or Python command. The target file
path is a CLI argument; no filename is special-cased. Stdout is one JSON
summary line (file content is never printed). Full format list and refusal
rules: dokumente/x86/DRAFT-RECOVERY.md.

Run: python3 instrumente/recover-lane-draft.py --help
"""
import argparse
import ast
import hashlib
import json
import re
import sys
from bisect import bisect_right

TOOL_VERSION = "642.1"
DEFAULT_MAX_BYTES = 200 * 1024 * 1024
DEFAULT_MAX_EVENTS = 100000
DEFAULT_MAX_CONTENT = 20 * 1024 * 1024

# Angle-bracket tool records are matched with patterns assembled at
# runtime so this source stays plain text. INVOKE_RE matches one tool
# record block, PARAM_RE matches one named value element inside it.
_LT = chr(60)
INVOKE_RE = re.compile(
    _LT + "invoke\\b[^>]*\\bname\\s*=\\s*\"(?P<name>[^\"]+)\"[^>]*>"
    r"(?P<body>.*?)"
    + _LT + "/invoke" + chr(62),
    re.S)
PARAM_RE = re.compile(
    _LT + "parameter\\b[^>]*\\bname\\s*=\\s*\"(?P<name>[^\"]+)\"[^>]*>"
    r"(?P<value>.*?)"
    + _LT + "/parameter" + chr(62),
    re.S)
HEREDOC_QUOTED_RE = re.compile(
    r"^\s*cat\s+>\s*(?P<q1>['\"])(?P<path>.+?)(?P=q1)"
    r"\s+<<\s*(?P<q2>['\"])(?P<delim>.+?)(?P=q2)\s*$")
HEREDOC_ANY_RE = re.compile(r"^\s*cat\s+>.*<<")
PATCH_BEGIN_RE = re.compile(r"^\s*\*\*\*\s+Begin\s+Patch\s*$")
PATCH_END_RE = re.compile(r"^\s*\*\*\*\s+End\s+Patch\s*$")
PATCH_SECTION_RE = re.compile(
    r"^\s*\*\*\*\s+(?P<action>Add File|Update File|Delete File|Rename|Move|Copy)"
    r"\s*:\s*(?P<path>.+?)\s*$")
HUNK_RE = re.compile(r"^@@\s+-\d+(?:,\d+)?\s+\+\d+(?:,\d+)?\s+@@")
FENCE_OPEN_RE = re.compile(r"^\s*```python\w*\s*$")
FENCE_CLOSE_RE = re.compile(r"^\s*```\s*$")

WRITE_MODES = frozenset(["w", "wt", "w+", "w+t"])
READ_MODES = frozenset(["r", "rt", "r+t", "U", "rU"])
TRUE_WORDS = frozenset(["1", "true", "yes"])
FALSE_WORDS = frozenset(["0", "false", "no", ""])


def build_parser():
    p = argparse.ArgumentParser(description="recover one draft from a log")
    p.add_argument("--input", required=True, help="recorded log file (-=stdin)")
    p.add_argument("--target", required=True, help="exact target file path")
    p.add_argument("--output", required=True, help="reconstructed file path")
    p.add_argument("--seed", default=None, help="optional seed file")
    p.add_argument("--expect-md5", default=None)
    p.add_argument("--expect-lines", type=int, default=None)
    p.add_argument("--max-bytes", type=int, default=DEFAULT_MAX_BYTES)
    p.add_argument("--max-events", type=int, default=DEFAULT_MAX_EVENTS)
    p.add_argument("--max-content", type=int, default=DEFAULT_MAX_CONTENT)
    p.add_argument("--report", default=None, help="optional JSON report path")
    return p


def unescape_xml(value):
    return (value.replace("&lt;", "<").replace("&gt;", ">")
            .replace("&quot;", "\"").replace("&apos;", "'")
            .replace("&amp;", "&"))


def parse_replace_all(value):
    if isinstance(value, bool):
        return value
    if isinstance(value, int):
        if value == 1:
            return True
        if value == 0:
            return False
        return None
    if isinstance(value, str):
        word = value.strip().lower()
        if word in TRUE_WORDS:
            return True
        if word in FALSE_WORDS:
            return False
    return None


def is_str_const(node):
    return isinstance(node, ast.Constant) and isinstance(node.value, str)


def open_call_path_mode(call, want):
    """If call is open(P[, mode]) with constant args, return (path, mode)."""
    if not (isinstance(call, ast.Call) and isinstance(call.func, ast.Name)
            and call.func.id == "open" and not call.keywords):
        return None
    if len(call.args) == 1 and is_str_const(call.args[0]):
        if want == "any" or "r" in want:
            return (call.args[0].value, "")
    if len(call.args) == 2 and is_str_const(call.args[0]) \
            and is_str_const(call.args[1]):
        return (call.args[0].value, call.args[1].value)
    return None


def analyse_python_block(source, target):
    """Return (ops, refusal). Straight-line literal file effects only.

    Allowed: imports (skipped), docstring expressions (skipped),
    literal Path/open aliases, literal reads, constant-only writes and
    read().replace(O, N) write-backs, all against the exact target.
    Anything else poisons the whole block: replay nothing from it.
    Never executes.
    """
    try:
        tree = ast.parse(source)
    except (SyntaxError, ValueError):
        return (None, "python_syntax")
    env = {}
    ops = []
    for stmt in tree.body:
        if not process_py_stmt(stmt, target, env, ops):
            name = type(stmt).__name__
            if isinstance(stmt, ast.Expr):
                name = "Expr:" + type(stmt.value).__name__
            return (None, "python_unsupported:" + name)
    return (ops, None)


def process_py_stmt(stmt, target, env, ops):
    if isinstance(stmt, (ast.Import, ast.ImportFrom)):
        return True
    if isinstance(stmt, ast.Expr) and is_str_const(stmt.value):
        return True
    if isinstance(stmt, ast.With):
        return process_py_with(stmt, target, env, ops)
    if isinstance(stmt, ast.Assign):
        if len(stmt.targets) != 1 or not isinstance(stmt.targets[0], ast.Name):
            return False
        return process_py_assign(stmt.targets[0].id, stmt.value, target, env)
    if isinstance(stmt, ast.AnnAssign):
        if not isinstance(stmt.target, ast.Name) or stmt.value is None:
            return False
        return process_py_assign(stmt.target.id, stmt.value, target, env)
    if isinstance(stmt, ast.Expr):
        return process_py_write_expr(stmt.value, target, env, ops)
    return False


def process_py_assign(name, value, target, env):
    if is_str_const(value):
        env[name] = ("lit", value.value)
        return True
    if isinstance(value, ast.Call) and isinstance(value.func, ast.Name) \
            and value.func.id == "Path" and len(value.args) == 1 \
            and is_str_const(value.args[0]) and not value.keywords:
        env[name] = ("path", value.args[0].value)
        return True
    if isinstance(value, ast.Call) and isinstance(value.func, ast.Name) \
            and value.func.id == "open" and not value.keywords:
        pm = open_call_path_mode(value, "any")
        if pm is None:
            return False
        path, mode = pm
        if mode in WRITE_MODES:
            env[name] = ("openw", path)
            return True
        if mode == "" or mode in READ_MODES:
            env[name] = ("openr", path)
            return True
        return False
    if read_of_target(value, target, env):
        env[name] = ("readvar", None)
        return True
    edit = replace_of(value, target, env)
    if edit is not None:
        env[name] = ("pending_edit", edit[0], edit[1])
        return True
    return False


def read_of_target(node, target, env):
    """True if node is a literal read of the exact target."""
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
            and not node.args and not node.keywords):
        return False
    recv = node.func.value
    attr = node.func.attr
    if attr == "read" and isinstance(recv, ast.Call):
        pm = open_call_path_mode(recv, "r")
        if pm is not None and pm[0] == target \
                and (pm[1] == "" or pm[1] in READ_MODES):
            return True
        if isinstance(recv.func, ast.Name) and recv.func.id in env:
            kind, path = env[recv.func.id][0], env[recv.func.id][1]
            if kind == "openr" and path == target and not node.args:
                return True
        return False
    if attr == "read_text" and isinstance(recv, ast.Call) \
            and isinstance(recv.func, ast.Name) and recv.func.id == "Path":
        call = recv
        if len(call.args) == 1 and is_str_const(call.args[0]) \
                and not call.keywords:
            return call.args[0].value == target
        return False
    if attr in ("read", "read_text") and isinstance(recv, ast.Name) \
            and recv.id in env and env[recv.id][0] == "path":
        return env[recv.id][1] == target
    return False


def replace_of(node, target, env):
    """If node is read(T).replace(O, N) with constants, return (O, N)."""
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
            and node.func.attr == "replace" and not node.keywords
            and len(node.args) == 2 and is_str_const(node.args[0])
            and is_str_const(node.args[1])):
        return None
    recv = node.func.value
    if read_of_target(recv, target, env):
        return (node.args[0].value, node.args[1].value)
    if isinstance(recv, ast.Name) and recv.id in env \
            and env[recv.id][0] == "readvar":
        return (node.args[0].value, node.args[1].value)
    return None


def write_receiver_target(expr, target, env):
    """Resolve a write call receiver. True/False/None = target/other/poison."""
    func = expr.func
    if not isinstance(func, ast.Attribute) or func.attr not in (
            "write", "write_text"):
        return None
    recv = func.value
    if isinstance(recv, ast.Call):
        if func.attr == "write" and isinstance(recv.func, ast.Name) \
                and recv.func.id == "open":
            pm = open_call_path_mode(recv, "w")
            if pm is None:
                return None
            if pm[1] not in WRITE_MODES:
                return None
            return pm[0] == target or False
        if func.attr == "write_text" and isinstance(recv.func, ast.Name) \
                and recv.func.id == "Path" and len(recv.args) == 1 \
                and is_str_const(recv.args[0]) and not recv.keywords:
            if any(kw.arg != "encoding" or not is_str_const(kw.value)
                   for kw in expr.keywords):
                return None
            return recv.args[0].value == target or False
        return None
    if isinstance(recv, ast.Name) and recv.id in env:
        kind, path = env[recv.id][0], env[recv.id][1]
        if func.attr == "write" and kind == "openw":
            return path == target or False
        if func.attr == "write_text" and kind == "path":
            if any(kw.arg != "encoding" or not is_str_const(kw.value)
                   for kw in expr.keywords):
                return None
            return path == target or False
    return None


def process_py_write_expr(expr, target, env, ops):
    if not isinstance(expr, ast.Call):
        return False
    verdict = write_receiver_target(expr, target, env)
    if verdict is None:
        return False
    if verdict is False:
        return True
    if len(expr.args) != 1:
        return False
    arg = expr.args[0]
    if is_str_const(arg):
        ops.append({"kind": "write", "content": arg.value})
        return True
    if isinstance(arg, ast.Name) and arg.id in env:
        binding = env[arg.id]
        if binding[0] == "lit":
            ops.append({"kind": "write", "content": binding[1]})
            return True
        if binding[0] == "pending_edit":
            ops.append({"kind": "edit", "old": binding[1],
                        "new": binding[2], "replace_all": False})
            return True
        return False
    edit = replace_of(arg, target, env)
    if edit is not None:
        ops.append({"kind": "edit", "old": edit[0], "new": edit[1],
                    "replace_all": False})
        return True
    return False


def process_py_with(stmt, target, env, ops):
    if len(stmt.items) != 1 or stmt.items[0].optional_vars is None:
        return False
    pm = open_call_path_mode(stmt.items[0].context_expr, "w")
    alias = stmt.items[0].optional_vars
    if pm is None or pm[0] != target or pm[1] not in WRITE_MODES:
        if pm is not None and pm[0] != target:
            return True
        return False
    if not isinstance(alias, ast.Name):
        return False
    saved = env.get(alias.id)
    env[alias.id] = ("openw", target)
    for sub in stmt.body:
        if isinstance(sub, ast.Expr) and is_str_const(sub.value):
            continue
        if isinstance(sub, (ast.Assign, ast.AnnAssign)):
            names = sub.targets if isinstance(sub, ast.Assign) else None
            if names is not None and len(names) == 1 \
                    and isinstance(names[0], ast.Name):
                if not process_py_assign(names[0].id, sub.value, target, env):
                    return False
                continue
            if isinstance(sub, ast.AnnAssign) \
                    and isinstance(sub.target, ast.Name) \
                    and sub.value is not None:
                if not process_py_assign(sub.target.id, sub.value, target,
                                         env):
                    return False
                continue
            return False
        if isinstance(sub, ast.Expr):
            if not process_py_write_expr(sub.value, target, env, ops):
                return False
            continue
        return False
    if saved is None:
        env.pop(alias.id, None)
    else:
        env[alias.id] = saved
    return True


def apply_edit(state, old, new, replace_all):
    if old == "":
        return (None, "empty_old")
    count = state.count(old)
    if count == 0:
        return (None, "no_match")
    if count > 1 and not replace_all:
        return (None, "not_unique:%d" % count)
    if replace_all:
        return (state.replace(old, new), None)
    return (state.replace(old, new, 1), None)


def split_keep(text):
    if text == "":
        return ([], False)
    parts = text.split("\n")
    if parts[-1] == "":
        return (parts[:-1], True)
    return (parts, False)


def apply_patch_update(state, hunks):
    lines, trailing = split_keep(state)
    idx = 0
    for hunk_no, hunk in enumerate(hunks):
        for prefix, body in hunk:
            if prefix == "+":
                lines.insert(idx, body)
                idx += 1
            elif prefix in (" ", "-"):
                if idx >= len(lines) or lines[idx] != body:
                    return (None, "patch_hunk_mismatch:%d" % hunk_no)
                if prefix == "-":
                    del lines[idx]
                else:
                    idx += 1
            else:
                return (None, "patch_bad_prefix:%d" % hunk_no)
    out = "\n".join(lines)
    if trailing or (lines and not trailing and state.endswith("\n")):
        out += "\n" if lines else ""
    return (out, None)


def main(argv=None):
    args = build_parser().parse_args(argv)
    data = read_bounded(args.input, args.max_bytes)
    text = data.decode("utf-8", "replace")
    offsets = line_offsets(text)
    events = []
    unsupported = []

    def line_of(pos):
        return bisect_right(offsets, pos)

    if "invoke" in text and _LT in text:
        for match in INVOKE_RE.finditer(text):
            if len(events) + len(unsupported) >= args.max_events:
                break
            collect_xml_event(match, args.target, line_of(match.start()),
                              events, unsupported, args.max_content)
    collect_line_events(text, offsets, args.target, events, unsupported,
                        args.max_events, args.max_content)
    events.sort(key=lambda e: (e["pos"], e["seq"]))
    state, seeded, replayed, unreplayed = replay(
        events, unsupported, args.target, args.seed, args.max_content)
    return finish(args, text, state, seeded, replayed, unreplayed, unsupported)


def read_bounded(path, limit):
    data = b""
    fh = sys.stdin.buffer if path == "-" else open(path, "rb")
    with fh:
        while True:
            chunk = fh.read(65536)
            if not chunk:
                break
            data += chunk
            if len(data) > limit:
                raise SystemExit("input exceeds --max-bytes")
    return data


def line_offsets(text):
    offsets = [0]
    pos = text.find("\n")
    while pos != -1:
        offsets.append(pos + 1)
        pos = text.find("\n", pos + 1)
    return offsets


def collect_xml_event(match, target, line, events, unsupported, max_content):
    name = match.group("name").strip().lower()
    if name not in ("write", "edit", "read"):
        return
    params = {}
    for pmatch in PARAM_RE.finditer(match.group("body")):
        params[pmatch.group("name").strip()] = unescape_xml(
            pmatch.group("value"))
    path = params.get("filePath", params.get("path"))
    if path != target:
        return
    if name == "write":
        content = params.get("content")
        if not isinstance(content, str):
            unsupported.append({"kind": "xml_incomplete", "line": line,
                                "detail": "write without content"})
            return
        events.append({"pos": match.start(), "seq": len(events),
                       "kind": "write", "line": line, "content": content})
    elif name == "read":
        content = params.get("content")
        if not isinstance(content, str):
            return
        events.append({"pos": match.start(), "seq": len(events),
                       "kind": "seed", "line": line, "content": content})
    else:
        old = params.get("oldString", params.get("old_string"))
        new = params.get("newString", params.get("new_string"))
        raw_all = params.get("replaceAll", params.get("replace_all", False))
        replace_all = parse_replace_all(raw_all)
        if not isinstance(old, str) or not isinstance(new, str) \
                or replace_all is None:
            unsupported.append({"kind": "xml_incomplete", "line": line,
                                "detail": "edit without old/new/flag"})
            return
        events.append({"pos": match.start(), "seq": len(events),
                       "kind": "edit", "line": line, "old": old,
                       "new": new, "replace_all": replace_all})


def collect_line_events(text, offsets, target, events, unsupported,
                        max_events, max_content):
    lines = text.split("\n")
    pos = 0
    i = 0
    seq_base = len(events)
    while i < len(lines):
        line = lines[i]
        if len(events) + len(unsupported) >= max_events + seq_base:
            break
        if PATCH_BEGIN_RE.match(line):
            new_i = collect_patch_block(lines, i, pos, offsets, target,
                                        events, unsupported, max_content)
            pos += sum(len(l) + 1 for l in lines[i:new_i])
            i = new_i
            continue
        if FENCE_OPEN_RE.match(line):
            new_i = collect_python_block(
                lines, i, pos, target, events, unsupported, offsets)
            pos += sum(len(l) + 1 for l in lines[i:new_i])
            i = new_i
            continue
        matched = HEREDOC_QUOTED_RE.match(line)
        if matched:
            new_i = collect_heredoc(
                lines, i, pos, offsets, matched, target, events,
                unsupported, max_content)
            pos += sum(len(l) + 1 for l in lines[i:new_i])
            i = new_i
            continue
        if HEREDOC_ANY_RE.match(line) and target in line:
            unsupported.append({"kind": "unquoted_heredoc",
                                "line": bisect_right(offsets, pos),
                                "detail": "refused: delimiter not quoted"})
        stripped = line.strip()
        if stripped.startswith("{") and stripped.endswith("}"):
            collect_json_line(stripped, target, bisect_right(offsets, pos),
                              pos, len(events), events, unsupported)
        pos += len(line) + 1
        i += 1


def collect_json_line(stripped, target, line, pos, seq, events, unsupported):
    try:
        obj = json.loads(stripped)
    except (ValueError, json.JSONDecodeError):
        return
    if not isinstance(obj, dict):
        return
    op = obj.get("op")
    if not isinstance(op, str) or op.strip().lower() not in (
            "write", "edit", "read"):
        return
    op = op.strip().lower()
    if obj.get("filePath") != target:
        return
    if op == "write":
        content = obj.get("content")
        if not isinstance(content, str):
            unsupported.append({"kind": "json_incomplete", "line": line,
                                "detail": "write without content"})
            return
        events.append({"pos": pos, "seq": seq, "kind": "write",
                       "line": line, "content": content})
    elif op == "read":
        content = obj.get("content")
        if isinstance(content, str):
            events.append({"pos": pos, "seq": seq, "kind": "seed",
                           "line": line, "content": content})
    else:
        old, new = obj.get("oldString"), obj.get("newString")
        replace_all = parse_replace_all(obj.get("replaceAll", False))
        if not isinstance(old, str) or not isinstance(new, str) \
                or replace_all is None:
            unsupported.append({"kind": "json_incomplete", "line": line,
                                "detail": "edit without old/new/flag"})
            return
        events.append({"pos": pos, "seq": seq, "kind": "edit",
                       "line": line, "old": old, "new": new,
                       "replace_all": replace_all})


def collect_heredoc(lines, i, pos, offsets, matched, target, events,
                    unsupported, max_content):
    line_no = bisect_right(offsets, pos)
    if matched.group("path") != target:
        return i + 1
    delim = matched.group("delim")
    buf = []
    j = i + 1
    while j < len(lines) and lines[j] != delim:
        buf.append(lines[j])
        j += 1
    if j >= len(lines):
        unsupported.append({"kind": "truncated_heredoc", "line": line_no,
                            "detail": "no closing delimiter"})
        return len(lines)
    content = "\n".join(buf) + ("\n" if buf else "")
    if len(content) > max_content:
        unsupported.append({"kind": "oversized_event", "line": line_no,
                            "detail": "heredoc content too large"})
    else:
        events.append({"pos": pos, "seq": len(events), "kind": "write",
                       "line": line_no, "content": content})
    return j + 1


def collect_python_block(lines, i, pos, target, events, unsupported,
                         offsets):
    line_no = bisect_right(offsets, pos)
    buf = []
    j = i + 1
    while j < len(lines) and not FENCE_CLOSE_RE.match(lines[j]):
        buf.append(lines[j])
        j += 1
    if j >= len(lines):
        return len(lines)
    source = "\n".join(buf)
    if target in source:
        ops, refusal = analyse_python_block(source, target)
        if refusal is not None:
            unsupported.append({"kind": refusal, "line": line_no,
                                "detail": "python block not replayed"})
        else:
            for op in ops:
                op["pos"] = pos
                op["seq"] = len(events)
                op["line"] = line_no
                events.append(op)
    return j + 1


def collect_patch_block(lines, i, pos, offsets, target, events, unsupported,
                        max_content):
    start = pos
    j = i + 1
    while j < len(lines) and not PATCH_END_RE.match(lines[j]):
        j += 1
    if j >= len(lines):
        unsupported.append({"kind": "truncated_patch",
                            "line": bisect_right(offsets, start),
                            "detail": "no end marker"})
        return len(lines)
    body = lines[i + 1:j]
    sections = []
    current = None
    for raw in body:
        sec = PATCH_SECTION_RE.match(raw)
        if sec:
            current = {"action": sec.group("action"),
                       "path": sec.group("path"), "lines": []}
            sections.append(current)
        elif current is not None:
            current["lines"].append(raw)
        elif raw.strip() != "":
            current = {"action": "preamble", "path": "", "lines": [raw]}
            sections.append(current)
    for sec in sections:
        if sec["path"] != target:
            continue
        line_no = bisect_right(offsets, start)
        if sec["action"] == "Add File":
            content_parts = []
            bad = False
            for raw in sec["lines"]:
                if not raw.startswith("+"):
                    bad = True
                    break
                content_parts.append(raw[1:] + "\n")
            if bad:
                unsupported.append({"kind": "patch_add_mixed",
                                    "line": line_no,
                                    "detail": "add section has non-+ lines"})
            else:
                content = "".join(content_parts)
                if len(content) > max_content:
                    unsupported.append({"kind": "oversized_event",
                                        "line": line_no,
                                        "detail": "patch add too large"})
                else:
                    events.append({"pos": start, "seq": len(events),
                                   "kind": "write", "line": line_no,
                                   "content": content})
        elif sec["action"] == "Update File":
            hunks, ok = parse_hunks(sec["lines"])
            if not ok:
                unsupported.append({"kind": "patch_bad_hunk",
                                    "line": line_no,
                                    "detail": "hunk header or prefix"})
            else:
                events.append({"pos": start, "seq": len(events),
                               "kind": "patch", "line": line_no,
                               "hunks": hunks})
        else:
            unsupported.append({"kind": "patch_refused",
                                "line": line_no,
                                "detail": sec["action"]})
    return j + 1


def parse_hunks(raw_lines):
    hunks = []
    current = None
    for raw in raw_lines:
        if HUNK_RE.match(raw):
            current = []
            hunks.append(current)
            continue
        if current is None:
            if raw.strip() == "":
                continue
            return (None, False)
        if raw.startswith((" ", "-", "+")):
            current.append((raw[0], raw[1:]))
        elif raw.strip() == "\\ No newline at end of file":
            continue
        else:
            return (None, False)
    if not hunks:
        return (None, False)
    return (hunks, True)


def replay(events, unsupported, target, seed_path, max_content):
    state = None
    seeded = None
    if seed_path is not None:
        try:
            with open(seed_path, "rb") as fh:
                seed_data = fh.read(max_content + 1)
        except OSError as exc:
            raise SystemExit("cannot read --seed: %s" % exc)
        if len(seed_data) > max_content:
            raise SystemExit("seed exceeds --max-content")
        state = seed_data.decode("utf-8", "replace")
        seeded = "seed_file"
    replayed = []
    unreplayed = []
    for event in events:
        kind = event["kind"]
        if kind == "seed":
            if state is None:
                if len(event["content"]) > max_content:
                    unsupported.append({"kind": "oversized_event",
                                        "line": event["line"],
                                        "detail": "seed content too large"})
                    continue
                state = event["content"]
                seeded = "log_read"
                replayed.append({"kind": "seed", "line": event["line"]})
            continue
        if kind == "write":
            if len(event["content"]) > max_content:
                unsupported.append({"kind": "oversized_event",
                                    "line": event["line"],
                                    "detail": "write content too large"})
                continue
            state = event["content"]
            replayed.append({"kind": "write", "line": event["line"]})
            continue
        if state is None:
            unreplayed.append({"kind": kind + "_without_base",
                               "line": event["line"],
                               "detail": "no write or seed before this event"})
            continue
        if kind == "edit":
            if len(event["old"]) + len(event["new"]) > max_content:
                unsupported.append({"kind": "oversized_event",
                                    "line": event["line"],
                                    "detail": "edit strings too large"})
                continue
            new_state, problem = apply_edit(
                state, event["old"], event["new"], event["replace_all"])
            if problem is not None:
                unreplayed.append({"kind": "edit_" + problem.split(":")[0],
                                   "line": event["line"],
                                   "detail": problem})
                continue
            state = new_state
            replayed.append({"kind": "edit", "line": event["line"]})
            continue
        if kind == "patch":
            new_state, problem = apply_patch_update(state, event["hunks"])
            if problem is not None:
                unreplayed.append({"kind": problem.split(":")[0],
                                   "line": event["line"],
                                   "detail": problem})
                continue
            state = new_state
            replayed.append({"kind": "patch", "line": event["line"]})
            continue
    return (state, seeded, replayed, unreplayed)


def finish(args, text, state, seeded, replayed, unreplayed, unsupported):
    summary = {"tool": TOOL_VERSION, "target": args.target,
               "input_chars": len(text), "seeded": seeded,
               "replayed": len(replayed),
               "unreplayed": len(unreplayed),
               "unsupported": len(unsupported), "recovered": state is not None,
               "verified": None, "reason": None}
    if state is not None:
        raw = state.encode("utf-8")
        summary["bytes"] = len(raw)
        summary["lines"] = 0 if state == "" else state.count("\n") + (
            0 if state.endswith("\n") else 1)
        summary["md5"] = hashlib.md5(raw).hexdigest()
        with open(args.output, "w", encoding="utf-8") as fh:
            fh.write(state)
    problems = []
    if args.expect_md5 is not None:
        if state is None or summary.get("md5", "") != args.expect_md5.lower():
            problems.append("digest_mismatch")
    if args.expect_lines is not None:
        if state is None or summary.get("lines") != args.expect_lines:
            problems.append("line_mismatch")
    if problems:
        summary["verified"] = False
        summary["reason"] = "+".join(problems)
    elif args.expect_md5 is not None or args.expect_lines is not None:
        summary["verified"] = True
        summary["reason"] = "expectations_match"
    if args.report is not None:
        with open(args.report, "w", encoding="utf-8") as fh:
            json.dump({"summary": summary, "replayed": replayed,
                       "unreplayed": unreplayed,
                       "unsupported": unsupported}, fh, indent=2)
    print(json.dumps(summary))
    if problems:
        return 3
    return 0


if __name__ == "__main__":
    sys.exit(main())
