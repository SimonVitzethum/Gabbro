#!/usr/bin/env python3
"""Lean file layout: every folder holds at most MAXIMUM entries (files + folders), sensibly grouped.

Simon, 2026-10-05: "alle lean dateien, wirklich alle sollen sinnvoll in ordnern organisiert werden,
maximal 20 dateien + ordner pro ordner, und das ist pflicht auch rueckwirkend".

Modes
  --check   exit 1 if any folder that holds Lean files (or leads to them inside a Lean project) has more
            than MAXIMUM entries, counting every tracked file and sub-folder. The guardian and the merge gate.
  --plan    show where every Lean module would go under RULES and which folders stay too full.
  --apply   git mv the modules to their place, rewrite `import` lines, and rewrite old module / file path
            references in tracked text files. Idempotent; also places NEW modules a lane added in the flat
            folder (the merge gate runs it after every merge).

A module is placed by the FIRST rule of its folder whose regex matches the module name. A name no rule
matches stays where it is; if that folder is then too full, --check fails and names the folder: add a rule.
The old->new module map is kept in lean-layout-map.json so branches that still import an old name are rewritten.
"""
import json
import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MAXIMUM = 20
MAPFILE = ROOT / 'instrumente' / 'lean-layout-map.json'

# folder (repo-relative) -> ordered (regex over the module name, sub-folder below that folder)
RULES = {}


def rules(folder, table):
    RULES[folder] = [(re.compile(r), sub) for r, sub in table]


PINNED = set()
exec(open(ROOT / 'instrumente' / 'lean-layout-rules.py').read())

# Lean projects: folders from the project root down to a folder holding Lean files are counted.
PROJECTS = ['grammatik', 'bruecke', 'passlogik', 'programmlogik']
TEXT_TREES = ['crates', 'instrumente', 'dokumente', 'beispiele', 'bibliothek', 'laufzeit', 'bruecke',
              'passlogik', 'programmlogik', 'beweise', 'README.md', 'TODO.md', 'DIRECT-COMPILER-DESIGN.md',
              'AGENTS.md', 'DONE.md', 'grammatik']
SKIP_PREFIX = ('messung/muse/', 'lanes/', '.claude/', '.town/', 'target/', '.lake',
               'instrumente/lean-layout')   # the tool's own rules and map name paths on purpose (PINNED): never rewritten


def git(*a):
    return subprocess.check_output(['git', *a], cwd=ROOT, text=True)


def tracked():
    return [f for f in git('ls-files').split('\n') if f]


def lean_files(files):
    return [f for f in files if f.endswith('.lean')]


def target_of(path):
    """Repo-relative target path of one tracked Lean file under RULES, or the same path."""
    if path in PINNED:
        return path
    p = Path(path)
    folder = str(p.parent)
    name = p.stem
    for sub_folder, table in RULES.items():
        if folder == sub_folder:
            for rx, sub in table:
                if rx.search(name):
                    return os.path.normpath(str(Path(folder) / sub / p.name))
            return path
    return path


def module_of(path):
    """grammatik/Grammatik/X86/Foo.lean -> Grammatik.X86.Foo (project dir stripped)."""
    parts = Path(path).with_suffix('').parts
    if parts[0] in PROJECTS and len(parts) > 1:
        return '.'.join(parts[1:])
    return None


def entries_of(files):
    ents = {}
    for f in files:
        parts = f.split('/')
        for i in range(len(parts)):
            ents.setdefault('/'.join(parts[:i]), set()).add(parts[i])
    return ents


def lean_dirs(files):
    dirs = set()
    for f in lean_files(files):
        parts = f.split('/')
        if parts[0] not in PROJECTS:
            # loose measurement probes: only the folder that directly holds the file
            dirs.add('/'.join(parts[:-1]))
            continue
        for i in range(1, len(parts)):
            dirs.add('/'.join(parts[:i]))
    return dirs


def overfull(files):
    ents = entries_of(files)
    return sorted(((len(v), k) for k, v in ents.items() if k in lean_dirs(files) and len(v) > MAXIMUM),
                  reverse=True)


CATCHALL_FILL = 16          # a catch-all folder takes at most this many files (headroom below MAXIMUM)


def planned(files):
    """Moves by rule. A module of a ruled folder that NO rule matches stays where it is while the folder
    holds at most MAXIMUM entries; once it would overflow, the unmatched modules go to <folder>/Neu, Neu2, ...
    so a new lane file never blocks an integration. A maintainer turns those into proper rules."""
    moves = {}
    unmatched = []
    for f in lean_files(files):
        t = target_of(f)
        if t != f:
            moves[f] = t
        elif str(Path(f).parent) in RULES:
            unmatched.append(f)
    if unmatched:
        ents = entries_of([moves.get(f, f) for f in files])
        by_folder = {}
        for f in unmatched:
            by_folder.setdefault(str(Path(f).parent), []).append(f)
        for folder, fs in by_folder.items():
            if len(ents.get(folder, ())) <= MAXIMUM:
                continue
            count = {}
            k = 1
            for f in sorted(fs):
                while True:
                    d = f'{folder}/Neu' if k == 1 else f'{folder}/Neu{k}'
                    if len([x for x in ents.get(d, ())]) + count.get(d, 0) < CATCHALL_FILL:
                        break
                    k += 1
                count[d] = count.get(d, 0) + 1
                moves[f] = f'{d}/{Path(f).name}'
    return moves


def final_files(files, moves):
    return [moves.get(f, f) for f in files]


def cmd_check():
    files = tracked()
    bad = overfull(files)
    unplaced = planned(files)
    for n, k in bad:
        print(f'TOO FULL: {k or "."}: {n} entries (maximum {MAXIMUM})')
    if unplaced:
        print(f'NOT PLACED: {len(unplaced)} Lean file(s) sit where a rule says they belong elsewhere; '
              f'run: python3 instrumente/lean-layout.py --apply   (first: {next(iter(unplaced))})')
    if bad or unplaced:
        return 1
    print(f'lean-layout: every folder holds at most {MAXIMUM} entries; all {len(lean_files(files))} Lean files placed.')
    return 0


def cmd_plan():
    files = tracked()
    moves = planned(files)
    after = final_files(files, moves)
    print(f'{len(moves)} of {len(lean_files(files))} Lean modules would move.')
    bad = overfull(after)
    for n, k in bad:
        print(f'  still too full after the plan: {k}: {n}')
        ents = sorted(entries_of(after)[k])
        print('     ' + ' '.join(ents[:60]))
    sizes = sorted(((len(v), k) for k, v in entries_of(after).items() if k in lean_dirs(after)), reverse=True)
    print('largest folders after the plan:', ', '.join(f'{k.split("/")[-1] or "."}={n}' for n, k in sizes[:12]))
    if '--verbose' in sys.argv:
        for a, b in sorted(moves.items()):
            print(f'  {a} -> {b}')
    return 1 if bad else 0


def load_map():
    return json.loads(MAPFILE.read_text()) if MAPFILE.exists() else {}


def cmd_apply():
    files = tracked()
    moves = planned(files)
    mapping = load_map()
    for src, dst in moves.items():
        (ROOT / dst).parent.mkdir(parents=True, exist_ok=True)
        subprocess.check_call(['git', 'mv', src, dst], cwd=ROOT)
        a, b = module_of(src), module_of(dst)
        if a and b:
            mapping[a] = b
    # collapse chains old -> mid -> new
    for k in list(mapping):
        seen = set()
        while mapping[k] in mapping and mapping[k] not in seen:
            seen.add(mapping[k])
            mapping[k] = mapping[mapping[k]]
    MAPFILE.write_text(json.dumps(dict(sorted(mapping.items())), indent=1) + '\n')
    files = tracked()
    changed = rewrite_imports(files, mapping)
    changed_text = rewrite_text(files, moves, mapping)
    print(f'moved {len(moves)} Lean modules; rewrote imports in {changed} Lean files and references in {changed_text} text files.')
    return 0


IMPORT = re.compile(r'^([ \t]*import[ \t]+)(Grammatik(?:\.[A-Za-z0-9_]+)+)([ \t]*)$', re.M)


def rewrite_imports(files, mapping):
    n = 0
    for f in lean_files(files):
        p = ROOT / f
        s = p.read_text()
        t = IMPORT.sub(lambda m: m.group(1) + mapping.get(m.group(2), m.group(2)) + m.group(3), s)
        if t != s:
            p.write_text(t)
            n += 1
    return n


def rewrite_text(files, moves, mapping):
    """Old file path / old module references in tracked text files (not history, not lane tasks)."""
    path_map = {}
    for src, dst in moves.items():
        path_map[src] = dst
        path_map[src[len('grammatik/'):]] = dst[len('grammatik/'):] if src.startswith('grammatik/') else dst
    path_old = {}
    for a, b in mapping.items():
        path_old['grammatik/' + a.replace('.', '/') + '.lean'] = 'grammatik/' + b.replace('.', '/') + '.lean'
        path_old[a.replace('.', '/') + '.lean'] = b.replace('.', '/') + '.lean'
    path_map.update(path_old)
    keys = sorted(path_map, key=len, reverse=True)
    rx_path = re.compile('(?<![A-Za-z0-9_-])(' + '|'.join(re.escape(k) for k in keys) + ')(?![A-Za-z0-9_])') if keys else None
    imp_old = sorted(mapping, key=len, reverse=True)
    rx_imp = re.compile(r'((?:\b|(?<=\\n))import\s+)(' + '|'.join(re.escape(k) for k in imp_old) + r')(?![A-Za-z0-9_.])') if imp_old else None
    n = 0
    for f in files:
        if f.endswith('.lean') or f.startswith(SKIP_PREFIX):
            continue
        if not any(f == t or f.startswith(t.rstrip('/') + '/') for t in TEXT_TREES):
            continue
        p = ROOT / f
        try:
            s = p.read_text()
        except (UnicodeDecodeError, OSError):
            continue
        t = s
        if rx_path:
            t = rx_path.sub(lambda m: path_map[m.group(1)], t)
        if rx_imp:
            t = rx_imp.sub(lambda m: m.group(1) + mapping[m.group(2)], t)
        if t != s:
            p.write_text(t)
            n += 1
    return n


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else '--check'
    return {'--check': cmd_check, '--plan': cmd_plan, '--apply': cmd_apply}.get(mode, cmd_check)()


if __name__ == '__main__':
    sys.exit(main())
