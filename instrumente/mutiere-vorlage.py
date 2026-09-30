#!/usr/bin/env python3
"""Planted defects for the SOURCE-PINNED template (`gabbro prove --template --source`, P6).

    ./instrumente/mutiere-vorlage.py [--datei beispiele/104-referenz.gab] [--nur NAME] [--binary PATH]

The template pins the source text and states the duties by Lean functions of it; the stage
outputs (tokens, items, the elaborated program) are HINTS the kernel must check. A check that
cannot fail proves nothing, so this script writes the template of one program, demands that it
compiles with no error (its only `sorry`s are the duties a person still owes: BASELINE), and then
plants the defects a wrong hint, a changed text or a weakened statement would be:

  * a changed count in the elaborated program `u`        -> `elab_ok` must fail
  * a changed literal in the pinned source text          -> `lex_ok` must fail (the tokens differ)
  * a changed token in `toks`                            -> `lex_ok` must fail
  * a changed literal in `items`                         -> `parse_ok` must fail
  * a duty stated with a different function index        -> `pflichten` must fail (the statement is
                                                            the computed one, not the template's)
  * a duty statement weakened to `True`                  -> `pflichten` must fail

Each mutated copy is compiled on its own (the scratch file lives under `~/claude-lane/kratz` or
`$TMPDIR`; the tree is never written). The verdict of a mutation is "caught" when Lean reports an
`error`; a mutation that compiles is a SURVIVOR. Exit 0: baseline green and all caught. 1: a
survivor. 2: it could not measure (no binary, baseline red, a memory kill).
A Lean run needs ~4 GB: `free -g` beside it, one run at a time.
"""
import argparse, os, pathlib, re, subprocess, sys, time

ROOT = pathlib.Path(__file__).resolve().parent.parent
BR = ROOT / 'bruecke'
KAP_KB = 9_000_000


def lean(datei):
    """Compile `datei` in the bridge project; (errors, sorries, killed)."""
    env = dict(os.environ)
    lp = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=BR, text=True).strip()
    env['LEAN_PATH'] = lp
    p = subprocess.Popen(['lean', str(datei)], cwd=BR, stdout=subprocess.PIPE,
                         stderr=subprocess.STDOUT, text=True, env=env)
    t = time.time()
    while p.poll() is None:
        try:
            rss = int(open(f'/proc/{p.pid}/statm').read().split()[1]) * 4
        except OSError:
            rss = 0
        if rss > KAP_KB:
            p.kill()
            return None, None, f'killed at {rss} KB (memory, not a finding)'
        if time.time() - t > 600:
            p.kill()
            return None, None, 'timeout'
        time.sleep(0.5)
    aus = p.stdout.read()
    fehler = [l for l in aus.splitlines() if re.search(r':\d+:\d+: error', l)]
    sorries = [l for l in aus.splitlines() if 'declaration uses `sorry`' in l]
    return fehler, sorries, None


def mutationen(text):
    """(name, mutated text) -- every one must change the text. Each copy is CUT after the theorem it
    targets: a defect upstream makes every later stage fail too, and a failing `rfl` on a wrong
    stage output can run for minutes, which measures nothing."""
    m = []
    def einmal(name, alt, neu, nach, bis=None):
        j = text.index(alt, nach)
        s = text[:j] + neu + text[j + len(alt):]
        if bis:
            k = s.index(bis)
            s = s[:k] + 'end ' + text[text.index('namespace ') + 10:].split('\n')[0] + '\n'
        m.append((name, s))
    u_at = text.index('\ndef u : UProg')
    einmal('elaborated-count-changed', 'count := 2', 'count := 3', u_at, 'theorem low_ok')
    einmal('pinned-source-literal-changed', ' 2;', ' 3;', text.index('def zeilen'), 'theorem parse_ok')
    einmal('token-changed', '.wort "module"', '.wort "modulf"', text.index('def toks'), 'theorem parse_ok')
    einmal('items-literal-changed', 'SExpr.lit 2)', 'SExpr.lit 3)', text.index('def items'), 'theorem elab_ok')
    einmal('duty-index-changed', 'theorem pflicht_0 : ∃ body, zuBody u (fnAt u ⟨0,',
           'theorem pflicht_0 : ∃ body, zuBody u (fnAt u ⟨1,', 0)
    einmal('duty-weakened-to-true',
           'theorem pflicht_1 : ∃ body, zuBody u (fnAt u ⟨1, by decide⟩) = some body ∧\n    meetsU u (wfU u) (fnAt u ⟨1, by decide⟩) body',
           'theorem pflicht_1 : ∃ body, zuBody u (fnAt u ⟨1, by decide⟩) = some body ∧\n    True', 0)
    return m


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--datei', default='beispiele/104-referenz.gab')
    ap.add_argument('--nur')
    ap.add_argument('--binary', default=str(ROOT / 'target/debug/gabbro'))
    a = ap.parse_args()
    if not pathlib.Path(a.binary).is_file():
        print('ABBRUCH: no binary', a.binary); return 2
    scratch = pathlib.Path(os.environ.get('TMPDIR', str(pathlib.Path.home() / 'claude-lane/kratz'))) / 'vorlage-mut'
    scratch.mkdir(parents=True, exist_ok=True)
    r = subprocess.run([a.binary, 'prove', '--template', '--source', a.datei], cwd=ROOT,
                       capture_output=True, text=True)
    if r.returncode != 0 or not r.stdout.startswith('import Bruecke.Quelle'):
        print('ABBRUCH: the template writer failed:\n', r.stdout[:300], r.stderr[:600]); return 2
    text = r.stdout
    basis = scratch / 'basis.lean'
    basis.write_text(text)
    fehler, sorries, tot = lean(basis)
    if tot:
        print('ABBRUCH: baseline', tot); return 2
    if fehler:
        print('ABBRUCH: baseline is RED (' + str(len(fehler)) + ' errors):\n' + '\n'.join(fehler[:5])); return 2
    print(f'baseline: green, {len(sorries)} owed duty proof(s) (`sorry`)')
    ueberlebt = 0; gemessen = 0
    for name, neu in mutationen(text):
        if a.nur and a.nur != name:
            continue
        assert neu != text, name
        f = scratch / f'{name}.lean'
        f.write_text(neu)
        fehler, sorries, tot = lean(f)
        if tot:
            print(f'ABBRUCH: {name}: {tot}'); return 2
        gemessen += 1
        if fehler:
            print(f'caught    {name}: {fehler[0][-110:]}')
        else:
            print(f'SURVIVED  {name}'); ueberlebt += 1
    print(f'{gemessen - ueberlebt} of {gemessen} planted defects caught')
    return 1 if ueberlebt else 0


if __name__ == '__main__':
    sys.exit(main())
