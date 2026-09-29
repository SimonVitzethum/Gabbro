#!/usr/bin/env python3
"""Bridge S0 -- the OVERLAP of GabbroV's model (`Gabbro.Body`) and machine G, over the corpus.

    ./instrumente/miss-bruecke-ueberlappung.py [--binary PATH] [--out FILE]

For every `beispiele/*.gab` it records
  * G   : `gabbro lean-g` exits 0 (the unit is a G program term), and which G constructors
          (`Stmt`/`Block`/`Endblock`/`Expr`, names read from `Grammatik/Syntax.lean`) the term uses;
  * Body: a duty file `programmlogik/Duty/*.lean` carries the unit (the `@duty N <file>` line,
          with `goals`/`refused` counts), and which `Body` constructors (names read from
          `Gabbro/Body.lean`) its datum uses;
and prints the intersection and, per constructor, how many units use it on each side.
A counter, not a guard: exit 0 once it measured. A constructor token is a `.name` whose name
is a constructor of the respective inductive -- a textual count, a superset of the truth
where two inductives share a name (`ite`, `call`, ...), and it says so in the table header.
"""
import argparse, collections, pathlib, re, subprocess, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent


def ctors(path, inductive):
    """Constructor names of the top-level `inductive <inductive>` in a Lean file."""
    text = path.read_text()
    m = re.search(r'^inductive %s\b.*?(?=^\S)' % re.escape(inductive), text, re.S | re.M)
    if not m:
        sys.exit("ABBRUCH: no `inductive %s` in %s" % (inductive, path))
    return set(re.findall(r'^\s*\|\s*([a-zA-Z]\w*)', m.group(0), re.M))


def uses(text, names):
    got = collections.Counter()
    for n in re.findall(r'(?<![\w.])\.([a-zA-Z]\w*)', text):
        if n in names:
            got[n] += 1
    return got


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--binary', default=str(ROOT / 'target/release/gabbro'))
    ap.add_argument('--out')
    a = ap.parse_args()
    syn = ROOT / 'grammatik/Grammatik/Syntax.lean'
    gnames = {'Stmt': set(), 'Expr': set()}
    for ind in ('Stmt', 'Block', 'Endblock'):
        gnames['Stmt'] |= ctors(syn, ind)
    gnames['Expr'] = ctors(syn, 'Expr')
    body = ROOT / 'programmlogik/Gabbro/Body.lean'
    bnames = {'Stmt': ctors(body, 'Stmt'), 'Expr': ctors(body, 'Expr')}
    duty = {}
    for f in sorted((ROOT / 'programmlogik/Duty').glob('Duty*.lean')):
        t = f.read_text()
        m = re.search(r'@duty \d+\s+(beispiele/\S+\.gab)\s+total (\d+)\s+goals (\d+)\s+refused (\d+)', t)
        if m:
            duty[m.group(1)] = (f, t, int(m.group(3)), int(m.group(4)))
    units = sorted(ROOT.glob('beispiele/*.gab'))
    g_ok, both = [], []
    guse = {k: collections.Counter() for k in gnames}
    buse = {k: collections.Counter() for k in bnames}
    refusal = collections.Counter()
    for u in units:
        rel = str(u.relative_to(ROOT))
        r = subprocess.run([a.binary, 'lean-g', rel], cwd=ROOT, capture_output=True, text=True, timeout=300)
        gok = r.returncode == 0 and r.stdout.strip() != ''
        if gok:
            g_ok.append(rel)
            for k in gnames:
                for n in uses(r.stdout, gnames[k]):
                    guse[k][n] += 1
        else:
            m = re.search(r'\[(\w+)\]', r.stderr)
            refusal[m.group(1) if m else 'other'] += 1
        if rel in duty:
            for k in bnames:
                for n in uses(duty[rel][1], bnames[k]):
                    buse[k][n] += 1
            if gok:
                both.append(rel)
    out = []
    p = out.append
    p('# Bridge overlap (S0) -- `instrumente/miss-bruecke-ueberlappung.py`\n')
    p('corpus units (`beispiele/*.gab`): %d' % len(units))
    p('units with a duty file (Body side): %d' % len(duty))
    p('units that export as a G term (`gabbro lean-g` exit 0): %d' % len(g_ok))
    p('**units on BOTH sides (the bridge population): %d**' % len(both))
    p('`lean-g` refusals by code: ' + ', '.join('%s %d' % kv for kv in sorted(refusal.items())))
    for k in ('Stmt', 'Expr'):
        p('\n## %s constructors (units using each; textual, shared names over-count)\n' % k)
        p('| ctor | Body units | G units | in Body | in G |')
        p('|---|---|---|---|---|')
        for n in sorted(bnames[k] | gnames[k]):
            p('| %s | %d | %d | %s | %s |' % (n, buse[k][n], guse[k][n],
                                              'yes' if n in bnames[k] else '', 'yes' if n in gnames[k] else ''))
    p('\n## The bridge population\n')
    p('\n'.join('- %s (duty goals %d, refused %d)' % (b, duty[b][2], duty[b][3]) for b in both))
    text = '\n'.join(out) + '\n'
    if a.out:
        pathlib.Path(a.out).write_text(text)
    print(text)


main()
