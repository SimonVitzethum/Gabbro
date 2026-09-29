#!/usr/bin/env python3
"""Planted defects for the bridge's per-unit checks (S1/S2 of AUFTRAG-GABBROV-VERIFIKATION).

    ./instrumente/mutiere-bruecke.py [--nur NAME] [--keep-going]

The per-unit checks in `bruecke/Bruecke/Instanz*.lean` compare the duty file the RUST printer wrote
(`programmlogik/Duty/*.lean`) with what `Bruecke/Pflichten.lean` computes in Lean from the parser's
`UProg`. A check that cannot fail proves nothing, so this script plants the defects a wrong printer
would make -- a dropped `ensures` conjunct, `<` for `<=`, a wrong callee contract, a wrong body
constant, a dropped frame, a widened shape -- into the printed text and demands that the check
FAILS, in the `Instanz` file and not somewhere else.

Method. The proofs of the duty file are irrelevant to the check and would fail first under a
mutated statement, so every run strips the proofs to `sorry` (`--baseline` runs that alone and must
PASS: the check does not depend on a proof). Each mutation is applied on top of the stripped text;
the duty file is restored byte for byte (SHA-256) afterwards, and a mismatch is an ABBRUCH. One
mutation at a time, in the checkout, never beside another Lean build in `bruecke/`.
A counter, not a guard for the tree: exit 0 when every planted defect was caught, 1 when one
survived, 2 (ABBRUCH) when it could not measure (baseline red, file not restored).
"""
import argparse, hashlib, pathlib, re, subprocess, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
BR = ROOT / 'bruecke'
D104 = ROOT / 'programmlogik/Duty/Duty104Referenz.lean'
D108 = ROOT / 'programmlogik/Duty/Duty108DisjointStartLocks.lean'

# (name, duty file, instance module, old text, new text)
MUTATIONS = [
    ('ensures-conjunct-dropped', D104, 'Bruecke.Instanz104',
     '  ∧ -- ensures #1\n  (∀ o1, eval s (.place "Konto" (.name "i") "stand") = some o1 → eval { world := s\'.world, local\' := (bindLocal s.local\' "old#1" o1) } (.bin .le (.name "old#1") (.place "Konto" (.name "i") "stand")) = some (.bool true))\n', ''),
    ('le-swapped-for-lt', D104, 'Bruecke.Instanz104', '(.bin .le (.name "old#1")', '(.bin .lt (.name "old#1")'),
    ('callee-precondition-widened', D104, 'Bruecke.Instanz104',
     'def lies_pre : Expr :=\n  (.bin .and (.hasShape "i" (.intIn 0 1))', 'def lies_pre : Expr :=\n  (.bin .and (.hasShape "i" (.intIn 0 2))'),
    ('call-site-precondition-wrong', D104, 'Bruecke.Instanz104',
     '(.call "lies" ["k", "i"] [(.name "k"), (.name "i")] (.bin .and (.hasShape "i" (.intIn 0 1))', '(.call "lies" ["k", "i"] [(.name "k"), (.name "i")] (.bin .and (.hasShape "i" (.intIn 0 2))'),
    ('body-constant-changed', D104, 'Bruecke.Instanz104', '(.lit (.int 100))', '(.lit (.int 99))'),
    ('call-to-the-wrong-callee', D104, 'Bruecke.Instanz104', '(.call "lies" ["k", "i"]', '(.call "einzahlen" ["k", "i"]'),
    ('held-requires-dropped', D104, 'Bruecke.Instanz104',
     '(.bin .and (.hasShape "b" (.intIn 0 10)) (.lit (.bool true)))', '(.hasShape "b" (.intIn 0 10))'),
    ('slot-range-widened', D104, 'Bruecke.Instanz104', 'some (.intIn 0 100)', 'some (.intIn 0 101)'),
    ('result-range-widened', D104, 'Bruecke.Instanz104', 'x ≤ 100)', 'x ≤ 101)'),
    ('frame-dropped', D104, 'Bruecke.Instanz104', 'def einzahlen_writes : List String := ["Konto"]', 'def einzahlen_writes : List String := []'),
    ('callee-frame-hypothesis-dropped', D104, 'Bruecke.Instanz104',
     '    -- the frame of `lies`\n    (fr_lies : Frame ρ "lies" lies_writes),', '    ,'),
    ('read-index-changed', D108, 'Bruecke.Instanz108', '(.place "T" (.lit (.int 1)) "v")', '(.place "T" (.lit (.int 0)) "v")'),
    ('result-range-dropped', D108, 'Bruecke.Instanz108',
     '(∃ x, r = some (.int x) ∧ 0 ≤ x ∧ x ≤ 4294967295)\n\n/-! ### `read_c` -/', '(∃ x, r = some (.int x))\n\n/-! ### `read_c` -/'),
]


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def strip_proofs(text):
    """Every `theorem … := by` block becomes `:= sorry`: the check must not lean on a proof."""
    out, skipping = [], False
    for line in text.split('\n'):
        if skipping:
            if line.startswith(' ') or line == '':
                if line == '':
                    skipping = False
                    out.append(line)
                continue
            skipping = False
        if line.startswith('theorem ') or re.match(r'^theorem ', line):
            pass
        if line.rstrip().endswith(':= by') and (line.startswith('theorem ') or out and _in_theorem(out)):
            out.append(line.rstrip()[:-len(':= by')] + ':= sorry')
            skipping = True
            continue
        out.append(line)
    return '\n'.join(out)


def _in_theorem(out):
    for l in reversed(out):
        if l.startswith('theorem '):
            return True
        if l == '' or l.startswith('def ') or l.startswith('/-'):
            return False
    return False


def build(module):
    r = subprocess.run(['lake', 'build', module], cwd=BR, capture_output=True, text=True, timeout=1800,
                       env={**__import__('os').environ, 'LEAN_NUM_THREADS': '4'})
    return r.returncode, r.stdout + r.stderr


def failed_in(text, module):
    """Where did the FIRST error come from -- the instance file (the check) or elsewhere?"""
    m = re.search(r'^error: (\S+?\.lean):\d+', text, re.M)
    return m.group(1) if m else None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--nur')
    a = ap.parse_args()
    orig = {p: p.read_bytes() for p in (D104, D108)}
    shas = {p: sha(p) for p in orig}
    survived, caught, other = [], [], []
    try:
        for p in orig:
            p.write_text(strip_proofs(orig[p].decode()))
        for mod in ('Bruecke.Instanz104', 'Bruecke.Instanz108'):
            rc, txt = build(mod)
            print('baseline (proofs stripped) %s: %s' % (mod, 'PASS' if rc == 0 else 'RED'))
            if rc != 0:
                print(txt[-2000:])
                sys.exit('ABBRUCH: the baseline is red -- the mutations would measure nothing')
        for name, p, mod, old, new in MUTATIONS:
            if a.nur and a.nur != name:
                continue
            text = strip_proofs(orig[p].decode())
            if text.count(old) < 1:
                print('ABBRUCH: the anchor of %s is not in the duty file' % name)
                other.append(name)
                continue
            p.write_text(text.replace(old, new, 1))
            rc, out = build(mod)
            p.write_text(strip_proofs(orig[p].decode()))
            where = failed_in(out, mod)
            if rc == 0:
                survived.append(name)
                print('SURVIVED  %s' % name)
            elif where and 'Instanz' in where:
                caught.append(name)
                print('caught    %s   (%s)' % (name, where))
            else:
                other.append(name)
                print('FAILED ELSEWHERE %s   (%s)' % (name, where))
    finally:
        for p in orig:
            p.write_bytes(orig[p])
        for p in orig:
            if sha(p) != shas[p]:
                sys.exit('ABBRUCH: %s was NOT restored byte for byte' % p)
    total = len(caught) + len(survived) + len(other)
    print('\n%d of %d planted defects caught by the per-unit check; %d survived; %d failed elsewhere/unmeasured'
          % (len(caught), total, len(survived), len(other)))
    sys.exit(0 if not survived and not other else 1)


main()
