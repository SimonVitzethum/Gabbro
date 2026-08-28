#!/usr/bin/env python3
"""Zaehlt je Datei die Schleifen (for/while/loop) im PRODUKTIONSteil
(also ausserhalb test-/messgegatterter Items) und die Funktionen, die eine enthalten."""
import sys, re, os, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
WORDS = re.compile(r'\b(selftest|kernel-fuzz|soak|dfprobe|kein-df-ist|test)\b')
LOOP = re.compile(r'(^|[^\w.])(for|while)\s|(^|[^\w.])loop\s*\{')
FN   = re.compile(r'^\s*(pub(\([^)]*\))?\s+)?(const\s+)?(async\s+)?(unsafe\s+)?(extern\s+"[^"]*"\s+)?fn\s+([A-Za-z_][A-Za-z0-9_]*)')

def strip_code(line, in_block):
    out = []; i = 0; n = len(line)
    while i < n:
        if in_block:
            j = line.find('*/', i)
            if j < 0: return ''.join(out), True
            i = j + 2; in_block = False; continue
        c = line[i]
        if c == '/' and i+1 < n and line[i+1] == '/': break
        if c == '/' and i+1 < n and line[i+1] == '*':
            in_block = True; i += 2; continue
        if c == '"':
            i += 1
            while i < n:
                if line[i] == '\\': i += 2; continue
                if line[i] == '"': i += 1; break
                i += 1
            continue
        if c == "'":
            m = re.match(r"'(\\.|[^\\'])'", line[i:])
            if m: i += m.end(); continue
            i += 1; continue
        out.append(c); i += 1
    return ''.join(out), in_block

WHOLE = {
 'kernel/src/threads/mod.rs','kernel/src/threads/fuzz.rs','kernel/src/threads/soak.rs',
 'kernel/src/selftest.rs','kernel/src/dmatests.rs','kernel/src/sperrmark.rs',
 'kernel/src/arch/x86_64/dmar_selftest.rs'}

def analyse(path):
    if path in WHOLE:
        return dict(path=path, loops=0, fns=0, loopfns=0, fnlines=0, loopfnlines=0)
    lines = open(path, encoding='utf-8', errors='replace').readlines()
    in_block=False; pending=False; depth=0; active=False; started=False
    # Funktions-Tracking
    fn_depth=None; fn_has_loop=False; fn_lines=0
    loops=0; fns=0; loopfns=0; fnlines=0; loopfnlines=0
    cur_depth=0
    for raw in lines:
        s=raw.strip()
        code,in_block=strip_code(raw,in_block)
        gated_line=False
        if active:
            gated_line=True
            for c in code:
                if c in '{([': depth+=1; started=True
                elif c in '})]': depth-=1
            if started and depth<=0: active=False; started=False; depth=0
            elif not started and ';' in code: active=False
        elif s.startswith('#['):
            if 'cfg' in s and WORDS.search(s): pending=True
            gated_line=True
        elif pending and s:
            pending=False; active=True; depth=0; started=False; gated_line=True
            for c in code:
                if c in '{([': depth+=1; started=True
                elif c in '})]': depth-=1
            if started and depth<=0: active=False
            elif not started and ';' in code: active=False
        if gated_line:
            continue
        # ungegattert: Funktions- und Schleifenerkennung
        if fn_depth is None:
            m=FN.match(raw)
            if m and '{' in code:
                fn_depth=0; fn_has_loop=False; fn_lines=0
        if fn_depth is not None:
            if s: fn_lines+=1
            if LOOP.search(code): fn_has_loop=True; loops+=1
            for c in code:
                if c=='{': fn_depth+=1
                elif c=='}': fn_depth-=1
            if fn_depth<=0:
                fns+=1; fnlines+=fn_lines
                if fn_has_loop: loopfns+=1; loopfnlines+=fn_lines
                fn_depth=None
        else:
            if LOOP.search(code): loops+=1
    return dict(path=path, loops=loops, fns=fns, loopfns=loopfns, fnlines=fnlines, loopfnlines=loopfnlines)

rows=[analyse(p) for p in sys.argv[1:]]
json.dump(rows, open('/home/simon/Dokumente/Gabbro/messung/gegenrechnung/schleifen.json','w'))
T=lambda k: sum(r[k] for r in rows)
print(f"Produktionsfunktionen: {T('fns')}")
print(f"  davon mit Schleife:  {T('loopfns')}  ({100*T('loopfns')/T('fns'):.1f}%)")
print(f"Schleifen gesamt:      {T('loops')}")
print(f"Zeilen in Produktionsfunktionen:      {T('fnlines')}")
print(f"  davon in Funktionen MIT Schleife:   {T('loopfnlines')} ({100*T('loopfnlines')/T('fnlines'):.1f}%)")
