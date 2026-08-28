#!/usr/bin/env python3
"""Vollzaehlung in vier Toepfen: {Geruest,Produktion} x {Kommentar,Code}."""
import sys, re, json
WORDS = re.compile(r'\b(selftest|kernel-fuzz|soak|dfprobe|kein-df-ist|test)\b')
ORD = re.compile(r'Ordering::')
UNSAFE = re.compile(r'\bunsafe\s*\{')
WHOLE = {
 'kernel/src/threads/mod.rs','kernel/src/threads/fuzz.rs','kernel/src/threads/soak.rs',
 'kernel/src/selftest.rs','kernel/src/dmatests.rs','kernel/src/sperrmark.rs',
 'kernel/src/arch/x86_64/dmar_selftest.rs'}

def strip_code(line, in_block):
    out=[];i=0;n=len(line)
    while i<n:
        if in_block:
            j=line.find('*/',i)
            if j<0: return ''.join(out),True
            i=j+2;in_block=False;continue
        c=line[i]
        if c=='/' and i+1<n and line[i+1]=='/': break
        if c=='/' and i+1<n and line[i+1]=='*': in_block=True;i+=2;continue
        if c=='"':
            i+=1
            while i<n:
                if line[i]=='\\': i+=2;continue
                if line[i]=='"': i+=1;break
                i+=1
            continue
        if c=="'":
            m=re.match(r"'(\\.|[^\\'])'",line[i:])
            if m: i+=m.end();continue
            i+=1;continue
        out.append(c);i+=1
    return ''.join(out),in_block

def analyse(path):
    lines=open(path,encoding='utf-8',errors='replace').readlines()
    b=dict(gk=0,gc=0,pk=0,pc=0,ord_p=0,ord_g=0,uns_p=0,uns_g=0)
    whole = path in WHOLE
    in_block=False;pending=False;depth=0;active=False;started=False;file_gated=False
    for raw in lines:
        s=raw.strip()
        code,in_block=strip_code(raw,in_block)
        if not s: continue
        if s.startswith('#![') and 'cfg' in s and WORDS.search(s): file_gated=True
        g = whole or file_gated
        if not g:
            if active: g=True
            elif s.startswith('#['):
                if 'cfg' in s and WORDS.search(s): pending=True; g=True
                else: g=False
            elif pending: g=True
        # Zustandsfortschreibung
        if not (whole or file_gated):
            if active:
                for c in code:
                    if c in '{([': depth+=1;started=True
                    elif c in '})]': depth-=1
                if started and depth<=0: active=False;started=False;depth=0
                elif not started and ';' in code: active=False
            elif s.startswith('#['):
                pass
            elif pending:
                pending=False;active=True;depth=0;started=False
                for c in code:
                    if c in '{([': depth+=1;started=True
                    elif c in '})]': depth-=1
                if started and depth<=0: active=False
                elif not started and ';' in code: active=False
        iscomment = not code.strip()
        if g:
            b['gk' if iscomment else 'gc'] += 1
            b['ord_g'] += len(ORD.findall(raw)); b['uns_g'] += len(UNSAFE.findall(raw))
        else:
            b['pk' if iscomment else 'pc'] += 1
            b['ord_p'] += len(ORD.findall(raw)); b['uns_p'] += len(UNSAFE.findall(raw))
    b['path']=path
    return b

rows=[analyse(p) for p in sys.argv[1:]]
json.dump(rows,open('/home/simon/Dokumente/Gabbro/messung/gegenrechnung/voll.json','w'))
T=lambda k: sum(r[k] for r in rows)
tot=T('gk')+T('gc')+T('pk')+T('pc')
print(f"nichtleer gesamt          {tot}")
print(f"  Geruest  Kommentar      {T('gk'):6d}")
print(f"  Geruest  Code           {T('gc'):6d}")
print(f"  Produkt. Kommentar      {T('pk'):6d}")
print(f"  Produkt. Code           {T('pc'):6d}")
print()
print(f"Geruest gesamt            {T('gk')+T('gc'):6d}  = {100*(T('gk')+T('gc'))/tot:.1f}%")
print(f"Produktion gesamt         {T('pk')+T('pc'):6d}  = {100*(T('pk')+T('pc'))/tot:.1f}%")
print(f"Kommentar gesamt          {T('gk')+T('pk'):6d}  = {100*(T('gk')+T('pk'))/tot:.1f}%")
print(f"PRODUKTIONSCODE (ohne Kommentar, ohne Geruest) {T('pc')} = {100*T('pc')/tot:.1f}%")
print()
print(f"Ordering:: Produktion {T('ord_p')}, Geruest {T('ord_g')}")
print(f"unsafe{{  Produktion {T('uns_p')}, Geruest {T('uns_g')}")
