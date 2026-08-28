import re,glob
SPEC=re.compile(r'^\s*(pub\s+)?(open\s+|closed\s+)?spec\s+fn\b')
PROOF=re.compile(r'^\s*(pub\s+)?proof\s+fn\b')
EXEC=re.compile(r'^\s*(pub\s+)?fn\b')
TYPE=re.compile(r'^\s*(pub\s+)?(struct|enum)\b')
tot={}; rows=[]
for f in sorted(glob.glob('Verification/*/proofs/*.rs'))+sorted(glob.glob('verus/*.rs')):
    L=open(f,encoding='utf-8').readlines()
    b={}; mode=None; d=0; started=False
    def add(k,n=1): b[k]=b.get(k,0)+n
    for l in L:
        s=l.strip()
        if not s: continue
        if s.startswith('//'): add('komm'); continue
        if mode is None:
            m = 'spec' if SPEC.match(l) else 'proof' if PROOF.match(l) else 'typ' if TYPE.match(l) else 'exec' if EXEC.match(l) else None
            if m:
                mode=m; d=0; started=False
            else:
                add('rahmen'); continue
        add(mode)
        o=l.count('{'); c=l.count('}')
        if o: started=True
        d+=o-c
        if started and d<=0: mode=None
        elif not started and s.endswith(';'): mode=None
    rows.append((f,b))
    for k,v in b.items(): tot[k]=tot.get(k,0)+v
print(f"{'spec':>6}{'proof':>7}{'exec':>6}{'typ':>6}{'rahm':>6}{'komm':>6}  Datei")
for f,b in rows:
    print(f"{b.get('spec',0):6d}{b.get('proof',0):7d}{b.get('exec',0):6d}{b.get('typ',0):6d}{b.get('rahmen',0):6d}{b.get('komm',0):6d}  {f}")
print('---')
print(f"{tot.get('spec',0):6d}{tot.get('proof',0):7d}{tot.get('exec',0):6d}{tot.get('typ',0):6d}{tot.get('rahmen',0):6d}{tot.get('komm',0):6d}  SUMME")
