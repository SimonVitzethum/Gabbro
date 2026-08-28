import re,sys,json
FN=re.compile(r'^(\s*)(pub(\([^)]*\))?\s+)?(const\s+)?(async\s+)?(unsafe\s+)?(extern\s+"[^"]*"\s+)?fn\s+([A-Za-z_][A-Za-z0-9_]*)')
WORDS=re.compile(r'\b(selftest|kernel-fuzz|soak|dfprobe|kein-df-ist|test)\b')
BRANCH=re.compile(r'(^|[^\w.])(if|match|for|while|loop)[\s({]')
WHOLE={'kernel/src/threads/mod.rs','kernel/src/threads/fuzz.rs','kernel/src/threads/soak.rs',
 'kernel/src/selftest.rs','kernel/src/dmatests.rs','kernel/src/sperrmark.rs',
 'kernel/src/arch/x86_64/dmar_selftest.rs'}
buckets={'trivial':0,'klein':0,'mittel':0,'gross':0}
cnt={'trivial':0,'klein':0,'mittel':0,'gross':0}
grosse=[]
for path in sys.argv[1:]:
    if path in WHOLE: continue
    L=open(path,encoding='utf-8',errors='replace').readlines()
    i=0
    gate=0
    while i<len(L):
        s=L[i].strip()
        if s.startswith('#[') and 'cfg' in s and WORDS.search(s): gate=1; i+=1; continue
        m=FN.match(L[i])
        if m and '{' in L[i]:
            if gate: gate=0
            d=L[i].count('{')-L[i].count('}'); j=i+1; body=[]
            while j<len(L) and d>0:
                body.append(L[j]); d+=L[j].count('{')-L[j].count('}'); j+=1
            gate_this = False
            n=sum(1 for x in body if x.strip() and not x.strip().startswith('//'))
            hasbr=any(BRANCH.search(x) for x in body)
            k = 'trivial' if n<=3 and not hasbr else 'klein' if n<=10 else 'mittel' if n<=40 else 'gross'
            buckets[k]+=n+1; cnt[k]+=1
            if k=='gross': grosse.append((n,path,m.group(8)))
            i=j; continue
        gate=0; i+=1
tot=sum(buckets.values())
print(f"{'Klasse':10}{'Fn':>6}{'Zeilen':>8}{'Anteil':>8}")
for k in ('trivial','klein','mittel','gross'):
    print(f"{k:10}{cnt[k]:6d}{buckets[k]:8d}{100*buckets[k]/tot:7.1f}%")
print(f"{'gesamt':10}{sum(cnt.values()):6d}{tot:8d}")
print("\nDie 20 groessten Produktionsfunktionen:")
for n,p,f in sorted(grosse,reverse=True)[:20]: print(f"  {n:5d}  {p}::{f}")
