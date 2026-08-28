import re,sys
# misst die Rumpflaenge der Audit-Funktionen (nichtleer, ohne reine Kommentarzeilen)
targets=[('crates/caprock-cap/src/space.rs','audit_cdt'),
 ('crates/caprock-ipc/src/lib.rs','audit'),
 ('crates/caprock-hal/src/x86_64/dmar.rs','audit'),
 ('crates/caprock-loader/src/manifest.rs','audit'),
 ('crates/caprock-microkit/src/lib.rs','domain_audit'),
 ('crates/caprock-microkit/src/lib.rs','dma_bounds_audit'),
 ('crates/caprock-sched/src/lib.rs','audit'),
 ('kernel/src/loader.rs','manifest_audit'),
 ('kernel/src/loader.rs','trust_audit'),
 ('kernel/src/system.rs','cap_audit_cdt'),
 ('kernel/src/system.rs','vspace_audit'),
 ('kernel/src/system.rs','dma_audit'),
 ('kernel/src/system.rs','sched_audit_all'),
 ('kernel/src/system.rs','ipc_audit'),
 ('kernel/src/system.rs','loader_audit'),
 ('kernel/src/system.rs','domain_audit'),
]
tot=0; totc=0
seen=set()
for path,name in targets:
    L=open(path,encoding='utf-8').readlines()
    for i,l in enumerate(L):
        if re.match(r'\s*(pub\s+)?fn\s+'+name+r'\b', l) and '{' in l:
            if (path,i) in seen: continue
            seen.add((path,i))
            d=0; n=0; c=0
            for j in range(i,len(L)):
                s=L[j].strip()
                if s:
                    n+=1
                    if s.startswith('//'): c+=1
                d+=L[j].count('{')-L[j].count('}')
                if d<=0 and j>i: break
            print(f'{n-c:5d} Code + {c:4d} Komm.  {path}::{name} (Z. {i+1})')
            tot+=n-c; totc+=c
            break
print(f'--- SUMME: {tot} Codezeilen + {totc} Kommentarzeilen in den Audit-Funktionen')
