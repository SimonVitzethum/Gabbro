import json, collections
Z = {
'F': [ # Formate / Parser / Kodierung
 'crates/caprock-fat/src/lib.rs','crates/caprock-part/src/lib.rs','crates/caprock-dtb/src/lib.rs',
 'crates/caprock-loader/src/elf.rs','crates/caprock-loader/src/archive.rs','crates/caprock-loader/src/cert.rs',
 'crates/caprock-loader/src/manifest.rs','crates/caprock-loader/src/lib.rs','crates/caprock-cap/src/checkpoint.rs',
 'kernel/src/arch/x86_64/multiboot.rs','kernel/src/arch/x86_64/bootinfo.rs',
 'crates/caprock-hal/src/x86_64/acpi.rs','crates/caprock-hal/src/x86_64/dmar.rs',
 'crates/caprock-hal/src/x86_64/irte.rs','crates/caprock-abi/src/lib.rs',
 'crates/caprock-hal/src/cache_decode.rs','crates/caprock-sched/src/redirect.rs',
 'kernel/src/manifest_keys.rs','kernel/src/trusted_keys.rs','crates/caprock-trust/src/lib.rs'],
'T': [ # Tabellen / Strukturen mit Invariante ueber Mutationen
 'crates/caprock-cap/src/space.rs','crates/caprock-cap/src/object.rs','crates/caprock-cap/src/lib.rs',
 'crates/caprock-hal/src/x86_64/mmu.rs','crates/caprock-hal/src/aarch64/mmu.rs',
 'crates/caprock-hal/src/x86_64/vtd.rs','crates/caprock-hal/src/aarch64/smmu.rs',
 'crates/caprock-mem/src/alloc.rs','crates/caprock-mem/src/region.rs','crates/caprock-mem/src/cap.rs',
 'crates/caprock-mem/src/lib.rs','crates/caprock-mem/src/color.rs','crates/caprock-slab/src/lib.rs',
 'crates/caprock-region/src/lib.rs','crates/caprock-region/src/heap.rs','crates/caprock-region/src/state.rs',
 'crates/caprock-microkit/src/lib.rs','kernel/src/loader.rs','kernel/src/colors.rs'],
'N': [ # nebenlaeufiger Kern
 'kernel/src/system.rs','crates/caprock-sched/src/lib.rs','crates/caprock-sched/src/cycles.rs',
 'crates/caprock-ipc/src/lib.rs','crates/caprock-sync/src/lib.rs','crates/caprock-wait/src/lib.rs',
 'kernel/src/verifizierer.rs','kernel/src/sidecarkopie.rs','kernel/src/grossdma.rs',
 'crates/caprock-dma/src/lib.rs','crates/caprock-dma/src/gross.rs','kernel/src/addr.rs'],
'B': [ # Boot / Entry / arch-Glue
 'kernel/src/arch/x86_64/bringup.rs','kernel/src/arch/x86_64/mod.rs','kernel/src/arch/x86_64/ist.rs',
 'kernel/src/arch/aarch64/boot.rs','kernel/src/arch/aarch64/mod.rs','kernel/src/arch/mod.rs',
 'kernel/src/main.rs','kernel/src/panic.rs'],
'M': [ # Messcode, der im Produktivbau mitlaeuft
 'kernel/src/kstackmark.rs','kernel/src/userstackmark.rs','kernel/src/handlermess.rs'],
'G': ['kernel/src/threads/mod.rs','kernel/src/threads/fuzz.rs','kernel/src/threads/soak.rs',
       'kernel/src/selftest.rs','kernel/src/dmatests.rs','kernel/src/sperrmark.rs',
       'kernel/src/arch/x86_64/dmar_selftest.rs'],
'P': ['programs/'],
}
rows=json.load(open('/home/simon/Dokumente/Gabbro/messung/gegenrechnung/voll.json'))
loops={r['path']:r for r in json.load(open('/home/simon/Dokumente/Gabbro/messung/gegenrechnung/schleifen.json'))}
m={}
for k,v in Z.items():
    for p in v: m[p]=k
def cls(p):
    if p in m: return m[p]
    if p.startswith('programs/'): return 'P'
    return 'D'
agg=collections.defaultdict(lambda: collections.Counter())
for r in rows:
    c = 'G' if (r['gc']+r['gk'])>0 and r['pc']==0 and r['pk']<=30 else cls(r['path'])
    k=cls(r['path'])
    agg[k]['pc']+=r['pc']; agg[k]['pk']+=r['pk']; agg[k]['g']+=r['gc']+r['gk']
    agg[k]['gc']+=r['gc']; agg[k]['gk']+=r['gk']
    agg[k]['ord']+=r['ord_p']; agg[k]['uns']+=r['uns_p']
    L=loops.get(r['path'],{})
    agg[k]['loops']+=L.get('loops',0); agg[k]['loopfns']+=L.get('loopfns',0); agg[k]['fns']+=L.get('fns',0)
NAM={'F':'Formate/Parser','T':'Tabellen+Invarianten','N':'nebenlaeufiger Kern','D':'Treiber/HAL/Register',
     'B':'Boot/Entry/arch-Glue','M':'Messcode im Produktivbau','P':'Userland-Programme','G':'reine Geruestdateien'}
gtot=sum(a['g'] for a in agg.values())
print(f"{'Kl':3}{'Prod-Code':>10}{'Prod-Komm':>11}{'Geruest':>9}{'Schl':>6}{'Ord':>6}{'unsafe':>8}  Name")
tp=tk=tg=tl=to=tu=0
for k in ['N','T','D','B','F','P','M','G']:
    a=agg[k]
    print(f"{k:3}{a['pc']:10d}{a['pk']:11d}{a['g']:9d}{a['loops']:6d}{a['ord']:6d}{a['uns']:8d}  {NAM[k]}")
    tp+=a['pc'];tk+=a['pk'];tg+=a['g'];tl+=a['loops'];to+=a['ord'];tu+=a['uns']
print(f"{'':3}{tp:10d}{tk:11d}{tg:9d}{tl:6d}{to:6d}{tu:8d}  SUMME")
print()
print(f"Geruest (mechanisch, cfg-gegattert):      {tg}  Code {sum(a['gc'] for a in agg.values())} + Komm {sum(a['gk'] for a in agg.values())}")
print(f"Produktionszeilen (nichtleer):            {tp+tk}")
print(f"Produktions-CODE (ohne Kommentar):        {tp}")
print(f"nichtleer gesamt:                         {tp+tk+tg}")
for k in ['N','T','D','B','F','P','M','G']:
    print(f"  {k}: Prod-Code {agg[k]['pc']:6d} = {100*agg[k]['pc']/tp:5.1f}% des Produktionscodes")
