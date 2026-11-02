import os,re
mods=set()
T=["grammatik","stage0","bruecke","runner"]
for top in T:
  for r,_,fs in os.walk(top):
    if ".lake" in r: continue
    for f in fs:
      if f.endswith(".lean"): mods.add(os.path.relpath(os.path.join(r,f),top)[:-5].replace("/","."))
bad=0
for top in T:
  for r,_,fs in os.walk(top):
    if ".lake" in r: continue
    for f in fs:
      if f.endswith(".lean"):
        for l in open(os.path.join(r,f),encoding="utf-8"):
          m=re.match(r"\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?((?:Grammatik|Stage0|Bruecke|Runner)\S*)",l)
          if m and m.group(1) not in mods: bad+=1; print(os.path.join(r,f),m.group(1))
print("unresolved",bad)
