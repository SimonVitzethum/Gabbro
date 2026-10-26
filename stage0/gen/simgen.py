import re, sys, json, pathlib
G = pathlib.Path(__file__).resolve().parent
W = G.parent.parent
src = open(str(W / 'grammatik') + '/Grammatik/Logik/Ruf/Maschine/RufMaschineG/T2.lean').read()
lines = src.split('\n')
start = next(i for i,l in enumerate(lines) if l.startswith('inductive RufSchrittG'))
end = next(i for i,l in enumerate(lines) if i > start and (l.startswith('end ') or l.startswith('/-! ') or l.startswith('theorem') or l.startswith('def ')))
body = lines[start+2:end]
# strip doc comments
txt = '\n'.join(body)
txt = re.sub(r'/--.*?-/', '', txt, flags=re.S)
txt = re.sub(r'--[^\n]*', '', txt)
parts = re.split(r'\n  \| ', '\n' + txt)
rules = []
for p in parts:
    p = p.strip('\n')
    if not p.strip(): continue
    m = re.match(r'\s*([A-Za-z]+)\s*(.*)', p, re.S)
    name, rest = m.group(1), m.group(2)
    k = rest.index('RufSchrittG P O passes M f')
    binders = rest[:k].rstrip()
    assert binders.endswith(':'), name
    binders = binders[:-1].rstrip()
    target = rest[k+len('RufSchrittG P O passes M f'):].strip()
    binders = re.sub(r'^\(M : RufMaschineG D\)\s*\(f : Faden\)', '', binders.strip()).strip()
    rules.append((name, binders, target))
def subM(t):
    t = re.sub(r'\bM\.', '(normal ww M).', t)
    t = re.sub(r'RufFreiG M f', 'RufFreiG (normal ww M) f', t)
    t = re.sub(r'\bO\b', 'OF', t)
    return t
def binder_names(b):
    names = []
    depth = 0; cur = ''
    i = 0
    groups = []
    while i < len(b):
        ch = b[i]
        if ch in '({[': 
            if depth == 0: cur = ''
            depth += 1
            cur += ch
        elif ch in ')}]':
            depth -= 1; cur += ch
            if depth == 0: groups.append(cur)
        else:
            if depth > 0: cur += ch
        i += 1
    for g in groups:
        inner = g[1:-1]
        hd = inner.split(':')[0]
        names += hd.split()
    return names
out = {}
for name, b, t in rules:
    out[name] = {'binders': subM(b), 'target': subM(t), 'names': binder_names(b)}
json.dump(out, open(str(G / 'rules.json'),'w'), indent=1, ensure_ascii=False)
print(len(rules))
print(rules[0][0], binder_names(rules[0][1]))
print(rules[-1][0], binder_names(rules[-1][1]))
