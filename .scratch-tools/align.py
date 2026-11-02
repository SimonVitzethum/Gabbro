import sys,re,pathlib
FIELD=re.compile(r'^(\s*)([A-Za-z_][A-Za-z0-9_\']*)\s*:=')
def fix(text):
    lines=text.split("\n"); out=[]; i=0; changed=0
    while i<len(lines):
        l=lines[i]; out.append(l)
        # find an opening '{' followed by a field on the same line, with unbalanced braces
        m=re.search(r'\{\s*([A-Za-z_][A-Za-z0-9_\']*\s*:=|[A-Za-z_][A-Za-z0-9_.\']* with\s+[A-Za-z_][A-Za-z0-9_\']*\s*:=)',l)
        if m and l.count('{')>l.count('}'):
            # column of first field
            sub=l[m.start()+1:]
            off=len(sub)-len(sub.lstrip())
            fm=re.match(r'[A-Za-z_][A-Za-z0-9_.\']* with\s+',sub.lstrip())
            col=m.start()+1+off+(fm.end() if fm else 0)
            depth=l.count('{')-l.count('}'); prev_end_comma=l.rstrip().endswith(',')
            j=i+1
            while j<len(lines) and depth>0:
                nl=lines[j]; fm2=FIELD.match(nl)
                if fm2 and prev_end_comma and len(fm2.group(1))<col:
                    nl=" "*col+nl.lstrip(); changed+=1
                out.append(nl); depth+=nl.count('{')-nl.count('}'); prev_end_comma=nl.rstrip().endswith(','); j+=1
            i=j; continue
        i+=1
    return "\n".join(out),changed
for f in sys.argv[1:]:
    p=pathlib.Path(f); t=p.read_text(); t2,c=fix(t)
    if c: p.write_text(t2); print(f,c)
