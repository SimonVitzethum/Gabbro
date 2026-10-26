import json, re, sys, pathlib
G = pathlib.Path(__file__).resolve().parent
W = G.parent.parent
sys.path.insert(0, str(G))
from manuell import M as MAN
r = json.load(open(str(G / 'rules.json')))
names = list(r.keys())
def groups(b):
    out=[]; depth=0; cur=''
    for ch in b:
        if ch in '({[':
            if depth==0: cur=''
            depth+=1; cur+=ch
        elif ch in ')}]':
            depth-=1; cur+=ch
            if depth==0: out.append(cur)
        elif depth>0: cur+=ch
    return out
def toM(e):
    e = e.replace('(normal ww M)', 'M')
    e = re.sub(r'\bOF\b', 'OM', e)
    return e
HEADER = '''/-
  File:      stage0/Stage0/Schnell/Sim/{f}.lean
  Subject:   The simulation of the normal form, rules {a} .. {b} of `RufSchrittG` (`Schnell/Sim.lean`): a step of
             `normal ww M` under the fast oracle is a step of `M` under the machine's oracle, to the same normal form.
-/
import Stage0.Schnell.Werkzeug

namespace Gabbro.Stage0

open Gabbro.Grammatik

variable {{D : Deklaration}} {{P : Programm D}} {{OF OM : Orakel D}} {{passes : Nat}} {{ww : World D}}
'''
def lemma(n):
    v = r[n]
    b = v['binders'].replace('(_ :', '(hkopf_ :')
    gs = groups(b)
    # binder names in order, with kind
    args = []
    substs = []
    worlddef = {}
    for g in gs:
        inner = g[1:-1]
        hd, ty = inner.split(':',1)
        for nm in hd.split():
            args.append((nm, ty.strip(), g[0]))
    names_ = [a[0] for a in args]
    tys = {a[0]: a[1] for a in args}
    prefix = ''
    repl = {}
    def subw(e):
        for k2, v2 in worlddef.items():
            if v2 != 'rfl' and k2 in [a[0] for a in args if a[1] == 'World D']:
                e = re.sub(re.escape(k2) + r'(?![\w\'₀-₉])', '(' + v2 + ')', e)
        return e
    worldF = {}
    def subF(e):
        for k2, v2 in worldF.items():
            e = re.sub(re.escape(k2) + r'(?![\w\'₀-₉])', '(' + v2 + ')', e)
        return e
    # a leaf step whose outcome is `leave`/`next`: the step reduces
    if 'hstep' in names_:
        prefix += '  simp only [execStmt] at hstep\n  cases hstep\n'
        worlddef["σ'"] = '(M.weltVon f)'
        repl['hstep'] = 'rfl'
        repl["ρ'"] = '_'
    # world definitions
    for i,(nm,ty,br) in enumerate(args):
        if ty == 'World D' and i+1 < len(args):
            nm2, ty2, _ = args[i+1]
            m = re.match(r'^' + re.escape(nm) + r'\s*=\s*(.*)$', ty2, re.S)
            m2 = re.match(r'^(.*?)\s*=\s*' + re.escape(nm) + r'$', ty2, re.S)
            if m:
                worlddef[nm] = subw(toM(m.group(1))); worlddef[nm2] = 'rfl'; substs.append(nm2); worldF[nm] = subF(m.group(1))
            elif m2:
                worlddef[nm] = subw(toM(m2.group(1))); worlddef[nm2] = 'rfl'; substs.append(nm2); worldF[nm] = subF(m2.group(1))
    post = ''
    if 'hpop' in names_:
        mm = re.match(r'.*=\s*(\w+)\s*::\s*(\w+)\s*$', tys['hpop'], re.S)
        cn, rn = mm.group(1), mm.group(2)
        post += f"""  obtain ⟨cM, rM, hM, hc, hr⟩ : ∃ cM rM, (M.faeden f).stapel = cM :: rM ∧ {cn} = cM.ohne ww ∧
      {rn} = rM.map (RufRahmenG.ohne ww) := by
    cases hs : (M.faeden f).stapel with
    | nil => simp [normal, fadenNormal, hs] at hpop
    | cons cM rM =>
      simp only [normal, fadenNormal, hs, List.map_cons, List.cons.injEq] at hpop
      exact ⟨cM, rM, rfl, hpop.1.symm, hpop.2.symm⟩
  subst hc hr
"""
        repl[cn] = 'cM'; repl[rn] = 'rM'; repl['hpop'] = 'hM'
    if 'hfg' in names_ and re.search(r'=\s*g\s*$', tys['hfg']):
        post += '  subst hfg\n'; repl['g'] = '_'; repl['hfg'] = 'rfl'
    tail = ''
    if 'hv' in names_ and tys['hv'].strip().startswith('v ='):
        repl['hv'] = '(hv.trans hE)'
        mv = re.search(r'evalErg (\S+) (\S+) (\S+) (\S+)$', tys['hv'].strip())
        wv, ex, en = mv.group(1), mv.group(2), mv.group(4)
        post += f'  have hE : evalErg ({worldF[wv]}) {ex} ({worldF[wv]}) {en} = evalErg ({worlddef[wv]}) {ex} ({worlddef[wv]}) {en} :=\n    Paar.evalErg (sF := kompakt (M.faeden f).spur) (sM := (M.faeden f).spur) (by paar) (by paar) {ex} {en}\n'
    if n == 'dannExchange':
        wF, wM = worldF['σ₁'], worlddef['σ₁']
        post += f'  have hE : eval ({wF}) neuE ({wF}) (.cons (({wF}).globs g) ρ) = eval ({wM}) neuE ({wM}) (.cons (({wM}).globs g) ρ) :=\n    Paar.eval (sF := kompakt (M.faeden f).spur) (sM := (M.faeden f).spur) (by paar) (by paar) neuE _\n  rw [hE] at hneu\n'
        tail += '  all_goals try (rw [hE]; sim_ziel)\n'
    if 'hax' in names_:
        sonst = 'axiomAntwortSonst' in tys['hax']
        lem = 'axiomSonst_paar\'' if sonst else 'axiom_paar\''
        post += f"""  obtain ⟨⟨σ₂M, oM⟩, hZ, hq, ho⟩ := {lem} hO (schwanz_normal M f)
    (Paar.lese (schwanz_normal M f) (paar_normal (w := ww) M f) _ _) hax
    (ρM := evalArgs ({worlddef['σ₁']}) args ({worlddef['σ₁']}) ρ) (by first | (sim_simp; done) | (sim_simp; rfl))
  simp only at ho
  subst ho
"""
        repl['σ₂'] = 'σ₂M'; repl['hax'] = 'hZ'
    margs = []
    worldvars = [nm for nm,ty,br in args if ty == 'World D']
    for nm,ty,br in args:
        if br == '{': continue
        if nm in repl: margs.append(repl[nm])
        elif nm in worlddef: margs.append('(' + worlddef[nm] + ')')
        elif 'OF.regLies' in ty:
            margs.append(f'(by rw [← hO.zeiger, ← hO.regLies r (schwanz_normal M f) (Paar.fragt (paar_normal (w := ww) M f) _)]; exact {nm})')
        elif 'OF.sichtbar' in ty:
            margs.append(f'(by rw [← hO.sichtbar g (schwanz_normal M f) (Paar.fragt (paar_normal (w := ww) M f) _)]; exact {nm})')
        elif ty == 'World D': margs.append('?_')
        elif any(k in ty for k in ['.spur', 'weltVon', 'OF', 'RufFreiG']) or any(re.search(r'(?<![\w.])' + re.escape(x) + r'(?![\w])', ty) for x in worldvars):
            margs.append('?_')
        else:
            margs.append(nm)
    t = v['target']
    s = f'''theorem sim_{n} {{M : RufMaschineG D}} {{f : Faden}} (hO : OrakelPaar (fremdZahl (M.faeden f).spur) OF OM)
    {b} :
    ∃ M' : RufMaschineG D, RufSchrittG P OM passes M f M' ∧
      normal ww ({t} : RufMaschineG D) = normal ww M' ∧
      fremdZahl (M'.faeden f).spur =
        fremdZahl ((({t} : RufMaschineG D)).faeden f).spur + fremdZahl (M.faeden f).spur := by
'''
    if n in MAN:
        return s + MAN[n]
    s += prefix
    for h in substs: s += f'  subst {h}\n'
    s += post
    s += f'  refine ⟨_, RufSchrittG.{n} M f {" ".join(margs)}, sim_schluss ?_ ?_ ?_ (neu := ?neu) ?_ ?_⟩\n'
    s += '  all_goals try sim_ziel\n' + tail
    return s
chunks = [names[i:i+10] for i in range(0, len(names), 10)]
import string
for ci, ch in enumerate(chunks):
    fn = 'S' + string.ascii_uppercase[ci]
    a = ci*10+1; bb = ci*10+len(ch)
    txt = HEADER.format(f=fn, a=a, b=bb) + '\n' + '\n'.join(lemma(n) for n in ch) + '\nend Gabbro.Stage0\n'
    open(str(W / 'stage0/Stage0/Schnell/Sim' / (fn + '.lean')),'w').write(txt)
    print(fn, ch)
