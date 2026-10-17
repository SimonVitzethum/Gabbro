#!/usr/bin/env python3
"""Coverage matrix of the Lean parser (Track P, `dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md` section 9a).

One row per EBNF rule of `dokumente/SYNTAX.md` (189 defined rules), four columns, one measured column.

  reader    S  structured and shape-faithful      P  structured, some spellings refused or a part dropped
            R  balanced words kept as raw text    X  no reader (refused / fails on the corpus)
  printer   E  a Lean printer exists (`druckToks`)  .  none
  rtrip     P  a round-trip theorem for the printable shapes   .  none
  elab      U  `elabU`/`lowerAllg` lowers the rule into `UProg`/`declOf`/`Programm`   .  none
  corpus    number of `beispiele/*.gab` files that use the rule's head word(s) (a text scan)

The corpus lines come from the Lean census (`Grammatik/Parser/Cover/Census.lean`, run through `lake env lean
--run`): per file `lex`, whole-file `parse` and `elab`, and the first failing items. This script only reads the
census text (`--census FILE`) or runs it (`--run`); the status letters are maintained by hand next to the Lean
sources they describe, and every change of a letter belongs in the same commit as the Lean change.

  python3 instrumente/parser-deckung.py --run            # run the census, print the matrix and the totals
  python3 instrumente/parser-deckung.py --census FILE    # the same from a saved census
  python3 instrumente/parser-deckung.py --run --md       # markdown for the plan document
"""
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# (rule, group, reader, printer, rtrip, elab, corpus regex or None, note)
RULES = [
    # --- lexical
    ("ident", "lex", "S", ".", ".", ".", None, "`lex`, total (`lex_total`)"),
    ("letter", "lex", "S", ".", ".", ".", None, ""),
    ("digit", "lex", "S", ".", ".", ".", None, ""),
    ("hexdigit", "lex", "S", ".", ".", ".", None, ""),
    ("int", "lex", "S", ".", ".", ".", None, "`Token.num` (value only: the spelling is lost)"),
    ("dec", "lex", "S", ".", ".", ".", None, ""),
    ("hex", "lex", "S", ".", ".", ".", None, ""),
    ("bin", "lex", "S", ".", ".", ".", None, ""),
    ("float", "lex", "S", ".", ".", ".", None, ""),
    ("string", "lex", "S", ".", ".", ".", None, "`Token.text`; the expression reader has no string primary"),
    ("char", "lex", "S", ".", ".", ".", None, ""),
    ("quote", "lex", "S", ".", ".", ".", None, ""),
    ("newline", "lex", "S", ".", ".", ".", None, ""),
    ("comment", "lex", "S", ".", ".", ".", None, ""),
    ("path", "lex", "S", ".", ".", ".", None, "`nimmPfad`"),
    ("pathseg", "lex", "S", ".", ".", ".", None, ""),
    ("identlist", "lex", "S", ".", ".", ".", None, ""),
    ("regbind", "lex", "S", ".", ".", ".", None, "`SRegBind`"),
    # --- section 1: program, items
    ("program", "item", "S", ".", ".", "U", None, "`parseTopTief`; `elabU` takes tables, locks, impl fns, consts, entries"),
    ("item", "item", "S", ".", ".", "U", None, "`SItemTief`, 32 constructors"),
    ("buildgate", "item", "S", ".", ".", ".", r"\bwhen\s+TESTBUILD", "`torT`"),
    ("bootdecl", "item", "S", ".", ".", ".", r"^\s*boot\s", "`startT`"),
    ("bootstep", "item", "S", ".", ".", ".", r"^\s*step\s", "`SBootSchritt`"),
    ("entrydecl", "item", "S", ".", ".", "U", r"^\s*(pub\s+)?entry\s+[a-z_A-Z]", "`SEingang`; `elabU` reads only the dispatch roots"),
    ("entrustdecl", "item", "S", ".", ".", ".", r"^\s*entrust\s", ""),
    ("entryextra", "item", "S", ".", ".", ".", r"\bnested\s+(never|masked|bounded)|\bper\s+cpu\b", ""),
    ("syscalldecl", "item", "P", ".", ".", ".", r"^\s*(pub\s+)?syscall\s", "pre-O31 form only; `syscall V;` and `via V` refused"),
    ("sysbind", "item", "S", ".", ".", ".", r"\bnumber\s", ""),
    ("syscontract", "item", "S", ".", ".", ".", None, ""),
    ("syspair", "item", "S", ".", ".", ".", r"\b(falsifier|unfalsifiable|kernel)\s", ""),
    ("targetdecl", "item", "X", ".", ".", ".", r"^\s*target\s", "no `target` word in the lexer table, no reader"),
    ("targetbind", "item", "X", ".", ".", ".", r"^\s*target\s", ""),
    ("errmap", "item", "P", ".", ".", ".", r"\berrors\s*\{", "the errno number of `E = n => R` is dropped"),
    ("accdecl", "item", "S", ".", ".", ".", r"^\s*accumulates\s", "`akkumT`"),
    ("moduledecl", "item", "P", ".", ".", "U", r"^\s*(pub\s+)?module\s", "`modulT`; `pub` is dropped"),
    ("usedecl", "item", "S", ".", ".", ".", r"^\s*(pub\s+)?use\s", ""),
    ("constdecl", "item", "S", ".", ".", "U", r"^\s*(pub\s+)?const\s+[A-Za-z_]", "`konstT`"),
    ("constexpr", "item", "S", "E", "P", "U", None, "an `SExpr`"),
    ("constwert", "item", "P", ".", ".", ".", None, "a flat array literal only"),
    ("arraylit", "item", "P", ".", ".", ".", r"=\s*\[", "nested literals refused (123)"),
    ("staticdecl", "item", "P", ".", ".", ".", r"^\s*(pub\s+)?static\s", "array statics refused (175, 186, 192)"),
    ("typedecl", "item", "S", ".", ".", "U", r"^\s*(pub\s+)?(opaque\s+|linear\s+|ghost\s+|tagged\s+)*type\s", "`typT`; elab reads range aliases"),
    ("markorder", "item", "S", ".", ".", ".", r"\border\s*\{", ""),
    # --- section 2: types
    ("typeexpr", "type", "P", ".", ".", "U", None, "`STyp`; struct, variants, fn pointer ride raw"),
    ("stringty", "type", "X", ".", ".", ".", r"\bstring\s+max\b", "refused (1123, 1124, 1126, 1159, 161, 191, 192)"),
    ("stringkopf", "type", "X", ".", ".", ".", r"\bstring\s+max\b", ""),
    ("indexty", "type", "S", ".", ".", "U", r"\bindex\s+into\b", "`STyp.index`"),
    ("nevertype", "type", "S", ".", ".", ".", r"->\s*never\b", ""),
    ("intty", "type", "S", ".", ".", "U", r"\b[ui](8|16|32|64)\b", ""),
    ("uint", "type", "S", ".", ".", "U", r"\bu([1-9]|[1-5][0-9]|6[0-4])\b", ""),
    ("int", "type", "S", ".", ".", "U", r"\bi([1-9]|[1-5][0-9]|6[0-4])\b", "second definition of `int` (signed sugar)"),
    ("nonzero", "type", "S", ".", ".", ".", None, ""),
    ("floatty", "type", "P", ".", ".", ".", r"\bf(32|64)\b", "read as an atom plus `in`; no float elaboration"),
    ("frange", "type", "P", ".", ".", ".", r"\bf(32|64)\s+in\b", ""),
    ("fexpr", "type", "P", ".", ".", ".", r"\brounded\b", ""),
    ("boolty", "type", "S", ".", ".", "U", r"\bbool\b", ""),
    ("range", "type", "S", ".", ".", "U", r"\bin\s+[^;]*\.\.", ""),
    ("array", "type", "S", ".", ".", ".", r"\[\s*[A-Za-z_0-9]+\s*;", "`STyp.reihe`"),
    ("structty", "type", "R", ".", ".", ".", r"\btype\s+\w+\s*=\s*\{", "balanced, uninterpreted"),
    ("field", "type", "R", ".", ".", ".", None, "inside a struct type: raw; inside `format`/`slot`: `SFeld`"),
    ("fieldty", "type", "R", ".", ".", ".", None, ""),
    ("bitpos", "type", "S", ".", ".", ".", r"\bat\s+\d+\b|@\s*\d+", ""),
    ("variants", "type", "R", ".", ".", ".", r"\btagged\s+type\b", "balanced, uninterpreted"),
    ("fnptr", "type", "R", ".", ".", ".", r":\s*fn\s*\(", "balanced, uninterpreted"),
    ("fncontract", "type", "S", ".", ".", ".", None, ""),
    ("entryfn", "type", "X", ".", ".", ".", r"\bentry\s+fn\b", "refused (184)"),
    ("typelist", "type", "S", ".", ".", ".", None, ""),
    ("params", "type", "S", ".", ".", "U", None, ""),
    ("fnptrparams", "type", "R", ".", ".", ".", None, ""),
    ("fnptrparam", "type", "R", ".", ".", ".", None, ""),
    ("ptrty", "type", "P", ".", ".", "U", r"\bptr\s*<", "one right word; `r + w` and `own @ x` read as a name"),
    ("space", "type", "S", ".", ".", "U", None, ""),
    ("rights", "type", "P", ".", ".", "U", None, ""),
    ("right", "type", "P", ".", ".", "U", None, ""),
    # --- section 4: expressions
    ("expr", "expr", "S", "E", "P", "U", None, "`SExpr`; `druckToks`, `parse_druck_*` for `gutKern`..`gutEmb`"),
    ("orexpr", "expr", "S", "E", "P", "U", None, ""),
    ("andexpr", "expr", "S", "E", "P", "U", None, ""),
    ("cmpexpr", "expr", "S", "E", "P", "U", None, ""),
    ("bitexpr", "expr", "S", "E", "P", "U", None, ""),
    ("addexpr", "expr", "S", "E", "P", "U", None, ""),
    ("mulexpr", "expr", "S", "E", "P", "U", None, ""),
    ("unary", "expr", "S", "E", "P", "U", None, ""),
    ("fnvalue", "expr", "S", "E", "P", ".", r"&\s*[A-Za-z_]", "`fnwert`"),
    ("primary", "expr", "P", "E", "P", "U", None, "no string primary, no `count`"),
    ("stringlit", "expr", "X", ".", ".", ".", r"=\s*\"|\(\s*\"", "no `SExpr` constructor"),
    ("countexpr", "expr", "X", ".", ".", ".", r"\bcount\s+\w+\s+in\b", ""),
    ("reasonval", "expr", "S", "E", "P", ".", r"\b[A-Z]\w*::[A-Z]\w*", "`SExpr.why`"),
    ("optionexpr", "expr", "S", "E", "P", ".", r"\b(Some|None)\b", "`ruf \"Some\"`"),
    ("paren", "expr", "S", "E", "P", "U", None, ""),
    ("call", "expr", "S", "E", "P", "U", None, ""),
    ("arglist", "expr", "S", "E", "P", "U", None, ""),
    ("arg", "expr", "P", "E", "P", "U", None, "the label of `P(a: 1)` is dropped"),
    ("builtin", "expr", "S", "E", "P", "U", r"\b(sizeof|lenof|aligned)\s*\(", ""),
    ("oldexpr", "expr", "S", "E", "P", "U", r"\bold\s*\(", "`SExpr.alt`"),
    ("place", "expr", "S", "E", "P", "U", None, ""),
    ("placesuffix", "expr", "S", "E", "P", "U", None, ""),
    ("placelist", "expr", "S", "E", "P", "U", None, ""),
    # --- section 5: predicates
    ("pred", "pred", "P", "E", "P", "U", None, "an `SExpr`; the quantified forms have no shape"),
    ("orpred", "pred", "S", "E", "P", "U", None, ""),
    ("andpred", "pred", "S", "E", "P", "U", None, ""),
    ("notpred", "pred", "P", "E", "P", "U", r"=>", "`=>` has no shape"),
    ("atompred", "pred", "P", "E", "P", "U", None, ""),
    ("heldpred", "pred", "S", "E", "P", "U", r"\bHeld\s*\(", "rides `ruf \"Held\"`"),
    ("quant", "pred", "X", ".", ".", ".", r"\b(forall|exists)\s", "refused: `reserved head forall` (12 files)"),
    ("domain", "pred", "X", ".", ".", ".", r"\b(slots\s+of|descendants\s+of|ancestors\s+of|queue\s|elems\s+of|mappings\s+of)\b", ""),
    ("member", "pred", "X", ".", ".", ".", None, ""),
    ("reach", "pred", "X", ".", ".", ".", r"\breaches\b", ""),
    ("predlist", "pred", "S", ".", ".", "U", None, ""),
    # --- section 6: function declarations
    ("fndecl", "fn", "S", ".", ".", "U", r"\bfn\s+[a-z_A-Z]", "`FnSig` + `SAnw`; elab: `impl fn` only"),
    ("asmrumpf", "fn", "R", ".", ".", ".", r"=\s*asm\s*\{", "`asmT`, body raw"),
    ("asmops", "fn", "R", ".", ".", ".", None, ""),
    ("asmop", "fn", "R", ".", ".", ".", None, ""),
    ("inductlist", "fn", "R", ".", ".", ".", r"\binduction\s+over\b", "raw string"),
    ("induct", "fn", "R", ".", ".", ".", None, ""),
    ("efflist", "fn", "S", ".", ".", "U", None, ""),
    ("eff", "fn", "S", ".", ".", "U", r"\beffects\s*\{", ""),
    # --- section 7: statements
    ("breakstmt", "stmt", "S", ".", ".", ".", r"\bbreaking\s", "`bricht`"),
    ("block", "stmt", "S", ".", ".", "U", None, "`SAnw.block`"),
    ("endblock", "stmt", "S", ".", ".", "U", None, ""),
    ("endstmt", "stmt", "S", ".", ".", "U", r"\b(return|leave|next)\b", ""),
    ("stmt", "stmt", "P", ".", ".", "U", None, "`SAnw`; no `grow`, `free`, `child`; no printer"),
    ("leavestmt", "stmt", "S", ".", ".", ".", r"\bleave\s", ""),
    ("nextstmt", "stmt", "S", ".", ".", ".", r"\bnext\s", ""),
    ("advstmt", "stmt", "S", ".", ".", ".", r"\badvances\s+\w+\s*->", ""),
    ("awaitload", "stmt", "P", ".", ".", ".", r"\bawaits\s*\{", "payload list raw"),
    ("exchstmt", "stmt", "R", ".", ".", ".", r"\bexchange\s", "transform raw"),
    ("xform", "stmt", "R", ".", ".", ".", r"\bexchange\s", ""),
    ("letstmt", "stmt", "P", ".", ".", ".", r"\blet\s", "`let` keeps no type ascription; elab: none"),
    ("assign", "stmt", "S", ".", ".", "U", None, "slot writes only in elab"),
    ("stateassign", "stmt", "S", ".", ".", ".", r"\btransition\s+[^{]*:\s*\w+\s*->", ""),
    ("exprstmt", "stmt", "S", ".", ".", "U", None, "direct calls only in elab"),
    ("ifstmt", "stmt", "S", ".", ".", ".", r"\bif\s", "`wenn`, `sonstWenn`"),
    ("matchstmt", "stmt", "S", ".", ".", ".", r"\bmatch\s", "`matchS`"),
    ("matcharm", "stmt", "S", ".", ".", ".", r"=>\s*\{", "`arm`"),
    ("narrowstmt", "stmt", "P", ".", ".", ".", r"\bnarrow\s", "target range kept as raw words"),
    ("allocstmt", "stmt", "S", ".", ".", ".", r"\balloc\s", "`allocS`"),
    ("resetstmt", "stmt", "P", ".", ".", ".", r"\breset\s", "whole-arena form only; `at i count n` refused"),
    ("growstmt", "stmt", "X", ".", ".", ".", r"^\s*grow\s", "no `grow` word, no constructor"),
    ("freestmt", "stmt", "X", ".", ".", ".", r"^\s*free\s", "no `free` word, no constructor"),
    ("childstmt", "stmt", "X", ".", ".", ".", r"^\s*child\s*\{", ""),
    ("libcall", "stmt", "R", ".", ".", ".", r"@\s*\w+\s*#", "region skipped balanced"),
    ("libregion", "stmt", "R", ".", ".", ".", None, ""),
    ("translatordecl", "stmt", "S", ".", ".", ".", r"\btranslator\s", "`uebersetzerT`"),
    ("loopform", "stmt", "R", ".", ".", ".", r"\b(traverse|retry|forever)\b", "header raw"),
    ("traverse", "stmt", "R", ".", ".", ".", r"\btraverse\s", "header raw"),
    ("retry", "stmt", "R", ".", ".", ".", r"\bretry\b", ""),
    ("forever", "stmt", "R", ".", ".", ".", r"\bforever\b", ""),
    # --- sections 9-10: tables, formats, devices
    ("table", "decl", "S", ".", ".", "U", r"\btable\s", "`tabelleT`; elab: integer fields"),
    ("treedecl", "decl", "S", ".", ".", ".", r"\btree\s*\{", ""),
    ("kante", "decl", "S", ".", ".", ".", None, ""),
    ("occdecl", "decl", "S", ".", ".", ".", r"\boccupied\s", ""),
    ("opdecl", "decl", "S", ".", ".", ".", r"\bops\s", ""),
    ("opname", "decl", "S", ".", ".", ".", None, ""),
    ("walkdecl", "decl", "S", ".", ".", ".", r"^\s*walk\s", "`SWeg`"),
    ("slotdecl", "decl", "S", ".", ".", "U", r"\bslot\s*\{", ""),
    ("slotfeld", "decl", "S", ".", ".", "U", None, ""),
    ("arena", "decl", "P", ".", ".", ".", r"\barena\s", "no `max`, no `pb`/`blw`, no `pub`"),
    ("slottype", "decl", "S", ".", ".", ".", r"\bwrapping\b", ""),
    ("invariant", "decl", "S", ".", ".", ".", r"\binvariant\s", ""),
    ("costexpr", "decl", "S", ".", ".", ".", r"\bcost\s+O\s*\(", ""),
    ("format", "decl", "P", ".", ".", ".", r"\bformat\s", "`@version` refused (04, 51)"),
    ("reason", "decl", "S", ".", ".", ".", r"^\s*(pub\s+)?reason\s", "`grundT`"),
    ("state", "decl", "S", ".", ".", ".", r"^\s*state\s", "`zustandT`"),
    ("device", "decl", "S", ".", ".", ".", r"\bdevice\s", "`geraetT`"),
    ("mirrors", "decl", "S", ".", ".", ".", r"\bmirrors\s", ""),
    ("bank", "decl", "R", ".", ".", ".", r"\bbank\s", "`bankRoh`"),
    ("regdecl", "decl", "S", ".", ".", ".", r"\breg\s", "`SReg`"),
    ("regklasse", "decl", "S", ".", ".", ".", None, ""),
    ("regphasen", "decl", "S", ".", ".", ".", None, ""),
    ("regfeld", "decl", "S", ".", ".", ".", None, ""),
    ("carrier", "decl", "S", ".", ".", ".", r"\bdepends\s", ""),
    ("transition", "decl", "S", ".", ".", ".", r"\btransition\s+\w+\s*\{", "`STrans`"),
    ("transset", "decl", "S", ".", ".", ".", None, ""),
    ("placeshift", "decl", "S", ".", ".", ".", None, ""),
    ("shiftplace", "decl", "S", ".", ".", ".", None, ""),
    # --- sections 11-14: concurrency, assumptions, profiles, checks
    ("atomicdecl", "conc", "S", ".", ".", ".", r"\batomic\s", "`atomarT`"),
    ("publishstmt", "conc", "P", ".", ".", ".", r"\bpublishes\s", "payload list raw"),
    ("nutzlast", "conc", "R", ".", ".", ".", None, ""),
    ("lockdecl", "conc", "P", ".", ".", "U", r"^\s*(pub\s+)?lock\s", "`invariant` clause after `rank` refused (118, 119, 124, 157)"),
    ("lockstmt", "conc", "S", ".", ".", "U", r"\blocks\s+\w", "`sperrt`"),
    ("rcudecl", "conc", "S", ".", ".", ".", r"^\s*rcu\s", ""),
    ("observestmt", "conc", "S", ".", ".", ".", r"\bobserves\s", ""),
    ("gruppedecl", "conc", "S", ".", ".", ".", r"^\s*group\s", ""),
    ("concurrentdecl", "conc", "S", ".", ".", ".", r"^\s*concurrent\s", "`nebenT`"),
    ("assume", "assume", "S", ".", ".", ".", r"^\s*assume\s", ""),
    ("axiom", "assume", "S", ".", ".", ".", r"^\s*axiom\s", ""),
    ("profiledecl", "assume", "S", ".", ".", ".", r"^\s*profile\s*\{", ""),
    ("requiresprofile", "assume", "S", ".", ".", ".", r"requires\s+profile", ""),
    ("profileentry", "assume", "S", ".", ".", ".", None, ""),
    ("check", "assume", "S", ".", ".", ".", r"^\s*check\s", ""),
]


def strip(src):
    out = []
    for line in src.split("\n"):
        i = line.find("--")
        out.append(line if i < 0 else line[:i])
    return "\n".join(out)


def corpus_text():
    d = os.path.join(ROOT, "beispiele")
    res = {}
    for n in sorted(os.listdir(d)):
        if n.endswith(".gab"):
            with open(os.path.join(d, n), encoding="utf-8") as f:
                res[n] = strip(f.read())
    return res


def load_census(path):
    res = {}
    for l in open(path, encoding="utf-8"):
        f = l.rstrip("\n").split(" | ")
        if len(f) < 4 or not f[0].endswith(".gab"):
            continue
        res[f[0]] = f
    return res


def run_census():
    out = os.path.join(ROOT, ".claude", "muse-arbeit", "kratz", "census.txt")
    os.makedirs(os.path.dirname(out), exist_ok=True)
    env = dict(os.environ)
    env.pop("ELAN_TOOLCHAIN", None)
    with open(out, "w") as fh:
        subprocess.run(["lake", "env", "lean", "--run", "Grammatik/Parser/Cover/Census.lean", "../beispiele"],
                       cwd=os.path.join(ROOT, "grammatik"), env=env, stdout=fh, check=True)
    return out


def main(argv):
    md = "--md" in argv
    if "--run" in argv:
        census = load_census(run_census())
    elif "--census" in argv:
        census = load_census(argv[argv.index("--census") + 1])
    else:
        print(__doc__)
        return 2
    corpus = corpus_text()
    total = len(corpus)
    parse_ok = [n for n, f in census.items() if f[2] == "parse=ok"]
    elab_ok = [n for n, f in census.items() if f[3] == "elab=ok"]
    lex_err = [n for n, f in census.items() if f[1] != "lex=ok"]
    rows = []
    for rule, grp, rd, pr, rt, el, rx, note in RULES:
        n = None
        if rx:
            r = re.compile(rx, re.M)
            n = sum(1 for t in corpus.values() if r.search(t))
        rows.append((rule, grp, rd, pr, rt, el, n, note))
    names = [r[0] for r in RULES]
    distinct = len(set(names))
    assert distinct == 189, distinct
    if md:
        print("| rule | group | reader | printer | rtrip | elab | corpus files | note |")
        print("|---|---|---|---|---|---|---|---|")
        for r in rows:
            print(f"| `{r[0]}` | {r[1]} | {r[2]} | {r[3]} | {r[4]} | {r[5]} | {'' if r[6] is None else r[6]} | {r[7]} |")
        print()
    else:
        for r in rows:
            print(f"{r[0]:16} {r[1]:6} {r[2]} {r[3]} {r[4]} {r[5]}  {'' if r[6] is None else r[6]:>4}  {r[7]}")
    cnt = {}
    for key, idx in (("reader", 2), ("printer", 3), ("rtrip", 4), ("elab", 5)):
        c = {}
        for r in rows:
            c[r[idx]] = c.get(r[idx], 0) + 1
        cnt[key] = c
    print(f"rules: {len(rows)} rows, {distinct} distinct rule names (SYNTAX.md defines 189; `int` is defined twice)")
    for k, c in cnt.items():
        print(f"{k:8}", ", ".join(f"{a}={b}" for a, b in sorted(c.items())))
    full = sum(1 for r in rows if r[2] == "S" and r[3] == "E" and r[4] == "P" and r[5] == "U")
    print(f"rules complete in all four columns: {full}")
    print(f"corpus: {total} files; lex ok {total - len(lex_err)}; whole-file parse ok {len(parse_ok)}; elab ok {len(elab_ok)}")
    bad = [n for n in census if census[n][2] != "parse=ok"]
    if bad:
        print("parse failures (first blocker of each):")
        for n in sorted(bad):
            f = census[n]
            tail = f[-1].replace("blockers=", "")
            print("  ", n, "|", tail.split(" ;; ")[0][:150])
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
