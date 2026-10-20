#!/usr/bin/env python3
"""Coverage matrix of the Lean parser (Track P, `dokumente/PLAN-TRANSLATION-VALIDATION.md` section 9a).

One row per EBNF rule of `dokumente/SYNTAX.md` (190 defined rules), four columns, one measured column.

  reader    S  structured and shape-faithful      P  structured, some spellings refused or a part dropped
            R  balanced words kept as raw text    X  no reader (refused / fails on the corpus)
  printer   E  a Lean printer exists (`druckToks`)  .  none
  rtrip     P  a round-trip theorem for the printable shapes
            M  measured: decided witnesses with negative twins (`Print/Proben`) and the corpus census
               (`rt=` function bodies, `ri=` items); no theorem      .  none
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
    ("int", "lex", "S", "E", "M", ".", None, "`Token.num` (value only: the spelling is lost)"),
    ("dec", "lex", "S", ".", ".", ".", None, ""),
    ("hex", "lex", "S", ".", ".", ".", None, ""),
    ("bin", "lex", "S", ".", ".", ".", None, ""),
    ("float", "lex", "S", ".", ".", ".", None, ""),
    ("string", "lex", "S", ".", ".", ".", None, "`Token.text`; the expression reader has no string primary"),
    ("char", "lex", "S", ".", ".", ".", None, ""),
    ("quote", "lex", "S", ".", ".", ".", None, ""),
    ("newline", "lex", "S", ".", ".", ".", None, ""),
    ("comment", "lex", "S", ".", ".", ".", None, "`//`, nesting `/* */` (depth counter), `///` doc trivia (`lexDoku`); `lex_ohne_doku`"),
    ("path", "lex", "S", ".", ".", ".", None, "`nimmPfad`"),
    ("pathseg", "lex", "S", ".", ".", ".", None, ""),
    ("identlist", "lex", "S", ".", ".", ".", None, ""),
    ("regbind", "lex", "S", ".", ".", ".", None, "`SRegBind`"),
    # --- section 1: program, items
    ("program", "item", "S", "E", "M", "U", None, "`parseTopTief`; `elabU` takes tables, locks, impl fns, consts, entries"),
    ("item", "item", "S", "E", "M", "U", None, "`SItemTief`, 32 constructors"),
    ("buildgate", "item", "S", "E", "M", ".", r"\bwhen\s+TESTBUILD", "`gateT`"),
    ("bootdecl", "item", "S", "E", "M", ".", r"^\s*boot\s", "`bootT`"),
    ("bootstep", "item", "S", "E", "M", ".", r"^\s*step\s", "`SBootSchritt`"),
    ("entrydecl", "item", "S", "E", "M", "U", r"^\s*(pub\s+)?entry\s+[a-z_A-Z]", "`SEingang`; `elabU` reads only the dispatch roots"),
    ("entrustdecl", "item", "S", "E", "M", ".", r"^\s*entrust\s", ""),
    ("entryextra", "item", "S", "E", "M", ".", r"\bnested\s+(never|masked|bounded)|\bper\s+cpu\b", ""),
    ("syscalldecl", "item", "S", "E", "M", ".", "^\\s*(pub\\s+)?syscall\\s", "literal, `via V` and `syscall V;` forms"),
    ("sysbind", "item", "S", "E", "M", ".", r"\bnumber\s", ""),
    ("syscontract", "item", "S", "E", "M", ".", None, ""),
    ("syspair", "item", "S", "E", "M", ".", r"\b(falsifier|unfalsifiable|kernel)\s", ""),
    ("targetdecl", "item", "S", "E", "M", ".", "^\\s*target\\s", "`goalT`; the lexer table gained `target`"),
    ("targetbind", "item", "S", "E", "M", ".", "^\\s*target\\s", "`goalT` bindings"),
    ("errmap", "item", "S", "E", "M", ".", "\\berrors\\s*\\{", "`errno [= n] => R`"),
    ("accdecl", "item", "S", "E", "M", ".", r"^\s*accumulates\s", "`accT`"),
    ("moduledecl", "item", "P", "E", "M", "U", r"^\s*(pub\s+)?module\s", "`modT`; `pub` is dropped"),
    ("usedecl", "item", "S", "E", "M", ".", r"^\s*(pub\s+)?use\s", ""),
    ("constdecl", "item", "S", "E", "M", "U", r"^\s*(pub\s+)?const\s+[A-Za-z_]", "`konstT`"),
    ("constexpr", "item", "S", "E", "P", "U", None, "an `SExpr`"),
    ("constwert", "item", "S", "E", "M", ".", None, "nested rows (`SKonstWert` (`one`, `rows`))"),
    ("arraylit", "item", "S", "E", "M", ".", "=\\s*\\[", "nested rows"),
    ("staticdecl", "item", "S", "E", "M", "U", "^\\s*(pub\\s+)?static\\s", "`aligned`, array initialiser lists; `pub` dropped"),
    ("typedecl", "item", "S", "E", "M", "U", r"^\s*(pub\s+)?(opaque\s+|linear\s+|ghost\s+|tagged\s+)*type\s", "`typT`; elab reads range aliases and `tagged` types (the raw body is lexed again)"),
    ("markorder", "item", "S", "E", "M", ".", r"\border\s*\{", ""),
    # --- section 2: types
    ("typeexpr", "type", "P", "E", "M", "U", None, "`STyp`; struct, variants, fn pointer ride raw"),
    ("stringty", "type", "S", "E", "M", ".", "\\bstring\\s+max\\b", "`STyp.str`"),
    ("stringkopf", "type", "S", "E", "M", ".", "\\bstring\\s+max\\b", "`STyp.str`"),
    ("indexty", "type", "S", "E", "M", "U", r"\bindex\s+into\b", "`STyp.index`"),
    ("nevertype", "type", "S", "E", "M", ".", r"->\s*never\b", ""),
    ("intty", "type", "S", "E", "M", "U", r"\b[ui](8|16|32|64)\b", ""),
    ("uint", "type", "S", "E", "M", "U", r"\bu([1-9]|[1-5][0-9]|6[0-4])\b", ""),
    ("int", "type", "S", "E", "M", "U", r"\bi([1-9]|[1-5][0-9]|6[0-4])\b", "second definition of `int` (signed sugar)"),
    ("nonzero", "type", "S", "E", "M", ".", None, ""),
    ("floatty", "type", "P", "E", "M", ".", r"\bf(32|64)\b", "read as an atom plus `in`; no float elaboration"),
    ("frange", "type", "P", "E", "M", ".", r"\bf(32|64)\s+in\b", ""),
    ("fexpr", "type", "P", "E", "M", ".", r"\brounded\b", ""),
    ("boolty", "type", "S", "E", "M", "U", r"\bbool\b", ""),
    ("range", "type", "S", "E", "M", "U", r"\bin\s+[^;]*\.\.", ""),
    ("array", "type", "S", "E", "M", ".", r"\[\s*[A-Za-z_0-9]+\s*;", "`STyp.reihe`"),
    ("structty", "type", "R", "E", "M", ".", r"\btype\s+\w+\s*=\s*\{", "balanced, uninterpreted"),
    ("field", "type", "R", "E", "M", ".", None, "inside a struct type: raw; inside `format`/`slot`: `SFeld`"),
    ("fieldty", "type", "R", "E", "M", ".", None, ""),
    ("bitpos", "type", "S", "E", "M", ".", r"\bat\s+\d+\b|@\s*\d+", ""),
    ("variants", "type", "R", "E", "M", "U", r"\btagged\s+type\b", "balanced, uninterpreted"),
    ("fnptr", "type", "R", "E", "M", ".", r":\s*fn\s*\(", "balanced, uninterpreted"),
    ("fncontract", "type", "S", "E", "M", ".", None, ""),
    ("entryfn", "type", "P", "E", "M", ".", "\\bentry\\s+fn\\b", "`STyp.entry`: parameter words raw"),
    ("typelist", "type", "S", "E", "M", ".", None, ""),
    ("params", "type", "S", "E", "M", "U", None, ""),
    ("fnptrparams", "type", "R", "E", "M", ".", None, ""),
    ("fnptrparam", "type", "R", "E", "M", ".", None, ""),
    ("ptrty", "type", "S", "E", "M", "U", "\\bptr\\s*<", "rights kept as one string (`rw+own`, `own@h`)"),
    ("space", "type", "S", "E", "M", "U", None, ""),
    ("rights", "type", "S", "E", "M", "U", None, "`parseRechte`"),
    ("right", "type", "S", "E", "M", "U", None, "`parseRechte`"),
    # --- section 4: expressions
    ("expr", "expr", "S", "E", "P", "U", None, "`SExpr`; `druckToks`, `parse_druck_*` for `gutKern`..`gutEmb`"),
    ("orexpr", "expr", "S", "E", "P", "U", None, ""),
    ("andexpr", "expr", "S", "E", "P", "U", None, ""),
    ("cmpexpr", "expr", "S", "E", "P", "U", None, ""),
    ("bitexpr", "expr", "S", "E", "P", "U", None, ""),
    ("addexpr", "expr", "S", "E", "P", "U", None, ""),
    ("mulexpr", "expr", "S", "E", "P", "U", None, ""),
    ("unary", "expr", "S", "E", "P", "U", None, ""),
    ("fnvalue", "expr", "S", "E", "P", ".", r"&\s*[A-Za-z_]", "`fnref`"),
    ("primary", "expr", "S", "E", "P", "U", None, "string literal and `count` read; both `ext`"),
    ("stringlit", "expr", "S", "E", "M", ".", r'=\s*"|\(\s*"', "`ext .text`"),
    ("countexpr", "expr", "S", "E", "M", ".", "\\bcount\\s+\\w+\\s+in\\b", "`ext .count`"),
    ("reasonval", "expr", "S", "E", "P", "U", r"\b[A-Z]\w*::[A-Z]\w*", "`SExpr.why`"),
    ("optionexpr", "expr", "S", "E", "P", ".", r"\b(Some|None)\b", "`call` named Some"),
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
    ("pred", "pred", "S", "E", "P", "U", None, "`parsePred`; forms outside the core ride `ext`"),
    ("orpred", "pred", "S", "E", "P", "U", None, ""),
    ("andpred", "pred", "S", "E", "P", "U", None, ""),
    ("notpred", "pred", "S", "E", "P", "U", "=>", "`=>` is `ext .imp`"),
    ("atompred", "pred", "S", "E", "P", "U", None, ""),
    ("heldpred", "pred", "S", "E", "P", "U", r"\bHeld\s*\(", "rides `ruf \"Held\"`"),
    ("quant", "pred", "S", "E", "M", ".", "\\b(forall|exists)\\s", "`SExpr.ext .all/.any` (layout at `XKind`); no printer: `ext` has no spelling in `druckToks`"),
    ("domain", "pred", "S", "E", "M", ".", "\\b(slots\\s+of|descendants\\s+of|ancestors\\s+of|queue\\s|elems\\s+of|mappings\\s+of)\\b", "the eight domains, as names and place operands of `ext`"),
    ("member", "pred", "S", "E", "M", ".", None, "`ext .mem`"),
    ("reach", "pred", "S", "E", "M", ".", "\\breaches\\b", "`ext .reach`"),
    ("predlist", "pred", "S", "E", "M", "U", None, ""),
    # --- section 6: function declarations
    ("fndecl", "fn", "S", "E", "M", "U", r"\bfn\s+[a-z_A-Z]", "`FnSig` + `SAnw`; elab: `impl fn` (with an `or R` channel) and `extern fn`"),
    ("asmrumpf", "fn", "R", "E", "M", ".", r"=\s*asm\s*\{", "`asmT`, body raw"),
    ("asmops", "fn", "R", "E", "M", ".", None, ""),
    ("asmop", "fn", "R", "E", "M", ".", None, ""),
    ("inductlist", "fn", "R", "E", "M", ".", r"\binduction\s+over\b", "raw string"),
    ("induct", "fn", "R", "E", "M", ".", None, ""),
    ("efflist", "fn", "S", "E", "M", "U", None, ""),
    ("eff", "fn", "S", "E", "M", "U", r"\beffects\s*\{", ""),
    # --- section 7: statements
    ("breakstmt", "stmt", "S", "E", "M", ".", r"\bbreaking\s", "`waive`"),
    ("block", "stmt", "S", "E", "P", "U", None, "`SAnw.block`"),
    ("endblock", "stmt", "S", "E", "P", "U", None, ""),
    ("endstmt", "stmt", "S", "E", "P", "U", r"\b(return|leave|next)\b", ""),
    ("stmt", "stmt", "S", "E", "M", "U", None, "`SAnw`; no printer; `start { }` is read but SYNTAX.md has no rule for it"),
    ("leavestmt", "stmt", "S", "E", "P", "U", r"\bleave\s", ""),
    ("nextstmt", "stmt", "S", "E", "P", "U", r"\bnext\s", ""),
    ("advstmt", "stmt", "S", "E", "M", ".", r"\badvances\s+\w+\s*->", ""),
    ("awaitload", "stmt", "P", "E", "M", ".", r"\bawaits\s*\{", "payload list raw"),
    ("exchstmt", "stmt", "R", "E", "M", ".", r"\bexchange\s", "transform raw"),
    ("xform", "stmt", "R", "E", "M", ".", r"\bexchange\s", ""),
    ("letstmt", "stmt", "S", "E", "P", "U", "\\blet\\s", "the type ascription is read (`bind`, `bindElse`, `bindLib`, `alloc`)"),
    ("assign", "stmt", "S", "E", "M", "U", None, "slot writes only in elab"),
    ("stateassign", "stmt", "S", "E", "M", ".", r"\btransition\s+[^{]*:\s*\w+\s*->", ""),
    ("exprstmt", "stmt", "S", "E", "M", "U", None, "direct calls only in elab"),
    ("ifstmt", "stmt", "S", "E", "M", "U", r"\bif\s", "`cond`, `elsif`"),
    ("matchstmt", "stmt", "S", "E", "M", "U", r"\bmatch\s", "`cases`"),
    ("matcharm", "stmt", "S", "E", "M", "U", r"=>\s*\{", "`arm`"),
    ("narrowstmt", "stmt", "P", "E", "M", "U", r"\bnarrow\s", "target range kept as raw words"),
    ("allocstmt", "stmt", "S", "E", "M", "U", r"\balloc\s", "`alloc`"),
    ("resetstmt", "stmt", "S", "E", "M", "U", "\\breset\\s", "with `at i count n`"),
    ("growstmt", "stmt", "S", "E", "M", ".", "^\\s*grow\\s", "`SAnw.grow`"),
    ("freestmt", "stmt", "S", "E", "M", ".", "^\\s*free\\s", "`SAnw.free`"),
    ("childstmt", "stmt", "S", "E", "M", ".", "^\\s*child\\s*\\{", "`SAnw.child`"),
    ("startstmt", "stmt", "S", "E", "M", "U", "^\\s*start\\s*\\{", "`SAnw.start`; written into SYNTAX.md 2026-10-17"),
    ("libcall", "stmt", "R", "E", "M", ".", r"@\s*\w+\s*#", "region skipped balanced"),
    ("libregion", "stmt", "R", "E", "M", ".", None, ""),
    ("translatordecl", "stmt", "S", "E", "M", ".", r"\btranslator\s", "`transT`"),
    ("loopform", "stmt", "P", "E", "M", "U", r"\b(traverse|retry|forever)\b", "header raw"),
    ("traverse", "stmt", "S", "E", "M", "U", r"\btraverse\s", "header raw"),
    ("retry", "stmt", "R", "E", "M", "U", r"\bretry\b", "the raw header is lexed again by the elaboration"),
    ("forever", "stmt", "R", "E", "M", "U", r"\bforever\b", "the raw header is lexed again by the elaboration"),
    # --- sections 9-10: tables, formats, devices
    ("table", "decl", "S", "E", "M", "U", r"\btable\s", "`tableT`; elab: integer fields"),
    ("treedecl", "decl", "S", "E", "M", ".", r"\btree\s*\{", ""),
    ("kante", "decl", "S", "E", "M", ".", None, ""),
    ("occdecl", "decl", "S", "E", "M", ".", r"\boccupied\s", ""),
    ("opdecl", "decl", "S", "E", "M", ".", r"\bops\s", ""),
    ("opname", "decl", "S", "E", "M", ".", None, ""),
    ("walkdecl", "decl", "S", "E", "M", ".", r"^\s*walk\s", "`SWeg`"),
    ("slotdecl", "decl", "S", "E", "M", "U", r"\bslot\s*\{", ""),
    ("slotfeld", "decl", "S", "E", "M", "U", None, ""),
    ("arena", "decl", "P", "E", "M", "U", "\\barena\\s", "`max`, `pb`/`blw` read; `pub` dropped"),
    ("slottype", "decl", "S", "E", "M", ".", r"\bwrapping\b", ""),
    ("invariant", "decl", "S", "E", "M", ".", r"\binvariant\s", ""),
    ("costexpr", "decl", "S", "E", "M", ".", r"\bcost\s+O\s*\(", ""),
    ("format", "decl", "S", "E", "M", ".", "\\bformat\\s", "`@version` read"),
    ("reason", "decl", "S", "E", "M", "U", r"^\s*(pub\s+)?reason\s", "`whyT`"),
    ("state", "decl", "S", "E", "M", ".", r"^\s*state\s", "`stateT`"),
    ("device", "decl", "S", "E", "M", ".", r"\bdevice\s", "`devT`"),
    ("mirrors", "decl", "S", "E", "M", ".", r"\bmirrors\s", ""),
    ("bank", "decl", "R", "E", "M", ".", r"\bbank\s", "`bank`"),
    ("regdecl", "decl", "S", "E", "M", ".", r"\breg\s", "`SReg`"),
    ("regklasse", "decl", "S", "E", "M", ".", None, ""),
    ("regphasen", "decl", "S", "E", "M", ".", None, ""),
    ("regfeld", "decl", "S", "E", "M", ".", None, ""),
    ("carrier", "decl", "S", "E", "M", ".", r"\bdepends\s", ""),
    ("transition", "decl", "S", "E", "M", ".", r"\btransition\s+\w+\s*\{", "`STrans`"),
    ("transset", "decl", "S", "E", "M", ".", None, ""),
    ("placeshift", "decl", "S", "E", "M", ".", None, ""),
    ("shiftplace", "decl", "S", "E", "M", ".", None, ""),
    # --- sections 11-14: concurrency, assumptions, profiles, checks
    ("atomicdecl", "conc", "S", "E", "M", "U", r"\batomic\s", "`atomT`"),
    ("publishstmt", "conc", "P", "E", "M", "U", r"\bpublishes\s", "payload list raw"),
    ("nutzlast", "conc", "R", "E", "M", ".", None, ""),
    ("lockdecl", "conc", "S", "E", "M", "U", "^\\s*(pub\\s+)?lock\\s", "`invariant` read (`lockT` 7th field)"),
    ("lockstmt", "conc", "S", "E", "M", "U", r"\blocks\s+\w", "`locks`"),
    ("rcudecl", "conc", "S", "E", "M", ".", r"^\s*rcu\s", ""),
    ("observestmt", "conc", "S", "E", "M", ".", r"\bobserves\s", ""),
    ("gruppedecl", "conc", "S", "E", "M", ".", r"^\s*group\s", ""),
    ("concurrentdecl", "conc", "S", "E", "M", "U", r"^\s*concurrent\s", "`concT`"),
    ("assume", "assume", "S", "E", "M", "U", r"^\s*assume\s", ""),
    ("axiom", "assume", "S", "E", "M", ".", r"^\s*axiom\s", ""),
    ("profiledecl", "assume", "S", "E", "M", ".", r"^\s*profile\s*\{", ""),
    ("requiresprofile", "assume", "S", "E", "M", ".", r"requires\s+profile", ""),
    ("profileentry", "assume", "S", "E", "M", ".", None, ""),
    ("check", "assume", "S", "E", "M", ".", r"^\s*check\s", ""),
]


def strip(src):
    """The code of a source text: strings kept, `//` and nesting `/* */` comments dropped
    (the lexer's rule, `Parser/Lex/Lexer.lean`)."""
    out = []
    i, n = 0, len(src)
    while i < n:
        if src[i] == '"':
            j = i + 1
            while j < n and src[j] not in '"\n':
                j += 1
            out.append(src[i:j + 1])
            i = j + 1
        elif src.startswith("//", i):
            while i < n and src[i] != "\n":
                i += 1
        elif src.startswith("/*", i):
            tiefe, i = 1, i + 2
            while i < n and tiefe:
                if src.startswith("/*", i):
                    tiefe, i = tiefe + 1, i + 2
                elif src.startswith("*/", i):
                    tiefe, i = tiefe - 1, i + 2
                else:
                    i += 1
        else:
            out.append(src[i])
            i += 1
    return "".join(out)


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
    lower_ok = [n for n, f in census.items() if len(f) > 4 and f[4] == "lower=ok"]
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
    assert distinct == 190, distinct
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
    print(f"rules: {len(rows)} rows, {distinct} distinct rule names (SYNTAX.md defines 190; `int` is defined twice)")
    for k, c in cnt.items():
        print(f"{k:8}", ", ".join(f"{a}={b}" for a, b in sorted(c.items())))
    full = sum(1 for r in rows if r[2] == "S" and r[3] == "E" and r[4] in "PM" and r[5] == "U")
    print(f"rules with all four columns present (round trip: proved on `gut` shapes (P) or measured (M)): {full}")
    print(f"corpus: {total} files; lex ok {total - len(lex_err)}; whole-file parse ok {len(parse_ok)}; elab ok {len(elab_ok)}; lower ok {len(lower_ok)}")
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
