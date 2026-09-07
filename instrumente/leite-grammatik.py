#!/usr/bin/env python3
"""**Derive the grammar FROM THE PARSER** -- one production per rule function, and the
FORM POPULATION as a set a machine extracted rather than a set somebody wrote down.

`instrumente/pruefe-grammatiktafel.py` computes FORM x ZUSTAENDIGKEIT and demands that
`UNGEDECKT` be empty. **Its population is read out of a DOCUMENT** -- its own line 8:

> *"The population here is the grammar: the rules and terminals `dokumente/SYNTAX.md`
> carries, and that is the set 'beliebig' means."*

So a form `parse.rs` accepts and `SYNTAX.md` does not carry is in no population, gets no
state, and an empty `UNGEDECKT` says nothing about it. **The guard is green over a hole it
cannot see** -- `W16` in its purest form. This tool supplies the other population: the one
the reader actually implements.

WHAT A FORM IS HERE, AND WHY IT IS COUNTABLE
--------------------------------------------
`parse.rs` says of itself: *"laid rule by rule against SYNTAX.md: every EBNF rule has a
function carrying its name."* That gives the productions. A production is not yet a form a
user CHOOSES -- `fndecl` is one function and eighteen decisions. So the population is the
set of **decision points**, and there are exactly two kinds, both mechanically visible:

    WAHL      an alternative arm keyed on a word: `Art::Wort(Kw::X) =>` inside a `match`
              over a token. The user picks one of the arms.
    OPTION    a clause the user may write or omit: `friss_kw(Kw::X)` / `ist_kw(Kw::X)`
              guarding an `if`.

A `erwarte_kw(Kw::X)` is neither -- it is a DEMAND. The user does not choose it; it is the
skeleton the chosen form is made of. Counting demands would count the same form many times.
*The denominator is what a user decides, not what the parser consumes.*

**Punctuation-keyed alternatives count too** (`Art::Zeichen(Z::Y) =>` in a token match,
`friss_z`/`ist_z` guarding an optional). `[T; N]` and `{ … }` are forms a user writes, and
they carry no word at all -- which is exactly why the terminal-keyed table upstream cannot
see them: `pruefe-wortschatz.py` extracts only `"[A-Za-z_]…"` terminals from the EBNF.

WHAT IT CANNOT DERIVE, AND SAYS SO
----------------------------------
A decision the parser makes by LOOKAHEAD rather than by a word (`verbund_oder_varianten`
looks at token 2; `fnptr_params` at the `:`; `letform` at the word after the first
expression) is one form to this tool and several to a user. Those are printed under
`ZWEIDEUTIG` and are named, not counted away.

THE SPEECH TEST, AND IT RUNS IN BOTH DIRECTIONS
------------------------------------------------
A derivation that reads a source file can go silent the way `pruefe-grammatiktafel.py:253`
did -- a regex that stops matching drops a word and says nothing. So the run holds itself
against a DOCTORED copy of `parse.rs`:

    a new decision point put in     -> the population must GROW by exactly one
    an existing one taken out       -> it must SHRINK by exactly one
    an `erwarte_kw` put in          -> it must NOT move (a demand is not a form)
    a decision point inside a `//`  -> it must NOT move (prose is not code)

*A tool that only ever reads the real file cannot tell "no forms here" from "I stopped
looking".* The fourth direction is the one that would have caught the whitespace bug.

    ./instrumente/leite-grammatik.py            the derived grammar, rule by rule
    ./instrumente/leite-grammatik.py --formen   one line per form -- the population
    ./instrumente/leite-grammatik.py --zahl     only the counts
    ./instrumente/leite-grammatik.py --probe    only the speech test
"""
import pathlib
import re
import sys

W = pathlib.Path(__file__).resolve().parent.parent
PARSE = W / "crates" / "gabbro-syntax" / "src" / "parse.rs"
KW = W / "crates" / "gabbro-syntax" / "src" / "kw.rs"
LEX = W / "crates" / "gabbro-syntax" / "src" / "lex.rs"

# The tooling of the parser -- not rules of the grammar. Every one of them is a helper
# `parse.rs` itself files under "Basic tooling" or a recursion guard.
KEINE_REGEL = {
    "blick", "blick_n", "span", "ende", "vor", "absage", "versuch", "ist_z", "ist_kw",
    "friss_z", "friss_kw", "erwarte_z", "erwarte_z_mit", "erwarte_kw", "ist_ortfortsetzung",
    "wort_ist_anweisungskopf", "vorheriger_span", "tiefer", "synchronisiere",
    "synchronisiere_anweisung", "kein_verbundliteral", "vertrag", "parse",
    "abgeschaffte_form", "faengt_item_an",
}

# Rules whose choice the parser makes by LOOKAHEAD and not by a leading word. Named here
# because a tool that silently folded them would understate the population.
ZWEIDEUTIG = {
    "verbund_oder_varianten": "`{` at token 2: `:` -> record, else sum type (`P035` for `{ }`)",
    "fnptr_params": "`:` at token 2 tells the named parameter from the bare type",
    "letform": "the word AFTER the first expression: `awaits` / `exchange` / `else` / none",
    "primary": "`(` or `::` after the first name tells a call/path from a place",
    "zuweisung_oder_ruf": "`(` tells a call from an assignment; `::` forces the path form",
    "stmt": "`ist_ortfortsetzung` -- a statement head word followed by `= += -= &= |= . -> [ ::` is a PLACE",
    "typ_oder_ort": "a type word (or `[`/`{`) tells a type from a place inside `sizeof`/`lenof`",
    "bitpos": "`[` tells a bit RANGE from a single bit",
    "atompred": "backtracking: `Held(` , then `cmpexpr`-headed forms, then `( pred )`",
    "bootdecl": "`(` or `::` after the step's name tells a call from an assignment",
    "slottype": "an integer word opens the `wrapping` branch; anything else is a plain type",
}


def regelbloecke(text):
    """`fn name(...)` up to the next one at the same indent -- the rule functions."""
    kopf = re.compile(r"^    (?:pub )?fn ([a-z_0-9]+)\s*(?:<[^>]*>)?\s*\(", re.M)
    treffer = list(kopf.finditer(text))
    aus = {}
    for i, m in enumerate(treffer):
        bis = treffer[i + 1].start() if i + 1 < len(treffer) else len(text)
        aus[m.group(1)] = text[m.start():bis]
    return aus


def ohne_kommentar(rumpf):
    """Strip `//` comments -- a word named in prose is not a word the parser reads."""
    return "\n".join(re.sub(r"//.*$", "", z) for z in rumpf.splitlines())


# **List punctuation is not a form.** `if !self.friss_z(Z::Komma) { break; }` and
# `while !self.ist_z(Z::GeschweiftZu)` are how a repetition ENDS -- the user does not choose
# between writing a `,` and writing a form, he writes the next entry or stops. Counting them
# would inflate the denominator with the same three marks once per list in the language.
# *`W25`: a number proves its denominator.* Opening marks stay -- `[` opens an array type,
# `(` a call, `{` a record -- and those are choices.
STRUKTURZEICHEN = {"@Komma", "@GeschweiftZu", "@RundZu", "@EckZu", "@Semi"}


def formen_der_regel(name, rumpf):
    """The decision points of one rule -- `(art, terminal, roh)` triples."""
    code = ohne_kommentar(rumpf)
    aus = []
    # WAHL: an arm of a token match, keyed on a word or a punctuation mark. `|` chains
    # (`Kw::Fn | Kw::Spec | …`) are one arm and several forms -- the user picks one word.
    for m in re.finditer(r"Art::Wort\(\s*(?:\w+\s*@\s*\(\s*)?((?:Kw::\w+\s*\|\s*)*Kw::\w+)"
                         r"[^)]*\)?\s*\)?(?:\s*\|\s*Art::Wort\((Kw::\w+)\))*"
                         r"\s*(?:if [^=]*)?=>", code):
        for gruppe in m.groups():
            for w in re.findall(r"Kw::(\w+)", gruppe or ""):
                aus.append(("WAHL", w, name))
    # `if let Art::Wort(…) = …` -- an arm without a `=>`, in both spellings. **The bare
    # `Kw::X` form was invisible until the speech test asked for it** (2026-09-07): only the
    # `k @ ( … )` shape was handled, so a decision written the other way fell out of the
    # population without a word. *A tool that reads a source file must be asked what it
    # cannot see, or it answers about the half it can.*
    for m in re.finditer(r"if let Art::Wort\(\s*(?:\w+\s*@\s*\()?([^)]*)\)?\s*\)", code):
        for w in re.findall(r"Kw::(\w+)", m.group(1)):
            aus.append(("WAHL", w, name))
    # **A guard on a PREDICATE, not on a word.** `Art::Wort(k) if k.ist_intty()` is one arm
    # and eight forms -- `u8` and `i64` are separate things a user writes. Without this the
    # ten number-type words would fall out of the population entirely, and a population
    # that silently drops what it cannot pattern-match is the very defect this tool exists
    # to name.
    #
    # **The eight words are counted ONCE, at the rule that builds the type.** Four other
    # rules test the same predicate -- `typeexpr_innen` and `slottype` to delegate to
    # `intty`, `pfad` and `primary` to admit `u64::max`, `typ_oder_ort` to tell a type from
    # a place. There the predicate is ONE decision, not eight, and counting eight in each
    # would put the same choice in the denominator five times. *A denominator that counts a
    # thing once per mention is not a denominator.*
    if "ist_intty()" in code:
        if name == "intty":
            for w in ("U8", "U16", "U32", "U64", "I8", "I16", "I32", "I64"):
                aus.append(("WAHL", w, name))
        else:
            aus.append(("WAHL", "@@intty", name))
    if "ist_floatty()" in code:
        if name == "typeexpr_innen":
            for w in ("F32", "F64"):
                aus.append(("WAHL", w, name))
        else:
            aus.append(("WAHL", "@@floatty", name))
    for m in re.finditer(r"Art::Zeichen\(\s*((?:Z::\w+\s*\|\s*)*Z::\w+)\s*\)\s*=>", code):
        for z in re.findall(r"Z::(\w+)", m.group(1)):
            aus.append(("WAHL", "@" + z, name))
    # OPTION: a clause the user may write or omit.
    for m in re.finditer(r"(?:friss_kw|ist_kw)\(Kw::(\w+)\)", code):
        aus.append(("OPTION", m.group(1), name))
    for m in re.finditer(r"(?:friss_z|ist_z)\(Z::(\w+)\)", code):
        if "@" + m.group(1) not in STRUKTURZEICHEN:
            aus.append(("OPTION", "@" + m.group(1), name))
    return aus


def nichtterminale(rumpf, regeln):
    return sorted({m for m in re.findall(r"self\.([a-z_0-9]+)\(", ohne_kommentar(rumpf))
                   if m in regeln and m not in KEINE_REGEL})


def gefordert(rumpf):
    """`erwarte_kw` -- the SKELETON. Named per rule, never counted as a form."""
    code = ohne_kommentar(rumpf)
    return (re.findall(r"erwarte_kw\(Kw::(\w+)\)", code),
            re.findall(r"erwarte_z(?:_mit)?\(\s*Z::(\w+)", code))


def wortschatz():
    # **The whitespace is not cosmetic.** `kw.rs` writes `Ancestors => "ancestors"  ,   ctx;`
    # with spaces before the comma, and a regex demanding `",` DROPS that word without
    # saying so. `pruefe-grammatiktafel.py:253` has the tight form and loses `ancestors`
    # -- measured 2026-09-07, 220 against 221. *A guard that reads a source file reads its
    # whitespace too.*
    p = re.findall(r"=>\s*\"([^\"]+)\"\s*,\s*(res|ctx);", KW.read_text())
    return {t: k for t, k in p}, {v: t for v, t in
                                  re.findall(r"^\s*(\w+)\s*=>\s*\"([^\"]+)\"\s*,\s*(?:res|ctx);",
                                             KW.read_text(), re.M)}


def zeichentext():
    return dict(re.findall(r"Z::(\w+) => \"([^\"]+)\"", LEX.read_text()))


def zaehle(text):
    """The size of the population over an ARBITRARY parser text -- the speech test's handle."""
    alle = regelbloecke(text)
    regeln = {n: r for n, r in alle.items() if n not in KEINE_REGEL}
    gesehen = set()
    for name in regeln:
        for art, term, regel in formen_der_regel(name, regeln[name]):
            gesehen.add(f"{regel}.{term}")
    return len(gesehen)


def sprechprobe():
    """Four doctored parsers, four required reactions. Returns the number of failures."""
    echt = PARSE.read_text()
    grund = zaehle(echt)
    anker = "    fn intty(&mut self) -> Erg<IntTy> {\n"
    if anker not in echt:
        print("  ABBRUCH: the speech test's anchor is gone from `parse.rs` -- "
              "NOTHING was measured by it, neither yes nor no")
        return -1          # not a BEFUND -- an ABBRUCH, and `main` turns it into exit 2
    faelle = [
        ("a new WAHL arm grows the population by one",
         echt.replace(anker, anker + "        if let Art::Wort(Kw::Retry) = self.blick().art "
                      "{ let _zz = 1; }\n", 1),
         grund + 1),
        ("a new OPTION grows it by one",
         echt.replace(anker, anker + "        let _zz = self.friss_kw(Kw::Retry);\n", 1),
         grund + 1),
        ("a new `erwarte_kw` does NOT move it -- a demand is not a form",
         echt.replace(anker, anker + "        let _zz = self.erwarte_kw(Kw::Retry);\n", 1),
         grund),
        ("a decision point inside a COMMENT does NOT move it",
         echt.replace(anker, anker + "        // self.friss_kw(Kw::Retry)\n", 1),
         grund),
        ("an existing WAHL arm taken out SHRINKS it by one",
         echt.replace("            Art::Wort(Kw::Threads) => {\n                self.pos += 1;\n"
                      "                Ok(Domaene::Threads)\n            }\n", "", 1),
         grund - 1),
    ]
    schlecht = 0
    print(f"== Sprechprobe -- the real parser gives {grund} forms ==")
    for satz, doktoriert, soll in faelle:
        if doktoriert == echt:
            print(f"  GESCHEITERT   {satz} -- the doctoring changed NOTHING, so the case is empty")
            schlecht += 1
            continue
        ist = zaehle(doktoriert)
        ok = ist == soll
        schlecht += not ok
        print(f"  {'ok         ' if ok else 'GESCHEITERT'}   {satz} ({ist}, expected {soll})")
    return schlecht


def main():
    if not PARSE.exists() or not KW.exists() or not LEX.exists():
        print("ABBRUCH: `crates/gabbro-syntax/src/` is not there -- this tool derives the "
              "grammar FROM the parser, and without it NOTHING was measured.")
        return 2
    if "--probe" in sys.argv:
        schlecht = sprechprobe()
        if schlecht < 0:
            return 2
        if schlecht:
            print(f"== BEFUND: {schlecht} Richtung(en) der Sprechprobe halten NICHT ==")
            return 1
        print("== SPRECHPROBE: alle Richtungen halten ==")
        return 0
    text = PARSE.read_text()
    alle = regelbloecke(text)
    regeln = {n: r for n, r in alle.items() if n not in KEINE_REGEL}
    worte, variante_zu_text = wortschatz()
    ztext = zeichentext()

    def lesbar(t):
        if t.startswith("@@"):
            return t[2:]
        if t.startswith("@"):
            return ztext.get(t[1:], t)
        return variante_zu_text.get(t, t)

    formen = []
    for name in sorted(regeln):
        for art, term, regel in formen_der_regel(name, regeln[name]):
            formen.append((f"{regel}.{lesbar(term)}", art, regel, lesbar(term), term))
    # One rule may test the same word twice (a lookahead and then the eat). One form.
    gesehen, eindeutig = set(), []
    for f in formen:
        if f[0] not in gesehen:
            gesehen.add(f[0])
            eindeutig.append(f)

    if "--formen" in sys.argv:
        for kennung, art, regel, term, _ in eindeutig:
            print(f"{kennung}\t{art}\t{regel}\t{term}")
        return 0

    if "--zahl" not in sys.argv:
        print("== THE DERIVED GRAMMAR -- one production per rule function of `parse.rs` ==\n")
        for name in sorted(regeln):
            kws, zs = gefordert(regeln[name])
            nt = nichtterminale(regeln[name], alle)
            eigen = [f for f in eindeutig if f[2] == name]
            print(f"{name}")
            if kws:
                print("   demands   " + " ".join(f"`{variante_zu_text.get(k, k)}`" for k in dict.fromkeys(kws)))
            if zs:
                print("   punct     " + " ".join(f"`{ztext.get(z, z)}`" for z in dict.fromkeys(zs)))
            if nt:
                print("   calls     " + " ".join(nt))
            for _, art, _, term, _ in eigen:
                print(f"   {art:<9} `{term}`")
            if name in ZWEIDEUTIG:
                print(f"   ZWEIDEUTIG {ZWEIDEUTIG[name]}")
            print()

    wahl = [f for f in eindeutig if f[1] == "WAHL"]
    opt = [f for f in eindeutig if f[1] == "OPTION"]
    print(f"== {len(regeln)} rule functions · {len(eindeutig)} FORMS "
          f"({len(wahl)} WAHL, {len(opt)} OPTION) ==")
    print(f"   {len(ZWEIDEUTIG)} rules decide by LOOKAHEAD and not by a word -- "
          "they are one form here and several to a user")
    res = sorted(t for t, k in worte.items() if k == "res")
    print(f"   vocabulary: {len(worte)} words, {len(res)} reserved -- {' '.join(res)}")
    print()
    schlecht = sprechprobe()
    if schlecht < 0:
        return 2
    if schlecht:
        print(f"== BEFUND: {schlecht} Richtung(en) der Sprechprobe halten NICHT -- "
              "die Zahl darueber ist damit UNGEDECKT ==")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
