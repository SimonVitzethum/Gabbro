#!/usr/bin/env python3
"""**Die C-Formen, die Gabbro wirklich emittiert -- gezaehlt, nicht behauptet.**

    ./instrumente/zaehle-c-formen.py [--stellen] [--uebersetzer] [--tafel]

WOZU
----
`dokumente/BEWEIS.md`, *„Item 2 -- WHICH C"*, traegt seit dem 2026-08-14 den Satz, an dem
Gabbros ganzer Verifikationsweg haengt:

> **seL4 formalisiert C. Gabbro emittiert so wenig C, dass seine Semantik eine ENDLICHE
> TABELLE ist.** Was nie emittiert wird, braucht keine Semantik.

Darunter stehen eine **Erlaubtliste** von Formen und eine **Nie-Liste**, und darunter stand
zwei Wochen lang ein leeres Kaestchen: *„The list is to be counted and ratcheted, like the
axiom layer."*

**Das ist keine Buchfuehrung, sondern die Entscheidung selbst.** Haelt die Tabelle, braucht
Gabbro AutoCorres nie und die C-Semantik passt in eine Datei. Waechst sie mit jedem neuen
Programm, ist die Formalisierung von C ein Teilprojekt -- *und dieselbe Bewegung wie eine
wachsende Axiomschicht.*

DIE DREI MENGEN
---------------
Eine Erlaubtliste hat drei Verhaeltnisse zur Wirklichkeit, und **nur eines davon ist ein
Befund**:

  A  **erlaubt und benutzt**       -- die eigentliche Tabelle. *Was zu formalisieren waere.*
  B  **erlaubt und NIE benutzt**   -- tote Eintraege. Die Tabelle kann sie verlieren, und
                                     jeder verlorene Eintrag ist Beweisarbeit, die entfaellt.
  C  **benutzt und NICHT erlaubt** -- die Befunde. Zwei Unterfaelle, und sie wiegen
                                     verschieden schwer:
                                       N -- die Form steht auf der **Nie-Liste**. Ein
                                            Widerspruch: das Dokument sagt, es gebe sie nicht.
                                       U -- die Form steht auf **keiner der beiden Listen**.
                                            Eine Luecke: niemand hat sie je entschieden.

WARUM NICHT `grep`
------------------
**Ein `grep`-Zaehler ueber erzeugtes C zaehlt Zeichenketten und Kommentare mit.** Das
Erzeugnis dieses Ordners besteht zu einem erheblichen Teil aus erklaerenden Blockkommentaren
-- gemessen 2026-08-31: von 8001 Zeilen C sind 1631 Kommentar --, und in denen stehen
deutsche und englische Saetze ueber `?:`, ueber `void*` und ueber Zeigerarithmetik. *Wer
darueber `grep -c` laufen laesst, misst die Erklaerung und nicht den Gegenstand.*

Darum steht hier ein **Lexer**: Zeilenfortsetzung, Kommentarentfernung, Zeichen- und
Textliterale als ein Token. Erst danach wird gezaehlt. **Der Unterschied ist gemessen und
steht unter `--tafel`** -- er ist nicht klein.

DREI STUFEN DER ENTSCHEIDBARKEIT, UND SIE STEHEN NEBENEINANDER GEDRUCKT
-----------------------------------------------------------------------
**Nicht jede Form der beiden Listen ist lexikalisch entscheidbar, und ein Werkzeug, das das
verschweigt, verkauft eine Vermutung als Zahl.**

  `lex`     aus dem Tokenstrom allein, exakt. `?:`, `...`, `void *`, jedes Schluesselwort,
            jede Praeprozessordirektive.
  `struk`   aus Klammer- und Blockschachtelung, **mit benannter Naeherung**: Kommaoperator,
            Zuweisung im Ausdruck, Bitfeld, Sprungmarke, Zeigerarithmetik.
  `cc`      vom **zweiten Instrument** (`--uebersetzer`): implizite Umwandlung, `const`-
            Verwurf, VLA. Das sind semantische Fragen, und ein selbstgebauter Halbparser,
            der sie beantwortet, ist eine zweite Fehlerquelle ueber demselben Gegenstand.
            *Die `checkfat.py`-Lehre: der Nachrechner ist ein zweites Programm mit eigenem
            Muster.*

RICHTUNG DES FEHLERS (W10)
--------------------------
**Menge C ist eine UNTERE Schranke.** Was hier nicht gefunden wird, kann trotzdem im
Erzeugnis stehen:

* Eine Form, die im **Katalog gar nicht vorkommt**, faellt nicht durch -- sie faellt in
  `UNBEKANNT` und wird mit Namen gedruckt. *Der Zaehler ist ueber dem Tokenstrom TOTAL:*
  jedes Schluesselwort und jedes Satzzeichen muss einem Eintrag zugeordnet sein, sonst
  meldet der Lauf es. **Das ist der Unterschied zwischen einer Zaehlung und einer Abhakliste
  -- eine Abhakliste kann nur finden, was jemand vorher vermutet hat.**
* Die drei `cc`-Klassen bleiben ohne `--uebersetzer` **ungemessen** und heissen dann so.
* Was das Werkzeug ueberhaupt nicht sehen kann, steht in `UNGEMESSEN` unten -- mit Namen.

**Menge B ist dagegen eine OBERE Schranke:** ein Eintrag gilt als tot, wenn diese 102
Einheiten ihn nicht ausloesen. Ein 103. Programm kann ihn wiederbeleben. *Darum ist der
Nenner gedruckt, und darum ist die Zahl eine Ratsche und kein Beweis.*

DIE RATSCHE
-----------
Zwei Marken, und beide duerfen **fallen**; steigt eine, muss der Grund hier stehen -- genau
die Bewegung, die `BEWEIS.md` mit einer wachsenden Axiomschicht vergleicht.

  `MARKE_TABELLE`  die Zahl der VERSCHIEDENEN benutzten Formen (A + C). *Das ist die
                   Tabelle, die eines Tages eine Semantik bekommen muss.*
  `MARKE_UNERLAUBT` die Zahl der verschiedenen Formen in C. *Eine Tabelle, die schrumpft,
                   waehrend die Verstoesse wachsen, kaeme sonst gruen durch.*

**Der Ruecklaufwert ist 1, sobald eine Marke steigt** -- und 2, wenn nichts gemessen wurde.
"""
import importlib.util
import os
import pathlib
import re
import subprocess
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import abschnitt  # noqa: E402

W = pathlib.Path(__file__).resolve().parent.parent

# **DIE MARKEN, gemessen 2026-08-31** ueber den Korpus bei `e6a3c63`: 102 emittierende
# Uebersetzungseinheiten, 8001 Zeilen C. Sie sind die MESSUNG und kein Ziel -- eine Ratsche,
# die unter ihrem Gegenstand beginnt, ist am Tag ihrer Niederschrift rot und sagt niemandem
# etwas. Was sie kauft, ist der ZWEITE Tag.
#
# **Beide Marken sind mit `--uebersetzer` genommen**, also mit der vollsten Messung, die
# dieses Werkzeug kann. Ein Lauf ohne die Schalter misst hoechstens dasselbe und nie mehr;
# die Marke ist damit in beide Richtungen sicher.
#
#   64  Formen im Erzeugnis  =  35 erlaubt+benutzt  +  29 benutzt+nicht erlaubt
#   29  davon nicht erlaubt  =   7 auf der Nie-Liste + 18 ungenannt + 4 weit gedeckt
MARKE_TABELLE = 64
MARKE_UNERLAUBT = 29

# **The same sieve `zaehle-absagen.korpuslauf` uses, and for its reason** (W7). `rglob` from
# the repo root walks into every agent worktree; the exclusion is RELATIVE to the root,
# because the root of an agent IS `.../.claude/worktrees/agent-X` and an absolute match takes
# the corpus to zero there.
AUS_BAU = ("target", ".claude", ".lake")
# One deadline per file. An expiry is an ABORT, never an empty result (W17).
FRIST = 60

# The second instrument. `-Werror` is deliberately ABSENT: these switches are meant to fire,
# and their firing IS the measurement. `-Wconversion` alone would make every acceptance run
# of `pruefe-emission.sh` red, which is why it does not stand there.
CC_MESSSCHALTER = [
    "-std=c11", "-Wconversion", "-Wsign-conversion", "-Wcast-qual", "-Wpointer-arith",
    "-Wvla", "-Wbad-function-cast", "-Wdouble-promotion", "-Wfloat-equal",
]
CC_UMGEBUNG = dict(os.environ, LC_ALL="C", LANG="C", LANGUAGE="C")


def _lade(name):
    """Load a sibling tool as a module -- the shared form (its file name has a dash in it)."""
    spec = importlib.util.spec_from_file_location(name.replace("-", "_").replace(".py", ""),
                                                  W / "instrumente" / name)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


# ----------------------------------------------------------------------------------------
# DER LEXER
# ----------------------------------------------------------------------------------------

# The C punctuators, longest first -- a shorter one first would cut `<<=` into `<` `<=`.
SATZZEICHEN = sorted(
    ["...", "<<=", ">>=", "->", "++", "--", "<<", ">>", "<=", ">=", "==", "!=", "&&", "||",
     "+=", "-=", "*=", "/=", "%=", "&=", "^=", "|=", "##", "<:", ":>", "<%", "%>",
     "{", "}", "[", "]", "(", ")", ";", ":", "?", ".", ",", "+", "-", "*", "/", "%",
     "&", "|", "^", "~", "!", "=", "<", ">", "#"],
    key=len, reverse=True)

_ZAHL = re.compile(r"\.?\d(?:[eEpP][+-]|[0-9a-zA-Z_.])*")
_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")


def entkommentiere(text):
    """Translation phases 2 and 3: line splicing and comment removal.

    Returns `(code, kommentarzeilen)`. **Comments become ONE space, not nothing** -- glueing
    `a/**/b` into `ab` would invent an identifier that is not in the file.

    *A string literal is not a comment and a comment is not a string literal*, and the only
    way to know which is which is to walk the text once, in order. That is why this is a
    loop and not three regular expressions.
    """
    text = text.replace("\\\n", "")
    aus, i, n, kz = [], 0, len(text), 0
    while i < n:
        c = text[i]
        if c == "/" and i + 1 < n and text[i + 1] == "*":
            j = text.find("*/", i + 2)
            j = n if j < 0 else j + 2
            kz += text.count("\n", i, j) + 1
            # Keep the newlines: the line number of everything after it must survive.
            aus.append(" " + "\n" * text.count("\n", i, j))
            i = j
        elif c == "/" and i + 1 < n and text[i + 1] == "/":
            j = text.find("\n", i)
            kz += 1
            aus.append(" ")
            i = n if j < 0 else j
        elif c in "\"'":
            # A literal is ONE token from here on. Its content never reaches the counter --
            # which is the whole point of not using `grep`.
            j = i + 1
            while j < n and text[j] != c:
                j += 2 if text[j] == "\\" else 1
            aus.append(("@TEXT@" if c == '"' else "@ZEICHEN@") + " ")
            i = min(j + 1, n)
        else:
            aus.append(c)
            i += 1
    return "".join(aus), kz


def lies_tokens(text):
    """`(art, text, zeile)` je Token. `art` in {`pp`, `name`, `zahl`, `text`, `op`}.

    `pp` is a preprocessing directive INTRODUCER (`#include`, `#define`, ...) -- the `#` and
    its word together, because `# define` with a space is the same directive and two tokens
    would make it a different one.

    **The body of `#include` is skipped, every other body is lexed.** A header name
    (`<stdint.h>`) is not a token sequence -- lexing it would count a `.` and a `/` that
    exist nowhere in the language. Every other directive body IS code: a `#define` body
    reaches the translation unit at each use site, and a form that hides in one is emitted.

    **A directive ENDS at the newline, and that end is a token** (`ppende`). Without it the
    line after `#define ZZ 4u` does not begin a new statement, and the counter reads
    `static const char *zzs` as a continuation of the macro body -- *pointer declarator
    counted as dereference*. The speech test found it at the first run after the rebuild;
    it is invisible in the corpus, where a `;` usually stands in between.
    """
    code, _ = entkommentiere(text)
    aus = []
    zeile = 1
    i, n = 0, len(code)
    zeilenanfang = True
    in_direktive = False
    while i < n:
        c = code[i]
        if c == "\n":
            if in_direktive:
                aus.append(("ppende", "", zeile))
                in_direktive = False
            zeile += 1
            zeilenanfang = True
            i += 1
            continue
        if c in " \t\r\f\v":
            i += 1
            continue
        if c == "#" and zeilenanfang:
            j = i + 1
            while j < n and code[j] in " \t":
                j += 1
            m = _NAME.match(code, j)
            wort = m.group(0) if m else ""
            aus.append(("pp", "#" + wort, zeile))
            i = (m.end() if m else i + 1)
            zeilenanfang = False
            in_direktive = True
            if wort == "include":
                j = code.find("\n", i)
                i = n if j < 0 else j
            continue
        zeilenanfang = False
        if code.startswith("@TEXT@", i):
            aus.append(("text", "@TEXT@", zeile))
            i += 6
            continue
        if code.startswith("@ZEICHEN@", i):
            aus.append(("text", "@ZEICHEN@", zeile))
            i += 9
            continue
        m = _NAME.match(code, i)
        if m:
            aus.append(("name", m.group(0), zeile))
            i = m.end()
            continue
        m = _ZAHL.match(code, i)
        if m:
            aus.append(("zahl", m.group(0), zeile))
            i = m.end()
            continue
        for s in SATZZEICHEN:
            if code.startswith(s, i):
                aus.append(("op", s, zeile))
                i += len(s)
                break
        else:
            aus.append(("op", c, zeile))
            i += 1
    return aus


# ----------------------------------------------------------------------------------------
# DER KATALOG
# ----------------------------------------------------------------------------------------
#
# **Every entry carries WHERE IT COMES FROM, and that is not decoration.** `stand` is `E`
# (`BEWEIS.md` allow list), `N` (its never list) or `U` (on neither -- a gap, not a
# contradiction). `quelle` is the phrase it was read out of, verbatim enough to be found
# again. A catalogue whose entries cannot be traced back to the document is a second
# document.
#
# **`weit` is the GENEROUS reading, and it exists so the report cannot inflate itself.**
# `->` is not in the list; „field access" plainly means it. `+=` is not in the expression
# row; „assignment" in the statement row plainly means it. Whoever counts those as findings
# gets a big number and no result. So each `U` entry says which allow-list entry a generous
# reading would put it under -- or `None`, and then no reading covers it and it is a finding
# under BOTH readings. *Both totals are printed. W25: a number vouches for its denominator.*
#
# Fields: name -> (gruppe, stand, stufe, quelle, weit)
E, N, U = "E", "N", "U"
KATALOG = {
    # --- Praeprozessor ---------------------------------------------------------------
    "#if": ("Praeprozessor", E, "lex", "preprocessor ... `#if` out of `when`", None),
    "#endif": ("Praeprozessor", E, "lex", "gehoert zu `#if`", None),
    "#else": ("Praeprozessor", E, "lex", "gehoert zu `#if`", None),
    "#elif": ("Praeprozessor", E, "lex", "gehoert zu `#if`", None),
    "#include": ("Praeprozessor", N, "lex", "NIE: preprocessor other than `#if` out of `when`", None),
    "#define": ("Praeprozessor", N, "lex", "NIE: preprocessor other than `#if` out of `when`",
                "Declarations: enum-free constants"),
    "#undef": ("Praeprozessor", N, "lex", "NIE: preprocessor other than `#if`", None),
    "#pragma": ("Praeprozessor", N, "lex", "NIE: preprocessor other than `#if`", None),
    "#error": ("Praeprozessor", N, "lex", "NIE: preprocessor other than `#if`", None),
    "#ifdef": ("Praeprozessor", N, "lex", "NIE: preprocessor other than `#if`", "`#if`"),
    "#ifndef": ("Praeprozessor", N, "lex", "NIE: preprocessor other than `#if`", "`#if`"),
    "#line": ("Praeprozessor", N, "lex", "NIE: preprocessor other than `#if`", None),
    # --- Deklarationen ---------------------------------------------------------------
    "static": ("Deklaration", E, "lex", "Declarations: static", None),
    "extern": ("Deklaration", E, "lex", "Declarations: extern", None),
    "struct-definition": ("Deklaration", E, "struk", "Declarations: struct/union definition", None),
    "union-definition": ("Deklaration", E, "struk", "Declarations: struct/union definition", None),
    "typedef": ("Deklaration", N, "lex", "NIE (Lesart): `typedef-free` struct/union definition", None),
    "enum": ("Deklaration", N, "lex", "NIE (Lesart): `enum-free` constants", None),
    "konstante-#define": ("Deklaration", E, "struk", "Declarations: enum-free constants", None),
    # --- Typen ------------------------------------------------------------------------
    "uintN_t": ("Typ", E, "lex", "Types: uint{8,16,32,64}_t", None),
    "intN_t": ("Typ", E, "lex", "Types: int{8,16,32,64}_t", None),
    "_Bool": ("Typ", E, "lex", "Types: _Bool", None),
    "bool": ("Typ", U, "lex", "auf keiner Liste -- `<stdbool.h>`, nicht `_Bool`", "Types: _Bool"),
    "true/false": ("Typ", U, "lex", "auf keiner Liste -- Makros aus `<stdbool.h>`",
                   "Expressions: literal"),
    "zeigertyp": ("Typ", E, "struk", "Types: T*", None),
    "feldtyp": ("Typ", E, "struk", "Types: T[N]", None),
    "struct": ("Typ", E, "lex", "Types: struct", None),
    "union": ("Typ", E, "lex", "Types: union", None),
    "void": ("Typ", U, "lex", "auf keiner Liste -- die Typenzeile nennt `void` NICHT", None),
    "void*": ("Typ", N, "lex", "NIE: `void*`", None),
    "char": ("Typ", U, "lex", "auf keiner Liste", None),
    "short": ("Typ", U, "lex", "auf keiner Liste", None),
    "int": ("Typ", U, "lex", "auf keiner Liste", None),
    "long": ("Typ", U, "lex", "auf keiner Liste", None),
    "signed": ("Typ", U, "lex", "auf keiner Liste", None),
    "unsigned": ("Typ", U, "lex", "auf keiner Liste", None),
    "float": ("Typ", U, "lex", "auf keiner Liste -- die Typenzeile kennt kein Gleitkomma", None),
    "double": ("Typ", U, "lex", "auf keiner Liste -- die Typenzeile kennt kein Gleitkomma", None),
    "size_t": ("Typ", U, "lex", "auf keiner Liste", None),
    # --- Anweisungen ------------------------------------------------------------------
    "zuweisung": ("Anweisung", E, "struk", "Statements: assignment", None),
    "if": ("Anweisung", E, "lex", "Statements: if/else", None),
    "else": ("Anweisung", E, "lex", "Statements: if/else", None),
    "switch": ("Anweisung", E, "lex", "Statements: switch (exhaustive, no default)", None),
    "case": ("Anweisung", E, "lex", "gehoert zu `switch`", None),
    "default": ("Anweisung", N, "lex", "NIE (Lesart): switch ... `no default`", None),
    "for": ("Anweisung", E, "lex", "Statements: for (counting loop)", None),
    "return": ("Anweisung", E, "lex", "Statements: return", None),
    "goto": ("Anweisung", E, "lex", "Statements: goto ONLY as a generated loop exit", None),
    "sprungmarke": ("Anweisung", E, "struk", "Ziel von `goto`", None),
    "ruf": ("Anweisung", E, "struk", "Statements: call / Expressions: call", None),
    "while": ("Anweisung", U, "lex", "auf keiner Liste -- die Anweisungszeile kennt nur `for`", None),
    "do": ("Anweisung", U, "lex", "auf keiner Liste", None),
    "break": ("Anweisung", U, "lex", "auf keiner Liste", None),
    "continue": ("Anweisung", U, "lex", "auf keiner Liste", None),
    # --- Ausdruecke --------------------------------------------------------------------
    "literal": ("Ausdruck", E, "lex", "Expressions: literal", None),
    "bezeichner": ("Ausdruck", E, "lex", "Expressions: identifier", None),
    "feldzugriff .": ("Ausdruck", E, "lex", "Expressions: field access", None),
    "feldzugriff ->": ("Ausdruck", U, "lex", "auf keiner Liste", "Expressions: field access"),
    "index []": ("Ausdruck", E, "struk", "Expressions: index", None),
    "unaer !": ("Ausdruck", E, "struk", "Expressions: unary !/-", None),
    "unaer -": ("Ausdruck", E, "struk", "Expressions: unary !/-", None),
    "unaer ~": ("Ausdruck", U, "struk", "auf keiner Liste -- die Zeile nennt nur `!` und `-`", None),
    "unaer +": ("Ausdruck", U, "struk", "auf keiner Liste", "Expressions: unary !/-"),
    "adresse &": ("Ausdruck", U, "struk", "auf keiner Liste", None),
    "dereferenz *": ("Ausdruck", U, "struk", "auf keiner Liste", None),
    "cast": ("Ausdruck", E, "struk", "Expressions: EXPLICIT cast", None),
    "sizeof": ("Ausdruck", U, "lex", "auf keiner Liste", None),
    "?:": ("Ausdruck", N, "lex", "NIE: `?:`", None),
    "komma-operator": ("Ausdruck", N, "struk", "NIE: comma operator", None),
    "zuweisung im ausdruck": ("Ausdruck", N, "struk", "NIE: assignment inside an expression", None),
    "geschachtelte zuweisung": ("Ausdruck", N, "struk", "NIE: nested assignment", None),
    "inkrement ++/--": ("Ausdruck", U, "struk",
                        "auf keiner Liste -- und es IST eine Zuweisung im Ausdruck", None),
    "verbundzuweisung": ("Ausdruck", U, "struk", "auf keiner Liste",
                         "Statements: assignment"),
    "&&/||": ("Ausdruck", U, "lex",
              "auf keiner Liste -- die binaere Zeile nennt `&` und `|`, NICHT `&&`/`||`", None),
    "zeigerarithmetik": ("Ausdruck", N, "struk", "NIE: pointer arithmetic", None),
    # **`p[i]` IST `*(p+i)` -- das ist C's eigene Definition und keine Lesart.** Die
    # Erlaubtliste nennt „index"; ob sie damit auch die Indizierung eines ZEIGERS meint,
    # steht dort nicht. Darum eine eigene Zeile, mit beiden Lesarten gedruckt.
    "index auf zeiger": ("Ausdruck", N, "struk", "NIE: pointer arithmetic (`p[i]` = `*(p+i)`)",
                         "Expressions: index"),
    # `asm ( "…" : "=r"(x) : "r"(y) )` -- die Operandenlisten der einen `asm`-Stelle. Sie
    # gehoeren zu `Other: inline assembler`, sind aber ein eigenes Stueck Syntax.
    "asm-operanden": ("Sonstiges", E, "struk", "Other: inline assembler (Operandenliste)", None),
    "#?": ("Praeprozessor", U, "lex", "eine Direktive, die der Katalog nicht kennt", None),
    "varargs ...": ("Ausdruck", N, "lex", "NIE: variadic functions", None),
    "longjmp": ("Ausdruck", N, "lex", "NIE: `longjmp`", None),
    "VLA": ("Typ", N, "cc", "NIE: VLA", None),
    "bitfeld": ("Deklaration", N, "struk", "NIE: bitfields", None),
    "const-verwurf": ("Ausdruck", N, "cc", "NIE: `const` discarding", None),
    "implizite umwandlung": ("Ausdruck", N, "cc", "NIE: implicit conversion", None),
    "union-umdeutung ohne marke": ("Ausdruck", N, "struk",
                                   "NIE: `union` reinterpretation without a tag", None),
    # --- Sonstiges ----------------------------------------------------------------------
    "volatile": ("Sonstiges", E, "lex", "Other: volatile access", None),
    "_Atomic": ("Sonstiges", E, "lex", "Other: _Atomic with named ordering", None),
    "memory_order_*": ("Sonstiges", E, "lex", "Other: _Atomic with NAMED ordering", None),
    "_Noreturn": ("Sonstiges", E, "lex", "Other: _Noreturn", None),
    "restrict": ("Sonstiges", E, "lex", "Other: restrict", None),
    "asm": ("Sonstiges", E, "lex", "Other: inline assembler at exactly one emission site", None),
    "const": ("Sonstiges", U, "lex", "auf keiner Liste -- nur `const` DISCARDING steht dort", None),
    "inline": ("Sonstiges", U, "lex",
               "auf keiner Liste -- die `Other`-Zeile nennt `_Noreturn` und `restrict`", None),
    "__attribute__": ("Sonstiges", U, "lex", "auf keiner Liste -- eine GNU-Erweiterung", None),
    "__builtin_unreachable": ("Sonstiges", U, "lex",
                              "auf keiner Liste -- GNU, und sie sagt `hier ist es UB`", None),
    "__typeof__": ("Sonstiges", U, "lex", "auf keiner Liste -- eine GNU-Erweiterung", None),
    "_Static_assert": ("Sonstiges", U, "lex", "auf keiner Liste (aber `BEWEIS.md` §3 will es)", None),
    "_Alignas": ("Sonstiges", U, "lex", "auf keiner Liste", None),
    "_Thread_local": ("Sonstiges", U, "lex", "auf keiner Liste", None),
    "register": ("Sonstiges", U, "lex", "auf keiner Liste", None),
    "auto": ("Sonstiges", U, "lex", "auf keiner Liste", None),
}

# Name -> form, for the purely lexical ones. Everything not in here and not handled by the
# structural pass lands in `UNBEKANNT` -- see `zaehle`.
NAME_FORM = {
    "static": "static", "extern": "extern", "typedef": "typedef", "enum": "enum",
    "struct": "struct", "union": "union", "_Bool": "_Bool", "bool": "bool",
    "true": "true/false", "false": "true/false", "void": "void", "char": "char",
    "short": "short", "int": "int", "long": "long", "signed": "signed",
    "unsigned": "unsigned", "float": "float", "double": "double", "size_t": "size_t",
    "if": "if", "else": "else", "switch": "switch", "case": "case", "default": "default",
    "for": "for", "return": "return", "goto": "goto", "while": "while", "do": "do",
    "break": "break", "continue": "continue", "sizeof": "sizeof",
    "volatile": "volatile", "_Atomic": "_Atomic", "_Noreturn": "_Noreturn",
    "restrict": "restrict", "const": "const", "inline": "inline",
    "__attribute__": "__attribute__", "__builtin_unreachable": "__builtin_unreachable",
    "__typeof__": "__typeof__", "typeof": "__typeof__", "_Static_assert": "_Static_assert",
    "_Alignas": "_Alignas", "_Thread_local": "_Thread_local", "register": "register",
    "auto": "auto", "asm": "asm", "__asm__": "asm", "__volatile__": "asm",
    "longjmp": "longjmp", "setjmp": "longjmp",
}
_INT = re.compile(r"^u?int(8|16|32|64)_t$")
# The C keywords a lexical pass must recognise, so that an UNKNOWN one is loud. Anything
# outside this set is an ordinary identifier -- a name the program chose.
C_SCHLUESSEL = set("""auto break case char const continue default do double else enum extern
float for goto if inline int long register restrict return short signed sizeof static struct
switch typedef union unsigned void volatile while _Alignas _Alignof _Atomic _Bool _Complex
_Generic _Imaginary _Noreturn _Static_assert _Thread_local""".split())

def typnamen(tokens):
    """Die `typedef`-Namen dieser Uebersetzungseinheit -- **aus ihr selbst, per Vorlauf**.

    Ohne sie ist `Objekte *restrict o` von `a * b` nicht zu unterscheiden: beide sind
    `name * name`. **Am ersten Lauf dieses Werkzeugs war genau das der Fehler** -- die
    Zeigerdeklaratoren wurden als Multiplikation gelesen (13 statt 320 gezaehlt), und
    umgekehrt trug jede Multiplikation ihren rechten Operanden in die Zeigermenge ein.
    *Ein Zaehler, der Deklaration und Ausdruck verwechselt, zaehlt beide falsch.*

    Der Name eines `typedef` ist der letzte Bezeichner vor dem `;`, das ihn schliesst -- das
    gilt fuer `typedef struct {…} Name;` wie fuer `typedef uint32_t Name;`.
    """
    aus = set()
    i = 0
    while i < len(tokens):
        if tokens[i][1] != "typedef":
            i += 1
            continue
        tiefe, letzt = 0, None
        j = i + 1
        while j < len(tokens):
            a, t, _ = tokens[j]
            if t in "{[(":
                tiefe += 1
            elif t in "}])":
                tiefe -= 1
            elif t == ";" and tiefe <= 0:
                break
            elif a == "name":
                letzt = t
            j += 1
        if letzt:
            aus.add(letzt)
        i = j + 1
    return aus


GRUNDTYP = set("""void char short int long signed unsigned float double _Bool bool size_t
struct union enum""".split())
# Tokens that OPEN a declaration at the start of a statement. `inline`, `static` and the
# qualifiers count: after them a type name follows, and the whole thing is a declaration.
DEKL_ANFANG = GRUNDTYP | set("""static extern typedef const volatile restrict inline register
auto _Atomic _Noreturn _Alignas _Thread_local __attribute__""".split())


def zaehle(tokens, typen=None):
    """Tokenstrom -> `(Counter der Formen, Stellen, unbekannte Namen)`.

    **The pass is TOTAL over the token stream.** Every keyword and every punctuator must map
    to a catalogue entry; whatever does not is collected in `unbekannt` and printed. *An
    allow-list checker that only asks about forms someone already suspected cannot find a
    new one* -- and finding new ones is the entire purpose of this run.

    **DEKLARATION ODER AUSDRUCK -- das ist die einzige Unterscheidung, die hier zaehlt.**
    Vier Tokens bedeuten in den beiden Zusammenhaengen etwas voellig Verschiedenes:

        `*`   Zeigerdeklarator    ODER Multiplikation ODER Dereferenz
        `[`   Feldtyp `T[N]`      ODER Indizierung
        `(`   Funktionsdeklarator ODER Ruf ODER Gruppierung ODER Umwandlung
        `,`   Deklaratortrenner   ODER Argumenttrenner ODER Kommaoperator

    Der Zustand `deklaration` faellt an `;` und an `=`; er beginnt an einem Satzanfang mit
    einem Typwort und in jeder Parameterliste. **Das ist eine Naeherung und keine Grammatik**
    -- was sie nicht trifft, steht unter `UNGEMESSEN`.
    """
    typen = typen if typen is not None else typnamen(tokens)
    form = {}
    stellen = {}
    unbekannt = {}

    def zaehl(f, tok):
        form[f] = form.get(f, 0) + 1
        stellen.setdefault(f, []).append(tok)

    def typwort(t):
        return t in GRUNDTYP or t in typen or bool(_INT.match(t)) or t.endswith("_t")

    stapel = []             # (Zeichen, Rolle)
    vor = None
    fragen = []
    zuweisungen = 0         # `=` seit dem letzten `;` oder Deklaratorkomma
    seit_semikolon = []
    zeiger = set()
    satzanfang = True
    letzte_zu = None        # Rolle der zuletzt GESCHLOSSENEN Klammer
    deklaration = False     # wir stehen in einem Deklarator
    initialisierer = False  # ... hinter dessen `=`
    STEUER = {"if", "for", "while", "switch", "sizeof", "defined", "_Static_assert"}

    def in_verbund():
        return any(r == "verbund" for _, r in stapel)

    def tiefe_klammern():
        return sum(1 for z, _ in stapel if z in "([")

    def dekl():
        return deklaration and not initialisierer

    for idx, tok in enumerate(tokens):
        art, t, _ = tok
        naechst = tokens[idx + 1] if idx + 1 < len(tokens) else ("op", "", 0)

        if art == "pp":
            zaehl(t if t in KATALOG else "#?", tok)
            if t == "#define":
                zaehl("konstante-#define", tok)
            vor, satzanfang = tok, True
            deklaration = initialisierer = False
            seit_semikolon = []
            continue

        if art == "ppende":
            # Das Ende einer Direktivenzeile IST ein Satzende -- siehe `lies_tokens`.
            vor, satzanfang = None, True
            deklaration = initialisierer = False
            seit_semikolon = []
            continue

        if art in ("zahl", "text"):
            zaehl("literal", tok)
            vor = tok
            satzanfang = False
            seit_semikolon.append(tok)
            continue

        if art == "name":
            if satzanfang and (t in DEKL_ANFANG or typwort(t)):
                deklaration, initialisierer = True, False
            if _INT.match(t):
                zaehl("uintN_t" if t[0] == "u" else "intN_t", tok)
            elif t.startswith("memory_order_"):
                zaehl("memory_order_*", tok)
            elif t in NAME_FORM:
                zaehl(NAME_FORM[t], tok)
            elif t.startswith("__builtin_"):
                zaehl(t if t in KATALOG else "__builtin_*", tok)
                unbekannt[t] = unbekannt.get(t, 0) + 1
            elif t in ("va_list", "va_start", "va_arg", "va_end"):
                zaehl("varargs ...", tok)
            elif t in C_SCHLUESSEL or (t.startswith("_") and t[1:2].isupper()):
                unbekannt[t] = unbekannt.get(t, 0) + 1
            else:
                zaehl("bezeichner", tok)
                # A name declared behind a run of `*` (and `restrict`) IS a pointer. The run
                # is only recognised inside a declarator -- which is why the pre-pass exists.
                if dekl() and vor and vor[1] in ("*", "restrict") and \
                        any(x[1] == "*" for x in seit_semikolon[-4:]):
                    zeiger.add(t)
            vor = tok
            satzanfang = False
            seit_semikolon.append(tok)
            continue

        # ---- Satzzeichen -------------------------------------------------------------
        vorher = vor[1] if vor else ""
        vorart = vor[0] if vor else ""
        endet_ausdruck = (vorart in ("name", "zahl", "text")
                          and vorher not in C_SCHLUESSEL) or vorher in (")", "]")

        if t == "(":
            if dekl() and vorart == "name" and vorher not in GRUNDTYP:
                rolle = "dekl"                    # Funktionsdeklarator / Parameterliste
            elif vorher in STEUER:
                rolle = "steuer"
            elif endet_ausdruck:
                rolle = "ruf"
                zaehl("ruf", tok)
            else:
                rolle = "gruppe"
            stapel.append(("(", rolle))
            if rolle == "dekl":
                satzanfang = True                 # ein Parameter ist eine Deklaration
        elif t == "[":
            if dekl():
                zaehl("feldtyp", tok)
            else:
                zaehl("index []", tok)
                if vorher in zeiger:
                    # `p[i]` auf einem ZEIGER ist nach C's eigener Definition `*(p+i)` --
                    # Zeigerarithmetik. Getrennt gezaehlt, nie stillschweigend eingerechnet.
                    zaehl("index auf zeiger", tok)
            stapel.append(("[", "index"))
        elif t == "{":
            # **Drei Klammernpaare sehen gleich aus und sind es nicht** -- und zwei davon
            # haben diesen Zaehler beim ersten Lauf 24 „geschachtelte Zuweisungen" finden
            # lassen, die keine sind:
            #
            #   `enum { A = 0, B = 1 }`   -- Aufzaehlungswerte, keine Zuweisungen
            #   `(T){ .x = k, .y = n }`   -- ein VERBUNDLITERAL hinter einer Umwandlung
            #   `if (x) { … }`            -- ein Block, und davor steht auch ein `)`
            #
            # Die letzten beiden trennt nur die ROLLE der eben geschlossenen Klammer:
            # `gruppe` war eine Umwandlung, `steuer` war ein `if`.
            if vorher == "=" or (stapel and stapel[-1][1] in ("init", "aufzaehlung")):
                rolle = "init"
            elif vorher == ")" and letzte_zu == "gruppe":
                rolle = "init"                    # Verbundliteral `(T){ … }`
            elif any(x[1] == "enum" for x in seit_semikolon[-4:]):
                rolle = "aufzaehlung"
            elif any(x[1] in ("struct", "union") for x in seit_semikolon[-4:]):
                rolle = "verbund"
                zaehl("struct-definition" if any(x[1] == "struct" for x in seit_semikolon[-4:])
                      else "union-definition", tok)
            else:
                rolle = "block"
            stapel.append(("{", rolle))
            seit_semikolon = []
            zuweisungen = 0
            satzanfang = True
            if rolle != "init":
                deklaration = initialisierer = False
        elif t in (")", "]", "}"):
            rolle = stapel.pop()[1] if stapel else None
            letzte_zu = rolle
            if t == "}":
                seit_semikolon = []
                zuweisungen = 0
                satzanfang = True
                deklaration = initialisierer = False
            elif t == ")" and rolle == "dekl":
                satzanfang = False
        elif t == ";":
            seit_semikolon = []
            zuweisungen = 0
            satzanfang = True
            deklaration = initialisierer = False
            fragen = [f for f in fragen if f < tiefe_klammern()]
        elif t == "?":
            zaehl("?:", tok)
            fragen.append(tiefe_klammern())
        elif t == ":":
            if fragen and fragen[-1] == tiefe_klammern():
                fragen.pop()
            elif any(x[1] == "case" for x in seit_semikolon) or vorher == "default":
                pass
            elif in_verbund() and vorart in ("name", "zahl"):
                zaehl("bitfeld", tok)
            elif vorart == "name" and not stapel[-1:] or (stapel and stapel[-1][1] == "block"):
                zaehl("sprungmarke", tok)
                satzanfang = True
            else:
                # `asm ( "…" : "=r"(x) : "r"(y) )` -- die Operandenlisten. Sie stehen in
                # einer Steuerklammer und sind weder Marke noch Bitfeld noch `?:`.
                zaehl("asm-operanden", tok)
        elif t == ",":
            innen = stapel[-1][1] if stapel else "datei"
            if innen in ("ruf", "dekl", "steuer", "init", "index", "verbund", "aufzaehlung"):
                if innen == "dekl":
                    satzanfang = True
                    initialisierer = False
            elif deklaration:
                zuweisungen = 0             # `int a = 1, b = 2;` -- zwei Deklaratoren
                initialisierer = False
            elif innen == "gruppe":
                zaehl("komma-operator", tok)
        elif t == "=":
            innen = stapel[-1][1] if stapel else "datei"
            if deklaration or innen in ("init", "aufzaehlung"):
                initialisierer = True
                zaehl("zuweisung", tok)
            else:
                zuweisungen += 1
                if zuweisungen > 1:
                    zaehl("geschachtelte zuweisung", tok)
                if innen in ("ruf", "gruppe", "index"):
                    zaehl("zuweisung im ausdruck", tok)
                else:
                    zaehl("zuweisung", tok)
        elif t in ("+=", "-=", "*=", "/=", "%=", "&=", "^=", "|=", "<<=", ">>="):
            zaehl("verbundzuweisung", tok)
            if vorher in zeiger:
                zaehl("zeigerarithmetik", tok)
        elif t in ("++", "--"):
            zaehl("inkrement ++/--", tok)
            if vorher in zeiger or naechst[1] in zeiger:
                zaehl("zeigerarithmetik", tok)
        elif t in ("&&", "||"):
            zaehl("&&/||", tok)
        elif t == "...":
            zaehl("varargs ...", tok)
        elif t == ".":
            zaehl("feldzugriff .", tok)
        elif t == "->":
            zaehl("feldzugriff ->", tok)
        elif t == "*":
            if dekl() and (typwort(vorher) or vorher in ("*", "const", "volatile",
                                                         "_Atomic", "restrict")):
                zaehl("zeigertyp", tok)
                if vorher == "void" or (vorher == "*" and any(
                        x[1] == "void" for x in seit_semikolon[-3:])):
                    zaehl("void*", tok)
            elif endet_ausdruck:
                pass                                            # Multiplikation
            else:
                zaehl("dereferenz *", tok)
        elif t == "&":
            if not endet_ausdruck:
                zaehl("adresse &", tok)
        elif t == "-":
            if not endet_ausdruck:
                zaehl("unaer -", tok)
            elif vorher in zeiger or naechst[1] in zeiger:
                zaehl("zeigerarithmetik", tok)
        elif t == "+":
            if not endet_ausdruck:
                zaehl("unaer +", tok)
            elif vorher in zeiger or naechst[1] in zeiger:
                zaehl("zeigerarithmetik", tok)
        elif t == "!":
            zaehl("unaer !", tok)
        elif t == "~":
            zaehl("unaer ~", tok)
        elif t in ("/", "%", "|", "^", "<<", ">>", "==", "!=", "<", "<=", ">", ">=",
                   "#", "##"):
            pass                                                # binaer, alle erlaubt
        else:
            unbekannt[t] = unbekannt.get(t, 0) + 1
        vor = tok
        satzanfang = satzanfang and t in (";", "{", "}", ":")
        seit_semikolon.append(tok)

    n = _casts(tokens, typen)
    if n:
        form["cast"] = form.get("cast", 0) + n
        stellen.setdefault("cast", [])
    return form, stellen, unbekannt


TYPWORT = re.compile(r"^(u?int(8|16|32|64)_t|void|char|short|int|long|signed|unsigned|float|"
                     r"double|_Bool|bool|size_t|struct|union|enum|const|volatile|_Atomic|"
                     r"[A-Z][A-Za-z0-9_]*|[A-Za-z_][A-Za-z0-9_]*_t)$")


def _casts(tokens, typen=frozenset()):
    """`( Typwort+ *? )` gefolgt von etwas, das einen Ausdruck beginnt.

    **A cast and a call cannot be told apart by shape alone** -- `(T)(x)` and `f(x)` differ
    only in whether `T` names a type. What decides here is that the content consists of type
    WORDS and nothing else, plus the token before the `(` not ending an expression. The
    `typedef` names of the unit come in from the pre-pass, so a lowercase typedef is a type
    word here too. *What is still missed is a cast whose type is a macro; nothing is
    invented* (W10).
    """
    n = 0
    for i, (a, t, _) in enumerate(tokens):
        if t != "(":
            continue
        if i and tokens[i - 1][0] in ("name", "zahl") and tokens[i - 1][1] not in (
                "if", "for", "while", "switch", "sizeof", "return", "case"):
            continue
        j = i + 1
        inhalt = []
        while j < len(tokens) and tokens[j][1] != ")":
            inhalt.append(tokens[j])
            j += 1
        if not inhalt or j >= len(tokens) - 1:
            continue
        if not all((t2[0] == "name" and (TYPWORT.match(t2[1]) or t2[1] in typen))
                   or t2[1] == "*" for t2 in inhalt):
            continue
        nach = tokens[j + 1]
        if nach[0] in ("name", "zahl", "text") or nach[1] in ("(", "-", "~", "!", "&", "*"):
            n += 1
    return n


# ----------------------------------------------------------------------------------------
# DER KORPUS
# ----------------------------------------------------------------------------------------

def korpus(wurzel=None, gabbro=None):
    """Je emittierender `.gab`: das erzeugte C. **Ein Durchgang, nicht zwei.**

    Returns `(erzeugnisse, gesamt, unvollstaendig)`. `erzeugnisse` maps the relative path to
    its C; `gesamt` is every versioned `.gab` that was tried; `unvollstaendig` are the ones
    that left with `0` and produced nothing.

    **The population is the DENOMINATOR of every number below**, so it is measured here and
    printed, never assumed. The criterion is the one `pruefe-grammatiktafel.volle_emission`
    uses -- zero checker errors, zero `C001` -- read off the return code, which is `1`
    exactly when `absagen.fehler_zahl() > 0` (`gabbro-cli/src/main.rs:command_emit`). *Both
    readings are computed from the SAME run and their agreement is printed*, because two
    sweeps would be two registers over one thing (W7).
    """
    wurzel = pathlib.Path(wurzel or W)
    befehl = _lade("zaehle-absagen.py").binaer(wurzel, gabbro)
    erzeugnisse, gesamt, leer = {}, [], []
    for d in sorted(pathlib.Path(wurzel).rglob("*.gab")):
        rel = d.relative_to(wurzel)
        if any(teil in AUS_BAU for teil in rel.parts[:-1]):
            continue
        gesamt.append(str(rel))
        try:
            r = subprocess.run(befehl + ["emit", str(d)], cwd=wurzel,
                               capture_output=True, text=True, timeout=FRIST)
        except subprocess.TimeoutExpired:
            raise SystemExit(
                f"ABBRUCH: `gabbro emit {rel}` ueberschritt {FRIST} s -- es wurde NICHTS "
                "gemessen, und eine halbe Tabelle ist keine.")
        if r.returncode != 0:
            continue
        if not r.stdout.strip():
            leer.append(str(rel))
            continue
        erzeugnisse[str(rel)] = r.stdout
    return erzeugnisse, gesamt, leer


def uebersetzermessung(erzeugnisse):
    """Die drei semantischen Klassen -- **vom zweiten Instrument, nicht von hier**.

    `implicit conversion`, `const` discarding and VLA are questions about TYPES, and a
    half-parser that answers them is a second source of error over the same object. `cc`
    already has the answer and prints it with a switch name; the switch name is the
    classification.

    Returns `(Form -> (Treffer, Dateien), uebersetzt, gescheitert)`. **A missing `cc` is not
    a green result** -- it is `None`, and the report says the three classes stayed unmeasured
    (W1).

    **Und ein Erzeugnis, das `cc` GAR NICHT UEBERSETZT, hat null Warnungen und ist nicht
    gemessen.** Gemessen 2026-08-31: eine der 102 Einheiten faellt hier durch. Ohne diese
    Zahl daneben liest sich "kein einziger Treffer" als ein Urteil ueber 102 Einheiten, und
    es ist eines ueber 101. *Dieselbe Klasse wie eine leere Grundgesamtheit* (W1/W17).
    """
    if subprocess.run(["sh", "-c", "command -v cc"], capture_output=True).returncode != 0:
        return None
    karte = {"-Wconversion": "implizite umwandlung", "-Wsign-conversion": "implizite umwandlung",
             "-Wcast-qual": "const-verwurf", "-Wdiscarded-qualifiers": "const-verwurf",
             "-Wvla": "VLA", "-Wpointer-arith": "zeigerarithmetik",
             "-Wbad-function-cast": "cast", "-Wdouble-promotion": "implizite umwandlung",
             "-Wfloat-equal": "implizite umwandlung"}
    aus, uebersetzt, gescheitert = {}, 0, []
    for d, c in sorted(erzeugnisse.items()):
        r = subprocess.run(["cc"] + CC_MESSSCHALTER + ["-c", "-x", "c", "-o", os.devnull, "-"],
                           input=c, capture_output=True, text=True, env=CC_UMGEBUNG)
        if r.returncode != 0:
            gescheitert.append(d)
            continue
        uebersetzt += 1
        for m in re.finditer(r"\[(-W[a-z-]+)\]", r.stderr):
            f = karte.get(m.group(1))
            if not f:
                continue
            tr, ds = aus.get(f, (0, set()))
            aus[f] = (tr + 1, ds | {d})
    return aus, uebersetzt, gescheitert


# ----------------------------------------------------------------------------------------
# DIE SPRECHPROBE
# ----------------------------------------------------------------------------------------
GIFT = r'''
/* Ein Blockkommentar, in dem ?: und void* und __builtin_unreachable() stehen,
 * und ein , als Kommaoperator, und p + 1 als Zeigerarithmetik. Nichts davon
 * darf gezaehlt werden. */
#include <stdint.h>
#define ZZ 4u
static const char *zzs = "hier steht ?: und void * und ein , dazu und p + 1";
// ein Zeilenkommentar mit ?: und void * darin
static uint32_t zzf(uint32_t a, uint32_t b) {
    uint32_t z = (a > b) ? a : b;   /* EIN echtes ?: */
    char zzc = '?';
    z += (uint32_t)1;
    if (a && b) { z = z | 1u; }
    for (uint32_t i = 0; i < ZZ; i++) { z = z + i; }
    goto zzende;
zzende:
    return z;
}
/* Zwei Klammernpaare, die wie eine Zuweisungskette AUSSEHEN und keine sind. Beide
 * haben diesen Zaehler beim ersten Lauf 24 Funde erfinden lassen. */
enum ZzF { ZZ_X = 0, ZZ_Y = 2 };
typedef struct { uint32_t id; } ZzV;
static ZzV zzv(uint32_t k) { return (ZzV){ .id = k }; }
'''
# **Die NEGATIVE Richtung: was NICHT gezaehlt werden darf.** Jede Null hier ist eine Falle,
# an der ein `grep`-Zaehler stirbt.
ERWARTET = {"?:": 1, "&&/||": 1, "char": 2, "cast": 1, "verbundzuweisung": 1,
            "inkrement ++/--": 1, "#include": 1, "#define": 1, "sprungmarke": 1, "goto": 1,
            "for": 1, "if": 1, "zeigertyp": 1, "const": 1, "static": 3,
            "enum": 1, "typedef": 1, "literal": 8,
            "unaer !": 0, "komma-operator": 0, "__builtin_unreachable": 0, "void*": 0,
            "bitfeld": 0, "zeigerarithmetik": 0, "index auf zeiger": 0, "ruf": 0,
            "zuweisung im ausdruck": 0, "geschachtelte zuweisung": 0}

# **Die POSITIVE Richtung, und ohne sie waere das hier eine Zierde** (R11). Ein Zaehler, der
# nie etwas gefunden hat, ist von einem, der nichts finden KANN, nicht zu unterscheiden --
# und die interessante Menge dieses Werkzeugs ist genau die der Funde. Also traegt dieser
# Text **jede Form der Nie-Liste, die lexikalisch oder strukturell entscheidbar ist**, und
# jede muss auftauchen.
GIFT_POSITIV = r'''
#ifdef ZZIRGENDWAS
#endif
typedef struct { unsigned zza : 3; unsigned zzb : 5; } ZzBits;
enum ZzE { ZZ_A, ZZ_B };
static int zzvar(int n, ...);
static void *zzroh(void) { return 0; }
static int zzruf(int x) { return x; }
static void zzg(unsigned char *p, int n) {
    int a, b, c;
    a = b = 7;                 /* geschachtelte Zuweisung */
    zzruf((a = 3));            /* Zuweisung im Ausdruck */
    c = (a, b);                /* Kommaoperator */
    p = p + n;                 /* Zeigerarithmetik */
    p[0] = 1;                  /* Index auf einem Zeiger */
    while (a) { a--; }
    switch (n) { default: break; }
    (void)sizeof(int);
#if defined(__GNUC__)
    __builtin_unreachable();
#endif
}
'''
ERWARTET_POSITIV = {
    "?:": 0, "bitfeld": 2, "enum": 1, "varargs ...": 1, "void*": 1, "typedef": 1,
    "geschachtelte zuweisung": 1, "zuweisung im ausdruck": 1, "komma-operator": 1,
    "zeigerarithmetik": 1, "index auf zeiger": 1, "while": 1, "default": 1,
    "sizeof": 1, "__builtin_unreachable": 1, "#ifdef": 1, "#if": 1, "#endif": 2,
    "break": 1, "inkrement ++/--": 1, "ruf": 2,
}


def sprechprobe():
    """**Der Zaehler an zwei ERFUNDENEN Erzeugnissen, in beide Richtungen.**

    Gemessen wird nicht am echten C, sonst wandert die Probe mit ihrem Gegenstand.

    `GIFT` traegt jede Falle, an der ein `grep`-Zaehler stirbt: `?:` in einem Blockkommentar,
    in einem Zeilenkommentar, in einer Zeichenkette und als Zeichenliteral `'?'` -- und
    **genau ein** echtes `?:` daneben. *Ein `grep -c '?'` findet darin 6; die Zahl unten
    ist 1.*

    `GIFT_POSITIV` traegt **jede strukturell entscheidbare Form der Nie-Liste**, und jede
    muss gefunden werden. **Ohne diese Haelfte waere ein Zaehler, der nichts finden KANN,
    von einem, der nichts findet, nicht zu unterscheiden** (R11) -- und beim Bau dieses
    Werkzeugs war er es dreimal: die Zeigerdeklaratoren fielen in die Multiplikation, jede
    Multiplikation trug ihren rechten Operanden in die Zeigermenge, und eine
    Praeprozessorzeile hatte kein Ende.
    """
    schlecht = []
    for text, erwartet, richtung in ((GIFT, ERWARTET, "Fallen"),
                                     (GIFT_POSITIV, ERWARTET_POSITIV, "Funde")):
        form, _, _ = zaehle(lies_tokens(text))
        for f, soll in sorted(erwartet.items()):
            ist = form.get(f, 0)
            if ist != soll:
                schlecht.append(f"      [{richtung}] {f:24} erwartet {soll}, gezaehlt {ist}")
    _, _, unbekannt = zaehle(lies_tokens(GIFT))
    roh = GIFT.count("?")
    if roh <= ERWARTET["?:"]:
        schlecht.append(f"      die Gegenprobe traegt nicht: `?` roh {roh}, erwartet > 1")
    return schlecht, roh, unbekannt


def mengen(form, kat=None):
    """`(A, B, C_nie, C_ungenannt, C_ungenannt_weit)` -- die Mengen, als sortierte Listen."""
    kat = kat or KATALOG
    a = sorted(f for f, e in kat.items() if e[1] == E and form.get(f, 0) > 0)
    b = sorted(f for f, e in kat.items() if e[1] == E and form.get(f, 0) == 0)
    cn = sorted(f for f, e in kat.items() if e[1] == N and form.get(f, 0) > 0)
    cu = sorted(f for f, e in kat.items() if e[1] == U and form.get(f, 0) > 0 and e[4] is None)
    cw = sorted(f for f, e in kat.items() if e[1] == U and form.get(f, 0) > 0 and e[4] is not None)
    return a, b, cn, cu, cw


def main():
    stellen = "--stellen" in sys.argv
    mit_cc = "--uebersetzer" in sys.argv
    tafel = "--tafel" in sys.argv

    schlecht, roh, s_unbekannt = sprechprobe()
    print("== Sprechprobe: der Zaehler an einem erfundenen Erzeugnis")
    if schlecht:
        print("   GESCHEITERT -- der Zaehler misst nicht, was er sagt:")
        print("\n".join(schlecht))
        return 2
    print(f"   ok -- `?` steht {roh}x im Gift, gezaehlt wird 1. "
          f"Kommentar, Zeichenkette und Zeichenliteral zaehlen nicht mit.")

    erzeugnisse, gesamt, leer = korpus()
    if not erzeugnisse:
        print("   ABBRUCH: kein einziges Erzeugnis -- es wurde NICHTS gemessen.")
        return 2

    form, alle_stellen, unbekannt = {}, {}, {}
    kommentarzeilen = zeilen = 0
    je_datei = {}
    for d, c in sorted(erzeugnisse.items()):
        _, kz = entkommentiere(c)
        kommentarzeilen += kz
        zeilen += c.count("\n")
        f, st, ub = zaehle(lies_tokens(c))
        je_datei[d] = f
        for k, v in f.items():
            form[k] = form.get(k, 0) + v
        for k, v in st.items():
            alle_stellen.setdefault(k, []).extend((d, t) for t in v)
        for k, v in ub.items():
            unbekannt[k] = unbekannt.get(k, 0) + v

    cc_ergebnis = uebersetzermessung(erzeugnisse) if mit_cc else None
    cc, cc_ok, cc_schlecht = cc_ergebnis if cc_ergebnis else (None, 0, [])
    if cc:
        for f, (t, ds) in cc.items():
            form[f] = form.get(f, 0) + t

    print()
    print("== Der Korpus -- der NENNER jeder Zahl darunter")
    print(f"   {len(erzeugnisse)} von {len(gesamt)} versionierten `.gab` emittieren, "
          f"{zeilen} Zeilen C.")
    print(f"   Davon {kommentarzeilen} Zeilen Kommentar ({round(100*kommentarzeilen/max(zeilen,1))} %) "
          "-- die Flaeche, ueber die ein `grep`-Zaehler stolpert.")
    if leer:
        print(f"   {len(leer)} Datei(en) gingen ohne Fehler durch und lieferten NICHTS: "
              + ", ".join(leer))

    a, b, cn, cu, cw = mengen(form)
    benutzt = len(a) + len(cn) + len(cu) + len(cw)
    print()
    print(f"== Die drei Mengen  (Katalog: {len(KATALOG)} Formen aus `BEWEIS.md` §1)")
    print(f"   A  erlaubt und benutzt        {len(a):3}   <- die eigentliche Tabelle")
    print(f"   B  erlaubt und NIE benutzt    {len(b):3}   <- tote Eintraege, die Liste kann sie verlieren")
    print(f"   C  benutzt und NICHT erlaubt  {len(cn)+len(cu)+len(cw):3}   <- die BEFUNDE")
    print(f"        davon auf der Nie-Liste  {len(cn):3}   ein WIDERSPRUCH")
    print(f"        ungenannt, ungedeckt     {len(cu):3}   eine LUECKE, auch bei weiter Lesart")
    print(f"        ungenannt, weit gedeckt  {len(cw):3}   nur bei STRENGER Lesart ein Befund")
    print(f"   ---------------------------------")
    print(f"   Formen im Erzeugnis           {benutzt:3}   = A + C")

    for titel, menge, zeige_zahl in (
            ("A  ERLAUBT UND BENUTZT -- was eine C-Semantik bekommen muss", a, True),
            ("B  ERLAUBT UND NIE BENUTZT -- die Tabelle kann sie verlieren", b, False),
            ("C1 BENUTZT UND AUF DER NIE-LISTE -- der Widerspruch", cn, True),
            ("C2 BENUTZT UND UNGENANNT, von keiner Lesart gedeckt", cu, True),
            ("C3 BENUTZT UND UNGENANNT, aber weit gedeckt", cw, True)):
        print()
        print(f"== {titel}")
        if not menge:
            print("   (leer)")
            continue
        for f in menge:
            g, st, stufe, quelle, weit = KATALOG[f]
            n = f"{form.get(f, 0):5}" if zeige_zahl else "    -"
            print(f"   {n}  {f:28} {stufe:5} {g:13} {quelle}")
            if weit:
                print(f"          weite Lesart: {weit}")

    print()
    print("== UNBEKANNT -- was der Katalog nicht kennt")
    if unbekannt:
        for k, v in sorted(unbekannt.items()):
            print(f"   {v:5}  {k}")
        print("   **Jeder Eintrag hier ist eine Form ohne Urteil.** Der Zaehler ist ueber dem")
        print("   Tokenstrom total; was er nicht zuordnen kann, verschweigt er nicht.")
    else:
        print("   keiner -- jedes Schluesselwort und jedes Satzzeichen ist zugeordnet.")

    print()
    print("== Das zweite Instrument")
    if cc is not None:
        print(f"   `cc` hat {cc_ok} von {len(erzeugnisse)} Erzeugnissen UEBERSETZT.")
        if cc_schlecht:
            print(f"   {len(cc_schlecht)} nicht -- und darueber sagt dieser Abschnitt NICHTS:")
            for d in cc_schlecht:
                print(f"      {d}")
            print("   *Null Warnungen an einer Datei, die gar nicht uebersetzt, ist keine")
            print("   Messung* (W1).")
    if cc is None and not mit_cc:
        print("   NICHT GEFAHREN (`--uebersetzer`). Damit bleiben UNGEMESSEN:")
        print("   implizite Umwandlung · `const`-Verwurf · VLA -- drei Eintraege der Nie-Liste.")
    elif cc is None:
        print("   kein `cc` gefunden. **Das ist kein Freispruch**: implizite Umwandlung,")
        print("   `const`-Verwurf und VLA bleiben ungemessen (W1).")
    else:
        print(f"   `cc {' '.join(CC_MESSSCHALTER)}`")
        if not cc:
            print(f"   Kein einziger Treffer ueber die {cc_ok} uebersetzten Erzeugnisse --")
            print("   implizite Umwandlung, `const`-Verwurf und VLA halten, und zwar")
            print("   **gemessen und nicht behauptet**. `BEWEIS.md` §2 Zeile 7 sagt zur")
            print("   impliziten Umwandlung *\u201enone, but to be checked mechanically\u201c*")
            print("   -- das hier ist die mechanische Pruefung.")
        for f, (t, ds) in sorted(cc.items()):
            print(f"   {t:5}  {f:28} in {len(ds)} Datei(en)")

    if stellen:
        print()
        print("== Die Stellen der Befunde")
        for f in cn + cu:
            for d, tok in alle_stellen.get(f, [])[:40]:
                print(f"   {f:24} {d} -> C:{tok[2]}  {tok[1]}")

    if tafel:
        print()
        print("== Gegenprobe: derselbe Zaehler ohne Lexer (`grep` ueber den Rohtext)")
        print("   Form                      lexikalisch   roh   Differenz")
        roh_gesamt = "".join(erzeugnisse.values())
        for f, muster in (("for", r"\bfor\b"), ("index []", r"\["),
                          ("while", r"\bwhile\b"), ("if", r"\bif\b"),
                          ("switch", r"\bswitch\b"), ("case", r"\bcase\b"),
                          ("static", r"\bstatic\b"), ("?:", r"\?"),
                          ("__builtin_unreachable", r"__builtin_unreachable"),
                          ("goto", r"\bgoto\b"), ("typedef", r"\btypedef\b")):
            r = len(re.findall(muster, roh_gesamt))
            g = form.get(f, 0)
            print(f"   {f:24} {g:11}   {r:5}   {r - g:+}")
        print("   **Die Differenz ist die Kommentar- und Deklaratorflaeche.** Das Erzeugnis")
        print("   dieses Ordners erklaert sich auf Englisch, und `for`, `if`, `while`, `case`")
        print("   sind auch englische WOERTER: `grep` findet `for` 73mal, eine Anweisung ist")
        print("   es 49mal. Bei `[` trennt der Lexer den Feldtyp `T[N]` von der Indizierung")
        print("   -- zwei Formen, ein Zeichen.")
        print("   **Und die vier Formen mit Differenz NULL stehen daneben**: fuer `?:`,")
        print("   `goto`, `typedef` und `__builtin_unreachable` haette `grep` dasselbe")
        print("   gesagt. *Dass er recht gehabt HAETTE, weiss man erst hinterher.*")

    print()
    print("== UNGEMESSEN -- und darum hier genannt (W10)")
    print("   * `union`-Umdeutung ohne Marke: eine Frage an das Gabbro-Programm, nicht an")
    print("     sein C. Hier steht nur die Zahl der `union`-Definitionen.")
    print("   * Zeigerarithmetik: die Zeigermenge kommt aus `T *name`. Ein Zeiger, der ueber")
    print("     einen `typedef` kommt, fehlt darin -- die Zahl ist eine UNTERE Schranke.")
    print("   * Kommaoperator: gezaehlt wird nur der Fall in einer GRUPPIERUNGSKLAMMER. Ein")
    print("     Komma auf Anweisungsebene ist ohne Deklarationsparser nicht vom Deklarator-")
    print("     trenner zu unterscheiden und wird NICHT gezaehlt -- untere Schranke.")
    print("   * `goto` als `generated loop exit`: gezaehlt wird `goto`, nicht WOZU. Ob jeder")
    print("     Sprung ein Schleifenausgang ist, sagt diese Zaehlung nicht.")
    print("   * `asm` `at exactly one emission site`: gezaehlt werden die Vorkommen im C,")
    print("     nicht die Stellen in `emit.rs`.")
    print("   * Menge B ist eine OBERE Schranke: ein 103. Programm kann einen toten Eintrag")
    print("     wiederbeleben.")

    print()
    print("== Die Ratsche")
    befund = []
    for name, marke, ist in (("MARKE_TABELLE", MARKE_TABELLE, benutzt),
                             ("MARKE_UNERLAUBT", MARKE_UNERLAUBT, len(cn) + len(cu) + len(cw))):
        zeichen = "=" if ist == marke else ("faellt" if ist < marke else "STEIGT")
        print(f"   {name:16} Marke {marke:3}   gemessen {ist:3}   {zeichen}")
        if ist > marke:
            befund.append(f"{name}: {marke} -> {ist}")
    if befund:
        print()
        print("   **Eine Marke ist GESTIEGEN.** Das ist dieselbe Bewegung wie eine wachsende")
        print("   Axiomschicht: die C-Semantik, die Gabbro eines Tages formalisieren muss,")
        print("   ist gerade groesser geworden. Der Grund gehoert AN DIE MARKE, in diese Datei.")
        abschnitt.fertig()
        return 1
    abschnitt.fertig()
    return 0


if __name__ == "__main__":
    sys.exit(abschnitt.fahre(main))
