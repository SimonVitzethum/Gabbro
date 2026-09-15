#!/usr/bin/env python3
"""**Per FORM of the derived grammar: does the language carry it, or does the user?**

The population is `instrumente/leite-grammatik.py` -- the decision points of `parse.rs`,
not the terminals of a document. *The grammar is the language's own population; a corpus is
written from the language outwards and cannot answer completeness (trap 80).*

THE TEST IS DIFFERENTIAL, AND THAT IS THE WHOLE INSTRUMENT
-----------------------------------------------------------
A form is measured by TWO programs that differ in exactly it: a BASE without the form and a
VARIANT with it. Four runs on each, and the verdict falls out of the pair:

    REFUSES    the variant is refused BY NAME -- `C001` at the emitter, or a checker error
    DEMANDS    the variant is accepted and `gabbro pflichten` books an obligation the base
               does not -- the form is carried into a promise a HUMAN still owes
    CARRIES    the variant's C differs from the base's C, and that C compiles -- the
               generator wrote something nobody typed
    GUARDS     no C of its own and no obligation -- but a CHECKER ERROR TEXT names the
               word. A pass has a sentence about this form; the language carries it by
               refusing wrong uses rather than by generating right ones
    UNCOVERED  accepted, lowered, compiles, C BYTE-IDENTICAL to the base's, no new
               obligation, AND no checker error text names it.
               **Nothing in the tree has an answer for this form.**

**`GUARDS` is not a softening of `UNCOVERED`, it is the fifth cell the four-way table was
missing.** `requires` generates no C and books its obligation at the CALL SITE, not at the
declaration; a pointer SPACE has no counterpart in C at all. Judging those `UNCOVERED`
because the artefact does not move would say the language does nothing with a `requires`.
*The generator is one of two ways a language can carry a form; the other is a refusal.*

**The word register is READ, not copied** (`W7`): `prueferworte()` out of
`instrumente/pruefe-grammatiktafel.py`, which already computes "which words does a checker
error name" for its own `vom Pruefer` state. A second copy here would run away from it.

**The `UNCOVERED` cell is the whole point, and it is not hypothetical.** `SYNTAX.md` said of
`when` for months that it lowers to `#if`; the emitter never read the field, and an item with
`when` produced exactly the same C as one without. *A clause that changes neither the
artefact nor the obligation register is a promise nobody keeps* -- and it looks kept.

WHY A PAIR AND NOT A SINGLE FILE
---------------------------------
`gabbro emit` succeeding says the emitter did not refuse. It does not say the emitter READ
the form. Only the difference to a program without the form says that, and only a byte
comparison says it without a second emitter beside the emitter (`W7`).

WHAT THIS CANNOT SAY, AND SAYS SO
----------------------------------
* A C difference is not a CORRECT lowering. `cc -Werror` checks the language, not the
  meaning -- the grammar table carries the same caveat and for the same reason.
* A form with no obligation and no C difference may still be read by a pass that only
  refuses WRONG programs. The run therefore also records whether a deliberately broken
  variant is refused (`gegenprobe`), and prints that column beside the verdict.
* A form this file has no minimal host for is `NICHT GEPROBT` and is counted in the
  denominator all the same. *A denominator that drops what could not be measured is `W25`.*

    ./instrumente/miss-grammatikdeckung.py --probe    only the speech test
    ./instrumente/miss-grammatikdeckung.py             the table and the counts
    ./instrumente/miss-grammatikdeckung.py --nur ID    one form, with every command printed
    ./instrumente/miss-grammatikdeckung.py --liste     the probe table, no runs
"""
import argparse
import hashlib
import os
import pathlib
import subprocess
import sys
import tempfile

W = pathlib.Path(__file__).resolve().parent.parent
GABBRO = W / "target" / "debug" / "gabbro"
CC_SCHALTER = ["-std=c11", "-Wall", "-Wextra", "-Werror"]
CC_STUFEN = ("-O0", "-O2")
CC_UMGEBUNG = dict(os.environ, LC_ALL="C", LANG="C", LANGUAGE="C")
FRIST = 60

# ---------------------------------------------------------------------------------------
# The hosts. A host is a program that CHECKS and EMITS on its own; `{X}` is where the
# variant's snippet goes and the base puts the empty string there.
# ---------------------------------------------------------------------------------------
HOST = {
    # A module with one pure function -- the cheapest thing that emits.
    "modul": "module p {{\n{X}\n}}\n",
    # Inside a function body.
    "rumpf": ("module p {{\n"
              "    fn f(a : u32 in 0 .. 100, b : u32 in 1 .. 100) -> u32 in 0 .. 100000\n"
              "        effects {{ pure }} costs <= 40 ops {{\n"
              "        let mut r : u32 in 0 .. 100000 = a;\n"
              "{X}\n"
              "        return r;\n"
              "    }}\n}}\n"),
    # A clause at a function head -- `{X}` sits between the signature and `effects`.
    "fnkopf": ("module p {{\n"
               "    fn f(a : u32) -> u32 {X} effects {{ pure }} costs <= 4 ops {{\n"
               "        return a;\n"
               "    }}\n}}\n"),
    # A clause at a function head AFTER `costs`.
    "fnschwanz": ("module p {{\n"
                  "    fn f(a : u32) -> u32 effects {{ pure }} costs <= 4 ops {X} {{\n"
                  "        return a;\n"
                  "    }}\n}}\n"),
    # A `table` body.
    "tabelle": ("module p {{\n"
                "    table T count 8 {{\n"
                "        slot {{ wert : u32, belegt : u32, }}\n"
                "{X}\n"
                "    }}\n}}\n"),
    # A clause on the `table` head, between the name and the brace.
    "tabellenkopf": ("module p {{\n"
                     "    const K : u32 = 4;\n"
                     "    table T {X} {{\n"
                     "        slot {{ wert : u32, belegt : u32, }}\n"
                     "    }}\n}}\n"),
    # A `device` body.
    "geraet": ("module p {{\n"
               "    opaque type Pa = u64;\n"
               "    device D(basis : Pa) at mmio {{\n"
               "        reg CTRL : u32 @0x0 class rw\n"
               "{X}\n"
               "    }}\n}}\n"),
    # A clause on a `reg` declaration.
    "reg": ("module p {{\n"
            "    opaque type Pa = u64;\n"
            "    device D(basis : Pa) at mmio {{\n"
            "        reg CTRL : u32 @0x0 class rw {X}\n"
            "    }}\n}}\n"),
    # A type in a `const` declaration -- `{X}` is the TYPE, `{V}` the value.
    # **A `static`, not a `const`.** A `const` lowers to `#define K 1u` -- typeless -- so
    # every integer width gives byte-identical C and every type would score `UNCOVERED`
    # for the host's reason and not the language's. *A host that cannot show the answer
    # is not a probe.* Measured 2026-09-07: `const K : u8` and `const K : u64` produce the
    # same C to the byte.
    "typ": ("module p {{\n"
            "    fn f(x : {X}) effects {{ pure }} costs <= 1 ops {{\n"
            "        return;\n"
            "    }}\n}}\n"),
    # An effect in an `effects` block. The base carries `pure` because an EMPTY list is
    # `P014` -- *"an EMPTY list is not `no effects`: the word for that is `pure`"*.
    "wirkung": ("module p {{\n"
                "    static mut Z : u32 = 0;\n"
                "    fn f() effects {{ reads Z{X} }} costs <= 2 ops {{\n"
                "        let q : u32 = Z;\n"
                "        return;\n"
                "    }}\n}}\n"),
    # A predicate in an `ensures` clause. The base carries one, because `ensures` demands a
    # `predlist` and an empty one does not parse.
    "praedikat": ("module p {{\n"
                  "    table T count 8 {{ slot {{ wert : u32, }} }}\n"
                  "    fn f(a : u32) -> u32 ensures result == a{X} "
                  "effects {{ pure }} costs <= 4 ops {{\n"
                  "        return a;\n"
                  "    }}\n}}\n"),
    # A predicate ALONE in an `ensures` clause -- for the forms that cannot stand second.
    "praedikat1": ("module p {{\n"
                   "    table T count 8 {{ slot {{ wert : u32, }} }}\n"
                   "    fn f(a : u32) -> u32 ensures {X} "
                   "effects {{ pure }} costs <= 4 ops {{\n"
                   "        return a;\n"
                   "    }}\n}}\n"),
    # An EXPRESSION -- `{X}` is the whole right-hand side of a `let`.
    # **The ranges are not decoration.** Without them `a + b` is `M101`/`M104` -- the
    # overflow obligation -- and every arithmetic form would score `REFUSES` for the host's
    # reason and not the language's. `b` starts at 1 so `/` and `%` clear `M102`.
    "ausdruck": ("module p {{\n"
                 "    fn f(a : u32 in 0 .. 100, b : u32 in 1 .. 100) -> u32 in 0 .. 100000\n"
                 "        effects {{ pure }} costs <= 9 ops {{\n"
                 "        let r : u32 in 0 .. 100000 = {X};\n"
                 "        return r;\n"
                 "    }}\n}}\n"),
    # A quantifier DOMAIN -- `{X}` is what stands after `forall i in`.
    "domaene": ("module p {{\n"
                "    table T count 8 {{ slot {{ wert : u32, naechst : u32, }} "
                "tree {{ parent naechst }} }}\n"
                "    static mut G : T = T;\n"
                "    spec fn q() -> bool = forall i in {X} : true;\n"
                "}}\n"),
    # A clause on an `atomic` declaration.
    "atomic": "module p {{\n    atomic A : u32 {X};\n}}\n",
    # A clause on a `static` declaration.
    "statisch": "module p {{\n    static K : u32 = 4 {X};\n}}\n",
    # A whole item at module level -- for item heads.
    "item": "module p {{\n{X}\n}}\n",
    # A loop body -- the retry/forever host, with a bound the `progress` witness can move.
    "schleife": ("module p {{\n"
                 "    fn f(a : u32 in 0 .. 100) -> u32 in 0 .. 100\n"
                 "        effects {{ pure }} costs <= 40 ops {{\n"
                 "        let mut r : u32 in 0 .. 100 = a;\n"
                 "        retry m {X} bounded 4 ops on_exceeded g {{ r = 0; }}\n"
                 "        return r;\n"
                 "    }}\n}}\n"),
    # A `traverse` clause -- `{X}` sits between `by unvisited` and the block.
    "traverse": ("module p {{\n"
                 "    table T count 8 {{ slot {{ wert : u32, }} }}\n"
                 "    static mut g : T = T;\n"
                 "    fn f() effects {{ reads g }} costs <= 80 ops {{\n"
                 "        traverse i over slots of g by unvisited {X} {{ }}\n"
                 "    }}\n}}\n"),
    # An `entry` clause -- `{X}` sits after `stack s`.
    "eintritt": ("module p {{\n"
                 "    fn h() effects {{ pure }} costs <= 1 ops {{ return; }}\n"
                 "    entry e arch x86_64 {{ regs in {{ }} regs out {{ }} preserves {{ }} "
                 "clobbers {{ }} stack s {X} dispatch p::h; }}\n}}\n"),
    # An `asm` body -- `{X}` sits after the instruction text.
    "asm": ("module p {{\n"
            "    raw fn g() effects {{ pure }} costs <= 1 ops arch x86_64 = "
            "asm {{ \"nop\" {X} }};\n}}\n"),
    # A `boot` step -- `{X}` is one whole step line.
    "boot": ("module p {{\n"
             "    static mut z : u32 = 0;\n"
             "    fn h() effects {{ pure }} costs <= 1 ops {{ return; }}\n"
             "    boot b arch x86_64 {{ {X} dispatch p::h; }}\n}}\n"),
    # A `check` clause -- `{X}` sits after `can_fail { }`.
    "check": ("module p {{\n"
              "    static mut Z : u32 = 0;\n"
              "    fn g() effects {{ pure }} costs <= 1 ops {{ return; }}\n"
              "    check c {{ claim \"the claim\" measures Z gates g can_fail {{ }} {X} }}\n"
              "}}\n"),
    # A function-POINTER type -- `{X}` sits inside the `fn(...)` type's contract.
    "fnptr": ("module p {{\n"
              "    type F = fn(x : u32) {X} effects {{ pure }} costs <= 1 ops;\n"
              "    fn f(k : F) effects {{ pure }} costs <= 1 ops {{ return; }}\n}}\n"),
}

# ---------------------------------------------------------------------------------------
# The probe table: form id -> (host, base snippet, variant snippet, [extra host fields])
# The id is the one `leite-grammatik.py --formen` prints, so the two registers join.
# ---------------------------------------------------------------------------------------
PROBEN = {}


NICHT = None   # sentinel: this file has no minimal host that isolates the form


def probe(kennung, host, basis, variante, **felder):
    PROBEN[kennung] = (host, basis, variante, felder)


# -- item heads: `{X}` is one whole declaration at module level -------------------------
_ITEM = {
    "module": "module q { const Z : u32 = 1; }",
    "use": "use q::r;",
    "type": "type Q = u32;",
    "opaque": "opaque type Q = u32;",
    "linear": "linear type Q = u32;",
    "tagged": "tagged type Q = u32;",
    "const": "const Q : u32 = 1;",
    "static": "static Q : u32 = 1;",
    "fn": "fn q() effects { pure } costs <= 1 ops { return; }",
    "spec": "spec fn q() -> bool = true;",
    "impl": "impl fn q() effects { pure } costs <= 1 ops { return; }",
    "raw": "raw fn q() effects { pure } costs <= 1 ops { return; }",
    "divergent": "divergent fn q() -> never effects { diverges } costs <= 1 ops { return; }",
    "prim": "prim fn q() effects { pure } costs <= 1 ops;",
    "extern": "extern fn q() effects { pure } costs <= 1 ops;",
    "atomic": "atomic Q : u32 seq;",
    "format": "format Q { a : u32, }",
    "table": "table Q count 4 { slot { wert : u32, } }",
    "reason": 'reason Q { Leer = 1 "empty" }',
    "state": "state Q { transition t { s : 0 -> 1 } }",
    "device": "opaque type Pa = u64;\n    device Q(basis : Pa) at mmio "
              "{ reg R : u32 @0x0 class rw }",
    "assume": 'assume Q "a claim about the machine" unfalsifiable "no probe can refute it";',
    "axiom": 'axiom Q() effects { pure } unfalsifiable "no probe can refute it";',
    "check": 'check Q { claim "the claim" measures Z gates g can_fail { } }',
    "lock": "static mut Z : u32 = 0;\n    lock Q protects { Z } rank 0;",
    "rcu": "static mut Z : u32 = 0;\n    rcu Q protects { Z };",
    "group": "static mut A : u32 = 0;\n    static mut B : u32 = 0;\n"
             "    group Q over { A, B };",
    "accumulates": "accumulates Q : u32 merge max per cpu 4;",
    "walk": "walk Q levels 4 { node : [u64; 512], down : d when true, leaf : true, }",
    "entry": "fn h() effects { pure } costs <= 1 ops { return; }\n"
             "    entry Q arch x86_64 { regs in { } regs out { } preserves { } "
             "clobbers { } stack s dispatch p::h; }",
    "entrust": "entrust Q at gast arch x86_64 { regs in { } stack s assume a; }",
    "boot": "fn h() effects { pure } costs <= 1 ops { return; }\n"
            "    boot Q arch x86_64 { dispatch p::h; }",
}
for _w, _s in _ITEM.items():
    probe(f"item.{_w}", "item", "", "    " + _s)
probe("item.pub", "item", "    const Q : u32 = 1;", "    pub const Q : u32 = 1;")
probe("item.when", "item", "    const Q : u32 = 1;", "    when TESTBUILD const Q : u32 = 1;")
# Lane 111 (`constdecl.[`, the const-table literal): the base holds a scalar
# const, the variant the table form -- the C gains the `static const` array,
# so the form scores CARRIES. The broken twin (a short literal) is refused by
# name (`K191`, gift 861), which the `gegenprobe` column carries.
probe("constdecl.[", "modul", "    const Q : u32 = 1;",
      "    const Q : [u32; 2] = [1, 2];")

# -- statement heads ---------------------------------------------------------------------
_STMT = {
    "let": "        let z : u32 = a;",
    "if": "        if a == b { r = 1; }",
    "match": "",          # needs a sum type -- probed with its own host below
    "return": "        return r;",
    "leave": "",          # only inside a loop with a mark
    "next": "",
    "traverse": "",
    "retry": "",
    "forever": "",
    "breaking": "",
    "narrow": "        narrow r to 0 .. 10 else { return 0; }",
    "observes": "",
    "locks": "",
}
probe("stmt.let", "rumpf", "", _STMT["let"])
probe("stmt.if", "rumpf", "", _STMT["if"])
probe("stmt.return", "rumpf", "", "        return b;")
probe("stmt.narrow", "rumpf", "", _STMT["narrow"])
probe("stmt.finite", "rumpf", "", "")           # filled below with a float host
probe("stmt.shared", "rumpf", "", "")
probe("stmt.match", "rumpf", "", "")
probe("stmt.locks", "rumpf", "", "")
probe("stmt.observes", "rumpf", "", "")
probe("stmt.traverse", "rumpf", "", "")
probe("stmt.retry", "rumpf", "",
      "        retry m bounded 4 ops on_exceeded g { r = r + 1; }")
probe("stmt.forever", "rumpf", "", "")
probe("stmt.breaking", "rumpf", "", "")
probe("stmt.leave", "rumpf", "", "")
probe("stmt.next", "rumpf", "", "")

# -- assignment operators ----------------------------------------------------------------
for _k, _op in (("=", "="), ("+=", "+="), ("-=", "-="), ("&=", "&="), ("|=", "|=")):
    probe(f"zuweisung_oder_ruf.{_k}", "rumpf", "        r = r;", f"        r {_op} b;")
probe("zuweisung_oder_ruf.(", "rumpf", "        r = r;", "        p::g(a);")
probe("zuweisung_oder_ruf.::", "rumpf", "        r = r;", "        p::g(a);")
probe("zuweisung_oder_ruf.publishes", "rumpf", "        r = r;", NICHT)

# -- expressions -------------------------------------------------------------------------
for _k, _e in (("+", "a + b"), ("-", "a - b")):
    probe(f"addexpr.{_k}", "ausdruck", "a", _e)
# PLAN-BITS section 4 (lane 88): the overflow operators ride at the precedence
# of their base operator. On the `ausdruck` host neither operand has an exact
# unsigned range, so the wrapping variants score REFUSES (M153) and the
# saturating one REFUSES (M154) -- both are carried verdicts: the checker has
# a sentence about the form. The accept direction is pinned by
# `crates/gabbro-check/tests/ueberlauf.rs`.
for _k, _e in (("+%", "a +% b"), ("-%", "a -% b"), ("+|", "a +| b")):
    probe(f"addexpr.{_k}", "ausdruck", "a", _e)
for _k, _e in (("*", "a * b"), ("/", "a / b"), ("%", "a % b")):
    probe(f"mulexpr.{_k}", "ausdruck", "a", _e)
probe("mulexpr.*%", "ausdruck", "a", "a *% b")
for _k, _e in (("&", "a & b"), ("|", "a | b"), ("^", "a ^ b"),
               ("<<", "a << 1"), (">>", "a >> 1")):
    probe(f"bitexpr.{_k}", "ausdruck", "a", _e)
probe("bitexpr.<<%", "ausdruck", "a", "a <<% b")
for _k, _e in (("!", "!(a == b)"), ("-", "0 - a"), ("~", "~a")):
    probe(f"unary.{_k}", "ausdruck", "a", _e)
probe("orexpr.||", "praedikat", "", " || true")
probe("andexpr.&&", "rumpf", "        if a == b { r = 1; }",
      "        if a == b && b == 1 { r = 1; }")
for _k in ("==", "!=", "<", "<=", ">", ">="):
    probe(f"cmpexpr.{_k}", "rumpf", "        if a == b { r = 1; }",
          f"        if a {_k} b {{ r = 1; }}")
probe("primary.(", "ausdruck", "a", "(a)")
probe("primary.true", "rumpf", "        if a == b { r = 1; }",
      "        if true { r = 1; }")
probe("primary.false", "rumpf", "        if a == b { r = 1; }",
      "        if false { r = 1; }")
probe("primary.intty", "ausdruck", "a", "u64::max")
probe("primary.::", "ausdruck", "a", "u64::max")
probe("primary.rounded", "modul", "    static F : f64 = 0.5;",
      "    static F : f64 = 0.1 rounded;")
probe("primary.Self", "ausdruck", "a", NICHT)
probe("primary.Some", "ausdruck", "a", NICHT)
probe("primary.None", "ausdruck", "a", NICHT)
probe("primary.old", "modul",
      "    fn f(a : ptr<normal, rw> u32) ensures true effects { writes a } costs <= 4 ops { return; }",
      "    fn f(a : ptr<normal, rw> u32) ensures a == old(a) effects { writes a } costs <= 4 ops { return; }")
probe("primary.result", "praedikat1", "true", "result == a")
probe("primary.sizeof", "ausdruck", "a", "sizeof(u32)")
probe("primary.lenof", "modul",
      "    static A : [u32; 4] = 0;\n    const N : u32 = 4;",
      "    static A : [u32; 4] = 0;\n    const N : u32 = lenof(A);")
probe("primary.aligned", "praedikat1", "true", "aligned(a, 4)")
probe("place_ab..", "modul",
      "    type S = { g : u32, };\n    fn f(s : S) -> u32 effects { pure } costs <= 2 ops { return 1; }",
      "    type S = { g : u32, };\n    fn f(s : S) -> u32 effects { pure } costs <= 2 ops { return s.g; }")
probe("place_ab.[", "modul",
      "    static A : [u32; 4] = 0;\n    fn f() -> u32 effects { reads A } costs <= 2 ops { return 1; }",
      "    static A : [u32; 4] = 0;\n    fn f() -> u32 effects { reads A } costs <= 2 ops { return A[1]; }")
probe("place_ab.->", "modul",
      "    type S = { g : u32, };\n    fn f(s : ptr<normal, r> S) -> u32 effects { reads s } costs <= 2 ops { return 1; }",
      "    type S = { g : u32, };\n    fn f(s : ptr<normal, r> S) -> u32 effects { reads s } costs <= 2 ops { return s->g; }")
probe("place.Self", "ausdruck", "a", NICHT)
probe("pfad.::", "ausdruck", "a", "u64::max")
probe("pfad.intty", "ausdruck", "a", "u64::max")

# -- effects -----------------------------------------------------------------------------
for _k, _e in (("reads", ", reads Z"), ("writes", ", writes Z"),
               ("locks", ", locks Z"), ("masks", ", masks irq"),
               ("allocs", ", allocs heap"), ("consumes", ", consumes Z"),
               ("publishes", ", publishes Z"), ("diverges", ", diverges")):
    probe(f"eff.{_k}", "wirkung", "", _e)
probe("eff.pure", "wirkung", "", "")               # the base IS `pure`
probe("eff.shared", "wirkung", "", ", locks shared Z")

# -- types -------------------------------------------------------------------------------
for _w in ("u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64"):
    probe(f"intty.{_w}", "typ", "u32", _w, V="1")
# PLAN-BITS §1: `uN`/`iN` sugar -- the storage width moves the C, the exact range
# moves the checks; each probes against the `u32` base of the `typ` host.
for _w in ("u1", "u13", "i37", "u64"):
    probe(f"intty.{_w}", "typ", "u32", _w, V="1")
probe("intty.in", "typ", "u32", "u32 in 0 .. 10", V="1")
probe("range...<", "typ", "u32 in 0 .. 10", "u32 in 0 ..< 10", V="1")
probe("typeexpr_innen.bool", "typ", "u32", "bool", V="true")
probe("typeexpr_innen.f32", "typ", "u32", "f32", V="1.5")
probe("typeexpr_innen.f64", "typ", "u32", "f64", V="1.5")
probe("typeexpr_innen.never", "typ", "u32", "never", V="1")
probe("typeexpr_innen.ptr", "typ", "u32", "ptr<normal, r> u32", V="1")
probe("typeexpr_innen.fn", "typ", "u32", "u32", V="1")
probe("typeexpr_innen.option", "typ", "u32", "u32", V="1")
probe("typeexpr_innen.Self", "typ", "u32", "u32", V="1")
probe("typeexpr_innen.[", "typ", "u32", "u32", V="1")
probe("typeexpr_innen.{", "typ", "u32", "u32", V="1")
probe("typeexpr_innen.intty", "typ", "bool", "u32", V="1")
probe("typeexpr_innen.in", "typ", "u32", "u32 in 0 .. 10", V="1")

# -- pointer spaces and rights -----------------------------------------------------------
for _w in ("normal", "mmio", "dma", "code", "boot", "port"):
    probe(f"space.{_w}", "typ", "ptr<normal, r> u32", f"ptr<{_w}, r> u32", V="1")
for _w in ("r", "w", "rw", "x"):
    probe(f"right.{_w}", "typ", "ptr<normal, r> u32", f"ptr<normal, {_w}> u32", V="1")
probe("right.own", "typ", "ptr<normal, r> u32", "ptr<normal, own> u32", V="1")
probe("right.@", "typ", "ptr<normal, own> u32", "ptr<normal, own@m> u32", V="1")
probe("rights.+", "typ", "ptr<normal, r> u32", "ptr<normal, r+w> u32", V="1")

# -- table body --------------------------------------------------------------------------
probe("table.const", "tabelle", "", "        const K : u32 = 4;")
probe("table.pub", "tabelle", "        const K : u32 = 4;",
      "        pub const K : u32 = 4;")
probe("table.slot", "tabelle", "", "")             # the host always carries one
probe("table.invariant", "tabelle", "",
      "        invariant i cost O(1) runs offline : true;")
probe("table.ops", "tabelle", "", "        ops insert, remove;")
probe("table.occupied", "tabelle", "", "        occupied belegt;")
probe("table.tree", "tabelle", "", "        tree { parent belegt }")
probe("table.count", "tabellenkopf", "", " count 8")
probe("table.backed", "tabellenkopf", " count 8", " count 8 backed K")
probe("treedecl.parent", "tabelle", "", "        tree { parent belegt }")
probe("treedecl.child", "tabelle", "", "        tree { child belegt }")
probe("treedecl.sibling", "tabelle", "", "        tree { sibling belegt }")
for _w in ("insert", "remove", "relabel"):
    probe(f"opnamen.{_w}", "tabelle", "", f"        ops {_w};")
probe("slotdecl.by", "tabelle", "", "")
probe("slottype.wrapping", "tabelle", "", "")
probe("slottype.intty", "tabelle", "", "")
probe("invariant.online", "tabelle", "        invariant i cost O(1) runs offline : true;",
      "        invariant i cost O(1) runs online : true;")
probe("invariant.by", "tabelle", "        invariant i cost O(1) runs offline : true;",
      "        invariant i cost O(1) runs offline by induction over slots of T : true;")

# -- device body -------------------------------------------------------------------------
probe("device.reg", "geraet", "", "")              # the host always carries one
probe("device.bank", "geraet", "",
      "        bank B at 0x10 stride 8 count 4 { reg S : u32 @0x0 class rw }")
probe("device.mirrors", "geraet", "", "")
probe("device.transition", "geraet", "", "        transition t { CTRL : 0 -> 1 }")
probe("device.(", "geraet", "", "")                # the host always carries parameters
for _w in ("r", "w", "rw", "w1c", "rc"):
    probe(f"regklasse.{_w}", "reg", "", "")
probe("regdecl.wrapping", "geraet", "        reg X : u32 @0x8 class rw",
      "        reg X : u32 @0x8 wrapping class rw")
probe("regdecl.fields", "geraet", "        reg X : u32 @0x8 class rw",
      "        reg X : u32 @0x8 class rw fields { A @0 }")
probe("regdecl.class", "geraet", "        reg X : u32 @0x8 class rw fields { A @0 }",
      "        reg X : u32 @0x8 class rw fields { A @0 class w1c }")
probe("regdecl.in", "geraet", "        reg X : u32 @0x8 class rw", NICHT)
probe("regdecl.requires", "geraet", "        reg X : u32 @0x8 class rw", NICHT)
probe("regdecl.else", "geraet", "        reg X : u32 @0x8 class rw", NICHT)
probe("transition.requires", "geraet", "        transition t { CTRL : 0 -> 1 }",
      "        transition t { CTRL : 0 -> 1 } requires true")
probe("transition.effects", "geraet", "        transition t { CTRL : 0 -> 1 }",
      "        transition t { CTRL : 0 -> 1 } effects { pure }")

# -- fn head clauses ---------------------------------------------------------------------
probe("fndecl.requires", "fnkopf", "", "requires a == a")
probe("fndecl.ensures", "fnkopf", "", "ensures result == a")
probe("fndecl.maintains", "fnkopf", "", "")
probe("fndecl.advances", "fnkopf", "", "")
probe("fndecl.retires", "fnkopf", "", "")
probe("fndecl.refines", "fnkopf", "", "")
probe("fndecl.or", "fnkopf", "", "")
probe("fndecl.->", "modul",
      "    fn f() effects { pure } costs <= 1 ops { return; }",
      "    fn f() -> u32 effects { pure } costs <= 1 ops { return 1; }")
probe("fndecl.effects", "modul",
      "    prim fn f() costs <= 1 ops;",
      "    prim fn f() effects { pure } costs <= 1 ops;")
probe("fndecl.costs", "modul",
      "    prim fn f() effects { pure };",
      "    prim fn f() effects { pure } costs <= 1 ops;")
probe("fndecl.decreases", "fnschwanz", "", "decreases a")
probe("fndecl.by", "fnschwanz", "", "by induction over threads")
probe("fndecl.section", "fnschwanz", "", 'section ".text.hot"')
probe("fndecl.arch", "fnschwanz", "", "arch x86_64")
probe("fndecl.when", "fnschwanz", "", "when TESTBUILD")
probe("fndecl.{", "modul",
      "    prim fn f() effects { pure } costs <= 1 ops;",
      "    fn f() effects { pure } costs <= 1 ops { return; }")
probe("fndecl.=", "modul",
      "    prim fn f() -> bool effects { pure } costs <= 1 ops;",
      "    spec fn f() -> bool = true;")
probe("fndecl.asm", "modul",
      "    prim fn f() effects { pure } costs <= 1 ops;",
      "    raw fn f() arch x86_64 effects { pure } costs <= 1 ops = asm { \"nop\" };")
for _w in ("spec", "const", "impl", "raw", "divergent", "prim", "extern"):
    probe(f"fndecl.{_w}", "modul",
          "    fn f() effects { pure } costs <= 1 ops { return; }",
          "    " + _ITEM[_w].replace("q(", "f(").replace(" q ", " f "))

# -- fn pointer type ---------------------------------------------------------------------
for _k in ("requires", "ensures", "effects", "costs", "->"):
    probe(f"fnptr.{_k}", "typ", "u32", "u32", V="1")

# -- predicates --------------------------------------------------------------------------
probe("orpred.||", "praedikat", "", " || true")
probe("andpred.&&", "praedikat", "", " && true")
probe("notpred.!", "praedikat1", "result == a", "!(result == a)")
probe("notpred.=>", "praedikat1", "result == a", "true => result == a")
probe("atompred.(", "praedikat1", "result == a", "(result == a)")
probe("atompred.forall", "praedikat1", "true", "forall i in threads : true")
probe("atompred.exists", "praedikat1", "true", "exists i in threads : true")
probe("atompred.in", "praedikat1", "true", "a in threads")
probe("atompred.reaches", "praedikat1", "true", NICHT)
for _k in ("slots", "chain", "descendants", "ancestors", "queue",
           "fields", "elems", "threads", "mappings"):
    probe(f"domain.{_k}", "domaene", "threads", "threads")

# -- the rest, hosted where they stand ---------------------------------------------------
probe("staticdecl.mut", "modul", "    static Z : u32 = 0;", "    static mut Z : u32 = 0;")
probe("staticdecl.section", "statisch", "", ' section ".data.q"')
probe("atomicdecl.seq", "atomic", "seq", "seq")
probe("atomicdecl.acquire", "atomic", "seq", "acquire")
probe("atomicdecl.release", "atomic", "seq", "release")
probe("atomicdecl.relaxed", "atomic", "seq", "relaxed")
probe("atomicdecl.publishes", "atomic", "seq", "publishes nothing seq")
probe("atomicdecl.observed", "atomic", "seq", NICHT)
probe("typedecl.opaque", "modul", "    type Q = u32;", "    opaque type Q = u32;")
probe("typedecl.linear", "modul", "    type Q = u32;", "    linear type Q = u32;")
probe("typedecl.ghost", "modul", "    linear type Q = u32;", "    linear ghost type Q;")
probe("typedecl.tagged", "modul", "    type Q = u32;", "    tagged type Q = u32;")
probe("typedecl.order", "modul", "    linear ghost type Q;",
      "    linear ghost type Q order { roh, mmu };")
probe("typedecl.=", "modul", "    linear ghost type Q;", "    type Q = u32;")
probe("typedecl.(", "modul", "    type Q = u32;", NICHT)
probe("field_innen.@", "modul", "    format F { a : u32, }",
      "    format F { a : u32 @0, }")
probe("field_innen.where", "modul", "    format F { a : u32, }",
      "    format F { a : u32 where a == a, }")
probe("field_innen.reserved", "modul", "    format F { a : u32, }",
      "    format F { a : u32 reserved, }")
probe("field_innen.offset_into", "modul", "    format F { a : u32, }", NICHT)
probe("fieldty.embeds", "modul", "    format F { a : u32, }",
      "    format F { a : u32 embeds [11:0], }")
probe("fieldty.scale", "modul", "    format F { a : u32 embeds [11:0], }",
      "    format F { a : u32 embeds [11:0] scale 4096, }")
probe("bitpos.[", "modul", "    format F { a : u32 @0, }", "    format F { a : u32 @[3:0], }")
probe("format.@", "modul", "    format F { a : u32, }", "    format F @version 2 { a : u32, }")
probe("format.endian", "modul", "    format F { a : u32, }",
      "    format F endian big { a : u32, }")
probe("format.little", "modul", "    format F endian big { a : u32, }",
      "    format F endian little { a : u32, }")
probe("reason.exhaustive", "modul", '    reason R { Leer = 1 "empty" }',
      '    reason R { Leer = 1 "empty" exhaustive }')
probe("verbund_oder_varianten.(", "modul", "    type Q = { A, B };", "    type Q = { A(u32), B };")
probe("matchstmt.(", "rumpf", "", "")
probe("ifstmt.if", "rumpf", "        if a == b { r = 1; }",
      "        if a == b { r = 1; } else if a == 0 { r = 2; }")
probe("ifstmt.else", "rumpf", "        if a == b { r = 1; }",
      "        if a == b { r = 1; } else { r = 2; }")
probe("letform.mut", "rumpf", "        let z : u32 = a;", "        let mut z : u32 = a;")
probe("letform.:", "rumpf", "        let z = a;", "        let z : u32 = a;")
probe("letform.else", "rumpf", "", "")
probe("letform.awaits", "rumpf", "", "")
probe("letform.exchange", "rumpf", "", "")
probe("letform.publishes", "rumpf", "", "")
probe("nutzlast.nothing", "atomic", "publishes nothing seq", "publishes nothing seq")
probe("traverse.unvisited", "rumpf", "", "")
probe("traverse.consuming", "rumpf", "", "")
probe("traverse.of", "rumpf", "", "")
probe("traverse.decreases", "rumpf", "", "")
probe("traverse.touches", "rumpf", "", "")
probe("schleifeninvariante.invariant", "rumpf",
      "        retry m bounded 4 ops on_exceeded g { r = r + 1; }",
      "        retry m bounded 4 ops on_exceeded g invariant true { r = r + 1; }")
probe("retry.until", "rumpf", "        retry m bounded 4 ops on_exceeded g { r = r + 1; }",
      "        retry m until true bounded 4 ops on_exceeded g { r = r + 1; }")
probe("retry.progress", "rumpf", "        retry m bounded 4 ops on_exceeded g { r = r + 1; }",
      "        retry m bounded 4 ops progress r on_exceeded g { r = r + 1; }")
probe("retry.effects", "rumpf", "        retry m bounded 4 ops on_exceeded g { r = r + 1; }",
      "        retry m bounded 4 ops on_exceeded g effects { pure } { r = r + 1; }")
probe("forever.progress", "rumpf", "", "")
probe("forever.leaves", "rumpf", "", "")
probe("xform.update", "rumpf", "", "")
probe("xform.bounded", "rumpf", "", "")
probe("xform.on_exceeded", "rumpf", "", "")
probe("lockdecl.held", "modul", "    static mut Z : u32 = 0;\n    lock L protects { Z } rank 0;",
      "    static mut Z : u32 = 0;\n    lock L protects { Z } rank 0 held <= 8 ops;")
probe("lockdecl.shared", "modul", "    static mut Z : u32 = 0;\n    lock L protects { Z } rank 0;",
      "    static mut Z : u32 = 0;\n    lock L protects { Z } rank 0 shared held <= 8 ops;")
probe("lockdecl.masks", "modul", "    static mut Z : u32 = 0;\n    lock L protects { Z } rank 0;",
      "    static mut Z : u32 = 0;\n    lock L protects { Z } rank 0 masks irq;")
probe("rcudecl.reclaims", "modul", "    static mut Z : u32 = 0;\n    rcu C protects { Z };",
      "    static mut Z : u32 = 0;\n    rcu C protects { Z } reclaims Z;")
probe("gruppedecl.{", "modul",
      "    static mut A : u32 = 0;\n    static mut B : u32 = 0;\n    group N over { A, B };",
      "    static mut A : u32 = 0;\n    static mut B : u32 = 0;\n"
      "    group N over { A, B } { invariant i cost O(1) runs offline : true; }")
for _w in ("max", "min", "add", "or", "and"):
    probe(f"accdecl.{_w}", "modul", "    accumulates Q : u32 merge max per cpu 4;",
          f"    accumulates Q : u32 merge {_w} per cpu 4;")
probe("accdecl.per", "modul", "    accumulates Q : u32 merge max;",
      "    accumulates Q : u32 merge max per cpu 4;")
probe("annahmeklasse.falsifier", "modul",
      '    assume A "a claim" unfalsifiable "no probe";',
      '    fn pr() -> bool effects { pure } costs <= 1 ops { return true; }\n'
      '    assume A "a claim" falsifier pr;')
probe("annahmeklasse.unfalsifiable", "modul",
      '    assume A "a claim" unfalsifiable "no probe";',
      '    assume A "a claim" unfalsifiable "no probe";')
probe("assume.arch", "modul", '    assume A "a claim" unfalsifiable "no probe";',
      '    assume A arch x86_64 "a claim" unfalsifiable "no probe";')
probe("axiom.->", "modul", '    axiom X() effects { pure } unfalsifiable "no probe";',
      '    axiom X() -> u32 effects { pure } unfalsifiable "no probe";')
probe("axiom.requires", "modul", '    axiom X() effects { pure } unfalsifiable "no probe";',
      '    axiom X(a : u32) requires a == a effects { pure } unfalsifiable "no probe";')
probe("check.floor", "modul", "", "")
probe("check.counterprobe", "modul", "", "")
probe("walkdecl.invariant", "modul",
      "    walk Q levels 4 { node : [u64; 512], down : d when true, leaf : true, }",
      "    walk Q levels 4 { node : [u64; 512], down : d when true, leaf : true, "
      "invariant i cost O(1) runs offline : true; }")
probe("entrydecl.vector", "modul", "", "")
probe("entrydecl.via", "modul", "", "")
probe("entrydecl.per", "modul", "", "")
probe("entrydecl.ist", "modul", "", "")
probe("entrydecl.nested", "modul", "", "")
probe("entrydecl.never", "modul", "", "")
probe("entrydecl.masked", "modul", "", "")
probe("entrydecl.bounded", "modul", "", "")
probe("bootdecl.step", "modul", "", "")
probe("bootdecl.(", "modul", "", "")
probe("bootdecl.::", "modul", "", "")
probe("asmrumpf.in", "modul", "", "")
probe("asmrumpf.out", "modul", "", "")
probe("asmrumpf.clobbers", "modul", "", "")
probe("asmops.result", "modul", "", "")
probe("typname_als_ident.Self", "modul", "    format F { a : u32, }", NICHT)
probe("typ_oder_ort.{", "ausdruck", "a", NICHT)
probe("typ_oder_ort.intty", "ausdruck", "a", "sizeof(u32)")


def lauf(argv, eingabe=None):
    try:
        p = subprocess.run(argv, capture_output=True, text=True, timeout=FRIST,
                           input=eingabe, env=CC_UMGEBUNG, cwd=W)
        return p.returncode, p.stdout, p.stderr
    except subprocess.TimeoutExpired:
        return 124, "", "TIMEOUT"


def uebersetzt(c):
    """Does this C pass `cc -Werror` at BOTH levels? -> (ok, first message)."""
    for stufe in CC_STUFEN:
        rc, _, err = lauf(["cc", *CC_SCHALTER, stufe, "-c", "-x", "c", "-", "-o", "/dev/null"], c)
        if rc != 0:
            return False, f"{stufe} {err.strip().splitlines()[0] if err.strip() else '?'}"
    return True, ""


def messe(text):
    """One program -> everything the four runs say about it."""
    with tempfile.NamedTemporaryFile("w", suffix=".gab", dir="/tmp", delete=False) as f:
        f.write(text)
        pfad = f.name
    try:
        rc_p, aus_p, err_p = lauf([str(GABBRO), "pruefe", pfad])
        angenommen = rc_p == 0
        rc_e, c, err_e = lauf([str(GABBRO), "emit", pfad])
        c001 = "C001" in (c + err_e)
        gesenkt = rc_e == 0 and not c001
        cc_ok, cc_msg = uebersetzt(c) if gesenkt and c.strip() else (False, "no C")
        rc_o, aus_o, _ = lauf([str(GABBRO), "pflichten", pfad])
        pflichten = sum(1 for z in aus_o.splitlines() if z.startswith("obligation\t"))
        codes = sorted({z.split("[")[1].split("]")[0]
                        for z in (aus_p + err_p).splitlines()
                        if z.startswith("error: [") or z.startswith("hint: [")})
        return {
            "angenommen": angenommen, "codes": codes,
            "gesenkt": gesenkt, "c001": c001,
            "c": c, "c_hash": hashlib.sha256(c.encode()).hexdigest()[:12],
            "cc": cc_ok, "cc_msg": cc_msg,
            "pflichten": pflichten,
            "emit_meldung": (err_e + c).strip().splitlines()[:1],
        }
    finally:
        os.unlink(pfad)


def prueferworte():
    """The words a CHECKER ERROR names -- READ out of the grammar table, not copied."""
    import contextlib
    import importlib.util
    import io
    spec = importlib.util.spec_from_file_location(
        "tafel", W / "instrumente" / "pruefe-grammatiktafel.py")
    mod = importlib.util.module_from_spec(spec)
    alt = sys.argv
    sys.argv = ["x", "--probe"]
    try:
        with contextlib.redirect_stdout(io.StringIO()):
            spec.loader.exec_module(mod)
    except SystemExit:
        pass
    finally:
        sys.argv = alt
    return mod.prueferworte()[0]


PRUEFERWORTE = None


def urteil(b, v, term=""):
    """The verdict, and the reason beside it."""
    if not v["angenommen"]:
        return "REFUSES", "checker: " + ",".join(v["codes"])
    if v["c001"]:
        return "REFUSES", "emitter: C001"
    if not v["gesenkt"]:
        return "REFUSES", "emit failed without C001"
    if not v["cc"]:
        return "NICHT-C", v["cc_msg"]
    if v["pflichten"] > b["pflichten"]:
        return "DEMANDS", f"pflichten {b['pflichten']} -> {v['pflichten']}"
    if v["c_hash"] != b["c_hash"]:
        return "CARRIES", f"C differs ({b['c_hash']} -> {v['c_hash']})"
    if term and term in PRUEFERWORTE:
        return "GUARDS", "no C of its own -- but a checker error text names the word"
    return "UNCOVERED", "C byte-identical, no obligation, no checker error names it"


def baue(kennung):
    host, basis, variante, felder = PROBEN[kennung]
    if variante is NICHT:
        return None, None
    vorlage = HOST[host]
    f = dict(felder)
    return vorlage.format(X=basis, **f), vorlage.format(X=variante, **f)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--probe", action="store_true")
    ap.add_argument("--nur")
    ap.add_argument("--liste", action="store_true")
    ap.add_argument("--tsv")
    args = ap.parse_args()

    if args.liste:
        for k in sorted(PROBEN):
            bt, vt = baue(k)
            if bt is None:
                print(f"=== {k}\n--- NO HOST\n")
                continue
            print(f"=== {k}\n--- base\n{bt}--- variant\n{vt}")
        return 0

    if not GABBRO.exists():
        print(f"ABBRUCH: `{GABBRO}` is not built -- NOTHING was measured, "
              "neither yes nor no. `cargo build` first.")
        return 2
    global PRUEFERWORTE
    PRUEFERWORTE = prueferworte()
    if args.probe:
        schlecht = sprechprobe()
        if schlecht:
            print(f"== BEFUND: {schlecht} Richtung(en) der Sprechprobe halten NICHT ==")
            return 1
        print("== SPRECHPROBE: alle fuenf Richtungen halten ==")
        return 0
    kennungen = [args.nur] if args.nur else sorted(PROBEN)
    if args.nur and args.nur not in PROBEN:
        print(f"ABBRUCH: `{args.nur}` is not in the probe table -- nothing was measured.")
        return 2

    zeilen, zaehler = [], {}
    for k in kennungen:
        bt, vt = baue(k)
        # **A pair that is not a pair measures nothing, and says so.** Where this file has
        # no minimal host that isolates the form, base and variant come out identical --
        # and an identical pair would score `UNCOVERED` for the wrong reason. It is counted
        # in the denominator all the same: *a denominator that drops what could not be
        # measured is `W25`.*
        if bt is None or bt == vt:
            zaehler["NOT-PROBED"] = zaehler.get("NOT-PROBED", 0) + 1
            zeilen.append((k, "NOT-PROBED", "no minimal host isolates this form"))
            print(f"{k:<44} {'NOT-PROBED':<10} no minimal host isolates this form")
            continue
        b, v = messe(bt), messe(vt)
        if not b["angenommen"]:
            u, grund = "BASE-RED", "the base program itself does not check: " + ",".join(b["codes"])
        # **A base the emitter already refuses measures nothing.** With `C001` on both sides
        # the difference is zero for the HOST's reason, and reporting `REFUSES` would put the
        # host's refusal on the form's name. Measured 2026-09-07: `stmt.traverse` read as
        # *"the emitter refuses `traverse`"* when the refusal was the `static mut g : T`
        # beside it. *A differential whose base is already at the floor has no direction.*
        elif b["c001"]:
            u, grund = "BASIS-C001", "the base program is already refused by the emitter"
        else:
            u, grund = urteil(b, v, k.split(".", 1)[-1])
        zaehler[u] = zaehler.get(u, 0) + 1
        zeilen.append((k, u, grund))
        if args.nur:
            print(f"--- base\n{bt}--- variant\n{vt}")
            for name, m in (("base", b), ("variant", v)):
                print(f"{name}: accepted={m['angenommen']} codes={m['codes']} "
                      f"lowered={m['gesenkt']} C001={m['c001']} cc={m['cc']} "
                      f"obligations={m['pflichten']} C={m['c_hash']}")
                if m["cc_msg"]:
                    print(f"      cc: {m['cc_msg']}")
        print(f"{k:<44} {u:<10} {grund}")

    print()
    ganz = len(kennungen)
    for u in sorted(zaehler):
        print(f"   {u:<12} {zaehler[u]:>4}   {100.0 * zaehler[u] / ganz:5.1f} % of {ganz}")
    # **The headline, and its denominator is stated with it** (`W25`). `NOT-PROBED` and
    # `BASE-RED` stay in the denominator: they are forms this file could not measure, not
    # forms the language does not have.
    traegt = zaehler.get("CARRIES", 0) + zaehler.get("GUARDS", 0)
    nutzer = zaehler.get("DEMANDS", 0) + zaehler.get("REFUSES", 0) + zaehler.get("UNCOVERED", 0)
    gemessen = (ganz - zaehler.get("NOT-PROBED", 0) - zaehler.get("BASE-RED", 0)
                - zaehler.get("BASIS-C001", 0))
    print(f"\n== of {ganz} derived forms, {gemessen} were measured and "
          f"{ganz - gemessen} could not be ==")
    print(f"   the LANGUAGE carries  {traegt:>4}  ({100.0 * traegt / gemessen:.1f} % of the "
          f"{gemessen} measured, {100.0 * traegt / ganz:.1f} % of all {ganz})")
    print(f"   the USER carries      {nutzer:>4}  ({100.0 * nutzer / gemessen:.1f} % of the "
          f"{gemessen} measured)")
    print("   -- CARRIES + GUARDS against DEMANDS + REFUSES + UNCOVERED; `NICHT-C` is "
          "neither and is printed above")
    if args.tsv:
        pathlib.Path(args.tsv).write_text(
            "".join(f"{k}\t{u}\t{g}\n" for k, u, g in zeilen))
    print()
    schlecht = sprechprobe()
    if schlecht:
        print(f"== BEFUND: {schlecht} Richtung(en) der Sprechprobe halten NICHT -- "
              "die Tafel darueber ist damit UNGEDECKT ==")
        return 1
    return 0



# ============ probes added 2026-09-07 to close the `NOT-PROBED` column =============
# Every one of these replaces an entry that had no minimal host. The originals stay above
# and are overwritten here, so the diff shows what was closed and when.

# -- the retry host: the base overflowed (`M101`) and had no progress witness (`S007`) --
probe("retry.until", "schleife", "", "until true")
probe("retry.progress", "schleife", "", "progress r")
probe("retry.effects", "schleife", "", "effects { pure }")
probe("schleifeninvariante.invariant", "schleife", "", "invariant true")
probe("stmt.retry", "rumpf", "",
      "        retry m bounded 4 ops on_exceeded g { r = 0; }")

# -- `traverse` and its clauses --------------------------------------------------------
probe("stmt.traverse", "modul",
      "    table T count 8 { slot { wert : u32, } }\n    static mut g : T = T;\n"
      "    fn f() effects { reads g } costs <= 80 ops { return; }",
      "    table T count 8 { slot { wert : u32, } }\n    static mut g : T = T;\n"
      "    fn f() effects { reads g } costs <= 80 ops {\n"
      "        traverse i over slots of g by unvisited { }\n    }")
probe("traverse.unvisited", "traverse", "", "")
probe("traverse.consuming", "modul",
      "    table T count 8 { slot { wert : u32, } }\n    static mut g : T = T;\n"
      "    fn f() effects { reads g } costs <= 80 ops {\n"
      "        traverse i over slots of g by unvisited { }\n    }",
      "    table T count 8 { slot { wert : u32, } }\n    static mut g : T = T;\n"
      "    fn f() effects { reads g } costs <= 80 ops {\n"
      "        traverse i over slots of g by consuming { }\n    }")
probe("traverse.decreases", "traverse", "", "decreases 1")
probe("traverse.touches", "traverse", "", "touches reads g")
probe("traverse.of", "modul",
      "    table T count 8 { slot { wert : u32, } }\n    static mut g : T = T;\n"
      "    fn f() effects { reads g } costs <= 80 ops {\n"
      "        traverse i over slots of g by unvisited { }\n    }",
      "    table T count 8 { slot { wert : u32, } }\n    static mut g : T = T;\n"
      "    fn f() effects { reads g } costs <= 80 ops {\n"
      "        traverse i of g over slots of g by unvisited { }\n    }")

# -- the nine quantifier domains -------------------------------------------------------
_DOM = {
    "slots": "slots of g", "chain": "chain(naechst, naechst) in g",
    "descendants": "descendants of g", "ancestors": "ancestors of g",
    "queue": "queue g", "fields": "fields of T", "elems": "elems of g",
    "threads": "threads", "mappings": "mappings of g",
}
for _k, _d in _DOM.items():
    probe(f"domain.{_k}", "domaene", "threads", _d)

# -- the five register classes ---------------------------------------------------------
for _k in ("r", "w", "rw", "w1c", "rc"):
    probe(f"regklasse.{_k}", "geraet", "        reg X : u32 @0x8 class rw",
          f"        reg X : u32 @0x8 class {_k}")
probe("right.r", "typ", "ptr<normal, w> u32", "ptr<normal, r> u32")
probe("space.normal", "typ", "ptr<mmio, r> u32", "ptr<normal, r> u32")

# -- the type forms --------------------------------------------------------------------
probe("typeexpr_innen.[", "typ", "u32", "[u32; 4]")
probe("typeexpr_innen.{", "typ", "u32", "{ g : u32, }")
probe("typeexpr_innen.option", "modul",
      "    table T count 4 { slot { wert : u32, } }\n"
      "    fn f(x : index into T) effects { pure } costs <= 1 ops { return; }",
      "    table T count 4 { slot { wert : u32, } }\n"
      "    fn f(x : option index into T) effects { pure } costs <= 1 ops { return; }")
probe("typeexpr_innen.index", "modul",
      "    table T count 4 { slot { wert : u32, } }\n"
      "    fn f(x : u32) effects { pure } costs <= 1 ops { return; }",
      "    table T count 4 { slot { wert : u32, } }\n"
      "    fn f(x : index into T) effects { pure } costs <= 1 ops { return; }")
probe("typeexpr_innen.fn", "modul",
      "    type F = u32;",
      "    type F = fn(x : u32) effects { pure } costs <= 1 ops;")
probe("typeexpr_innen.Self", "modul",
      "    type S = { g : u32, };", "    type S = { g : ptr<normal, r> Self, };")
probe("typedecl.(", "modul", "    type Q = u32;", "    type Q(u32) = u32;")
probe("slottype.wrapping", "tabelle", "", NICHT)
probe("slottype.intty", "modul",
      "    table T count 4 { slot { wert : bool, } }",
      "    table T count 4 { slot { wert : u32, } }")
probe("intty.u32", "typ", "u64", "u32")
probe("cmpexpr.==", "rumpf", "        if a < b { r = 1; }", "        if a == b { r = 1; }")

# -- statements ------------------------------------------------------------------------
probe("stmt.match", "modul",
      "    tagged type K = { A, B };\n"
      "    fn f(k : K) effects { pure } costs <= 4 ops { return; }",
      "    tagged type K = { A, B };\n"
      "    fn f(k : K) effects { pure } costs <= 4 ops {\n"
      "        match k { A => { return; } B => { return; } }\n    }")
probe("matchstmt.(", "modul",
      "    tagged type K = { A(u32), B };\n"
      "    fn f(k : K) effects { pure } costs <= 4 ops {\n"
      "        match k { A => { return; } B => { return; } }\n    }",
      "    tagged type K = { A(u32), B };\n"
      "    fn f(k : K) effects { pure } costs <= 4 ops {\n"
      "        match k { A(v) => { return; } B => { return; } }\n    }")
probe("stmt.locks", "modul",
      "    static mut Z : u32 = 0;\n    lock L protects { Z } rank 0;\n"
      "    fn f() effects { pure } costs <= 8 ops { return; }",
      "    static mut Z : u32 = 0;\n    lock L protects { Z } rank 0;\n"
      "    fn f() effects { locks L, writes Z } costs <= 8 ops {\n"
      "        locks L { Z = 1; }\n    }")
probe("stmt.shared", "modul",
      "    static mut Z : u32 = 0;\n    lock L protects { Z } rank 0;\n"
      "    fn f() effects { locks L, reads Z } costs <= 8 ops {\n"
      "        locks L { let q : u32 = Z; }\n    }",
      "    static mut Z : u32 = 0;\n    lock L protects { Z } rank 0;\n"
      "    fn f() effects { locks shared L, reads Z } costs <= 8 ops {\n"
      "        locks shared L { let q : u32 = Z; }\n    }")
probe("stmt.finite", "modul",
      "    fn f(x : f64) effects { pure } costs <= 8 ops { return; }",
      "    fn f(x : f64) effects { pure } costs <= 8 ops {\n"
      "        narrow x to finite else { return; }\n    }")
probe("stmt.forever", "modul",
      "    fn f() -> never effects { diverges } costs <= 8 ops { return; }",
      "    fn f() -> never effects { diverges } costs <= 8 ops {\n"
      "        forever m per_pass bounded 4 ops on_exceeded g effects { pure } { }\n    }")
probe("stmt.leave", "modul",
      "    fn f() -> never effects { diverges } costs <= 8 ops {\n"
      "        forever m per_pass bounded 4 ops on_exceeded g effects { pure } { }\n    }",
      "    fn f() -> never effects { diverges } costs <= 8 ops {\n"
      "        forever m per_pass bounded 4 ops on_exceeded g effects { pure } "
      "{ leave m; }\n    }")
probe("stmt.next", "modul",
      "    fn f() -> never effects { diverges } costs <= 8 ops {\n"
      "        forever m per_pass bounded 4 ops on_exceeded g effects { pure } { }\n    }",
      "    fn f() -> never effects { diverges } costs <= 8 ops {\n"
      "        forever m per_pass bounded 4 ops on_exceeded g effects { pure } "
      "{ next m; }\n    }")
probe("forever.progress", "modul",
      "    fn f() -> never effects { diverges } costs <= 8 ops {\n"
      "        forever m per_pass bounded 4 ops on_exceeded g effects { pure } { }\n    }",
      "    fn f() -> never effects { diverges } costs <= 8 ops {\n"
      "        forever m per_pass bounded 4 ops on_exceeded g effects { pure } "
      "progress q { }\n    }")
probe("forever.leaves", "modul",
      "    fn f() -> never effects { diverges } costs <= 8 ops {\n"
      "        forever m per_pass bounded 4 ops on_exceeded g effects { pure } { }\n    }",
      "    fn f() -> never effects { diverges } costs <= 8 ops {\n"
      "        forever m per_pass bounded 4 ops on_exceeded g effects { pure } "
      "leaves inv { }\n    }")
probe("stmt.breaking", "modul",
      "    table T count 4 { slot { wert : u32, } invariant inv cost O(1) runs offline : true; }\n"
      "    static mut g : T = T;\n"
      "    fn f() effects { writes g } costs <= 8 ops { return; }",
      "    table T count 4 { slot { wert : u32, } invariant inv cost O(1) runs offline : true; }\n"
      "    static mut g : T = T;\n"
      "    fn f() effects { writes g } costs <= 8 ops { breaking inv { } }")
probe("stmt.observes", "modul",
      "    rcu R protects { };\n"
      "    fn f() effects { pure } costs <= 8 ops { return; }",
      "    rcu R protects { };\n"
      "    fn f() effects { pure } costs <= 8 ops { observes R { } }")

# -- `let` in its four shapes ----------------------------------------------------------
probe("letform.else", "modul",
      "    reason R { Leer = 1 \"empty\" }\n"
      "    prim fn q() -> u32 or R effects { pure } costs <= 1 ops;\n"
      "    fn f() effects { pure } costs <= 8 ops { return; }",
      "    reason R { Leer = 1 \"empty\" }\n"
      "    prim fn q() -> u32 or R effects { pure } costs <= 1 ops;\n"
      "    fn f() effects { pure } costs <= 8 ops {\n"
      "        let x = q() else (e) { return; }\n        return;\n    }")
probe("letform.awaits", "modul",
      "    atomic A : u32 publishes { Z } release;\n    static mut Z : u32 = 0;\n"
      "    fn f() effects { reads A } costs <= 8 ops { return; }",
      "    atomic A : u32 publishes { Z } release;\n    static mut Z : u32 = 0;\n"
      "    fn f() effects { reads A } costs <= 8 ops {\n"
      "        let x : u32 = A awaits { Z };\n        return;\n    }")
probe("letform.exchange", "modul",
      "    atomic A : u32 seq;\n"
      "    fn f() effects { reads A } costs <= 8 ops { return; }",
      "    atomic A : u32 seq;\n"
      "    fn f() effects { writes A } costs <= 8 ops {\n"
      "        let x : u32 = A exchange 1 when true returns r;\n        return;\n    }")
probe("letform.publishes", "modul",
      "    atomic A : u32 publishes { Z } release;\n    static mut Z : u32 = 0;\n"
      "    fn f() effects { writes A } costs <= 8 ops {\n"
      "        let x : u32 = A exchange 1 when true returns r;\n        return;\n    }",
      "    atomic A : u32 publishes { Z } release;\n    static mut Z : u32 = 0;\n"
      "    fn f() effects { writes A, publishes Z } costs <= 8 ops {\n"
      "        let x : u32 = A exchange 1 when true returns r publishes { Z };\n"
      "        return;\n    }")
probe("zuweisung_oder_ruf.publishes", "modul",
      "    atomic A : u32 publishes { Z } release;\n    static mut Z : u32 = 0;\n"
      "    fn f() effects { writes A } costs <= 8 ops { A = 1; }",
      "    atomic A : u32 publishes { Z } release;\n    static mut Z : u32 = 0;\n"
      "    fn f() effects { writes A, publishes Z } costs <= 8 ops "
      "{ A = 1 publishes { Z }; }")
probe("nutzlast.nothing", "modul",
      "    atomic A : u32 publishes { Z } release;\n    static mut Z : u32 = 0;",
      "    atomic A : u32 publishes nothing release;\n    static mut Z : u32 = 0;")
probe("xform.update", "modul",
      "    atomic A : u32 seq;\n"
      "    fn f() effects { writes A } costs <= 8 ops {\n"
      "        let x : u32 = A exchange 1 when true returns r;\n        return;\n    }",
      "    atomic A : u32 seq;\n"
      "    fn f() effects { writes A } costs <= 40 ops {\n"
      "        let x : u32 = A exchange update(v) { v = 1; }\n        return;\n    }")
probe("xform.bounded", "modul",
      "    atomic A : u32 seq;\n"
      "    fn f() effects { writes A } costs <= 40 ops {\n"
      "        let x : u32 = A exchange update(v) { v = 1; }\n        return;\n    }",
      "    atomic A : u32 seq;\n"
      "    fn f() effects { writes A } costs <= 40 ops {\n"
      "        let x : u32 = A exchange update(v) bounded 4 ops { v = 1; }\n"
      "        return;\n    }")
probe("xform.on_exceeded", "modul",
      "    atomic A : u32 seq;\n"
      "    fn f() effects { writes A } costs <= 40 ops {\n"
      "        let x : u32 = A exchange update(v) bounded 4 ops { v = 1; }\n"
      "        return;\n    }",
      "    atomic A : u32 seq;\n"
      "    fn f() effects { writes A } costs <= 40 ops {\n"
      "        let x : u32 = A exchange update(v) bounded 4 ops on_exceeded g "
      "{ v = 1; }\n        return;\n    }")

# -- device / table / atomic / fn clauses ------------------------------------------------
probe("device.reg", "modul",
      "    opaque type Pa = u64;\n    device D(basis : Pa) at mmio { }",
      "    opaque type Pa = u64;\n"
      "    device D(basis : Pa) at mmio { reg CTRL : u32 @0x0 class rw }")
probe("device.(", "modul",
      "    device D at mmio { reg CTRL : u32 @0x0 class rw }",
      "    opaque type Pa = u64;\n"
      "    device D(basis : Pa) at mmio { reg CTRL : u32 @0x0 class rw }")
probe("device.mirrors", "geraet", "        reg SHADOW : u32 @0x8 class w",
      "        reg SHADOW : u32 @0x8 class w\n        mirrors SHADOW from CTRL;")
probe("regdecl.in", "modul",
      "    opaque type Pa = u64;\n    linear ghost type St order { setup, live };\n"
      "    device D(basis : Pa) at mmio { reg X : u32 @0x0 class rw }",
      "    opaque type Pa = u64;\n    linear ghost type St order { setup, live };\n"
      "    device D(basis : Pa) at mmio { reg X : u32 @0x0 class rw in setup, r in live }")
probe("regdecl.requires", "geraet", "        reg X : u32 @0x8 class rw",
      "        reg X : u32 @0x8 class rw requires true")
probe("regdecl.else", "modul",
      "    opaque type Pa = u64;\n    reason R { Leer = 1 \"empty\" }\n"
      "    device D(basis : Pa) at mmio { reg X : u32 @0x0 class rw requires true }",
      "    opaque type Pa = u64;\n    reason R { Leer = 1 \"empty\" }\n"
      "    device D(basis : Pa) at mmio "
      "{ reg X : u32 @0x0 class rw requires true else R::Leer }")
probe("table.slot", "modul", "    table T count 4 { }",
      "    table T count 4 { slot { wert : u32, } }")
probe("slotdecl.by", "modul",
      "    table T count 4 { slot { wert : u32, } ops insert; occupied wert; }",
      "    table T count 4 { slot { wert : u32 by ops, } ops insert; occupied wert; }")
probe("atomicdecl.seq", "atomic", "", "seq")
probe("atomicdecl.observed", "modul",
      "    atomic A : u32 seq;\n"
      "    assume S \"the device reads it\" unfalsifiable \"no probe can refute it\";",
      "    atomic A : u32 seq observed by S;\n"
      "    assume S \"the device reads it\" unfalsifiable \"no probe can refute it\";")
probe("annahmeklasse.unfalsifiable", "modul",
      "    fn pr() -> bool effects { pure } costs <= 1 ops { return true; }\n"
      "    assume A \"a claim\" falsifier pr;",
      "    assume A \"a claim\" unfalsifiable \"no probe can refute it\";")
probe("accdecl.max", "modul", "    accumulates Q : u32 merge min per cpu 4;",
      "    accumulates Q : u32 merge max per cpu 4;")
probe("fndecl.maintains", "modul",
      "    table T count 4 { slot { wert : u32, } "
      "invariant inv cost O(1) runs offline : true; }\n"
      "    static mut g : T = T;\n"
      "    fn f() effects { writes g } costs <= 4 ops { return; }",
      "    table T count 4 { slot { wert : u32, } "
      "invariant inv cost O(1) runs offline : true; }\n"
      "    static mut g : T = T;\n"
      "    fn f() maintains inv effects { writes g } costs <= 4 ops { return; }")
probe("fndecl.or", "modul",
      "    reason R { Leer = 1 \"empty\" }\n"
      "    prim fn f() -> u32 effects { pure } costs <= 1 ops;",
      "    reason R { Leer = 1 \"empty\" }\n"
      "    prim fn f() -> u32 or R effects { pure } costs <= 1 ops;")
probe("fndecl.refines", "modul",
      "    spec fn s() -> bool = true;\n"
      "    impl fn f() effects { pure } costs <= 1 ops { return; }",
      "    spec fn s() -> bool = true;\n"
      "    impl fn f() refines p::s effects { pure } costs <= 1 ops { return; }")
probe("fndecl.advances", "modul",
      "    linear ghost type St order { roh, mmu };\n"
      "    fn f() effects { pure } costs <= 1 ops { return; }",
      "    linear ghost type St order { roh, mmu };\n"
      "    fn f() advances roh -> mmu effects { pure } costs <= 1 ops { return; }")
probe("fndecl.retires", "modul",
      "    linear ghost type St order { roh, mmu };\n"
      "    fn f() effects { pure } costs <= 1 ops { return; }",
      "    linear ghost type St order { roh, mmu };\n"
      "    fn f() retires t from boot unfalsifiable \"no probe can refute it\" "
      "effects { pure } costs <= 1 ops { return; }")
probe("fndecl.effects", "modul",
      "    prim fn f() effects { pure } costs <= 1 ops;",
      "    prim fn f() effects { diverges } costs <= 1 ops;")
probe("field_innen.offset_into", "modul",
      "    format F { a : u32, }",
      "    format F { a : u32 offset_into Self, }")
probe("typname_als_ident.Self", "modul",
      "    format F { a : u32, }", "    format F { a : u32 offset_into Self, }")
probe("gruppedecl.{", "modul",
      "    table A count 4 { slot { w : u32, } }\n    table B count 4 { slot { w : u32, } }\n"
      "    static mut x : A = A;\n    static mut y : B = B;\n"
      "    group N over { x, y };",
      "    table A count 4 { slot { w : u32, } }\n    table B count 4 { slot { w : u32, } }\n"
      "    static mut x : A = A;\n    static mut y : B = B;\n"
      "    group N over { x, y } { invariant i cost O(1) runs offline : true; }")

# -- the function-POINTER contract -------------------------------------------------------
probe("fnptr.->", "modul",
      "    type F = fn(x : u32) effects { pure } costs <= 1 ops;",
      "    type F = fn(x : u32) -> u32 effects { pure } costs <= 1 ops;")
probe("fnptr.requires", "fnptr", "", "requires x == x")
probe("fnptr.ensures", "fnptr", "", "ensures true")
probe("fnptr.effects", "modul",
      "    type F = fn(x : u32) effects { pure } costs <= 1 ops;", NICHT)
probe("fnptr.costs", "modul",
      "    type F = fn(x : u32) effects { pure } costs <= 1 ops;", NICHT)

# -- asm, boot, entry, check ---------------------------------------------------------------
probe("asmrumpf.in", "asm", "", "in { }")
probe("asmrumpf.out", "asm", "", "out { }")
probe("asmrumpf.clobbers", "asm", "", "clobbers { }")
probe("asmops.result", "asm", "out { }", "out { result : \"=a\" }")
probe("bootdecl.step", "boot", "", "step z = 1;")
probe("bootdecl.(", "boot", "step z = 1;", "step h();")
probe("bootdecl.::", "boot", "step z = 1;", "step p::h();")
for _k, _c in (("vector", "vector 0x20"), ("via", "via gate"), ("per", "per cpu"),
               ("ist", "ist 1"), ("nested", "nested never"), ("never", "nested never"),
               ("masked", "nested masked"), ("bounded", "nested bounded 2")):
    probe(f"entrydecl.{_k}", "eintritt", "", _c)
probe("check.floor", "check", "", "floor true")
probe("check.counterprobe", "check", "", "counterprobe \"the probe text\" expects g")

# -- the last four pairs that were not pairs ---------------------------------------------
probe("domain.threads", "domaene", "slots of g", "threads")
probe("regklasse.rw", "geraet", "        reg X : u32 @0x8 class r",
      "        reg X : u32 @0x8 class rw")
probe("traverse.unvisited", "modul",
      "    table T count 8 { slot { wert : u32, } }\n    static mut g : T = T;\n"
      "    fn f() effects { reads g } costs <= 80 ops { return; }",
      "    table T count 8 { slot { wert : u32, } }\n    static mut g : T = T;\n"
      "    fn f() effects { reads g } costs <= 80 ops {\n"
      "        traverse i over slots of g by unvisited { }\n    }")
probe("eff.pure", "modul",
      "    static mut Z : u32 = 0;\n"
      "    fn f() effects { reads Z } costs <= 2 ops { let q : u32 = Z; return; }",
      "    static mut Z : u32 = 0;\n"
      "    fn f() effects { pure } costs <= 2 ops { return; }")

# ============ round two: the base programs that did not check ==========================
# **A `BASE-RED` row measures the probe, not the language.** Twenty-five of them fell in
# the first full run; the hosts below are taken from programs the corpus already carries
# (`beispiele/04`, `beispiele/06`, `beispiele/67`, `messung/proben/probe-neun-domaenen.gab`)
# rather than invented, so that the base is a program somebody has already run.

# -- the nine domains, on the structure `probe-neun-domaenen.gab` uses for them ----------
HOST["domaene"] = (
    "module p {{\n"
    "    const N : u32 = 64;\n"
    "    const NR : u64 = 32;\n"
    "    type RingNr = u32 in 0 ..< 32;\n"
    "    table Knoten count N {{\n"
    "        tree {{ parent elter, child kind, sibling gesch }}\n"
    "        slot {{ belegt : bool, marke : u32,\n"
    "                elter : option index into Knoten,\n"
    "                kind  : option index into Knoten,\n"
    "                gesch : option index into Knoten, }}\n"
    "    }}\n"
    "    type Ring = {{ plaetze : [RingNr; NR], kopf : u32, zahl : u32, }};\n"
    "    format Wort endian little {{\n"
    "        gueltigkeit : bool @0,\n"
    "        schreibbar  : bool @1,\n"
    "        frei        : u64 @[11:2]  reserved,\n"
    "        rahmen      : u64 embeds [51:12] scale 4096,\n"
    "        hoch        : u64 @[63:52] reserved,\n"
    "    }}\n"
    "    walk Baum levels 2 {{\n"
    "        node : [Wort; 512],\n"
    "        down : rahmen when it.gueltigkeit && !it.schreibbar,\n"
    "        leaf : it.gueltigkeit && it.schreibbar,\n"
    "    }}\n"
    "    impl fn d(k : ptr<normal, rw> Knoten, r : ptr<normal, rw> Ring,\n"
    "              w : ptr<normal, rw> Baum, s : index into Knoten)\n"
    "        ensures forall i in {X} : k.slots[0].marke == 0\n"
    "        effects {{ reads k.slots, writes k.slots }}\n"
    "        costs   <= 4 ops\n"
    "    {{\n"
    "    }}\n}}\n")
_DOM2 = {
    "slots": "slots of k", "chain": "chain(kind, gesch) in k.slots[s]",
    "descendants": "descendants of k.slots[s]", "ancestors": "ancestors of k.slots[s]",
    "queue": "queue r", "fields": "fields of Wort", "elems": "elems of r.plaetze",
    "threads": "threads", "mappings": "mappings of w",
}
for _k, _d in _DOM2.items():
    probe(f"domain.{_k}", "domaene", "threads" if _k != "threads" else "slots of k", _d)

# -- `asm`, in the shape `beispiele/67` writes it ----------------------------------------
HOST["asm"] = ("module p {{\n"
               "    static mut TLB : u32 = 0;\n"
               "    impl fn g(adr : u64)\n"
               "        effects {{ writes TLB }}\n"
               "        costs   <= 1 ops\n"
               "        arch    x86_64\n"
               "        = asm {{ \"nop\" {X} }};\n}}\n")
probe("asmrumpf.in", "asm", "", 'in { adr : "r" }')
probe("asmrumpf.out", "asm", "", 'out { }')
probe("asmrumpf.clobbers", "asm", "", "clobbers { memory }")
probe("asmops.result", "asm", 'in { adr : "r" }', 'out { result : "=a" }')

# -- `forever`, with the two names it must be able to reach ------------------------------
_FOREVER_K = ('    extern fn wd() -> never effects {{ diverges }};\n'
              '    assume tick "the timer ticks" unfalsifiable "no probe can refute it";\n'
              '    table T count 4 {{ slot {{ w : u32, }} '
              'invariant inv cost O(1) runs offline : true; }}\n'
              '    static mut g : T = T;\n'
              '    divergent fn f() -> never effects {{ diverges }} costs <= 8 ops {{\n'
              '        forever m per_pass bounded 4 ops on_exceeded wd '
              'effects {{ pure }} {X} {{ {Y} }}\n    }}\n')
HOST["forever"] = "module p {{\n" + _FOREVER_K + "}}\n"
probe("stmt.forever", "modul",
      "    extern fn wd() -> never effects { diverges };\n"
      "    divergent fn f() -> never effects { diverges } costs <= 8 ops { return; }",
      "    extern fn wd() -> never effects { diverges };\n"
      "    divergent fn f() -> never effects { diverges } costs <= 8 ops {\n"
      "        forever m per_pass bounded 4 ops on_exceeded wd effects { pure } { }\n    }")
probe("forever.progress", "forever", "", "progress tick", Y="")
probe("forever.leaves", "forever", "", "leaves inv", Y="")
probe("stmt.leave", "forever", "", "", Y="leave m;")
probe("stmt.next", "forever", "", "", Y="next m;")
# `stmt.leave`/`stmt.next` differ in `{Y}`, so the pair is built from the SAME `{X}`.
PROBEN["stmt.leave"] = ("forever", "", "", {"Y": "leave m;"})
PROBEN["stmt.next"] = ("forever", "", "", {"Y": "next m;"})

# -- `check`, in the shape `beispiele/06` writes it ---------------------------------------
HOST["check"] = ("module p {{\n"
                 "    static mut Z : u32 = 0;\n"
                 "    fn abnahme() effects {{ pure }} costs <= 1 ops {{ return; }}\n"
                 "    fn sonde() effects {{ pure }} costs <= 1 ops {{ return; }}\n"
                 "    check c {{\n"
                 "        claim    \"the claim this check makes about the machine\"\n"
                 "        measures Z\n"
                 "        gates    abnahme\n"
                 "        can_fail {{ return true; }}\n"
                 "        {X}\n    }}\n}}\n")
probe("check.floor", "check", "", "floor Z >= 0")
probe("check.counterprobe", "check", "",
      'counterprobe "a probe that must make the duty fall" expects sonde')
probe("item.check", "item", "",
      "    static mut Z : u32 = 0;\n"
      "    fn abnahme() effects { pure } costs <= 1 ops { return; }\n"
      "    check c { claim \"the claim this check makes about the machine\"\n"
      "        measures Z gates abnahme can_fail { return true; } }")

# -- `exchange update`, in the shape `beispiele/05` writes it ------------------------------
_X = ("module p {{\n"
      "    extern fn wd() -> never effects {{ diverges }};\n"
      "    atomic A : u32 seq;\n"
      "    fn f() effects {{ writes A }} costs <= 40 ops {{\n"
      "        let alt = A exchange update(v) {X} {{ v = 1; }}\n"
      "        return;\n    }}\n}}\n")
HOST["xform"] = _X
probe("xform.update", "modul",
      "    atomic A : u32 seq;\n"
      "    fn f() effects { writes A } costs <= 40 ops {\n"
      "        let alt = A exchange 1 when true returns r;\n        return;\n    }",
      "    atomic A : u32 seq;\n"
      "    fn f() effects { writes A } costs <= 40 ops {\n"
      "        let alt = A exchange update(v) { v = 1; }\n        return;\n    }")
probe("xform.bounded", "xform", "", "bounded 4 ops")
probe("xform.on_exceeded", "xform", "bounded 4 ops", "bounded 4 ops on_exceeded wd")

# -- the rest --------------------------------------------------------------------------
probe("gruppedecl.{", "modul",
      "    table A count 4 { slot { w : u32, } }\n    table B count 4 { slot { w : u32, } }\n"
      "    static mut x : A = A;\n    static mut y : B = B;\n"
      "    group N over { x, y };",
      "    table A count 4 { slot { w : u32, } }\n    table B count 4 { slot { w : u32, } }\n"
      "    static mut x : A = A;\n    static mut y : B = B;\n"
      "    group N over { x, y } { invariant i cost O(1) runs offline : "
      "x.slots[0].w == y.slots[0].w; }")
probe("item.group", "item", "",
      "    table A count 4 { slot { w : u32, } }\n    table B count 4 { slot { w : u32, } }\n"
      "    static mut x : A = A;\n    static mut y : B = B;\n"
      "    group N over { x, y };")
probe("slotdecl.by", "modul",
      "    table T count 4 { slot { wert : u32, belegt : option index into T, }\n"
      "        ops insert; occupied belegt; }",
      "    table T count 4 { slot { wert : u32 by ops, belegt : option index into T, }\n"
      "        ops insert; occupied belegt; }")
probe("letform.publishes", "modul",
      "    atomic A : u32 publishes { Z } release;\n    static mut Z : u32 = 0;\n"
      "    fn f() effects { writes A } costs <= 40 ops {\n"
      "        let alt = A exchange update(v) { v = 1; }\n        return;\n    }",
      "    atomic A : u32 publishes { Z } release;\n    static mut Z : u32 = 0;\n"
      "    fn f() effects { writes A, publishes Z } costs <= 40 ops {\n"
      "        let alt = A exchange update(v) { v = 1; } publishes { Z };\n"
      "        return;\n    }")

# ============ round three ==============================================================
# `forever`: a `divergent fn` may not promise `costs` -- `K003`: *"a `forever` loop has no
# total cost -- its promise is `per_pass`"*. And `leaves` names a BINDING of the function,
# so the host carries a linear ghost parameter for it.
HOST["forever"] = (
    "module p {{\n"
    "    extern fn wd() -> never effects {{ diverges }};\n"
    "    fn probe() -> bool effects {{ pure }} costs <= 1 ops {{ return true; }}\n"
    "    assume tick \"the timer ticks on every core\" falsifier probe;\n"
    "    linear ghost type Marke;\n"
    "    divergent fn f(inv : Marke) -> never effects {{ diverges }} {{\n"
    "        forever m per_pass bounded 4 ops on_exceeded wd effects {{ pure }} {X} "
    "{{ {Y} }}\n    }}\n}}\n")
for _k in ("forever.progress", "forever.leaves", "stmt.leave", "stmt.next"):
    PROBEN.pop(_k, None)
probe("forever.progress", "forever", "", "progress tick", Y="")
probe("forever.leaves", "forever", "", "leaves inv", Y="")
PROBEN["stmt.leave"] = ("forever", "", "", {"Y": "leave m;"})
PROBEN["stmt.next"] = ("forever", "", "", {"Y": "next m;"})
probe("stmt.forever", "modul",
      "    extern fn wd() -> never effects { diverges };\n"
      "    divergent fn f() -> never effects { diverges } { return; }",
      "    extern fn wd() -> never effects { diverges };\n"
      "    divergent fn f() -> never effects { diverges } {\n"
      "        forever m per_pass bounded 4 ops on_exceeded wd effects { pure } { }\n    }")

# `exchange update(v) { … }` ends with a `;` like every `let`, and the function reads `A`.
HOST["xform"] = ("module p {{\n"
                 "    extern fn wd() -> never effects {{ diverges }};\n"
                 "    atomic A : u32 seq;\n"
                 "    fn f() effects {{ reads A, writes A }} costs <= 40 ops {{\n"
                 "        let alt = A exchange update(v) {X} {{ v = 1; }};\n"
                 "        return;\n    }}\n}}\n")
probe("xform.bounded", "xform", "", "bounded 4 ops")
probe("xform.on_exceeded", "xform", "bounded 4 ops", "bounded 4 ops on_exceeded wd")
probe("xform.update", "modul",
      "    atomic A : u32 seq;\n"
      "    fn f() effects { reads A, writes A } costs <= 40 ops {\n"
      "        let alt = A exchange 1 when true returns r;\n        return;\n    }",
      "    atomic A : u32 seq;\n"
      "    fn f() effects { reads A, writes A } costs <= 40 ops {\n"
      "        let alt = A exchange update(v) { v = 1; };\n        return;\n    }")
probe("letform.publishes", "modul",
      "    atomic A : u32 publishes { Z } release;\n    static mut Z : u32 = 0;\n"
      "    fn f() effects { reads A, writes A } costs <= 40 ops {\n"
      "        let alt = A exchange update(v) { v = 1; };\n        return;\n    }",
      "    atomic A : u32 publishes { Z } release;\n    static mut Z : u32 = 0;\n"
      "    fn f() effects { reads A, writes A, publishes Z } costs <= 40 ops {\n"
      "        let alt = A exchange update(v) { v = 1; } publishes { Z };\n"
      "        return;\n    }")

# `U002`: a carrier of a `group` sits under a lock.
_GRP = ("    table A count 4 {{ slot {{ w : u32, }} }}\n"
        "    table B count 4 {{ slot {{ w : u32, }} }}\n"
        "    static mut x : A = A;\n    static mut y : B = B;\n"
        "    lock L protects {{ x, y }} rank 0;\n"
        "    group N over {{ x, y }}{X}\n")
HOST["gruppe"] = "module p {{\n" + _GRP + "}}\n"
probe("gruppedecl.{", "gruppe", ";",
      " { invariant i cost O(1) runs offline : x.slots[0].w == y.slots[0].w; }")
probe("item.group", "item", "",
      "    table A count 4 { slot { w : u32, } }\n    table B count 4 { slot { w : u32, } }\n"
      "    static mut x : A = A;\n    static mut y : B = B;\n"
      "    lock L protects { x, y } rank 0;\n    group N over { x, y };")

# `D010`: `occupied` names a `bool` field.
probe("slotdecl.by", "modul",
      "    table T count 4 { slot { wert : u32, belegt : bool, }\n"
      "        ops insert; occupied belegt; }",
      "    table T count 4 { slot { wert : u32 by ops, belegt : bool, }\n"
      "        ops insert; occupied belegt; }")
probe("table.occupied", "modul",
      "    table T count 4 { slot { wert : u32, belegt : bool, } }",
      "    table T count 4 { slot { wert : u32, belegt : bool, } occupied belegt; }")
probe("table.ops", "modul",
      "    table T count 4 { slot { wert : u32, belegt : bool, } occupied belegt; }",
      "    table T count 4 { slot { wert : u32, belegt : bool, } occupied belegt;\n"
      "        ops insert; }")
for _w in ("insert", "remove", "relabel"):
    probe(f"opnamen.{_w}", "modul",
          "    table T count 4 { slot { wert : u32, belegt : bool, } occupied belegt; }",
          "    table T count 4 { slot { wert : u32, belegt : bool, } occupied belegt;\n"
          f"        ops {_w}; }}")

# `A004`: a function naming `result` in an `asm` out block returns something.
HOST["asmres"] = ("module p {{\n"
                  "    static mut TLB : u32 = 0;\n"
                  "    impl fn g(adr : u64) -> u64\n"
                  "        effects {{ writes TLB }}\n"
                  "        costs   <= 1 ops\n"
                  "        arch    x86_64\n"
                  "        = asm {{ \"nop\" {X} }};\n}}\n")
probe("asmops.result", "asmres", 'in { adr : "r" }', 'out { result : "=a" }')

# `D007`: a `tree` edge is an `option index into` field of the same table.
probe("table.tree", "modul",
      "    table T count 4 { slot { wert : u32, elter : option index into T, } }",
      "    table T count 4 { slot { wert : u32, elter : option index into T, }\n"
      "        tree { parent elter } }")
for _k, _e in (("parent", "parent"), ("child", "child"), ("sibling", "sibling")):
    probe(f"treedecl.{_k}", "modul",
          "    table T count 4 { slot { wert : u32, elter : option index into T, } }",
          "    table T count 4 { slot { wert : u32, elter : option index into T, }\n"
          f"        tree {{ {_e} elter }} }}")

# ============ round four (2026-09-15): the specification half ==========================
# **Four forms of the contract/predicate half had no host, and three of them had none for
# the SAME reason: the form is MANDATORY.** A differential whose base leaves out a clause
# the grammar demands measures the omission, not the clause -- it comes back `BASE-RED`
# and says nothing about the form. The base therefore carries the form in ANOTHER shape,
# exactly as `atomicdecl.seq` does (`seq` against `acquire`). *A pair that cannot leave
# the form out compares two of it.*

# -- `reaches` and `Self`, in the shape `beispiele/47-ops-wortmenge.gab` writes them ----
# A table invariant is the only place that can name its own carrier, and `Self` is the
# only name it has. The pair therefore differs in the PREDICATE, not in the host.
_TREE = ("    table T count 4 {{ slot {{ wert : u32, elter : option index into T, }}\n"
         "        tree {{ parent elter }}\n"
         "        invariant i cost O(1) runs offline : {X}; }}\n")
HOST["baum"] = "module p {{\n" + _TREE + "}}\n"
probe("atompred.reaches", "baum",
      "forall s in slots of Self : Self.slots[s].wert == Self.slots[s].wert",
      "forall s in slots of Self : Self.slots[s] reaches Self.slots[0] via elter")
probe("place.Self", "baum", "true", "Self.slots[0].wert == Self.slots[0].wert")

# -- the function-POINTER contract, in the shape `beispiele/49-dispatch-tabelle.gab` -----
# `N035` demands both clauses at the type, so neither can be left out; the pair changes
# WHICH effect and WHICH bound is promised.
_FNPTR = ("module p {{\n"
          "    static mut Z : u32 = 0;\n"
          "    type D = {{ b : fn() -> bool {X}, }};\n"
          "    fn f(d : D) effects {{ pure }} costs <= 1 ops {{ return; }}\n}}\n")
HOST["fnptr2"] = _FNPTR
probe("fnptr.effects", "fnptr2", "effects { pure } costs <= 4 ops",
      "effects { reads Z } costs <= 4 ops")
probe("fnptr.costs", "fnptr2", "effects { pure } costs <= 4 ops",
      "effects { pure } costs <= 8 ops")


# =======================================================================================
# THE SPEECH TEST -- five directions, and each one is a way this instrument could go quiet
# =======================================================================================
#
# The whole verdict rests on a BYTE COMPARISON of two emitted C files. That comparison can
# fail silently in exactly one direction -- if the emitter stopped producing C at all, every
# pair would come out identical and every form would read `UNCOVERED`. **A run in which
# everything is uncovered looks like a finding and is a broken pipe.** So the test drives one
# artificial pair per verdict and requires the verdict back.
#
# The fifth direction is the one that matters most and is the cheapest to forget: a variant
# that adds only a COMMENT must come out `UNCOVERED`. If it comes out `CARRIES`, the C
# carries the source text and the comparison is measuring the input.

SPRECHPROBEN = {
    "a statement that reaches the artefact is CARRIES": (
        "module p {\n    fn f(a : u32 in 0 .. 100) -> u32 in 0 .. 100\n"
        "        effects { pure } costs <= 8 ops { return a; }\n}\n",
        "module p {\n    fn f(a : u32 in 0 .. 100) -> u32 in 0 .. 100\n"
        "        effects { pure } costs <= 8 ops { let r : u32 in 0 .. 100 = a; return r; }\n}\n",
        "CARRIES"),
    "a COMMENT must NOT reach the artefact -- else the C carries the source": (
        "module p {\n    fn f(a : u32) -> u32 effects { pure } costs <= 4 ops { return a; }\n}\n",
        "module p {\n    -- a comment, and nothing else\n"
        "    fn f(a : u32) -> u32 effects { pure } costs <= 4 ops { return a; }\n}\n",
        "UNCOVERED"),
    "a variant the checker refuses is REFUSES": (
        "module p {\n    fn f(a : u32) -> u32 effects { pure } costs <= 4 ops { return a; }\n}\n",
        "module p {\n    fn f(a : u32) -> u32 effects { pure } costs <= 4 ops { return zz; }\n}\n",
        "REFUSES"),
    "a clause that books an obligation is DEMANDS": (
        "module p {\n    fn f(a : u32) -> u32 effects { pure } costs <= 4 ops { return a; }\n}\n",
        "module p {\n    fn f(a : u32) -> u32 ensures result == a\n"
        "        effects { pure } costs <= 4 ops { return a; }\n}\n",
        "DEMANDS"),
    "a base the emitter already refuses is BASIS-C001, not REFUSES": (
        "module p {\n    table T count 4 { slot { w : u32, } }\n    static mut g : T = T;\n}\n",
        "module p {\n    table T count 4 { slot { w : u32, } }\n    static mut g : T = T;\n"
        "    fn f() effects { reads g } costs <= 4 ops { return; }\n}\n",
        "BASIS-C001"),
}


def sprechprobe():
    """Returns the number of directions that do NOT hold."""
    global PRUEFERWORTE
    if PRUEFERWORTE is None:
        PRUEFERWORTE = prueferworte()
    schlecht = 0
    print("== Sprechprobe -- fuenf Richtungen ==")
    for satz, (bt, vt, soll) in SPRECHPROBEN.items():
        b, v = messe(bt), messe(vt)
        if not b["angenommen"]:
            ist = "BASE-RED"
        elif b["c001"]:
            ist = "BASIS-C001"
        else:
            ist = urteil(b, v, "")[0]
        ok = ist == soll
        schlecht += not ok
        print(f"  {'ok         ' if ok else 'GESCHEITERT'}   {satz} ({ist})")
    return schlecht

if __name__ == "__main__":
    sys.exit(main())
