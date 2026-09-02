#!/usr/bin/env python3
"""Push every NUMERIC and LEXICAL field of every declaration form to its boundaries -- and
hold the checker to the property this folder lives by.

    THE CHECKER EITHER ACCEPTS, OR IT REFUSES BY NAME.

A panic is a third answer. A silent wrap that turns a refusal into `0 errors` is a fourth,
and it is the worse of the two -- a crash is at least a measurement.

**And the two build profiles must agree.** There is no `[profile.release]` in `Cargo.toml`,
so Rust's overflow checks are ON in debug and OFF in release -- and release is what
`cargo install --path crates/gabbro-cli` produces, the install `README.md` documents. On
2026-09-01 `@[u128::MAX:0]` was measured at

    debug   -> panicked at umgebung.rs:1334, exit 101
    release -> 3 items, 0 errors, 0 hints, exit 0

*The same source file, two answers, and the honest one is the one nobody ships.* That
disagreement is mechanically decidable, needs no oracle for what the right answer IS, and
catches both third answers at once. It is the property this instrument measures.

Usage:
    fuzze-grenzen.py --debug target/debug/gabbro --release target/release/gabbro
    fuzze-grenzen.py ... --keep VERZ      keep every generated file (for a probe)
    fuzze-grenzen.py --deckung            coverage against `dokumente/SYNTAX.md`, no run

Exit: 0 when every case answered the same in both builds and neither panicked, 1 otherwise.

**NO `--fail-fast`.** A run that stops at the first hit answers "does at least one fire",
and the question asked is "which fire" (CLAUDE.md).

WHAT THE PROPERTY DOES NOT CATCH -- named, because a silent limit is the expensive kind
---------------------------------------------------------------------------------------
The judgement is *agreement plus absence of a panic*. It needs no oracle, and that is
exactly what it costs: **a value both builds accept in silence, and wrongly, passes.**
Measured on 2026-09-02 by disabling `N051` alone -- the sweep stayed green over the very
value `N051` exists for, because both builds then accepted it, together. The rule that
catches THAT is the poison corpus (`beispiele/gift/`), one probe per named refusal, in both
directions. *These two instruments do not overlap; neither replaces the other.*

WHAT THE SELF-CHECK MEASURED, 2026-09-02
----------------------------------------
`registerlagen()` was put back to its pre-repair `as i128` arithmetic and `N051` was taken
out of `device()`, reproducing the defect of 2026-09-01 exactly. The sweep reported it:

    reg-versatz  170141183460469231731687303715884105727
                 debug=PANIC (namen.rs:1595)  release=REFUSE N047

*An instrument nobody has watched find something is an ornament (R11).* This one has now
been watched twice: three times falling on its own way to green (below), and once over a
defect planted on purpose.
"""

import argparse
import pathlib
import re
import subprocess
import sys
import tempfile

# `sys.path` gets the tool's own directory, the same reason as in `pruefe-konstrukte.py`:
# this file may be LOADED rather than run, and then `sys.path[0]` is the working directory.
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import abschnitt  # noqa: E402

U8, U16, U32, U64 = 0xFF, 0xFFFF, 0xFFFF_FFFF, 0xFFFF_FFFF_FFFF_FFFF
U128 = (1 << 128) - 1

# The boundary ladder. Every rung is a value at which SOME width changes its mind:
# the type's own limit, one below it, one above it -- plus the small values where a
# `- 1` or a `+ 1` in the checker can leave the range.
LADDER = [
    0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 33, 63, 64, 65, 127, 128, 129,
    255, 256, 257, 1023, 1024, 65535, 65536, 65537,
    (1 << 31) - 1, 1 << 31, (1 << 31) + 1,
    U32 - 1, U32, U32 + 1, U32 + 2,
    (1 << 63) - 1, 1 << 63,
    U64 - 1, U64, U64 + 1,
    (1 << 127) - 1, 1 << 127,
    U128 - 1, U128,
]

# Values that are not legal integer literals at all, or that sit just past `u128`. The
# lexer owes a NAMED refusal for each; what it must not do is panic or disagree.
LEXICAL = [
    "0x", "0b", "0o", "0x_", "0xG", "0b2", "1__2", "_1", "1_",
    str(U128 + 1), str(U128 + 2), str(1 << 129), str(1 << 200),
    "0x" + "F" * 32, "0x" + "F" * 33, "0x" + "F" * 64,
    "9" * 40, "9" * 100,
    "0x1_0000_0000_0000_0000_0000_0000_0000_0000",
]

# **The MINUS side, added 2026-09-02.** `unary = [ "!" | "-" | "~" ] primary`, so a sign is
# grammatical wherever an expression is -- and every layout field the emitter lowers is
# unsigned. The pre-repair `registerlagen()` read `*v as i128` and got `-1` out of a
# `u128::MAX` the user never signed; a literal `-1` walks in through the front door.
NEGATIV = [
    "-0", "-1", "-2", "-3", "-8", "-127", "-128", "-129", "-255", "-256",
    "-2147483648", "-2147483649",
    "-" + str(1 << 63), "-" + str((1 << 63) + 1),
    "-" + str(U64), "-" + str(U64 + 1),
    "-" + str((1 << 127) - 1), "-" + str(1 << 127),
    "-" + str(U128), "-" + str(U128 + 1),
]

# **The same rungs written in the other two bases, added 2026-09-02.** `int = dec | hex |
# bin` are three separate paths through the lexer, and the ladder above walked only the
# first. `0x1_0000_0000_0000_0000_0000_0000_0000_0000` was already in `LEXICAL` as a shape
# that must be refused; these are the ones that must be READ, and read as the same number.
BASEN = [
    "0x0", "0x1", "0x7", "0x8", "0xF", "0x10", "0x1F", "0x20",
    "0xFF", "0x100", "0xFFFF", "0x1_0000",
    "0x7FFF_FFFF", "0x8000_0000", "0xFFFF_FFFF", "0x1_0000_0000",
    "0x7FFF_FFFF_FFFF_FFFF", "0x8000_0000_0000_0000",
    "0xFFFF_FFFF_FFFF_FFFF", "0x1_0000_0000_0000_0000",
    "0xFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF",
    "0b0", "0b1", "0b1111", "0b1_0000",
    "0b" + "1" * 32, "0b1" + "0" * 32, "0b" + "1" * 64, "0b1" + "0" * 64,
    "0b" + "1" * 128, "0b1" + "0" * 128,
]

ZAHLEN = [str(v) for v in LADDER] + LEXICAL + NEGATIV + BASEN

# **String literals have two ends too.** `string = quote { char } quote { quote { char }
# quote }` and `char = any character except quote and newline` -- so an unterminated string,
# a newline inside one, and the doubling form are all decidable at the lexer, and each owes
# a named refusal rather than a panic. The value carries its own quotes, so that the
# UNQUOTED and the HALF-QUOTED shapes are reachable at all.
TEXTE = [
    '""', '" "', '"a"', '"ab"',
    '"' + "a" * 63 + '"', '"' + "a" * 64 + '"',
    '"' + "a" * 4095 + '"', '"' + "a" * 4096 + '"', '"' + "a" * 65536 + '"',
    '"' + "ä" * 4096 + '"',
    '"a""b"', '"""a"""', '""""',
    '"', 'a', '"a', 'a"',
    '"a\nb"', '"a\\"',
    '"' + chr(0) + '"',
]

# **The LEXICAL ladder over names, added 2026-09-02.** `ident = ( letter | "_" ) { letter |
# digit | "_" }` puts no bound on the length, and the emitter writes the name into C, where
# C99 5.2.4.1 guarantees 63 significant characters in an internal identifier and 31 in an
# external one. An empty name and a keyword are the other two ends of the same slot.
NAMEN = [
    "a", "ab", "a" * 31, "a" * 32, "a" * 63, "a" * 64, "a" * 65,
    "a" * 127, "a" * 128, "a" * 255, "a" * 256, "a" * 257,
    "a" * 1023, "a" * 1024, "a" * 4096, "a" * 65536,
    "_", "__", "_1", "_" * 1024,
    "", " ", "1a", "9", "a-b", "a b",
    "ae", "ä", "ä" * 1024, "ä́",
    "u64", "module", "reg", "fn", "Self", "None",
]

# **The DEPTH ladder.** A recursive-descent parser answers "how deep" with its own stack,
# and a stack that runs out is a third answer -- neither an acceptance nor a named refusal.
# The rungs are the same shape as the numeric ones: powers of two and their neighbours.
TIEFEN = [0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128,
          255, 256, 511, 512, 1023, 1024, 4095, 4096]

LEITERN = {
    "zahl":          ZAHLEN,
    "name":          NAMEN,
    "text":          TEXTE,
    "tiefe-zeiger":  ["ptr<normal, rw> " * n + "u64" for n in TIEFEN],
    "tiefe-array":   ["[" * n + "u64" + "; 2]" * n for n in TIEFEN],
    "tiefe-klammer": ["(" * n + "1" + ")" * n for n in TIEFEN],
}

# ---------------------------------------------------------------------------------------
# The forms. Each names EVERY numeric field the grammar gives it, so that a sweep over one
# template covers one declaration form completely. `{V}` is the swept slot; the other
# numbers are small and fixed, so a finding names one field and not a combination.
#
# **Each form carries a KNOWN-GOOD value beside it, and the run checks it first.** The first
# draft of this instrument did not, and eight of its fifteen templates were not valid Gabbro
# -- `effects { }` instead of `effects { pure }`, a `walk` body with the wrong separator. The
# sweep then measured the same parse error 60 times per form and called it 595 findings.
# *A generator whose baseline does not parse has an EMPTY population, and `W17` says a green
# judgement over nothing looks exactly like a green judgement.*
#
# **And each form names the EBNF rule whose slot it drives** (`REGEL`). That is what makes
# the coverage claim in `--deckung` a measurement instead of an assertion: the numerator is
# read out of the same table the sweep runs over, so the two cannot drift apart.
# ---------------------------------------------------------------------------------------
GUT = {
    "bank-stride": "8", "bank-count": "4", "bank-at": "0x0", "bank-regversatz": "0x0",
    "reg-versatz": "0x8", "reg-bit-hi": "3", "reg-bit-lo": "0",
    "format-bit-hi": "31", "format-bit-lo": "0",
    "walk-levels": "4", "table-count": "8",
    "range-hi": "1000", "range-lo": "0",
    "ausdruck": "5", "costs": "2",
    # --- added 2026-09-02 -----------------------------------------------------------
    "range-einpunkt": "0", "range-verkehrt": "0", "range-offen-hi": "1000",
    "slot-bereich-hi": "1000",
    "const-wert": "7", "static-wert": "0", "array-laenge": "8", "walk-knoten": "512",
    "lock-rank": "0", "lock-held": "400", "lock-shared-held": "200",
    "acc-percpu": "8",
    "entry-vector": "0x80", "entry-ist": "3", "entry-nested-bounded": "2",
    "boot-step": "4096",
    "format-version": "1",
    "embeds-hi": "51", "embeds-lo": "12", "embeds-scale": "4096",
    "reason-code": "1",
    "invariant-kosten": "n", "aligned-n": "4096", "gleitkomma": "1.5",
    "index-stelle": "0", "retry-schranke": "1024", "forever-schranke": "4096",
    "const-als-schranke": "8",
    "name-const": "K", "name-modul": "f", "name-fn": "g", "name-feld": "a",
    "name-reg": "X", "name-tabelle": "T", "name-typ": "Pa", "name-parameter": "a",
    "typ-tiefe-zeiger": "u64", "typ-tiefe-array": "u64", "typ-tiefe-klammer": "1",
    "if-bedingung": "1", "let-wert": "1", "zuweisung": "1", "aufruf-argument": "1",
    "gleitkomma-bereich": "1.0",
    "traverse-abnahme": "s",
    "text-annahme": '"the device answers"', "text-grund": '"one"',
    "text-abschnitt": '".data"',
}

# Which value ladder each form is swept with. Absent means `"zahl"`.
LEITER = {
    "name-const": "name", "name-modul": "name", "name-fn": "name",
    "name-feld": "name", "name-reg": "name", "name-tabelle": "name",
    "name-typ": "name", "name-parameter": "name",
    # **`decreases` takes a NAME and not a number, and that is a measurement, not a
    # concession.** Swept with the numeric ladder, all 92 rungs came back `REFUSE S005`
    # ("a constant measure never falls") -- the same answer 92 times, which is the empty
    # population `W17` warns about wearing a green coat. The slot that HAS a boundary here
    # is the identifier.
    "traverse-abnahme": "name",
    "text-annahme": "text", "text-grund": "text", "text-abschnitt": "text",
    "typ-tiefe-zeiger": "tiefe-zeiger",
    "typ-tiefe-array": "tiefe-array",
    "typ-tiefe-klammer": "tiefe-klammer",
}

# The EBNF rule of `dokumente/SYNTAX.md` whose literal slot the form drives.
REGEL = {
    "bank-stride": "bank", "bank-count": "bank", "bank-at": "bank",
    "bank-regversatz": "regdecl", "reg-versatz": "regdecl",
    "reg-bit-hi": "bitpos", "reg-bit-lo": "bitpos",
    "format-bit-hi": "field", "format-bit-lo": "field",
    "walk-levels": "walkdecl", "table-count": "table",
    "range-hi": "range", "range-lo": "range",
    "ausdruck": "int", "costs": "fncontract",
    "range-einpunkt": "range", "range-verkehrt": "range", "range-offen-hi": "range",
    "slot-bereich-hi": "intty",
    "const-wert": "constdecl", "static-wert": "staticdecl",
    "array-laenge": "array", "walk-knoten": "array",
    "lock-rank": "lockdecl", "lock-held": "lockdecl", "lock-shared-held": "lockdecl",
    "acc-percpu": "accdecl",
    "entry-vector": "entrydecl", "entry-ist": "entryextra",
    "entry-nested-bounded": "entryextra",
    "boot-step": "bootstep",
    "format-version": "format",
    "embeds-hi": "fieldty", "embeds-lo": "fieldty", "embeds-scale": "fieldty",
    "reason-code": "reason",
    "invariant-kosten": "costexpr", "aligned-n": "builtin", "gleitkomma": "float",
    "index-stelle": "placesuffix",
    "retry-schranke": "retry", "forever-schranke": "forever",
    "const-als-schranke": "constexpr",
    "name-const": "ident", "name-modul": "path", "name-fn": "fndecl",
    "name-feld": "field", "name-reg": "regdecl", "name-tabelle": "table",
    "name-typ": "typedecl", "name-parameter": "params",
    "typ-tiefe-zeiger": "ptrty", "typ-tiefe-array": "array",
    "typ-tiefe-klammer": "paren",
    "if-bedingung": "ifstmt", "let-wert": "letstmt", "zuweisung": "assign",
    "aufruf-argument": "arg",
    "gleitkomma-bereich": "frange",
    "traverse-abnahme": "traverse",
    "text-annahme": "assume", "text-grund": "string", "text-abschnitt": "staticdecl",
}

FORMEN = {
    # `bank` -- three numeric fields, and `N048`/`N049`/`N050` all live here.
    "bank-stride": """module f {{
opaque type Pa = u64;
device D(basis : Pa) at mmio {{
    bank F at 0x0 stride {V} count 4 {{ reg X : u64 @0x0 class rw }}
}}
}}""",
    "bank-count": """module f {{
opaque type Pa = u64;
device D(basis : Pa) at mmio {{
    bank F at 0x0 stride 8 count {V} {{ reg X : u64 @0x0 class rw }}
}}
}}""",
    "bank-at": """module f {{
opaque type Pa = u64;
device D(basis : Pa) at mmio {{
    bank F at {V} stride 8 count 4 {{ reg X : u64 @0x0 class rw }}
}}
}}""",
    "bank-regversatz": """module f {{
opaque type Pa = u64;
device D(basis : Pa) at mmio {{
    bank F at 0x0 stride 8 count 4 {{ reg X : u64 @{V} class rw }}
}}
}}""",
    # `reg` -- the offset, and the two ends of a field's bit range (`N007`, `N047`).
    "reg-versatz": """module f {{
opaque type Pa = u64;
device D(basis : Pa) at mmio {{ reg X : u64 @{V} class rw }}
}}""",
    "reg-bit-hi": """module f {{
opaque type Pa = u64;
device D(basis : Pa) at mmio {{ reg X : u64 @0x0 class rw fields {{ A @[{V}:0] }} }}
}}""",
    "reg-bit-lo": """module f {{
opaque type Pa = u64;
device D(basis : Pa) at mmio {{ reg X : u64 @0x0 class rw fields {{ A @[63:{V}] }} }}
}}""",
    # `format` -- the same bit range on the other construct that has one.
    "format-bit-hi": """module f {{
format F endian big {{ a : u32 @[{V}:0], }}
}}""",
    "format-bit-lo": """module f {{
format F endian big {{ a : u32 @[31:{V}], }}
}}""",
    # `walk levels` -- the field whose modulo-2^32 wrap certified `slack 0` on 2026-09-01.
    "walk-levels": """module f {{
format Pte endian little {{
    praesent : bool @0,
    rest     : u64 @[63:1] reserved,
}}
walk T levels {V} {{
    node : [Pte; 512],
    down : rest when it.praesent,
    leaf : it.praesent,
}}
}}""",
    # `table count` -- the bound every `index into` inherits.
    "table-count": """module f {{
table T count {V} {{ slot {{ a : u32 in 0 .. 1000, }} }}
}}""",
    # A range type's two ends: the place `M104` reads its width from.
    "range-hi": """module f {{
type R = u32 in 0 .. {V};
}}""",
    "range-lo": """module f {{
type R = u64 in {V} .. 0xFFFF_FFFF_FFFF_FFFF;
}}""",
    # An integer literal in an ordinary expression -- the plain path into `M1`.
    "ausdruck": """module f {{
impl fn g() -> u64
    effects {{ pure }}
    costs   <= 2 ops
{{
    return {V};
}}
}}""",
    # `costs <= N ops` -- a numeric field on the clause that carries the cost proof.
    "costs": """module f {{
impl fn g() -> u32
    effects {{ pure }}
    costs   <= {V} ops
{{
    return 1;
}}
}}""",

    # ===================================================================================
    # Added 2026-09-02. Fifteen forms measured nine of the grammar's rules; what follows
    # takes the same ladder to every OTHER rule that has a literal slot to climb.
    # ===================================================================================

    # **The three range shapes the two-ended sweep above cannot reach.** `range-hi`/`-lo`
    # each hold one end still, so `lo == hi` occurs once and `lo > hi` only past the fixed
    # end. Here both ends move together (a single point at every rung) and against each
    # other (`hi` pinned at 0, so every rung above it is an inverted range).
    "range-einpunkt": """module f {{
type R = u64 in {V} .. {V};
}}""",
    "range-verkehrt": """module f {{
type R = u64 in {V} .. 0;
}}""",
    "range-offen-hi": """module f {{
type R = u32 in 0 ..< {V};
}}""",
    # The same refinement one level down, where a table slot reads its width.
    "slot-bereich-hi": """module f {{
table T count 8 {{ slot {{ a : u32 in 0 .. {V}, }} }}
}}""",

    # `const` and `static` -- the two places a literal enters as a declaration, not as
    # part of an expression inside one.
    "const-wert": """module f {{
const K : u64 = {V};
}}""",
    "static-wert": """module f {{
static mut x : u64 = {V};
}}""",
    # A `const` that is then USED as a table bound: the indirection every `index into`
    # crosses. A number that survives its own declaration can still break the bound.
    "const-als-schranke": """module f {{
const N : u32 = {V};
table T count N {{ slot {{ a : u32, }} }}
}}""",

    # `array` -- the length the emitter turns into a C array bound, in both places the
    # grammar admits one.
    "array-laenge": """module f {{
static mut A : [u64; {V}] = 0;
}}""",
    "walk-knoten": """module f {{
format Pte endian little {{
    praesent : bool @0,
    rest     : u64 @[63:1] reserved,
}}
walk T levels 4 {{
    node : [Pte; {V}],
    down : rest when it.praesent,
    leaf : it.praesent,
}}
}}""",

    # `lock` -- three numeric fields, and the rank is the one the lock ORDER is proved on.
    "lock-rank": """module f {{
table T count 8 {{ slot {{ a : u32, }} }}
lock L protects {{ T }} rank {V} held <= 400 ops;
}}""",
    "lock-held": """module f {{
table T count 8 {{ slot {{ a : u32, }} }}
lock L protects {{ T }} rank 0 held <= {V} ops;
}}""",
    "lock-shared-held": """module f {{
table T count 8 {{ slot {{ a : u32, }} }}
lock L protects {{ T }} rank 0 held <= 400 ops shared held <= {V} ops;
}}""",

    # `accumulates ... per cpu N` -- the CELL COUNT, and the emitter writes it as an array
    # bound over which it then generates a merge loop.
    "acc-percpu": """module f {{
const NK : u32 = {V};
accumulates h : u64 merge max per cpu NK;
}}""",

    # `entry` -- the interrupt vector, the stack-table index, and the nesting bound. All
    # three are lowered into a table the hardware indexes.
    #
    # *(The keyword for the middle one is a three-letter x86 acronym that the German word
    # list in `pruefe-englisch.py` reads as a verb; it is spelled out in the template below
    # and not in this comment, because that guardian is coarse on purpose -- it verifies
    # rather than acquits, W10, and a false positive costs a ratchet.)*
    "entry-vector": """module f {{
entry e vector {V} arch x86_64 {{
    regs in  {{ nr : rax, }}
    regs out {{ ret : rax, }}
    preserves {{ rbx }}
    clobbers  {{ rcx }}
    stack kernstapel per cpu nested never
    dispatch f::g;
}}
impl fn g()
    effects {{ pure }}
    costs   <= 2 ops
{{
    return;
}}
}}""",
    "entry-ist": """module f {{
entry e vector 2 arch x86_64 {{
    regs in  {{ }}
    regs out {{ }}
    preserves {{ rbx }}
    clobbers  {{ r11 }}
    stack nmi_stapel per cpu ist {V} nested bounded 2
    dispatch f::g;
}}
impl fn g()
    effects {{ pure }}
    costs   <= 2 ops
{{
    return;
}}
}}""",
    "entry-nested-bounded": """module f {{
entry e vector 2 arch x86_64 {{
    regs in  {{ }}
    regs out {{ }}
    preserves {{ rbx }}
    clobbers  {{ r11 }}
    stack nmi_stapel per cpu ist 3 nested bounded {V}
    dispatch f::g;
}}
impl fn g()
    effects {{ pure }}
    costs   <= 2 ops
{{
    return;
}}
}}""",

    # `boot step X = N` -- a constant written into a machine register before anything else
    # in the unit runs.
    "boot-step": """module f {{
const S : u64 = {V};
boot b arch x86_64 {{
    step stapelzeiger = S;
    dispatch f::g;
}}
impl fn g()
    effects {{ pure }}
    costs   <= 2 ops
{{
    return;
}}
}}""",

    # `format @version N` -- the format rule's OWN numeric slot; the bit ranges above sit
    # in `field`, one rule further down.
    "format-version": """module f {{
format F @version {V} endian big {{ a : u32 @[31:0], }}
}}""",

    # `embeds [hi:lo] scale N` -- an embedded pointer is a bit field AND a multiplier, and
    # the emitter multiplies the extracted value by the scale.
    "embeds-hi": """module f {{
format F endian little {{
    lo     : u64 @[11:0] reserved,
    rahmen : u64 embeds [{V}:12] scale 4096,
    hi     : u64 @[63:52] reserved,
}}
}}""",
    "embeds-lo": """module f {{
format F endian little {{
    lo     : u64 @[11:0] reserved,
    rahmen : u64 embeds [51:{V}] scale 4096,
    hi     : u64 @[63:52] reserved,
}}
}}""",
    "embeds-scale": """module f {{
format F endian little {{
    lo     : u64 @[11:0] reserved,
    rahmen : u64 embeds [51:12] scale {V},
    hi     : u64 @[63:52] reserved,
}}
}}""",

    # `reason X = N "text"` -- the numeric code a refusal is distinguishable by.
    "reason-code": """module f {{
reason R {{
    A = {V} "one"
    exhaustive
}}
}}""",

    # `cost O(...)` -- the cost term on a table invariant, the one rule where `costexpr`
    # stands on its own rather than behind `costs <=`.
    "invariant-kosten": """module f {{
table T count 8 {{
    slot {{ a : bool, }}
    invariant i cost O({V}) runs offline : forall s in slots of T : T.slots[s].a;
}}
}}""",

    # `aligned(p, N)` -- the alignment argument, and `aligned` is the builtin that read its
    # own first argument without declaring it (2026-09-01).
    "aligned-n": """module f {{
opaque type Pa = u64;
spec fn g(p : Pa) -> bool
    effects {{ pure }}
    = aligned(p, {V});
}}""",

    # A float literal. The numeric ladder is integers, so every rung here is a value the
    # lexer must either read as a float or refuse by name -- `1024` is not `1024.0`.
    "gleitkomma": """module f {{
const K : f64 = {V};
}}""",

    # `place [ N ]` -- the index suffix, where the bound of `index into` is discharged.
    "index-stelle": """module f {{
table T count 8 {{ slot {{ a : u32, }} }}
spec fn g() -> u32
    effects {{ pure }}
    = T.slots[{V}].a;
}}""",

    # The two bounded loop forms. `bounded N ops` is the number the termination argument
    # rests on; `per_pass bounded N ops` is the same number for a loop that never ends.
    "retry-schranke": """module f {{
opaque type Pa = u64;
device S(basis : Pa) at mmio {{ reg fertig : u32 @0x0 class r }}
assume geraet_antwortet "the device answers" falsifier zeitablauf;
impl fn g(s : ptr<mmio, r> S) -> u32
    effects {{ reads s }}
    costs   <= 2048 ops
{{
    retry warten until s.fertig == 1
        bounded {V} ops
        progress geraet_antwortet
        on_exceeded zeitablauf
        effects {{ reads s }}
    {{
        return 0;
    }}
    return 1;
}}
}}""",
    "forever-schranke": """module f {{
static mut erledigt : u64 = 0;
assume zeitgeber_tickt "the timer ticks" falsifier wachhund_schlug_an;
extern fn wachhund_schlug_an() -> never
    effects {{ diverges }};
impl fn g() -> u64
    effects {{ reads erledigt, writes erledigt }}
{{
    forever runde
        per_pass bounded {V} ops
        on_exceeded wachhund_schlug_an
        effects {{ reads erledigt, writes erledigt }}
        progress zeitgeber_tickt
    {{
        erledigt = 1;
    }}
}}
}}""",

    # ----------------------------------------------------------------------------------
    # The LEXICAL half: `ident`. A name has two ends -- empty and enormous -- and the
    # emitter writes every one of them into C, where the standard promises 63 significant
    # characters. Six positions, because the checker reaches a name by six different paths.
    # ----------------------------------------------------------------------------------
    "name-const": """module f {{
const {V} : u64 = 7;
}}""",
    "name-modul": """module {V} {{
const K : u64 = 7;
}}""",
    "name-fn": """module f {{
impl fn {V}() -> u64
    effects {{ pure }}
    costs   <= 2 ops
{{
    return 1;
}}
}}""",
    "name-feld": """module f {{
format F endian big {{ {V} : u32 @[31:0], }}
}}""",
    "name-reg": """module f {{
opaque type Pa = u64;
device D(basis : Pa) at mmio {{ reg {V} : u64 @0x0 class rw }}
}}""",
    "name-tabelle": """module f {{
table {V} count 8 {{ slot {{ a : u32, }} }}
}}""",

    "name-typ": """module f {{
opaque type {V} = u64;
}}""",
    "name-parameter": """module f {{
spec fn g({V} : u64) -> u64
    effects {{ pure }}
    = {V};
}}""",

    # ----------------------------------------------------------------------------------
    # The four STATEMENT rules that admit an expression. Every literal above stands in a
    # declaration; these are the same ladder inside a function body, where `M1` reads it.
    # ----------------------------------------------------------------------------------
    "if-bedingung": """module f {{
impl fn g() -> u64
    effects {{ pure }}
    costs   <= 4 ops
{{
    if {V} >= 1 {{
        return 1;
    }}
    return 0;
}}
}}""",
    "let-wert": """module f {{
impl fn g() -> u64
    effects {{ pure }}
    costs   <= 4 ops
{{
    let x : u64 = {V};
    return x;
}}
}}""",
    "zuweisung": """module f {{
static mut x : u64 = 0;
impl fn g()
    effects {{ writes x }}
    costs   <= 4 ops
{{
    x = {V};
}}
}}""",
    "aufruf-argument": """module f {{
spec fn h(a : u64) -> u64
    effects {{ pure }}
    = a;
spec fn g() -> u64
    effects {{ pure }}
    = h({V});
}}""",

    # `f64 in a .. b` -- the float refinement, the one range whose ends are not integers.
    "gleitkomma-bereich": """module f {{
type R = f64 in 0.0 .. {V};
}}""",

    # `traverse ... decreases X` -- swept over NAMES, see the note at `LEITER`.
    "traverse-abnahme": """module f {{
table T count 8 {{ slot {{ a : bool, }} }}
impl fn g()
    effects {{ reads T, writes T.slots }}
    costs   <= 200 ops
{{
    traverse s over slots of T by unvisited
        decreases {V}
        touches writes T.slots
    {{
        T.slots[s].a = false;
    }}
}}
}}""",

    # ----------------------------------------------------------------------------------
    # STRING literals -- the third lexical shape, and the only one with an UNTERMINATED
    # form. Three positions: the sentence of an assumption, the message of a refusal code,
    # and the linker section of a static.
    # ----------------------------------------------------------------------------------
    "text-annahme": """module f {{
assume a {V} falsifier zeitablauf;
}}""",
    "text-grund": """module f {{
reason R {{
    A = 1 {V}
    exhaustive
}}
}}""",
    "text-abschnitt": """module f {{
static mut x : u64 = 0 section {V};
}}""",

    # ----------------------------------------------------------------------------------
    # DEPTH. The parser is recursive descent; "how deep" is a question its own stack
    # answers, and a stack that runs out is a third answer.
    # ----------------------------------------------------------------------------------
    "typ-tiefe-zeiger": """module f {{
static p : {V} = 0;
}}""",
    "typ-tiefe-array": """module f {{
static mut A : {V} = 0;
}}""",
    "typ-tiefe-klammer": """module f {{
impl fn g() -> u64
    effects {{ pure }}
    costs   <= 2 ops
{{
    return {V};
}}
}}""",
}


def lauf(binaer, datei, timeout=25):
    """One run. Returns (exit, panicked, text). NEVER raises -- a crash is a datum."""
    try:
        p = subprocess.run(
            [binaer, "check", str(datei)],
            capture_output=True, text=True, timeout=timeout, errors="replace",
        )
    except subprocess.TimeoutExpired:
        return (None, False, "<TIMEOUT>")
    text = p.stdout + p.stderr
    panik = "panicked at" in text or "RUST_BACKTRACE" in text
    return (p.returncode, panik, text)


def antwort(exit_code, panik, text):
    """The ANSWER, reduced to what the property is about.

    Not the full diagnostic text: two builds may legitimately word a message differently
    one day. What must agree is *which* of the three answers came back, and -- when it is
    a refusal -- *which code*.
    """
    if panik:
        return "PANIC"
    if exit_code is None:
        return "TIMEOUT"
    if exit_code not in (0, 1, 2):
        return f"EXIT{exit_code}"
    # The diagnostic prints its code in brackets: `error: [N050] file:3:9: ...`. Stripping
    # `[]` is not cosmetic -- without it every refusal came back `EXIT1-UNNAMED`, and the
    # instrument reported 595 "unexpected exits" over a corpus that was answering correctly.
    codes = sorted({w.strip("[]:,.`") for w in text.split()
                    if len(w.strip("[]:,.`")) == 4
                    and w.strip("[]:,.`")[0].isupper()
                    and w.strip("[]:,.`")[1:].isdigit()})
    if exit_code == 0:
        return "ACCEPT"
    return "REFUSE " + ",".join(codes) if codes else f"EXIT{exit_code}-UNNAMED"


# ===========================================================================================
# COVERAGE -- the denominator, and there are two of them
# ===========================================================================================
#
# **A rule with no literal in it has no rung to climb, and counting it would be `W25` in this
# tool's own numbers.** `program = { item }` cannot be pushed to a boundary; `bank` can. So
# the fraction is published three times over, and the middle number is the honest one:
#
#     rules in `dokumente/SYNTAX.md`         everything the grammar defines
#     rules that CAN carry a boundary        those whose own production names a literal slot
#     rules this sweep drives                those a `REGEL` entry points at
#
# "Own production" and not "can reach one transitively": under the transitive reading
# `program` carries every boundary in the language, which is true and useless.

# The literal-producing nonterminals. A rule that names one of these in its own body has a
# slot a value can be written into.
NUM_LEAF = {"int", "dec", "hex", "bin", "float", "constexpr", "costexpr", "bitpos"}
LEX_LEAF = {"ident", "string", "path", "pathseg", "identlist", "char"}
# `expr` is numeric in every position the emitter lowers to arithmetic; a rule that admits
# one admits an integer literal, so it has a rung.
EXPR_LEAF = {"expr"}


def regeln_lesen(pfad):
    """Parse the EBNF blocks of `dokumente/SYNTAX.md` into {name: body}."""
    text = pathlib.Path(pfad).read_text(encoding="utf-8")
    bloecke = re.findall(r"```ebnf\n(.*?)```", text, re.S)
    quelle = re.sub(r"\(\*.*?\*\)", " ", "\n".join(bloecke), flags=re.S)
    stellen = [(m.start(), m.group(1))
               for m in re.finditer(r"^([a-z][a-z0-9_]*)\s*=", quelle, re.M)]
    regeln = {}
    for i, (pos, name) in enumerate(stellen):
        ende = stellen[i + 1][0] if i + 1 < len(stellen) else len(quelle)
        rumpf = quelle[pos:ende].split("=", 1)[1]
        regeln[name] = rumpf.rsplit(";", 1)[0] if ";" in rumpf else rumpf
    return regeln


def deckung(pfad="dokumente/SYNTAX.md"):
    """Print the three denominators. Returns (total, tragend, gefegt)."""
    regeln = regeln_lesen(pfad)

    def verweise(rumpf):
        return set(re.findall(r"\b[a-z][a-z0-9_]*\b", re.sub(r'"[^"]*"', " ", rumpf)))

    num, lex, tragend = set(), set(), set()
    for name, rumpf in regeln.items():
        v = verweise(rumpf)
        if (v & NUM_LEAF) or (v & EXPR_LEAF) or name in NUM_LEAF:
            num.add(name)
        if (v & LEX_LEAF) or name in LEX_LEAF:
            lex.add(name)
    tragend = num | lex

    gefegt = {r for r in REGEL.values()}
    fremd = sorted(gefegt - set(regeln))
    gefegt_gueltig = gefegt & set(regeln)

    print("== BOUNDARY COVERAGE against dokumente/SYNTAX.md ==")
    print(f"   {len(regeln):3d}  EBNF rules defined")
    print(f"   {len(tragend):3d}  can carry a boundary at all "
          f"({len(num)} numeric, {len(lex)} lexical, {len(num & lex)} both)")
    print(f"   {len(regeln) - len(tragend):3d}  carry no literal -- no rung to climb, "
          f"and counting them would be W25")
    print(f"   {len(gefegt_gueltig):3d}  driven by this sweep "
          f"({100 * len(gefegt_gueltig) // max(1, len(tragend))} % of what can carry one)")
    print()
    ungefegt = sorted(tragend - gefegt_gueltig)
    print(f"-- CAN CARRY A BOUNDARY, NOT SWEPT: {len(ungefegt)} --")
    for i in range(0, len(ungefegt), 6):
        print("   " + "  ".join(f"{r:16s}" for r in ungefegt[i:i + 6]))
    print()
    if fremd:
        print(f"-- REGEL NAMES NO RULE OF THE GRAMMAR: {len(fremd)} -- {' '.join(fremd)}")
        print("   a coverage claim whose numerator is not in the denominator is not one.")
        print()
    return len(regeln), len(tragend), len(gefegt_gueltig), fremd


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--debug")
    ap.add_argument("--release")
    ap.add_argument("--keep")
    ap.add_argument("--nur", help="only this form")
    ap.add_argument("--deckung", action="store_true",
                    help="coverage against the grammar, without running the checker")
    ap.add_argument("--syntax", default="dokumente/SYNTAX.md")
    args = ap.parse_args()

    # **The table's own closure, checked before anything reads it.** Four parallel dicts key
    # every form; a form added to one and forgotten in another is a template that never runs
    # (missing from `FORMEN`), a sweep with no baseline (missing from `GUT`), or a case that
    # counts for no rule (missing from `REGEL`). All three are silent.
    fehlt = []
    for name in sorted(FORMEN):
        if name not in GUT:
            fehlt.append(f"{name}: no GUT baseline")
        if name not in REGEL:
            fehlt.append(f"{name}: no REGEL entry, so it counts for no rule")
        if LEITER.get(name, "zahl") not in LEITERN:
            fehlt.append(f"{name}: LEITER names no ladder")
    for name in sorted(set(GUT) | set(REGEL) | set(LEITER)):
        if name not in FORMEN:
            fehlt.append(f"{name}: named beside the table, but there is no template")
    if fehlt:
        print("== THE FORM TABLE IS NOT CLOSED, AND NOTHING BELOW WAS MEASURED ==")
        for z in fehlt:
            print(f"   {z}")
        return 1

    if args.deckung:
        _, _, _, fremd = deckung(args.syntax)
        return 1 if fremd else 0

    if not args.debug or not args.release:
        ap.error("--debug and --release are required unless --deckung is given")

    formen = {k: v for k, v in FORMEN.items() if not args.nur or k == args.nur}
    if not formen:
        print(f"== `--nur {args.nur}` names no form, so NOTHING was measured ==")
        return 1

    arb = pathlib.Path(args.keep) if args.keep else pathlib.Path(tempfile.mkdtemp())
    arb.mkdir(parents=True, exist_ok=True)

    # **The instrument's own speech test, and it runs BEFORE the sweep.** A template whose
    # known-good value is refused is not measuring its numeric field -- it is measuring a
    # constant parse error, 60 times, and reporting it as findings.
    #
    # The counter-direction of this speech test is on the record rather than in a branch:
    # three runs of this tool over the same tree gave 7 panics, then 3, then 0, as the two
    # arithmetic repairs and the message repair landed. *A tool nobody has seen fall is an
    # ornament* (R11); this one has been seen falling twice on its way to green, and once
    # over a defect planted on purpose (see the module docstring).
    tot = []
    for form in sorted(formen):
        f = arb / f"basis-{form}.gab"
        f.write_text(formen[form].format(V=GUT[form]) + "\n")
        a = antwort(*lauf(args.debug, f))
        if a != "ACCEPT":
            tot.append((form, GUT[form], a))
    if tot:
        print("== THE GENERATOR IS BROKEN, AND NOTHING BELOW WAS MEASURED ==")
        for form, wert, a in tot:
            print(f"   {form:20s} baseline `{wert}` -> {a}, so every value gives the same answer")
        print("   A template whose baseline does not parse has an EMPTY population (W17).")
        return 1

    panics, uneinig, sonst = [], [], []
    verteilung = {}
    n = 0
    for form, schablone in sorted(formen.items()):
        verteilung[form] = {}
        for wert in LEITERN[LEITER.get(form, "zahl")]:
            n += 1
            f = arb / f"{form}--{n:05d}.gab"
            f.write_text(schablone.format(V=wert) + "\n")
            de, dp, dt = lauf(args.debug, f)
            re_, rp, rt = lauf(args.release, f)
            a_d, a_r = antwort(de, dp, dt), antwort(re_, rp, rt)
            verteilung[form][a_d] = verteilung[form].get(a_d, 0) + 1
            if a_d == "PANIC" or a_r == "PANIC":
                panics.append((form, wert, a_d, a_r, dt if dp else rt))
            elif a_d != a_r:
                uneinig.append((form, wert, a_d, a_r, ""))
            elif a_d.startswith("EXIT") or a_d == "TIMEOUT":
                sonst.append((form, wert, a_d, a_r, dt))

    je = {name: len(LEITERN[LEITER.get(name, "zahl")]) for name in formen}
    print(f"== BOUNDARY SWEEP: {n} cases over {len(formen)} forms ==")
    print(f"   {len(LADDER)} numeric rungs + {len(LEXICAL)} lexical shapes "
          f"+ {len(NEGATIV)} signed = {len(ZAHLEN)} per numeric form")
    print(f"   {len(NAMEN)} identifier shapes, {len(TIEFEN)} nesting depths")
    print(f"   {sum(1 for f in formen if LEITER.get(f, 'zahl') == 'zahl')} numeric forms, "
          f"{sum(1 for f in formen if LEITER.get(f) == 'name')} name forms, "
          f"{sum(1 for f in formen if str(LEITER.get(f, '')).startswith('tiefe'))} depth forms"
          f"  ({min(je.values())}..{max(je.values())} cases each)")
    print()

    def zeige(titel, liste, erklaerung):
        print(f"-- {titel}: {len(liste)} --")
        if erklaerung and liste:
            print(f"   {erklaerung}")
        for form, wert, a_d, a_r, extra in liste:
            kurz = wert if len(wert) <= 44 else f"{wert[:24]}...<{len(wert)} chars>"
            print(f"   {form:20s} {kurz:46s} debug={a_d:22s} release={a_r}")
            if extra:
                for zeile in extra.splitlines():
                    if "panicked at" in zeile or "overflowed its stack" in zeile:
                        print(f"        {zeile.strip()}")
        print()

    zeige("PANICS -- a third answer", panics,
          "the checker neither accepted nor refused by name")
    zeige("DEBUG/RELEASE DISAGREE -- a wrap that only the shipped build makes", uneinig,
          "release is what `cargo install` produces; the honest answer is the one nobody ships")
    zeige("OTHER -- unexpected exit or timeout", sonst, "")

    # **A form whose every rung comes back with the SAME answer measured its slot once and
    # then repeated itself.** The baseline speech test above catches a template that does
    # not parse; it cannot catch one that parses and whose swept slot the checker never
    # looks at -- the value goes in, the answer never moves, and 111 green cases are one
    # green case counted 111 times. *That is `W17` with a larger numerator, and a large
    # numerator is exactly what makes a clean sweep sound like a big claim.*
    #
    # This is a REPORT and not a refusal: `range-verkehrt` legitimately answers `M104` at
    # every rung above zero, and a slot the grammar admits but the checker has no rule for
    # is a finding for the poison corpus, not for this property.
    stumpf = sorted(f for f, v in verteilung.items() if len(v) <= 1)
    print(f"-- ONE ANSWER FOR EVERY RUNG: {len(stumpf)} of {len(formen)} forms --")
    if stumpf:
        print("   the swept slot moved and the answer did not; the population is one case")
        for f in stumpf:
            (a, k), = verteilung[f].items()
            print(f"   {f:20s} {k:4d} x {a}")
    print()
    print("-- ANSWERS PER FORM --")
    for f in sorted(verteilung):
        teile = ", ".join(f"{k} x {a}" for a, k in
                          sorted(verteilung[f].items(), key=lambda p: -p[1]))
        print(f"   {f:20s} {teile}")
    print()

    schlecht = len(panics) + len(uneinig) + len(sonst)
    if args.keep:
        print(f"   generated files kept in {arb}")
    print(f"== {n - schlecht} of {n} answered the same in both builds, without a panic ==")
    return 1 if schlecht else 0


if __name__ == "__main__":
    # **`abschnitt.fahre` and not a bare `main()`.** This tool has an exit ABOVE its sweep --
    # the broken-generator branch -- and a run that leaves there has measured nothing while
    # returning the same `1` a finding returns. *A tool that measured nothing must not look
    # like one that found something.*
    sys.exit(abschnitt.fahre(main))
