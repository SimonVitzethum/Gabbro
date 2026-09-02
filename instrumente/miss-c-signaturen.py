#!/usr/bin/env python3
"""**The HANDLE for the signature table of `N046` -- and for the need-count of `N041`.**

`W28`: a number that carries a rule belongs beside its handle. The 558-name table in
`crates/gabbro-check/src/cnamen.rs` carries its own -- this tool is the second half:
**which of those names can an `extern fn` bind at all, and with which signature?**

Three questions to the same compiler, and not one of them guessed:

  1. `#ifdef N`                        -- is the name a MACRO? Then there is no declaration
                                          site at all: the preprocessor rewrites the name
                                          before the parser ever sees a declaration.
  2. `N x;` compiles                   -- is the name a TYPEDEF? Then no function in the
                                          same scope can carry it.
  3. `cc -aux-info` / `expected '...'` -- the signature C knows for the name.

Then the fourth, and Gabbro asks that one: **can `emit.rs` write that signature at all?** A
`_Complex double` or a `char *` has no Gabbro form; an `int(int)` has one, namely
`extern fn N(a : i32) -> i32`.

    ./instrumente/miss-c-signaturen.py            # the report
    ./instrumente/miss-c-signaturen.py --tafel    # the Rust table for `cnamen.rs`
    ./instrumente/miss-c-signaturen.py --pruefe   # the BUILT-IN table against the measurement

**The equivalences are measured, not assumed.** `int == int32_t` and `long == int64_t` hold
under LP64 and not everywhere; the run falls when `_Static_assert` does not confirm them
here. *The same footing the 558-name table already stands on.*
"""
from __future__ import annotations

import os
import re
import subprocess
import sys
import tempfile
from collections import Counter

WURZEL = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CNAMEN = f"{WURZEL}/crates/gabbro-check/src/cnamen.rs"

# The four headers EVERY generated unit includes -- `emit.rs` writes them.
KOPF = ("#include <stdint.h>\n#include <stdbool.h>\n"
        "#include <stdatomic.h>\n#include <math.h>\n")

# What `ctyp` in `emit.rs` can produce at a position with none of the unit's own types.
CTYP = {"uint8_t", "uint16_t", "uint32_t", "uint64_t",
        "int8_t", "int16_t", "int32_t", "int64_t",
        "bool", "float", "double", "void"}

# How GCC spells the types -> how `emit.rs` spells them. **Measured, see below.**
GLEICH = {
    "int": "int32_t", "unsigned int": "uint32_t",
    "long": "int64_t", "long int": "int64_t",
    "unsigned long": "uint64_t", "long unsigned int": "uint64_t",
    # **`long long` is NOT here, and that is measured:** `_Static_assert` with
    # `__builtin_types_compatible_p` FAILS for `long long` against `int64_t`. Same WIDTH is
    # not the same type; `int64_t` is `long` here, and C keeps the two apart.
    # *Without this measurement `llabs`, `llrint` and `llround` would have landed in the
    # table with a signature `cc` rejects.*
    "short": "int16_t", "short int": "int16_t",
    "unsigned short": "uint16_t", "short unsigned int": "uint16_t",
    "signed char": "int8_t", "unsigned char": "uint8_t",
    "_Bool": "bool", "float": "float", "double": "double", "void": "void",
}
# And back -- for the refusal that names C in C's own words.
UMGANG = {"int32_t": "int", "uint32_t": "unsigned int", "int64_t": "long",
          "uint64_t": "unsigned long", "int16_t": "short", "uint16_t": "unsigned short",
          "int8_t": "signed char", "uint8_t": "unsigned char", "bool": "_Bool",
          "float": "float", "double": "double", "void": "void"}
# And the Gabbro words -- for the refusal that names the writer the FORM.
GABBRO = {"int32_t": "i32", "uint32_t": "u32", "int64_t": "i64", "uint64_t": "u64",
          "int16_t": "i16", "uint16_t": "u16", "int8_t": "i8", "uint8_t": "u8",
          "bool": "bool", "float": "f32", "double": "f64"}

# **The two POSIX spellings, and they are measured under `<unistd.h>` and not here.**
#
# `size_t` and `ssize_t` are names the STANDARDS give (C11 §7.19, POSIX); `__off_t`,
# `__pid_t`, `__uid_t` and `__gid_t` are glibc's own and stay out on purpose -- the same
# decision the 558-name table already took for the 883 underscore macros: *a list that
# carries them measures glibc and calls it POSIX.* A declaration that needs one of them is
# therefore not bindable, and the refusal names the type.
GLEICH_POSIX = {"size_t": "uint64_t", "ssize_t": "int64_t"}

UMGEBUNG = dict(os.environ, LC_ALL="C")
_TMP = tempfile.mkdtemp(prefix="gabbro-csig-")
# **Every execution with a deadline** -- the house rule, and this file stood outside it until
# 2026-09-02. A hang looks like "still running", not like a finding; on 2026-08-20 twenty-one
# runs of `pruefe-emission.sh` stood side by side because of exactly that, the oldest for
# three and a half hours. This tool drives `cc` about 1200 times in a run.
FRIST = 120


def _cc(rumpf: str, *zusatz: str) -> subprocess.CompletedProcess:
    c = f"{_TMP}/probe.c"
    with open(c, "w", encoding="utf-8") as f:
        f.write(KOPF + rumpf)
    return subprocess.run(["cc", "-std=c11", "-O0", *zusatz, "-fsyntax-only", c],
                          capture_output=True, text=True, env=UMGEBUNG, timeout=FRIST)


def sprechprobe() -> list[tuple[str, bool]]:
    """**Sieht dieses Werkzeug ueberhaupt einen Unterschied?** In beide Richtungen.

    Everything this file reports rests on one harness: `_cc` writes a fragment and reads a
    return code. **If that harness is broken, every answer comes out the same** -- and the
    same way round, because a `cc` that always fails makes every name unbindable and a `cc`
    that always succeeds makes every equivalence hold. Both look like a measurement.

    That is `D1` word for word: a broken fixture in `fuzze-grenzen.py` lowered 130 cases to
    non-compiling C for two days under a green run, and 195 of 273 non-compiling cases were
    three broken fixtures counted 195 times. *A fixture nobody has seen catching anything is
    not a fixture.*

    The subject is brought along, not found: two `_Static_assert`s over types every C
    implementation has, one true and one false.
    """
    gut = _cc('_Static_assert(__builtin_types_compatible_p(int, int), "x");\n')
    schlecht = _cc('_Static_assert(__builtin_types_compatible_p(int, double), "x");\n')
    return [
        ("eine WAHRE Aequivalenz (`int` == `int`) kommt durch", gut.returncode == 0),
        ("eine FALSCHE (`int` == `double`) faellt", schlecht.returncode != 0),
    ]


def tafel_lesen() -> tuple[list[str], list[tuple[str, str]], list[str]]:
    """The three tables out of `cnamen.rs` -- read, not copied."""
    q = open(CNAMEN, encoding="utf-8").read()

    def block(anfang: str) -> str:
        i = q.index(anfang)
        return q[i:q.index("];", i)]

    c11 = re.findall(r'"([^"]+)"', block("static C11_WORT"))
    hdr = re.findall(r'\("([^"]+)",\s*"([^"]+)"\)', block("static HEADER"))
    ein = re.findall(r'"([^"]+)"', block("static EINGEBAUT"))
    return c11, hdr, ein


def art_des_headernamens(n: str) -> str:
    if _cc(f"#ifdef {n}\n#else\n#error nein\n#endif\n").returncode == 0:
        return "Makro"
    if _cc(f"{n} gabbro_probe_x;\n").returncode == 0:
        return "Typedef"
    if _cc(f"void *gabbro_probe_p = (void *) &{n};\n").returncode == 0:
        return "Funktion"
    return "unklar"


def signaturen_aus_aux() -> dict[str, tuple[str, list[str]]]:
    """Every declaration of the four headers, as `cc -aux-info` writes it."""
    c, info = f"{_TMP}/aux.c", f"{_TMP}/aux.info"
    with open(c, "w", encoding="utf-8") as f:
        f.write(KOPF)
    subprocess.run(["cc", "-std=c11", "-aux-info", info, "-fsyntax-only", c],
                   capture_output=True, text=True, env=UMGEBUNG, cwd=_TMP, timeout=FRIST)
    aus: dict[str, tuple[str, list[str]]] = {}
    for zeile in open(info, encoding="utf-8"):
        m = re.match(r"^/\*.*\*/\s*extern\s+(.*?)\s*;\s*$", zeile.strip())
        if not m:
            continue
        m2 = re.match(r"^(.*?)\b([A-Za-z_][A-Za-z0-9_]*)\s*\((.*)\)$", m.group(1))
        if not m2:
            continue
        r, n, a = m2.group(1).strip(), m2.group(2), m2.group(3).strip()
        aus[n] = (r, [] if a in ("void", "") else [x.strip() for x in a.split(",")])
    return aus


def signatur_des_eingebauten(n: str) -> tuple[str, list[str]] | None:
    """`void N(void);` -- and GCC names in its `expected '...'` the signature it knows."""
    r = _cc(f"void {n}(void);\n", "-Wall", "-Wextra", "-Werror")
    if r.returncode == 0:
        return ("void", [])
    m = re.search(r"expected '([^']+)'", r.stderr)
    if not m:
        return None
    m2 = re.match(r"^(.*?)\((.*)\)$", m.group(1))
    if not m2:
        return None
    a = m2.group(2).strip()
    return (m2.group(1).strip(),
            [] if a in ("void", "") else [x.strip() for x in a.split(",")])


# **`void *` in a PARAMETER is writable; `void *` as a RESULT is not** -- and the asymmetry
# is the whole rule, not a convenience. See `cnamen.rs`, *"which way the precision flows"*.
#
#   parameter   `write(int, const void *, size_t)`   Gabbro says `ptr<normal, r> T`, C erases
#               it to `const void *`. **Gabbro SUPPLIES precision C did not ask for**, the
#               conversion is implicit in C, and the call is exact on the Gabbro side.
#   result      `void *memcpy(void *, const void *, size_t)`   Gabbro would have to say
#               `ptr<normal, rw> u8` for something C typed as "any object". **Gabbro would
#               INVENT precision C never had**, and nothing on either side can check it.
#
# *Measured 2026-09-02:* `int64_t write(int32_t, const void *, uint64_t);` compiles clean
# under `-Wall -Wextra -Werror` **with `<unistd.h>` beside it** -- it is compatible with the
# real declaration. `int64_t write(int32_t, const Text *, uint64_t);` is not.
ZEIGER = {"void *": "void *", "const void *": "const void *"}


def absenkbar(sig: tuple[str, list[str]]) -> tuple[str, str] | tuple[None, str]:
    """The signature in `emit.rs` spelling -- or the reason there is none."""
    r, args = sig
    if any("..." in t for t in args):
        return None, "variadic -- Gabbro has no variadic form"
    if "*" in r or "[" in r:
        # **The result position takes no pointer at all** -- see `ZEIGER` above.
        return None, f"C's declaration returns `{r.strip()}`, and Gabbro has no such type"
    teile = []
    for i, t in enumerate([r] + args):
        z = ZEIGER.get(t.strip())
        if z is not None and i > 0:
            teile.append(z)
            continue
        if "*" in t or "[" in t:
            return None, f"C's declaration takes `{t.strip()}`, and Gabbro has no such type"
        g = GLEICH.get(t.strip()) or GLEICH_POSIX.get(t.strip())
        if g is None or g not in CTYP:
            return None, f"C's declaration takes `{t.strip()}`, and Gabbro has no such type"
        teile.append(g)
    return f"{teile[0]}({','.join(teile[1:]) or 'void'})", ""


def gabbro_form(name: str, c: str) -> str:
    """The Gabbro line that produces exactly this C signature -- for the refusal."""
    m = re.match(r"^(\w+ \*|\w+)\((.*)\)$", c)
    r, a = m.group(1), m.group(2)
    ps = [] if a == "void" else a.split(",")
    # **`T` is the writer's own type, and it stays theirs.** C erased it to `void *`; the
    # Gabbro line names one and the emitted prototype writes C's word back.
    kopf = ", ".join(
        f"{chr(97 + i)} : " + ("ptr<normal, r> T" if t == "const void *"
                               else "ptr<normal, rw> T" if t == "void *"
                               else GABBRO[t])
        for i, t in enumerate(ps))
    schwanz = "" if r == "void" else f" -> {GABBRO[r]}"
    return f"extern fn {name}({kopf}){schwanz}"


def c_wort(sig: tuple[str, list[str]]) -> str:
    """C's declaration in C's OWN words -- what the refusal shows the writer."""
    r, args = sig
    return f"{r}({', '.join(args) or 'void'})"


# **The three names where the derivation below is WRONG, and each is named.**
#
# The test is *"a `char *` and no length beside it"*. These three carry a `size_t` -- and it
# bounds the OUTPUT buffer, not the FORMAT string, which is still read to its NUL:
#
#     snprintf(char *s, size_t n, const char *f, ...)   `n` bounds `s`. `f` is scanned.
#     vsnprintf(char *s, size_t n, const char *f, va)   the same.
#     strftime(char *s, size_t n, const char *f, tm)    the same.
#     strncat(char *d, const char *s, size_t n)         `n` bounds the READ from `s` -- and
#                                                       the write to `d` starts at `d`'s own
#                                                       NUL, which `strncat` must SCAN for.
#                                                       *The count bounds the wrong half.*
#
# *A derivation with four named exceptions is a measurement. One with none is a guess.*
ABSCHLUSS_DAZU = ("snprintf", "vsnprintf", "strftime", "strncat")

# And the two the derivation would call terminator-read and which are NOT: both sides of
# each are bounded by the count. `strncpy` stops at the source's NUL **or** at `n`, and
# `strncmp` likewise -- neither reads past `n` even when no NUL is there.
ABSCHLUSS_NICHT = ("strncpy", "strncmp")

# The words C uses for a count in the declarations `-aux-info` writes.
LAENGENWORT = ("long unsigned int", "unsigned long", "size_t")


def endet_in_den_daten(name: str, sig: tuple[str, list[str]]) -> bool:
    """**Does this function find the end of its data IN the data?**

    A `char *` with no count beside it means: the callee reads until it meets a NUL, and how
    far that is stands nowhere in the signature. *That is the property, and it is a property
    of the DECLARATION -- readable without knowing what the function does.*
    """
    if name in ABSCHLUSS_DAZU:
        return True
    if name in ABSCHLUSS_NICHT:
        return False
    _r, args = sig
    hat_zeichenzeiger = any("char *" in t for t in args)
    hat_laenge = any(w in t for t in args for w in LAENGENWORT)
    return hat_zeichenzeiger and not hat_laenge


# **The headers this measurement reads -- and the whole of the guard's second edge.**
#
# `<unistd.h>` is where the finding came from: `write` is not a C11 name, so the 558-name
# table never sees it, and a generated unit that declares `int64_t write(int32_t, const Text
# *, uint64_t)` compiles clean, links to the real symbol and disagrees with it.
#
# **The other three are here because the CORPUS reaches them, and for no other reason.**
# Measured 2026-09-02 over every `extern fn` in `beispiele/`, `messung/` and
# `dokumente/FRAGMENTE.md`: 266 sites, 157 distinct names, and exactly THREE of them name a
# symbol that a system header declares and libc exports -- `open` (`<fcntl.h>`), `signal`
# (`<signal.h>`) and `recv` (`<sys/socket.h>`). Those three headers, and not a fourth.
#
# *Anything these headers do not declare is OUTSIDE the guard, and `cnamen.rs` and the report
# below both say so in as many words.* Headers measured are a boundary; "POSIX" as a word
# would be a claim.
POSIX_KOEPFE = ("unistd.h", "fcntl.h", "signal.h", "sys/socket.h")


def kopf_signaturen(kopf: str) -> dict[str, tuple[str, list[str]]]:
    """Every function this header ITSELF declares -- `cc -aux-info`, same as the C11 half.

    **Only the declarations whose site IS the header.** `-aux-info` reports everything the
    preprocessor pulled in, and `<unistd.h>` pulls in `<stddef.h>` and the glibc internals
    with it; a table that keeps those measures glibc and calls it POSIX.
    """
    marke = re.sub(r"\W", "_", kopf)
    c, info = f"{_TMP}/posix-{marke}.c", f"{_TMP}/posix-{marke}.info"
    with open(c, "w", encoding="utf-8") as f:
        f.write(f"#include <{kopf}>\n")
    subprocess.run(["cc", "-std=c11", "-aux-info", info, "-fsyntax-only", c],
                   capture_output=True, text=True, env=UMGEBUNG, cwd=_TMP, timeout=FRIST)
    aus: dict[str, tuple[str, list[str]]] = {}
    for zeile in open(info, encoding="utf-8"):
        m = re.match(r"^/\*\s*(\S+):\d+:\w+\s*\*/\s*extern\s+(.*?)\s*;\s*$", zeile.strip())
        if not m or not m.group(1).endswith(f"/{kopf}"):
            continue
        m2 = re.match(r"^(.*?)\b([A-Za-z_][A-Za-z0-9_]*)\s*\((.*)\)$", m.group(2))
        if not m2:
            continue
        r, n, a = m2.group(1).strip(), m2.group(2), m2.group(3).strip()
        if n.startswith("__"):
            continue
        aus[n] = (r, [] if a in ("void", "") else [x.strip() for x in a.split(",")])
    return aus


def posix_signaturen() -> dict[str, tuple[str, tuple[str, list[str]]]]:
    """All four headers, name -> (header, signature). **The FIRST header that declares a
    name owns it**, and the order is the order of `POSIX_KOEPFE`.

    A name two headers declare is one name with one declaration; a table that carried it
    twice would answer a lookup by whichever row the binary search happened to land on.
    *`W7`, the same reason `POSIX` is not folded into `vergeben`.*
    """
    aus: dict[str, tuple[str, tuple[str, list[str]]]] = {}
    for kopf in POSIX_KOEPFE:
        for n, sig in kopf_signaturen(kopf).items():
            aus.setdefault(n, (kopf, sig))
    return aus


def messen() -> tuple[dict[str, tuple[str, str, str]], Counter, dict[str, str]]:
    """(name -> (C words, lowering, Gabbro form)), the tally, and (name -> reason).

    **The lowering and the Gabbro form are empty exactly when no `extern fn` can bind the
    name** -- and the row stands there anyway, because a refusal that shows
    `void *(void *, const void *, unsigned long)` explains itself and one that says
    "taken" does not.
    """
    c11, hdr, ein = tafel_lesen()
    aux = signaturen_aus_aux()
    tafel: dict[str, tuple[str, str, str]] = {}
    grund: dict[str, str] = {}
    z: Counter = Counter()

    for n in c11:
        z["C11-Wort"] += 1
        grund[n] = "a keyword of C11 -- no C declaration can carry it as a name"

    for n, _h in hdr:
        art = art_des_headernamens(n)
        z[f"Header/{art}"] += 1
        if art == "Makro":
            grund[n] = ("a macro of the header -- the preprocessor rewrites the name "
                        "before the parser sees a declaration")
            continue
        if art == "Typedef":
            grund[n] = ("a typedef of the header -- no function in the same scope "
                        "can carry the name")
            continue
        if art != "Funktion" or n not in aux:
            grund[n] = "no declaration this measurement could read"
            continue
        sig, warum = absenkbar(aux[n])
        if sig is None:
            grund[n] = warum
            tafel[n] = (c_wort(aux[n]), "", "")
            z["Header/Funktion nicht bindbar"] += 1
        else:
            tafel[n] = (c_wort(aux[n]), sig, gabbro_form(n, sig))
            z["Header/Funktion BINDBAR"] += 1

    for n in ein:
        z["Eingebaut"] += 1
        s = signatur_des_eingebauten(n)
        if s is None:
            grund[n] = "no declaration this measurement could read"
            continue
        sig, warum = absenkbar(s)
        if sig is None:
            grund[n] = warum
            tafel[n] = (c_wort(s), "", "")
            z["Eingebaut nicht bindbar"] += 1
        else:
            tafel[n] = (c_wort(s), sig, gabbro_form(n, sig))
            z["Eingebaut BINDBAR"] += 1
    return tafel, z, grund


def aequivalenzen_pruefen() -> list[str]:
    """`int == int32_t`? Not assumed -- `_Static_assert` says so.

    **And since 2026-09-02 that covers `GLEICH_POSIX` too.** It did not. The two POSIX
    spellings carried a comment saying they are *measured under `<unistd.h>` and not here*,
    and `absenkbar()` reads them at `:217` with exactly the trust it gives the asserted
    table -- both feed the same `BINDBAR` verdict. So the module docstring's *"The
    equivalences are measured, not assumed"* held for one of two tables, and the printed
    count `len(GLEICH) - 1` excluded the other by construction.

    They need a header `KOPF` does not carry, which is the whole reason they sat outside;
    that is one extra `#include` on the fragment, not a reason.
    """
    kaputt = []
    for c, s in sorted(GLEICH.items()):
        if s == "void":
            continue
        r = _cc(f"_Static_assert(__builtin_types_compatible_p({c}, {s}), \"x\");\n")
        if r.returncode != 0:
            kaputt.append(f"{c} != {s}")
    for c, s in sorted(GLEICH_POSIX.items()):
        r = _cc("#include <unistd.h>\n#include <sys/types.h>\n"
                f"_Static_assert(__builtin_types_compatible_p({c}, {s}), \"x\");\n")
        if r.returncode != 0:
            kaputt.append(f"{c} != {s}  (POSIX, LP64)")
    return kaputt


def tafel_gegen_cc(tafel: dict[str, tuple[str, str]]) -> list[str]:
    """**The counter-probe that counts:** every table line as a C declaration, through `cc`.

    A signature table nobody has compiled is an assertion. This loop turns every line into
    exactly what `emit.rs` would write and hands it to `cc` under `-Wall -Wextra -Werror`.
    *What passes here passes in the generated C.*
    """
    kaputt = []
    for n, spalten in sorted(tafel.items()):
        sig = spalten[1]
        if not sig:
            continue
        m = re.match(r"^(\w+)\((.*)\)$", sig)
        r, a = m.group(1), m.group(2)
        ps = "void" if a == "void" else ", ".join(
            f"{t} p{i}" for i, t in enumerate(a.split(",")))
        e = _cc(f"{r} {n}({ps});\n", "-Wall", "-Wextra", "-Werror")
        if e.returncode != 0:
            erste = next((z for z in e.stderr.splitlines() if "error" in z), "")
            kaputt.append(f"{r} {n}({ps});  ->  {erste.strip()[:110]}")
    return kaputt


def rust_tafel(tafel: dict[str, tuple[str, ...]], name: str = "SIGNATUR") -> str:
    """**The column count comes from the rows, not from a literal.** `SIGNATUR` carries
    three columns per name, `POSIX` carries four -- the header is the fourth, because a
    refusal over four headers has to name which one."""
    breite = len(next(iter(tafel.values()))) if tafel else 3
    zeilen = [f'    ({", ".join(chr(34) + s + chr(34) for s in (n, *spalten))}),'
              for n, spalten in sorted(tafel.items())]
    typ = ", ".join(["&str"] * (breite + 1))
    return (f"static {name}: [({typ}); {len(tafel)}] = [\n"
            + "\n".join(zeilen) + "\n];\n")


def rust_abschluss(namen: list[str]) -> str:
    zeilen = [f'    "{n}",' for n in sorted(namen)]
    return (f"static ABSCHLUSS: [&str; {len(namen)}] = [\n"
            + "\n".join(zeilen) + "\n];\n")


def eingebaute_tafel(name: str = "SIGNATUR") -> dict[str, tuple[str, ...]]:
    """The built-in table, read with as many columns as it has -- see `rust_tafel`."""
    q = open(CNAMEN, encoding="utf-8").read()
    i = q.index(f"static {name}")
    b = q[i:q.index("];", i)]
    aus: dict[str, tuple[str, ...]] = {}
    for zeile in re.findall(r'\(("(?:[^"]*"(?:,\s*)?)+)\)', b):
        felder = re.findall(r'"([^"]*)"', zeile)
        aus[felder[0]] = tuple(felder[1:])
    return aus


def eingebauter_abschluss() -> list[str]:
    q = open(CNAMEN, encoding="utf-8").read()
    i = q.index("static ABSCHLUSS")
    return re.findall(r'"([^"]+)"', q[i:q.index("];", i)])


def posix_messen() -> tuple[dict[str, tuple[str, str, str, str]], dict[str, str]]:
    """The four-header half -- the same three columns, plus the header that declared it.

    **The header is a column and not a constant**, because the guard's refusal names the
    finding site and four headers have four of those. Before 2026-09-02 it was one `&str`
    beside the table, and a second header would have made every refusal name the first.
    """
    c11, hdr, ein = tafel_lesen()
    schon = set(c11) | {n for n, _ in hdr} | set(ein)
    tafel: dict[str, tuple[str, str, str, str]] = {}
    grund: dict[str, str] = {}
    for n, (kopf, sig) in sorted(posix_signaturen().items()):
        # **A name C11 already took is C11's**, and `N041` reaches it through the other
        # table. Two homes for one name is the register `W7` warns about.
        if n in schon:
            continue
        s, warum = absenkbar(sig)
        if s is None:
            grund[n] = warum
            tafel[n] = (c_wort(sig), "", "", kopf)
        else:
            tafel[n] = (c_wort(sig), s, gabbro_form(n, s), kopf)
    return tafel, grund


def rohe_posix_signaturen() -> dict[str, tuple[str, list[str]]]:
    """`posix_signaturen` without the header column -- what `abschluss_messen` reads."""
    return {n: sig for n, (_kopf, sig) in posix_signaturen().items()}


def abschluss_messen(tafeln: list[dict[str, tuple[str, ...]]],
                     rohe: list[dict[str, tuple[str, list[str]]]]) -> list[str]:
    """**The names whose end is in the DATA** -- over both tables, one test."""
    namen = []
    for t, roh in zip(tafeln, rohe):
        for n in t:
            if n in roh and endet_in_den_daten(n, roh[n]):
                namen.append(n)
    return sorted(set(namen))


# **Headers this guard does NOT read.** They are here to be COUNTED against, never to be
# folded in: `kante` includes them so the blind spot is a number per run and not a sentence.
# *`fuzze-erzeuger.py` prints its own blind spot and `miss-erschoepfung.py` prints
# "NOT measured:" -- this is the same form, one tool over.*
WEITERE_KOEPFE = (
    "pthread.h", "sys/mman.h", "sys/stat.h", "sys/wait.h", "dirent.h", "poll.h",
    "sys/select.h", "netdb.h", "arpa/inet.h", "sched.h", "semaphore.h", "termios.h",
    "sys/uio.h", "sys/time.h", "grp.h", "pwd.h", "sys/ioctl.h", "sys/resource.h",
    "sys/utsname.h", "utime.h", "glob.h", "regex.h", "syslog.h", "dlfcn.h",
)


def korpus_extern_fn() -> dict[str, list[str]]:
    """Every `extern fn` name the corpus writes, and where. **This is the DENOMINATOR.**

    The guard's edge is worth a number only against the population it is an edge of: a
    header set that reaches nothing is as wide as one that reaches everything.
    """
    muster = re.compile(r"^\s*(?:pub\s+)?extern\s+fn\s+([A-Za-z_][A-Za-z0-9_]*)")
    aus: dict[str, list[str]] = {}
    wurzeln = [f"{WURZEL}/beispiele", f"{WURZEL}/messung"]
    dateien = []
    for w in wurzeln:
        for pfad, _verz, namen in os.walk(w):
            dateien += [f"{pfad}/{n}" for n in namen if n.endswith(".gab")]
    dateien.append(f"{WURZEL}/dokumente/FRAGMENTE.md")
    for d in sorted(dateien):
        try:
            zeilen = open(d, encoding="utf-8", errors="replace").read().splitlines()
        except OSError:
            continue
        for i, z in enumerate(zeilen, 1):
            m = muster.match(z)
            if m:
                aus.setdefault(m.group(1), []).append(
                    f"{os.path.relpath(d, WURZEL)}:{i}")
    return aus


def kante(tafel: dict[str, tuple[str, ...]], ptafel: dict[str, tuple[str, ...]]) -> None:
    """**What this guard does NOT cover -- printed every run, with a number beside it.**

    A table that implies completeness is worth less than one that names its edge. The list
    of headers left out is prose and would age silently; the corpus count beside it cannot,
    because it is measured against the tree on every run.
    """
    print("\n== The edge, named per run ==")
    print("   MEASURED: " + " ".join(f"<{h}>" for h in POSIX_KOEPFE)
          + f"  ({len(ptafel)} rows)")
    print("   NOT measured, and each of these is a name an `extern fn` binds unchecked:")
    print(f"     * {len(WEITERE_KOEPFE)} further POSIX headers this run knows the names of "
          f"({', '.join('<' + h + '>' for h in WEITERE_KOEPFE[:4])}, ...) "
          "-- and every one it does not")
    print("     * every GNU extension, every other library, every symbol the writer links")
    print("     * the glibc spellings `__pid_t`, `__uid_t`, `__gid_t`, `__off_t`: a table")
    print("       that resolved them would measure glibc and call it POSIX")
    print("     * this is a measurement of THIS toolchain, LP64")

    erreicht = korpus_extern_fn()
    gedeckt = set(tafel) | set(ptafel)
    c11, hdr, ein = tafel_lesen()
    gedeckt |= set(c11) | {n for n, _ in hdr} | set(ein)
    offen = {n: s for n, s in erreicht.items() if n not in gedeckt}
    stellen = sum(len(s) for s in erreicht.values())
    offene_stellen = sum(len(s) for s in offen.values())
    print(f"\n   The corpus writes {stellen} `extern fn` at {len(erreicht)} distinct names;"
          f" {offene_stellen} sites / {len(offen)} names reach no table.")
    print("   **Most of those are the program's OWN C, and refusing them would forbid every")
    print("   hand-written driver.** The ones that are not are the hole -- so they get named:")

    fremd: dict[str, str] = {}
    for h in WEITERE_KOEPFE:
        try:
            for n in kopf_signaturen(h):
                if n in offen:
                    fremd.setdefault(n, h)
        except (OSError, subprocess.SubprocessError):
            continue
    if fremd:
        for n, h in sorted(fremd.items()):
            print(f"     UNCHECKED  {n}  <{h}>  {', '.join(offen[n])}")
        print(f"   {len(fremd)} of {len(offen)} -- an `extern fn` on a name a header this")
        print("   guard does not read declares. THAT IS A HOLE WITH A NAME ON IT.")
    else:
        print(f"     none of the {len(offen)} is declared by any of the "
              f"{len(WEITERE_KOEPFE)} headers this run looked at.")
        print("   *That is not a proof of zero* -- it is a statement about those headers.")


def main() -> int:
    # **The speech test runs FIRST, and it costs two `cc` calls.** What it protects is the
    # other ~1200: a harness that cannot tell a true equivalence from a false one reports the
    # same table either way.
    print("== Sprechprobe ==")
    try:
        proben = sprechprobe()
    except (FileNotFoundError, subprocess.TimeoutExpired) as e:
        print(f"ABBRUCH: `cc` laesst sich nicht fahren ({type(e).__name__}) -- es wurde",
              file=sys.stderr)
        print("  NICHTS gemessen. Das ist keine gefallene Probe, sondern eine fehlende",
              file=sys.stderr)
        print("  Vorbedingung: ohne `cc` hat dieses Werkzeug keinen Gegenstand.",
              file=sys.stderr)
        return 2
    for was, ok in proben:
        print(f"  {'ok' if ok else 'GESCHEITERT'} -- {was}")
    if not all(ok for _, ok in proben):
        print("ABBRUCH: die `cc`-Vorrichtung unterscheidet nicht -- jede Zahl darunter",
              file=sys.stderr)
        print("  waere ueber demselben Ruecklaufwert gerechnet und saehe wie eine Messung",
              file=sys.stderr)
        print("  aus. Das ist KEIN gruener Lauf.", file=sys.stderr)
        return 2

    tafel, z, grund = messen()
    ptafel, pgrund = posix_messen()
    if "--tafel" in sys.argv:
        print(rust_tafel(tafel))
        print(rust_tafel(ptafel, "POSIX"))
        return 0
    if "--abschluss" in sys.argv:
        roh_c11 = dict(signaturen_aus_aux())
        for n in tafel:
            if n not in roh_c11:
                s = signatur_des_eingebauten(n)
                if s:
                    roh_c11[n] = s
        print(rust_abschluss(abschluss_messen([tafel, ptafel],
                                              [roh_c11, rohe_posix_signaturen()])))
        return 0

    kaputt = aequivalenzen_pruefen()
    print("Die 558-Namen-Tafel, nach BINDBARKEIT einer `extern fn` geteilt")
    print("=" * 66)
    for k, v in sorted(z.items()):
        print(f"  {v:4d}  {k}")
    gesamt = z["C11-Wort"] + sum(v for k, v in z.items() if k.startswith("Header/")
                                 and "/" in k and k.count("/") == 1
                                 and k.split("/")[1] in ("Makro", "Typedef", "Funktion",
                                                         "unklar")) + z["Eingebaut"]
    print(f"\n  Tafel gesamt: {gesamt}")
    bindbar = sum(1 for _c, s, _g in tafel.values() if s)
    print(f"  Zeilen in SIGNATUR (C's Deklaration lesbar): {len(tafel)}")
    print(f"  davon BINDBAR (Signatur bekannt): {bindbar}")
    print(f"  nicht bindbar (Absage mit Grund): {gesamt - bindbar}")
    # The denominator names BOTH tables, because both are now driven through `cc`. It used
    # to read `len(GLEICH) - 1` while `absenkbar()` consumed a second table nothing asserted.
    print(f"\n  Aequivalenzen geprueft: {len(GLEICH) - 1 + len(GLEICH_POSIX)} "
          f"({len(GLEICH) - 1} + {len(GLEICH_POSIX)} POSIX), davon kaputt: {len(kaputt)}")
    for k in kaputt:
        print(f"    KAPUTT: {k}")

    cc_kaputt = tafel_gegen_cc(tafel)
    print(f"  bindbare Tafelzeilen durch `cc -Wall -Wextra -Werror`: "
          f"{bindbar - len(cc_kaputt)}/{bindbar} gruen")
    for k in cc_kaputt[:10]:
        print(f"    KAPUTT: {k}")

    p_bindbar = sum(1 for spalten in ptafel.values() if spalten[1])
    p_cc_kaputt = tafel_gegen_cc(ptafel)
    koepfe = ", ".join(f"`<{h}>`" for h in POSIX_KOEPFE)
    print(f"\n{koepfe}, ohne die Namen, die C11 schon haelt: {len(ptafel)} Zeilen")
    for h in POSIX_KOEPFE:
        z = [n for n, s in ptafel.items() if s[3] == h]
        print(f"    <{h}>: {len(z)} Zeilen, "
              f"{sum(1 for n in z if ptafel[n][1])} bindbar")
    print(f"  davon BINDBAR: {p_bindbar}, durch `cc`: "
          f"{p_bindbar - len(p_cc_kaputt)}/{p_bindbar} gruen")
    for k in p_cc_kaputt[:10]:
        print(f"    KAPUTT: {k}")
    kante(tafel, ptafel)

    if "--pruefe" in sys.argv:
        schief: list[str] = []
        for name, gemessen in (("SIGNATUR", tafel), ("POSIX", ptafel)):
            eingebaut = eingebaute_tafel(name)
            fehlt = sorted(set(gemessen) - set(eingebaut))
            zuviel = sorted(set(eingebaut) - set(gemessen))
            anders = sorted(n for n in set(gemessen) & set(eingebaut)
                            if gemessen[n] != eingebaut[n])
            print(f"\n`cnamen.rs::{name}`: {len(eingebaut)} Zeilen")
            print(f"  fehlt: {len(fehlt)}   zuviel: {len(zuviel)}   anders: {len(anders)}")
            for n in (fehlt + zuviel + anders)[:20]:
                print(f"    {n}")
            schief += fehlt + zuviel + anders

        roh_c11 = dict(signaturen_aus_aux())
        for n in tafel:
            if n not in roh_c11:
                s = signatur_des_eingebauten(n)
                if s:
                    roh_c11[n] = s
        a_gemessen = abschluss_messen([tafel, ptafel], [roh_c11, rohe_posix_signaturen()])
        a_eingebaut = eingebauter_abschluss()
        a_schief = sorted(set(a_gemessen) ^ set(a_eingebaut))
        print(f"\n`cnamen.rs::ABSCHLUSS`: {len(a_eingebaut)} Namen, gemessen "
              f"{len(a_gemessen)}, verschieden: {len(a_schief)}")
        for n in a_schief[:20]:
            print(f"    {n}")

        if kaputt or cc_kaputt or p_cc_kaputt or schief or a_schief:
            print("\nBEFUND")
            return 1
        print("\nGRUEN -- die eingebauten Tafeln sind die gemessenen")
    return 0


if __name__ == "__main__":
    sys.exit(main())
