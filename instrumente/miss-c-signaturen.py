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

UMGEBUNG = dict(os.environ, LC_ALL="C")
_TMP = tempfile.mkdtemp(prefix="gabbro-csig-")


def _cc(rumpf: str, *zusatz: str) -> subprocess.CompletedProcess:
    c = f"{_TMP}/probe.c"
    with open(c, "w", encoding="utf-8") as f:
        f.write(KOPF + rumpf)
    return subprocess.run(["cc", "-std=c11", "-O0", *zusatz, "-fsyntax-only", c],
                          capture_output=True, text=True, env=UMGEBUNG)


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
                   capture_output=True, text=True, env=UMGEBUNG, cwd=_TMP)
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


def absenkbar(sig: tuple[str, list[str]]) -> tuple[str, str] | tuple[None, str]:
    """The signature in `emit.rs` spelling -- or the reason there is none."""
    r, args = sig
    if any("..." in t for t in args):
        return None, "variadic -- Gabbro has no variadic form"
    teile = []
    for t in [r] + args:
        if "*" in t or "[" in t:
            return None, f"C's declaration takes `{t.strip()}`, and Gabbro has no such type"
        g = GLEICH.get(t.strip())
        if g is None or g not in CTYP:
            return None, f"C's declaration takes `{t.strip()}`, and Gabbro has no such type"
        teile.append(g)
    return f"{teile[0]}({','.join(teile[1:]) or 'void'})", ""


def gabbro_form(name: str, c: str) -> str:
    """The Gabbro line that produces exactly this C signature -- for the refusal."""
    m = re.match(r"^(\w+)\((.*)\)$", c)
    r, a = m.group(1), m.group(2)
    ps = [] if a == "void" else a.split(",")
    kopf = ", ".join(f"{chr(97 + i)} : {GABBRO[t]}" for i, t in enumerate(ps))
    schwanz = "" if r == "void" else f" -> {GABBRO[r]}"
    return f"extern fn {name}({kopf}){schwanz}"


def c_wort(sig: tuple[str, list[str]]) -> str:
    """C's declaration in C's OWN words -- what the refusal shows the writer."""
    r, args = sig
    return f"{r}({', '.join(args) or 'void'})"


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
    """`int == int32_t`? Not assumed -- `_Static_assert` says so."""
    kaputt = []
    for c, s in sorted(GLEICH.items()):
        if s == "void":
            continue
        r = _cc(f"_Static_assert(__builtin_types_compatible_p({c}, {s}), \"x\");\n")
        if r.returncode != 0:
            kaputt.append(f"{c} != {s}")
    return kaputt


def tafel_gegen_cc(tafel: dict[str, tuple[str, str]]) -> list[str]:
    """**The counter-probe that counts:** every table line as a C declaration, through `cc`.

    A signature table nobody has compiled is an assertion. This loop turns every line into
    exactly what `emit.rs` would write and hands it to `cc` under `-Wall -Wextra -Werror`.
    *What passes here passes in the generated C.*
    """
    kaputt = []
    for n, (_c, sig, _g) in sorted(tafel.items()):
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


def rust_tafel(tafel: dict[str, tuple[str, str]]) -> str:
    zeilen = [f'    ("{n}", "{c}", "{s}", "{g}"),'
              for n, (c, s, g) in sorted(tafel.items())]
    return (f"static SIGNATUR: [(&str, &str, &str, &str); {len(tafel)}] = [\n"
            + "\n".join(zeilen) + "\n];\n")


def eingebaute_tafel() -> dict[str, tuple[str, str, str]]:
    q = open(CNAMEN, encoding="utf-8").read()
    i = q.index("static SIGNATUR")
    b = q[i:q.index("];", i)]
    return {n: (c, s, g) for n, c, s, g in
            re.findall(r'\("([^"]*)",\s*"([^"]*)",\s*"([^"]*)",\s*"([^"]*)"\)', b)}


def main() -> int:
    tafel, z, grund = messen()
    if "--tafel" in sys.argv:
        print(rust_tafel(tafel))
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
    print(f"\n  Aequivalenzen geprueft: {len(GLEICH) - 1}, davon kaputt: {len(kaputt)}")
    for k in kaputt:
        print(f"    KAPUTT: {k}")

    cc_kaputt = tafel_gegen_cc(tafel)
    print(f"  bindbare Tafelzeilen durch `cc -Wall -Wextra -Werror`: "
          f"{bindbar - len(cc_kaputt)}/{bindbar} gruen")
    for k in cc_kaputt[:10]:
        print(f"    KAPUTT: {k}")

    if "--pruefe" in sys.argv:
        eingebaut = eingebaute_tafel()
        fehlt = sorted(set(tafel) - set(eingebaut))
        zuviel = sorted(set(eingebaut) - set(tafel))
        anders = sorted(n for n in set(tafel) & set(eingebaut)
                        if tafel[n] != eingebaut[n])
        print(f"\n`cnamen.rs::SIGNATUR`: {len(eingebaut)} Zeilen")
        print(f"  fehlt: {len(fehlt)}   zuviel: {len(zuviel)}   anders: {len(anders)}")
        for n in (fehlt + zuviel + anders)[:20]:
            print(f"    {n}")
        if kaputt or cc_kaputt or fehlt or zuviel or anders:
            print("\nBEFUND")
            return 1
        print("\nGRUEN -- die eingebaute Tafel ist die gemessene")
    return 0


if __name__ == "__main__":
    sys.exit(main())
