#!/usr/bin/env python3
# `pruefe-atomar-zugriffe.py` -- DOES EVERY ACCESS TO AN ATOMIC GO THROUGH A
# C11 ATOMIC OPERATION? (server lane, TODO section 0e K6, 2026-09-28)
#
# THE QUESTION, AND WHY IT IS ASKED NOW. Until today a Gabbro `atomic` lowered
# to a C11 `_Atomic` carrier and nothing else, and on a `_Atomic` object even a
# PLAIN access -- `x = STAND;` -- is an atomic operation: C11 6.5.16.2 makes it
# implicitly `memory_order_seq_cst`. So a site the emitter wrote plainly was
# still ordered, and nobody had to ask.
#
# The kernel-module target (K6) takes that safety net away.
# Until the C-free lane's C2 a handwritten table mapped the emitter's nine C11 call forms
# onto the kernel's own primitives and `_Atomic` itself to `volatile` -- because
# the kernel has no C11 atomics and `atomic_t` is not a type a Gabbro
# declaration can become. From that moment a plain access would compile
# SILENTLY into an unordered one: no error, no warning, a weaker program. *The
# worst of the three possible answers.*
#
# So the emitter's own claim -- "every access to an atomic is one of the nine
# calls" -- stops being an internal nicety and becomes a premise of the module
# target. This script measures it over the whole corpus.
#
# WHY IT IS NOT A GREP, and that was measured before it was written. A
# line-based grep over the same corpus reports 61 "plain accesses" and every one
# of them is noise (session 4):
#   * a continuation line of a multi-line `atomic_compare_exchange_*` call --
#     the call name is on one line and its arguments on the next three;
#   * a `#define` whose name merely CONTAINS an atomic's name (`F` and
#     `F_ORDER`).
# Both disappear the moment the file is read as a token stream instead of a
# list of lines: the first because a call's argument span is found by matching
# parentheses across newlines, the second because `F_ORDER` is one identifier
# token and not an `F` next to something.
#
# THE MEASUREMENT, per emitted file:
#   1. comments and string/char literals are blanked (positions preserved);
#   2. every `_Atomic` declaration is read for the object it declares, and the
#      declaration's span `_Atomic … ;` is recorded;
#   3. every one of the nine call forms is found, and its argument span from
#      `(` to the matching `)` is recorded;
#   4. every identifier token equal to an atomic object's name is required to
#      lie inside a declaration span or inside a call's argument span.
# Anything else is a FINDING: the exact line, the object and the text around it.
#
# WHAT A GREEN RUN DOES AND DOES NOT SAY. It says: in the emitted C of this
# corpus, the name of an atomic occurs only where the mapping reaches it. It
# does NOT say the emitter cannot write a plain access for some source shape no
# corpus file has -- that is a statement about all programs, and this is a
# measurement over 276 files (258 corpus units and 18 of the 828 `beispiele/gift`
# probes, which are refused by the checker but still emit; their shapes are
# measured for free and that is why they are not filtered out). The corpus is
# `git ls-files`, so an unstaged `.gab` is not measured -- a trap this lane has
# paid for once.
#
# Usage:
#   instrumente/pruefe-atomar-zugriffe.py            # emit the corpus, check it
#   instrumente/pruefe-atomar-zugriffe.py FILE...    # check emitted C files
#   instrumente/pruefe-atomar-zugriffe.py --selbsttest   # the poison probes
#
# Exit codes: 0 clean, 1 findings, 2 NOT RUN (no binary, nothing emitted).

import os
import re
import subprocess
import sys
import tempfile

W = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# **A deadline on everything this script runs.** One `gabbro emit` over one unit takes
# milliseconds; a run that does not answer inside a minute is a hang, and a hang without a
# deadline is a state and not a verdict (`pruefe-waechter.py`, rule FRIST).
FRIST = 60

# **The nine forms, and the list is CLOSED.** `emit.rs` can write exactly these:
# the two access arms (`Publish`/`AwaitLoad` and the plain load/store), the five
# `holform` rows and the two compare-exchange arms. A tenth form appearing in an
# emitted file is itself a finding -- see `unbekannte_formen` below, which is why
# the list is written out rather than matched with `atomic_\w+`.
FORMEN = [
    "atomic_load_explicit",
    "atomic_store_explicit",
    "atomic_fetch_add_explicit",
    "atomic_fetch_sub_explicit",
    "atomic_fetch_or_explicit",
    "atomic_fetch_and_explicit",
    "atomic_fetch_xor_explicit",
    "atomic_compare_exchange_weak_explicit",
    "atomic_compare_exchange_strong_explicit",
]

KENNUNG = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")


def blanke(text):
    """Comments and string/char literals become spaces -- positions survive.

    A blank of the same length keeps every later offset valid, so a finding can
    still be reported at the line it stands on."""
    aus = list(text)
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c == "/" and i + 1 < n and text[i + 1] == "*":
            j = text.find("*/", i + 2)
            j = n if j < 0 else j + 2
            for k in range(i, j):
                if aus[k] != "\n":
                    aus[k] = " "
            i = j
        elif c == "/" and i + 1 < n and text[i + 1] == "/":
            j = text.find("\n", i)
            j = n if j < 0 else j
            for k in range(i, j):
                aus[k] = " "
            i = j
        elif c in "\"'":
            j = i + 1
            while j < n and text[j] != c:
                j += 2 if text[j] == "\\" else 1
            j = min(j + 1, n)
            for k in range(i, j):
                if aus[k] != "\n":
                    aus[k] = " "
            i = j
        else:
            i += 1
    return "".join(aus)


def klammerspanne(text, auf):
    """From the `(` at `auf` to its matching `)`. `None` if it never closes."""
    tiefe = 0
    for i in range(auf, len(text)):
        if text[i] == "(":
            tiefe += 1
        elif text[i] == ")":
            tiefe -= 1
            if tiefe == 0:
                return (auf, i)
    return None


def erhebe(text):
    """The atomic objects, their declaration spans and the call spans."""
    objekte = {}          # name -> the declaration's span
    deklarationen = []
    for m in re.finditer(r"\b_Atomic\b", text):
        ende = text.find(";", m.end())
        if ende < 0:
            continue
        deklarationen.append((m.start(), ende))
        kopf = text[m.end() : ende]
        # `_Atomic uint32_t REGEL[256]` -- the object's name is the last
        # identifier before the array brackets (or before the `;`).
        vor = kopf.split("[")[0]
        namen = KENNUNG.findall(vor)
        if namen:
            objekte[namen[-1]] = (m.start(), ende)
    rufe = []             # (form, argument span)
    for f in FORMEN:
        for m in re.finditer(r"\b" + f + r"\b", text):
            auf = text.find("(", m.end())
            if auf < 0:
                continue
            sp = klammerspanne(text, auf)
            if sp:
                rufe.append((f, sp))
    return objekte, deklarationen, rufe


def zeile_von(text, pos):
    return text.count("\n", 0, pos) + 1


def pruefe_datei(pfad, text):
    """Findings, and the counters a green run reports."""
    t = blanke(text)
    objekte, deklarationen, rufe = erhebe(t)
    befunde = []
    if not objekte:
        return befunde, {}, {}
    erlaubt = list(deklarationen) + [sp for _, sp in rufe]
    for m in KENNUNG.finditer(t):
        if m.group(0) not in objekte:
            continue
        p = m.start()
        if any(a <= p <= b for a, b in erlaubt):
            continue
        befunde.append(
            (
                pfad,
                zeile_von(t, p),
                m.group(0),
                text.split("\n")[zeile_von(t, p) - 1].strip()[:100],
            )
        )
    formzahl = {}
    for f, _ in rufe:
        formzahl[f] = formzahl.get(f, 0) + 1
    # **A tenth form would be a finding of its own.** `atomic_exchange_explicit`
    # or `atomic_thread_fence` in an emitted file means the mapping in
    # the generated module `<stdatomic.h>` (`treiber.rs::KMOD_STDATOMIC`) is incomplete, and an incomplete
    # mapping is an undefined name at the kernel build -- loud, but only if
    # somebody builds a module out of that unit. Here it is loud always.
    for m in re.finditer(r"\batomic_[A-Za-z0-9_]*\b", t):
        if m.group(0) not in FORMEN:
            befunde.append(
                (pfad, zeile_von(t, m.start()), m.group(0), "a C11 atomic form the mapping does not carry")
            )
    return befunde, objekte, formzahl


def korpus():
    aus = subprocess.run(
        ["git", "ls-files", "beispiele", "messung/proben"],
        cwd=W, capture_output=True, text=True, check=True, timeout=FRIST,
    ).stdout.split()
    return [f for f in aus if f.endswith(".gab")]


def binaer():
    """**Which binary, and is it younger than the sources it claims to be?** ONE register,
    ONE file: `instrumente/binaer.sh` (server lane, TODO section 0e K8).

    This function used to be a second copy of that question, and it answered it worse in
    two ways at once -- it preferred `target/release` even when `target/debug` was newer,
    and it counted `crates/*/tests/*.rs` among the sources, which is precisely the defect
    session 10 repaired in the shared file. *Measured on 2026-09-28: a run of
    `pruefe-emission.sh` was cut at stage 22c with "the binary is OLDER than 2 source
    file(s)" over two TEST files that no binary is built from.* The shell register answers
    for both, so there is nothing left to drift.

    Returns the path, or prints the reason and exits -- the reason is the shell's own
    sentence, not a paraphrase of it.
    """
    skript = os.path.join(W, "instrumente", "binaer.sh")
    r = subprocess.run(
        ["sh", "-c", '. "$1"; gabbro_binaer "$2"', "sh", skript, W],
        capture_output=True, text=True, timeout=FRIST,
    )
    antwort = r.stdout.strip()
    if r.returncode != 0:
        print("ATOMAR-ZUGRIFFE: NOT RUN -- %s" % (antwort or "binaer.sh gave no answer"))
        sys.exit(2)
    return antwort


def emittiere(ziel):
    """Every corpus unit the emitter accepts, as a file in `ziel`."""
    g = binaer()
    dateien = []
    for q in korpus():
        r = subprocess.run(
            [g, "emit", q], cwd=W, capture_output=True, text=True, timeout=FRIST
        )
        if r.returncode != 0:
            continue
        p = os.path.join(ziel, q.replace("/", "_") + ".c")
        with open(p, "w") as f:
            f.write(r.stdout)
        dateien.append(p)
    return dateien


# -- the poison probes ---------------------------------------------------------
#
# Each one is a MUTATION OF AN EMITTED FILE that puts a plain access where a
# call stood, and the check must report it. They are chosen so that no two are
# caught by the same step, and two of them are exactly the false positives a
# line-based grep produced (session 4) -- there they must stay SILENT.
GIFTE = {
    1: "a plain read replaces a load",
    2: "a plain write replaces a store",
    3: "the atomic's name on a line of its own (a bare statement)",
    4: "a `#define` whose name CONTAINS an atomic's -- must stay SILENT",
    5: "a compare-exchange whose target stands on a continuation line -- must stay SILENT",
    6: "a C11 atomic form the mapping does not carry",
}


def selbsttest():
    quelle = """#include <stdatomic.h>
_Atomic uint32_t STAND;
_Atomic bool F;
#define F_ORDER memory_order_release
static uint32_t lies(void) {
    uint32_t n = atomic_load_explicit(&STAND, memory_order_relaxed);
    atomic_store_explicit(&STAND, n + 1, memory_order_relaxed);
    bool b = false;
    if (atomic_compare_exchange_weak_explicit(
            &F, &b, true,
            memory_order_release, memory_order_acquire)) { n++; }
    return n;
}
"""
    mutationen = {
        1: lambda s: s.replace("atomic_load_explicit(&STAND, memory_order_relaxed)", "STAND"),
        2: lambda s: s.replace(
            "atomic_store_explicit(&STAND, n + 1, memory_order_relaxed);", "STAND = n + 1;"
        ),
        3: lambda s: s.replace("    return n;", "    (void)STAND;\n    return n;"),
        # 4 and 5 are the two FALSE POSITIVES a line-based grep produced over
        # this corpus (61 of them, session 4). They are real additions, not
        # identity mutations: a naive `grep STAND` hits `STANDARD_WERT`, and a
        # grep that recognises a call only when the name and the target share a
        # line hits the `&STAND` below. Both must stay silent here.
        4: lambda s: s.replace(
            "#define F_ORDER memory_order_release",
            "#define F_ORDER memory_order_release\n#define STANDARD_WERT 3u",
        ),
        5: lambda s: s.replace(
            "    return n;",
            "    if (atomic_compare_exchange_strong_explicit(\n"
            "            &STAND, &n, 5u,\n"
            "            memory_order_release, memory_order_acquire)) { n++; }\n"
            "    return n;",
        ),
        6: lambda s: s.replace(
            "    return n;", "    atomic_thread_fence(memory_order_seq_cst);\n    return n;"
        ),
    }
    still = {4, 5}
    gefangen, gesamt = 0, 0
    # The clean side first: the fixture itself must be silent, or every "caught"
    # below would be measuring the fixture and not the mutation.
    befunde, _, formen = pruefe_datei("<fixture>", quelle)
    if befunde:
        print("SELBSTTEST: the clean fixture already reports findings -- the check is broken:")
        for b in befunde:
            print("   %s:%d  %s  %s" % b)
        return 1
    print("SELBSTTEST: the clean fixture is silent (%d calls in it)" % sum(formen.values()))
    for g in sorted(GIFTE):
        gesamt += 1
        befunde, _, _ = pruefe_datei("<gift %d>" % g, mutationen[g](quelle))
        if g in still:
            if befunde:
                print("GIFT %d: WRONGLY CAUGHT -- %s" % (g, GIFTE[g]))
                for b in befunde:
                    print("   %s:%d  %s  %s" % b)
            else:
                print("GIFT %d: silent as it must be -- %s" % (g, GIFTE[g]))
                gefangen += 1
        else:
            if befunde:
                print("GIFT %d: caught (%d) -- %s" % (g, len(befunde), GIFTE[g]))
                gefangen += 1
            else:
                print("GIFT %d: NOT CAUGHT -- %s" % (g, GIFTE[g]))
    print()
    print("gifts: %d of %d as expected" % (gefangen, gesamt))
    return 0 if gefangen == gesamt else 1


def main():
    argumente = sys.argv[1:]
    if "--selbsttest" in argumente:
        sys.exit(selbsttest())
    dateien = [a for a in argumente if not a.startswith("--")]
    tmp = None
    if not dateien:
        tmp = tempfile.mkdtemp(prefix="gabbro-atomar.")
        dateien = emittiere(tmp)
        if not dateien:
            print("ATOMAR-ZUGRIFFE: NOT RUN -- nothing emitted")
            sys.exit(2)
    alle, objekte, formen, mit = [], 0, {}, 0
    for p in dateien:
        with open(p) as f:
            text = f.read()
        befunde, objs, fz = pruefe_datei(p, text)
        alle += befunde
        if objs:
            mit += 1
        objekte += len(objs)
        for k, v in fz.items():
            formen[k] = formen.get(k, 0) + v
    print("== every access to an atomic through a C11 atomic operation? ==")
    print("   files checked   %d (%d of them declare an atomic)" % (len(dateien), mit))
    print("   atomic objects  %d" % objekte)
    for k in FORMEN:
        if formen.get(k):
            print("   %-42s %d" % (k, formen[k]))
    print("   accesses        %d" % sum(formen.values()))
    print()
    if alle:
        print("RED: %d access(es) to an atomic outside the mapping:" % len(alle))
        for b in alle[:20]:
            print("   %s:%d  %s  %s" % b)
        sys.exit(1)
    print("GREEN: no plain access to an atomic in the emitted C.")
    sys.exit(0)


if __name__ == "__main__":
    main()
