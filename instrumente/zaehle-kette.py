#!/usr/bin/env python3
"""**The chain count** -- how many corpus programs pass the WHOLE translation-validation
chain, not one pillar of it.

    ./instrumente/zaehle-kette.py [--binary PATH] [--allow-stale] [--lean] [--dateien LISTE]

WHAT IT DOES
------------
PLAN-UEBERSETZUNGSVALIDIERUNG.md section 3 (revised 2026-09-13): coverage is
MULTIPLICATIVE -- the closing theorem holds only for programs that pass every sieve --
so the state is measured by closed chains, not by per-pillar percentages. This script
prints, per corpus program in `beispiele/*.gab`, which sieve it passes:

  (a) Lean parse -- the GENERIC Lean pipeline `uebersetzeAllg` (Schlusssatz.lean: lex,
      parse, the lane-162 preprocessing, elaborate, generic lowering), EVALUATED in
      Lean over the program's text with `--lean` (a generated `#eval` script run under
      `lake env lean`); the column names the stage that stops a program (`lex`,
      `parse: ...`, `elab: ...`, `lower: ...`). Without `--lean` it reads "not measured".
  (b) `gabbro lean-g` export succeeds (exit 0, nonempty output) -- DIAGNOSTIC: the
      generic chain parses in Lean and does not consume the Rust export.
  (c) `gabbro certificate` prints every body -- DIAGNOSTIC: the generic chain's model
      judgement is the checker's Bool `Akzeptiert` decided in Lean plus the user's
      proof, not the Rust statement certificate.
  (d) every emitted C form is in state lemma or named assumption -- the three states of
      `pruefe-cformen.py`, imported from that file (single source of truth). A program
      the emitter refuses has no emitted C, so the column reads "not measured".
  (e) the GENERIC correspondence certificate (`gabbro corr-lean`, section "generic",
      `KCert`) is printed with no `KREFUSAL`, and -- for a program with a chain
      instance -- the certificate the instance pastes IS that printed literal
      (whitespace-normalised text identity).

THE CHAIN COUNT (since 2026-09-15): a program's chain is CLOSED only when a Lean-checked
instance of the GENERIC closing theorem `schlusssatz` exists for it:
  * a file under `grammatik/Grammatik/` carries the marker `CHAIN-INSTANCE <program>
    <name>` and some file defines `def <name> : Kette <src>`;
  * the Lean string `<src>` IS the program's file, byte for byte (the parse fidelity of
    the chain is about that string -- a stale paste is a different program). The pin is
    read in EITHER form: one `String` literal, or the `SRC-BEGIN`/`SRC-END` block of
    `"…".toList` pieces the chain files use since O13 (`block_text`);
  * the instance's certificate IS the printer's (column (e));
  * some Lean file applies `schlusssatz <name>` (the theorem instantiated, a witness);
  * with `--lean`: `lake build` of every module involved is green, AND column (a)
    measured `OK` and column (d) passed.
Without `--lean` a present instance reads "Lean not re-run" and counts as NOT closed --
an unchecked instance is not a check. `Schlusssatz104.lean` (the by-hand theorem of one
program) no longer closes a chain on its own.

EXIT CODES -- a counter, not a guard: 0 once it measured (even when the chain count is
0 -- zero closed chains is the measurement, not a defect of the tree), 2 (ABBRUCH) when
it measured nothing: no binary, a stale binary without `--allow-stale`, an empty
population, a Lean measurement that printed no line for some program, or a failing
speech test. Every `gabbro` call runs under FRIST; a hang reads as a failed column, not
as a missing program. `--dateien LISTE` names the population explicitly (one path per
line, written where the version control can answer: on an rsynced worktree
`korpus.py` fails open and would count untracked files).
"""
import argparse
import importlib.util
import os
import pathlib
import re
import subprocess
import sys

W = pathlib.Path(__file__).resolve().parent.parent
GRAMMATIK = W / "grammatik" / "Grammatik"

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import korpus  # noqa: E402

_PC_SPEC = importlib.util.spec_from_file_location(
    "pruefe_cformen", W / "instrumente" / "pruefe-cformen.py")
_PC = importlib.util.module_from_spec(_PC_SPEC)
_PC_SPEC.loader.exec_module(_PC)

# A hang looks like "still running", not like a finding.
FRIST = 120
# A Lean build or evaluation of the whole corpus: minutes, not seconds.
LEAN_FRIST = 3600

MARKE = re.compile(r"CHAIN-INSTANCE\s+(\S+\.gab)\s+(\w+)")


def umgebung():
    """`LC_ALL=C`, and the toolchains on PATH.

    **`lake` lives in `~/.elan/bin` and is usually NOT on a non-interactive PATH.** Without
    this, `--lean` fell over its own launch (`OSError`) and the run printed no column at
    all -- the abort read like a finding. Measured 2026-09-15 by an Opus lane. The same
    holds for `cargo` in `~/.cargo/bin`."""
    env = dict(os.environ)
    env["LC_ALL"] = "C"
    zusatz = [str(pathlib.Path.home() / ".elan" / "bin"),
              str(pathlib.Path.home() / ".cargo" / "bin")]
    pfad = env.get("PATH", "")
    env["PATH"] = os.pathsep.join([p for p in zusatz if pathlib.Path(p).is_dir()] +
                                  ([pfad] if pfad else []))
    return env


def rufe(binary, args):
    """Run `[binary] + args`, under FRIST. Returns `(ok, stdout)`; a timeout or an
    unreadable launch reads as failure, never as a silent pass."""
    try:
        r = subprocess.run([str(binary)] + args, capture_output=True, text=True,
                           cwd=W, timeout=FRIST, env=umgebung())
    except (OSError, subprocess.TimeoutExpired):
        return False, ""
    return r.returncode == 0, r.stdout


# ---------------------------------------------------------------- Lean text helpers

def lean_unescape(body):
    """The value of a Lean string literal's body (between the quotes): `\\n`, `\\t`,
    `\\r`, `\\\\`, `\\"`, `\\'`, `\\xHH`, `\\uHHHH`; anything else is refused (None) --
    an escape this reader does not know must not become a guessed character."""
    out = []
    i = 0
    while i < len(body):
        ch = body[i]
        if ch != "\\":
            out.append(ch)
            i += 1
            continue
        if i + 1 >= len(body):
            return None
        nx = body[i + 1]
        simple = {"n": "\n", "t": "\t", "r": "\r", "\\": "\\", '"': '"', "'": "'"}
        if nx in simple:
            out.append(simple[nx])
            i += 2
        elif nx == "x" and re.fullmatch(r"[0-9a-fA-F]{2}", body[i + 2:i + 4] or ""):
            out.append(chr(int(body[i + 2:i + 4], 16)))
            i += 4
        elif nx == "u" and re.fullmatch(r"[0-9a-fA-F]{4}", body[i + 2:i + 6] or ""):
            out.append(chr(int(body[i + 2:i + 6], 16)))
            i += 6
        else:
            return None
    return "".join(out)


def lean_texte():
    """Every `.lean` file under `grammatik/Grammatik/`, path -> text."""
    texte = {}
    for p in sorted(GRAMMATIK.rglob("*.lean")):
        try:
            texte[p] = p.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
    return texte


STUECK = re.compile(r'"((?:[^"\\]|\\.)*)"\.toList')


def block_text(quelle, name):
    """The text of a PIECEWISE source pin, or None.

    A chain source may be pinned in two forms, and this reader knows both because
    the second one is a MEASURED necessity and not a style (O13):

        def <name> : String := "…"                      -- one literal

        -- SRC-BEGIN <name>
        def <name>Z : List (List Char) := ["…".toList, …]
        -- SRC-END <name>
        def <name> : String := String.ofList …

    In Lean 4.33 a `String` is a UTF-8 byte array and `String.toList` decodes the
    WHOLE text before it yields its first character; a 2064-byte literal costs the
    kernel tens of gigabytes, the same text as short `"…".toList` pieces about a
    gigabyte. The text is the concatenation of the literals in the block, in order --
    **this reader does not care how the text is cut, only what the bytes are**, so a
    re-cut pin is neither a finding nor a silent pass (the same contract as
    `pruefe-ctext.py` on the emitted-C side).
    """
    m = re.search(r"-- SRC-BEGIN " + re.escape(name) + r"\n(.*?)-- SRC-END "
                  + re.escape(name), quelle, re.S)
    if not m:
        return None
    stuecke = []
    for lit in STUECK.findall(m.group(1)):
        s = lean_unescape(lit)
        if s is None:
            return None
        stuecke.append(s)
    return "".join(stuecke) if stuecke else None


def string_def(texte, name):
    """The pinned source text of `name`: one `String` literal, or a `SRC-BEGIN` block
    of `"…".toList` pieces (see `block_text`). None when neither is readable."""
    muster = re.compile(r"def\s+" + re.escape(name) + r"\s*:\s*String\s*:=\s*\"((?:[^\"\\]|\\.)*)\"",
                        re.S)
    for t in texte.values():
        m = muster.search(t)
        if m:
            return lean_unescape(m.group(1))
    for t in texte.values():
        s = block_text(t, name)
        if s is not None:
            return s
    return None


def normiere(text):
    """Whitespace-normalised text of a certificate literal."""
    return re.sub(r"\s+", " ", text).strip()


def kcert_def(texte, name):
    """The literal of `def <name> : KCert <D> := <literal>` (up to the next blank line
    or declaration), normalised; or None."""
    muster = re.compile(r"def\s+" + re.escape(name) + r"\s*:\s*KCert\s+\S+\s*:=\s*(\[.*?\])\s*\n\s*\n",
                        re.S)
    for t in texte.values():
        m = muster.search(t)
        if m:
            return normiere(m.group(1))
    return None


def gedruckte_kcert(ausgabe):
    """The `KCert` literal `gabbro corr-lean` printed (generic section), normalised; or
    None when the section refused (`KREFUSAL`) or printed no literal."""
    teil = ausgabe.split("-- generic corr-lean certificate", 1)
    if len(teil) < 2:
        return None, "no generic section"
    teil = teil[1]
    absagen = [z for z in teil.splitlines() if z.startswith("-- KREFUSAL:")]
    if absagen:
        return None, f"{len(absagen)} KREFUSAL line(s): {absagen[0][14:80]}"
    m = re.search(r"-- pasteable as KCert[^\n]*\n(\[.*\])\s*$", teil, re.S)
    if not m:
        return None, "no pasteable KCert literal"
    return normiere(m.group(1)), "printed"


def instanzen(texte):
    """The chain instances: program file name -> (marker file, kette name)."""
    gefunden = {}
    for p, t in texte.items():
        for m in MARKE.finditer(t):
            gefunden.setdefault(pathlib.Path(m.group(1)).name, (p, m.group(2)))
    return gefunden


def pruefe_instanz(texte, kette, programm_text, gedruckt):
    """Verify one instance by text: returns (ok, detail, modules to build)."""
    m = None
    datei = None
    for p, t in texte.items():
        m = re.search(r"def\s+" + re.escape(kette) + r"\s*:\s*Kette\s+(\w+)", t)
        if m:
            datei = p
            break
    if not m:
        return False, f"no `def {kette} : Kette <src>`", []
    src = string_def(texte, m.group(1))
    if src is None:
        return False, f"source string `{m.group(1)}` not found or not readable", []
    if src != programm_text:
        return False, f"source string `{m.group(1)}` differs from the file (stale paste)", []
    kt = texte[datei]
    mz = re.search(r"def\s+" + re.escape(kette) + r"\s*:\s*Kette[^\n]*\n(?:.*\n)*?\s*zert\s*:=\s*(\w+)",
                   kt)
    if not mz:
        return False, "no `zert :=` field in the chain", []
    lit = kcert_def(texte, mz.group(1))
    if lit is None:
        return False, f"certificate `{mz.group(1)}` not found", []
    if gedruckt is None or lit != gedruckt:
        return False, f"certificate `{mz.group(1)}` is not the printer's literal", []
    anwender = [p for p, t in texte.items()
                if re.search(r"\bschlusssatz\s+" + re.escape(kette) + r"\b", t)]
    if not anwender:
        return False, f"no file applies `schlusssatz {kette}`", []
    module = sorted({modul(datei)} | {modul(p) for p in anwender})
    return True, f"instance `{kette}` in {datei.name}, applied in " + \
        ", ".join(p.name for p in anwender), module


def modul(pfad):
    """The Lean module name of a file under `grammatik/`."""
    rel = pfad.relative_to(W / "grammatik").with_suffix("")
    return ".".join(rel.parts)


# ---------------------------------------------------------------- the Lean measurements

LEAN_MESSUNG = """import Grammatik.Schlusssatz
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

-- The stages of `uebersetzeAllg` (Schlusssatz.lean), each named when it stops.
def stufeK (s : String) : String :=
  match lex s with
  | .error _ => "lex"
  | .ok toks =>
    match parseTopTief toks with
    | .error e => "parse: " ++ e
    | .ok items =>
      match elabU (pre108 items) with
      | .error e => "elab: " ++ e
      | .ok u =>
        match lowerAllg u with
        | .error e => "lower: " ++ e
        | .ok _ => "OK"

#eval show IO Unit from do
  for p in [DATEIEN] do
    let s <- IO.FS.readFile p
    IO.println ("STUFE\\t" ++ p ++ "\\t" ++ stufeK s)
"""


lean_grund = ""   # why column (a) has no answer; printed instead of a bare abort


def lean_stufen(dateien):
    """Column (a): evaluate the generic pipeline in Lean over every file. Returns a dict
    file name -> stage, or None when Lean did not answer for every file. The REASON of a
    `None` is left in `lean_grund`, so the caller can print it instead of a bare abort."""
    global lean_grund
    arbeit = W / "grammatik" / ".lake" / "zaehle-kette"
    arbeit.mkdir(parents=True, exist_ok=True)
    liste = ", ".join('"' + str(f.resolve()).replace("\\", "\\\\").replace('"', '\\"') + '"'
                      for f in dateien)
    skript = arbeit / "Messung.lean"
    skript.write_text(LEAN_MESSUNG.replace("[DATEIEN]", "[" + liste + "]"), encoding="utf-8")
    try:
        r = subprocess.run(["lake", "env", "lean", str(skript)], capture_output=True, text=True,
                           cwd=W / "grammatik", timeout=LEAN_FRIST, env=umgebung())
    except OSError as e:
        lean_grund = f"lake could not be launched: {e} (PATH={umgebung()['PATH'][:120]})"
        return None
    except subprocess.TimeoutExpired:
        lean_grund = f"lake did not answer within {LEAN_FRIST} s"
        return None
    stufen = {}
    for z in r.stdout.splitlines():
        teile = z.split("\t")
        if len(teile) == 3 and teile[0] == "STUFE":
            stufen[pathlib.Path(teile[1]).name] = teile[2]
    fehlend = [f.name for f in dateien if f.name not in stufen]
    if fehlend:
        # **The last line is rarely the one that matters** -- `lake` ends on chatter
        # ("toolchain not updated") while the cause stands further up. Take the first line
        # that says `error`, and fall back to the last line only when none does.
        zeilen = [z for z in (r.stderr + "\n" + r.stdout).splitlines() if z.strip()]
        fehler = [z for z in zeilen if "error" in z.lower()]
        lean_grund = (f"{len(fehlend)} of {len(dateien)} programs got no STUFE line "
                      f"(first: {fehlend[0]}); lake said: "
                      + ((fehler[0] if fehler else zeilen[-1])[:200] if zeilen
                         else "(nothing on stdout or stderr)"))
        return None
    return stufen


def lake_bau(module):
    """`lake build` of the named modules: green or not."""
    if not module:
        return True
    try:
        r = subprocess.run(["lake", "build"] + module, capture_output=True, text=True,
                           cwd=W / "grammatik", timeout=LEAN_FRIST, env=umgebung())
    except (OSError, subprocess.TimeoutExpired):
        return False
    return r.returncode == 0


# ---------------------------------------------------------------- speech test

def selbsttest():
    """**The speech test, in both directions: what must pass passes, what must fall
    falls.** A sieve nobody has seen fail is a decoration: the planted statements below
    must land in their forms and states, the planted garbage must stay unclassified, the
    assumption-name check must accept a binder and refuse an absent name, the Lean string
    reader must decode what Lean encodes and refuse what it does not know, and the
    certificate comparison must see a one-character difference.
    """
    unit = _PC.Unit("")
    faelle = [
        ("__asm__ __volatile__(", "stmt:asm", "assumption"),
        ("(*(volatile uint32_t *)(d->basis + 24)) = (uint32_t)x;", "stmt:reg-store",
         "assumption"),
        ("uint32_t _s = (*(volatile uint32_t *)(d->basis + 28));", "stmt:reg-load",
         "assumption"),
        ("Platz * tz = SPEICHER;", "stmt:decl-ptr", "uncovered"),
    ]
    ok = True
    print("== Speech test ==")
    for text, form, zustand in faelle:
        gefunden = _PC.classify_stmt(text, unit, False, None)
        gut = gefunden == form and _PC.form_state(gefunden) == zustand
        ok = ok and gut
        print(f"  {text[:50]:52s} -> {gefunden} / {zustand}: {'yes' if gut else 'NO'}")
    muell = _PC.classify_stmt("??? kein Satz ???;", unit, False, None)
    ok_mu = muell is None
    ok = ok and ok_mu
    print(f"  planted garbage stays unclassified: {'yes' if ok_mu else 'NO'}")
    # `(void)f(a);` is ONE call statement, not a call inside an expression (found
    # 2026-09-15 on 104's `(void)lies(k, i);`), while a call inside a condition stays one.
    void_ruf = "(void)lies(k, i);"
    vform = _PC.classify_stmt(void_ruf, unit, False, None)
    vexprs = _PC.classify_exprs(_PC.expression_part(void_ruf, vform), unit, set(), vform)
    inner = "if (!(f(v) >= 1u)) return false;"
    iform = _PC.classify_stmt(inner, unit, False, None)
    iexprs = _PC.classify_exprs(_PC.expression_part(inner, iform), unit, set(), iform)
    ok_void = vform.startswith("stmt:call") and "expr:call" not in vexprs and "expr:call" in iexprs
    ok = ok and ok_void
    print(f"  `(void)f(a);` is a call statement, a call in a condition is not: "
          f"{'yes' if ok_void else 'NO'}")
    ok_bind = _PC.assumption_exists("hdev", "(hdev : cWrap w x = y)")
    ok_weg = not _PC.assumption_exists("hdev", "nothing here names it")
    ok = ok and ok_bind and ok_weg
    print(f"  a binder occurrence verifies: {'yes' if ok_bind else 'NO'}")
    print(f"  an absent name falls: {'yes' if ok_weg else 'NO'}")
    ok_esc = lean_unescape('a\\nb\\"c\\\\d\\x41\\u00e9') == 'a\nb"c\\dAé'
    ok_unbek = lean_unescape("a\\qb") is None
    ok = ok and ok_esc and ok_unbek
    print(f"  a Lean string literal decodes: {'yes' if ok_esc else 'NO'}")
    print(f"  an unknown escape is refused, not guessed: {'yes' if ok_unbek else 'NO'}")
    # The piecewise source pin (O13): both directions, on a planted block, so the
    # reader that replaced the single literal is itself measured and not trusted.
    gut = ('-- SRC-BEGIN srcX\ndef srcXZ : List (List Char) :=\n'
           '  ["module a {\\n".toList,\n   "  fn f() {}\\n".toList,\n'
           '   "}\\n".toList]\n-- SRC-END srcX\n'
           'def srcX : String := String.ofList srcXZ.flatten\n')
    echt = "module a {\n  fn f() {}\n}\n"
    ok_pin = block_text(gut, "srcX") == echt
    ok_pin_byte = block_text(gut.replace("fn f()", "fn g()"), "srcX") != echt
    ok_pin_weg = block_text(gut, "srcY") is None
    ok_pin_schnitt = block_text(
        gut.replace('"module a {\\n".toList', '"module ".toList,\n   "a {\\n".toList'),
        "srcX") == echt
    ok = ok and ok_pin and ok_pin_byte and ok_pin_weg and ok_pin_schnitt
    print(f"  a piecewise source pin is read as its bytes: {'yes' if ok_pin else 'NO'}")
    print(f"  one byte changed is a DIFFERENT text: {'yes' if ok_pin_byte else 'NO'}")
    print(f"  a missing block is no text: {'yes' if ok_pin_weg else 'NO'}")
    print(f"  the same text cut differently is the same text: "
          f"{'yes' if ok_pin_schnitt else 'NO'}")
    a = normiere("[{ rows := [GRow.void 2],\n  vm := [0] }]")
    b = normiere("[{ rows := [GRow.void 2], vm := [0] }]")
    c = normiere("[{ rows := [GRow.void 3], vm := [0] }]")
    ok_gleich = a == b and a != c
    ok = ok and ok_gleich
    print(f"  certificate identity sees layout-only whitespace, and one digit: "
          f"{'yes' if ok_gleich else 'NO'}")
    return ok


# ---------------------------------------------------------------- main

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--binary", default=str(W / "target" / "debug" / "gabbro"))
    ap.add_argument("--allow-stale", action="store_true")
    ap.add_argument("--lean", action="store_true",
                    help="evaluate the Lean pipeline and build the chain instances (lake)")
    ap.add_argument("--dateien", help="file listing the population, one path per line")
    args = ap.parse_args()

    if not selbsttest():
        print("ABBRUCH: the speech test fell -- this run measures nothing")
        return 2

    binary = pathlib.Path(args.binary)
    if not binary.exists():
        print(f"ABBRUCH: no binary at {binary} -- build it or pass --binary")
        return 2
    stand = binary.stat().st_mtime
    neuer = sorted(q for q in W.glob("crates/*/src/*.rs") if q.stat().st_mtime > stand)
    if neuer and not args.allow_stale:
        print(f"ABBRUCH: the binary is OLDER than {len(neuer)} source file(s) under "
              f"crates/ (first: {neuer[0].relative_to(W)}) -- it measures another emitter")
        print("  (build it, or pass --allow-stale to measure that binary anyway)")
        return 2
    if neuer:
        print(f"  CAVEAT: binary older than {len(neuer)} crates/ source file(s)")

    if args.dateien:
        dateien = sorted((W / z.strip()) for z in
                         pathlib.Path(args.dateien).read_text(encoding="utf-8").splitlines()
                         if z.strip())
        fehlend = [f for f in dateien if not f.exists()]
        if fehlend:
            print(f"ABBRUCH: --dateien names {len(fehlend)} missing file(s), first {fehlend[0]}")
            return 2
    else:
        dateien = sorted(p for p in (W / "beispiele").glob("*.gab") if korpus.verfolgt(p, W))
    if not dateien:
        print("ABBRUCH: empty population -- no tracked beispiele/*.gab")
        return 2

    texte = lean_texte()
    inst = instanzen(texte)

    stufen = None
    lean_fehlt = False
    if args.lean:
        stufen = lean_stufen(dateien)
        if stufen is None:
            # **An abort that prints nothing reads like a finding.** Column (a) is missing and
            # the run stays RED for it -- but every other column and the totals are printed, so
            # the failure is visible AS a failure and not as an empty page.
            print(f"BEFUND: column (a) was NOT measured -- {lean_grund}")
            print("        every column below is measured; (a) reads '-' and the run exits red")
            lean_fehlt = True

    zeilen = []
    geschlossen_kandidaten = {}
    for f in dateien:
        # (a) Lean parse: the generic pipeline, evaluated.
        if stufen is None:
            a = ("-", "NOT measured -- see the BEFUND above" if lean_fehlt
                      else "not measured (needs --lean)")
        elif stufen[f.name] == "OK":
            a = ("pass", "uebersetzeAllg evaluates to .ok")
        else:
            a = ("FAIL", f"stops at {stufen[f.name][:90]}")

        # (b) lean-g export (diagnostic).
        ok_g, aus_g = rufe(binary, ["lean-g", str(f)])
        b = ("pass", "export printed") if ok_g and aus_g.strip() else ("FAIL", "export failed")

        # (c) statement certificate (diagnostic).
        ok_z, aus_z = rufe(binary, ["certificate", str(f)])
        if not ok_z:
            c = ("FAIL", "certificate failed (checker errors?)")
        else:
            zurueck = aus_z.count("REFUSED")
            ruempfe = aus_z.count(" term:\n")
            c = (("FAIL", f"{zurueck} refused bodie(s), {ruempfe} printed") if zurueck
                 else ("pass", f"{ruempfe} bodie(s) printed, none refused"))

        # (d) C-form states over the emitted C.
        ok_e, aus_e = rufe(binary, ["emit", str(f)])
        if not ok_e or not aus_e.strip():
            d = ("-", "not measured (emitter refused)")
        else:
            src = _PC.strip_comments(aus_e)
            unit = _PC.Unit(src)
            formen = set()
            unklass = 0
            for _fname, kanal, zeilen_c in unit.bodies:
                zellen = set()
                prev = None
                for ln in zeilen_c:
                    for s in _PC.split_statements(ln):
                        form = _PC.classify_stmt(s, unit, kanal, prev)
                        prev = form
                        if form is None:
                            unklass += 1
                            continue
                        if form != "brace":
                            formen.add(form)
                        if form == "stmt:decl-cell":
                            m = re.match(r"^\S+ (" + _PC.IDENT + r");$", s)
                            if m:
                                zellen.add(m.group(1))
                        for ex in set(_PC.classify_exprs(
                                _PC.expression_part(s, form), unit, zellen, form)):
                            formen.add(ex)
            dritt = sorted(f_ for f_ in formen if _PC.form_state(f_) == "uncovered")
            if unklass or dritt:
                d = ("FAIL", f"{unklass} unclassified, "
                              f"without semantics: {', '.join(dritt) or 'none'}")
            else:
                n_asm = sorted(f_ for f_ in formen if _PC.form_state(f_) == "assumption")
                d = ("pass", f"{len(formen)} forms lemma/assumption"
                              + (f" (assumption: {', '.join(n_asm)})" if n_asm else ""))

        # (e) the generic certificate, printed; identical to the instance's paste.
        ok_k, aus_k = rufe(binary, ["corr-lean", str(f)])
        gedruckt, wie = gedruckte_kcert(aus_k) if ok_k else (None, "corr-lean failed")
        if gedruckt is None:
            e = ("0", wie)
        elif f.name not in inst:
            e = ("-", "KCert printed, no chain instance pastes it")
        else:
            e = ("pass", "KCert printed")

        # The chain: a generic instance, verified by text; built with --lean.
        if f.name in inst:
            try:
                programm_text = f.read_text(encoding="utf-8")
            except OSError:
                programm_text = None
            ok_i, detail, module = pruefe_instanz(texte, inst[f.name][1], programm_text, gedruckt)
            if not ok_i:
                e = ("FAIL", f"instance: {detail}")
            else:
                geschlossen_kandidaten[f.name] = (detail, module)
        zeilen.append((f.name, a, b, c, d, e))

    gebaut = {}
    if args.lean:
        alle_module = sorted({m for _, mods in geschlossen_kandidaten.values() for m in mods})
        gruen = lake_bau(alle_module)
        for name in geschlossen_kandidaten:
            gebaut[name] = gruen

    print(f"zaehle-kette: {len(zeilen)} programs in beispiele/*.gab, binary {binary}")
    print("  sieve: (a) Lean parse [uebersetzeAllg]  (b) lean-g [diag]  (c) certificate [diag]  "
          "(d) C forms  (e) generic KCert")
    kette = 0
    stopps = {}
    for name, a, b, c, d, e in zeilen:
        marken = "".join({"pass": "Y", "FAIL": "F", "-": ".", "0": "0"}[col[0]]
                         for col in (a, b, c, d, e))
        zu = False
        if name in geschlossen_kandidaten:
            if not args.lean:
                zustand = "instance present, Lean not re-run (needs --lean)"
            elif not gebaut.get(name):
                zustand = "instance present, lake build RED"
            elif a[0] != "pass" or d[0] != "pass":
                zustand = "instance present, but sieve (a) or (d) did not pass"
            else:
                zustand = "CLOSED: " + geschlossen_kandidaten[name][0]
                zu = True
        else:
            zustand = "no chain instance"
        kette += zu
        print(f"  [{marken}] {name}: {zustand}")
        for tag, col in zip("abcde", (a, b, c, d, e)):
            if col[0] != "pass":
                print(f"        ({tag}) {col[0]}: {col[1]}")
        if not zu:
            # The first sieve that stops the program, in chain order.
            if a[0] != "pass":
                grund = "(a) " + (a[1].split(":")[0].replace("stops at ", "") if a[0] == "FAIL"
                                  else "not measured")
            elif d[0] != "pass":
                grund = "(d) C forms"
            elif e[0] != "pass":
                grund = "(e) correspondence certificate"
            else:
                grund = "no chain instance"
            stopps[grund] = stopps.get(grund, 0) + 1
    n = {tag: sum(1 for z in zeilen if z[i][0] == "pass") for i, tag in enumerate("abcde", 1)}
    print(f"\n  sieve totals: (a) {n['a']}  (b) {n['b']}  (c) {n['c']}  (d) {n['d']}  (e) {n['e']} "
          f"of {len(zeilen)}")
    print("  first stopping sieve of the programs without a closed chain: " +
          ", ".join(f"{k}: {v}" for k, v in sorted(stopps.items())))
    print(f"== CHAIN COUNT: {kette} of {len(zeilen)} programs have a CLOSED chain (a Lean-checked "
          f"instance of the generic `schlusssatz`) (unmeasured counts as not passed) ==")
    if lean_fehlt:
        print("== EXIT RED: `--lean` was asked for and column (a) did not answer ==")
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
