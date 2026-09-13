#!/usr/bin/env python3
"""**No emitted C form without its semantics** -- the guard of T4.

    ./instrumente/pruefe-cformen.py [--binary PATH] [--allow-stale] [--forms] [--examples N]

WHAT IT DOES
------------
It emits every tracked `beispiele/*.gab` with the built binary (`gabbro emit`), cuts the
function bodies of the emitted C into statements, and CLASSIFIES every statement and every
expression form in it against the table `FORMS` below. Each row of the table is one emitted
shape; a row that has a correspondence lemma NAMES it (the Lean theorem in `grammatik/`
that states the shape's correspondence to Gabbro), and the guard checks by grep that every
named lemma exists. A row without a lemma is an UNCOVERED form.

It prints, per form, how often the corpus emits it and in how many programs; then the
uncovered forms with their counts; then every statement it could not classify at all.

It FAILS (exit 1) when
  * a named lemma does not exist in `grammatik/Grammatik/*.lean`;
  * an uncovered form occurs that is not in `KNOWN_UNCOVERED` (a dated list, each entry
    with its reason) -- the emitter has started to emit a form nobody gave a meaning;
  * a statement matches no row at all -- a new shape, which is the same finding one step
    earlier: the classifier does not know it, so nothing can have proved it.
It ABORTS (exit 2) when the binary is older than a source file under `crates/` (it would
measure a different emitter than the tree's), unless `--allow-stale` is given; then every
number carries that caveat in the output.

WHAT THE NUMBERS DO NOT SAY
---------------------------
* **A named lemma is a claim that a lemma exists, not that it applies.** The classifier
  recognises shapes by regular expressions over the emitter's own layout (one statement per
  line, its brace style); it does not check that the lemma's premises hold at the site
  (range guarantees, frame conditions, the ordinal convention of reasons -- see the
  lemmas). A covered form means: this SHAPE has a correspondence lemma.
* **Some lemmas are per-step or uninhabited** (the `note` column): the device register
  forms (`regLies_step`, `regSchreib_step`) are per-step lemmas with the device window's
  liveness as a premise; `gcorr_onTag` is proved but its premise cannot hold (ValCorr has
  no case for a tagged union). Those rows are listed as KNOWN_UNCOVERED, not as covered.
* **The count is of emitted occurrences in the corpus**, not of distinct programs; the
  program count is printed beside it.
"""
import argparse
import collections
import pathlib
import re
import subprocess
import sys

W = pathlib.Path(__file__).resolve().parent.parent
GRAMMATIK = W / "grammatik" / "Grammatik"

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import korpus  # noqa: E402

# ---------------------------------------------------------------------------------------
# THE TABLE. (name, [lemmas], note). A form with an empty lemma list is UNCOVERED.
# The order of STMT_RULES below decides which row a statement lands in; the rows here only
# carry the lemma names.
# ---------------------------------------------------------------------------------------
FORMS = {
    # --- statements -------------------------------------------------------------------
    "stmt:return-void":        (["scorr_ret"], "S5"),
    "stmt:return-expr":        (["scorr_ret", "ergCorr_run"], "S5"),
    "stmt:channel-return-true": (["kcorr_ret"], "K2: `*_wert = e; return true;`"),
    "stmt:channel-return-false": (["kcorr_retGrund", "kcorr_weiterleiten"], "K1/R2"),
    "stmt:channel-grund-const": (["kcorr_retGrund"], "K1: `*_grund = F;`"),
    "stmt:channel-grund-fwd":  (["kcorr_weiterleiten"], "R2: `*_grund = e;`"),
    "stmt:channel-wert":       (["kcorr_ret"], "K2: `*_wert = e;`"),
    "stmt:decl-init":          (["cCorr_block", "cCorrG_block"], "S8: `T x = e;`"),
    "stmt:decl-cell":          (["cCorr_rufG", "cCorr_rufK"],
                                "`T x;`: no run-time effect (a C local starts unwritten; an "
                                "address-taken one is a frame cell, `enterFrame`)"),
    "stmt:assign-local":       (["scorr_assignVar"], "S1"),
    "stmt:assign-global":      (["scorr_assignGlob", "scorr_assignGlobAtomar"], "S4"),
    "stmt:compound-local":     (["scorr_plusGleich", "scorr_minusGleich", "scorr_undGleich",
                                 "scorr_oderGleich"], "S2: += -= &= |="),
    "stmt:store-slot-ptr":     (["scorr_assignSlotParam", "scorr_assignDurch"], "M2"),
    "stmt:store-slot-named":   (["scorr_assignSlotNamed"], "S3"),
    "stmt:void-expr":          (["cCorr_block"], "`(void)x;` (BlockCorr.pre)"),
    "stmt:if":                 (["scorr_ite", "gcorr_ite"], "S6"),
    "stmt:if-return":          (["scorr_ite", "scorr_ret"], "`if (c) return e;`"),
    "stmt:else":               (["scorr_ite"], "S6"),
    "stmt:if-call-else":       (["bsemG_bindCallElse"], "K4: `if (!f(a, &n, &e)) {`"),
    "stmt:switch-reason":      (["gcorr_onGrund"], "R1"),
    "stmt:case":               (["gcorr_onGrund"], "R1 (an arm)"),
    "stmt:case-end":           (["arm_brk"], "`} break;`"),
    "stmt:for-counting":       (["scorr_traverse"], "S7"),
    "stmt:retry-counter":      (["scorr_retry"], "retry: `uint32_t _rN = 0;`"),
    "stmt:retry-header":       (["scorr_retry", "scorrC_retry"], "retry loop header"),
    "stmt:retry-check":        (["scorr_retry", "scorrC_retry"], "retry: the check after"),
    "stmt:goto":               (["scorr_leave", "scorr_next"], "H1"),
    "stmt:label":              (["scorr_traverse", "scorr_retry"], "`m_ende: ;` / `m_weiter: ;`"),
    "stmt:call-unit":          (["scorr_call"], "M7"),
    "stmt:call-lock":          (["scorr_locks", "gcorr_locks", "scorr_extPre"], "M8"),
    "stmt:call-foreign":       (["scorr_axiomCall"], "H5"),
    "stmt:bind-call-unit":     (["bsem_bindCall"], "M7: `T x = f(a);`"),
    "stmt:publish":            (["scorr_publish"], "H2"),
    "stmt:awaits":             (["bsem_awaits"], "H3"),
    "stmt:unreachable":        (["gcorr_seqTot"], "`__builtin_unreachable();`"),
    "stmt:preproc":            (["gcorr_seqTot"], "`#if defined(__GNUC__)` around it"),
    # uncovered or per-step statement forms (see KNOWN_UNCOVERED)
    "stmt:switch-tag":         ([], "R5 proved (gcorr_onTag), not inhabitable"),
    "stmt:decl-union-payload": ([], "`T x = m.last.F;` (onTag payload)"),
    "stmt:reg-store":          ([], "H10 per-step only (regSchreib_step)"),
    "stmt:reg-load":           ([], "H9 per-step only (regLies_step)"),
    "stmt:forever":            ([], "`for (;;) {` (forever, CAS loop)"),
    "stmt:for-chain":          ([], "`for (v = a; v != N; v = next)` (chain walk)"),
    "stmt:cas-loop":           ([], "the `exchange update` CAS loop"),
    "stmt:cas":                (["cas_success", "cas_failure"], "H4 (one step)"),
    "stmt:compound-other":     ([], "compound assignment on a place or `x++`"),
    "stmt:store-array":        ([], "`A[i] = e;` (static array, byte view, arena)"),
    "stmt:struct-init":        ([], "`T x = (T){ .f = v };` (M10 has no Gabbro form)"),
    "stmt:call-indirect":      ([], "`t->f(a);` (callInd)"),
    "stmt:bind-call-foreign":  ([], "`T x = ext();` (bindAxiom)"),
    "stmt:asm":                ([], "inline asm (syscall/port stubs)"),
    "stmt:watchdog":           ([], "`static void (*const w)(void) = f;` (no run-time effect)"),
    "stmt:break":              ([], "`break;` outside a switch arm (CAS loop)"),
    "stmt:float":              ([], "floating point"),
    "stmt:store-deref":        ([], "`*p = e;` other than the channel"),
    "stmt:store-field":        ([], "`p->f = e;` on a struct that is not a table slot"),
    "stmt:walk":               ([], "the `descendants of` walk (`_k`, `_h`, `_w` locals)"),
    "stmt:trap-guard":         ([], "`if (!(i < N)) __builtin_trap();` (byte writer guard)"),
    # --- expressions ------------------------------------------------------------------
    "expr:slot-read":          (["ecorr_slotParam", "ecorr_slotNamed", "ecorr_durch"], "M1/E23"),
    "expr:sizeof":             (["ev_sizeofQuot", "hiSlots_ev"], "M5"),
    "expr:ternary":            (["ev_condT", "ev_condF", "cond_max"], "M4"),
    "expr:sat-u":              (["satU_run", "satU_zahl"], "E22"),
    "expr:le32":               (["ecorr_le32"], "H6"),
    "expr:byte-guard":         (["ecorr_byteGuard"], "H7"),
    "expr:bnot":               (["ecorr_bnot"], "E19"),
    "expr:shift":              (["ecorr_shl", "ecorr_shr"], "E15/E16"),
    "expr:cast":               (["ecorr_cast"], "E20"),
    "expr:land-lor":           (["ecorr_und", "ecorr_oder"], "M3"),
    "expr:lnot":               (["ecorr_nicht"], "E18"),
    "expr:atomic-load":        (["bsem_awaits"], "H3"),
    "expr:cell-read":          (["ev_zs"], "a read of an address-taken local"),
    "expr:reason-const":       (["ecorr_grundLit"], "a reason constant `R_F`"),
    "expr:sat-i":              ([], "`_gabbro_sat_i` (signed saturation)"),
    "expr:byte-reader-other":  ([], "byte readers other than `gabbro_le32`"),
    "expr:volatile":           ([], "device register read (per-step only)"),
    "expr:call":               ([], "a call inside an expression (CX has no call node)"),
    "expr:union-payload":      ([], "`m.last.F` (union payload)"),
    "expr:neg":                ([], "unary minus"),
    "expr:array-read":         ([], "`A[i]` outside a slot (static array, arena, byte view)"),
    "expr:field":              ([], "`p->f` / `x.f` outside a slot (device handle, view, struct)"),
    "expr:address-of":         ([], "`&x` outside an out-parameter call"),
}

# Forms known to have no correspondence lemma, with the date they were recorded and why.
KNOWN_UNCOVERED = {
    "stmt:switch-tag": ("2026-09-13", "gcorr_onTag is proved, but ValCorr has no case for "
                        "a tagged union, so no related state has a union variable"),
    "stmt:decl-union-payload": ("2026-09-13", "the payload read of an onTag arm"),
    "stmt:reg-store": ("2026-09-13", "regSchreib_step is per-step; corrW says nothing "
                       "about device windows"),
    "stmt:reg-load": ("2026-09-13", "regLies_step is per-step"),
    "stmt:forever": ("2026-09-13", "forever has no lemma of its own (T4 item 4)"),
    "stmt:for-chain": ("2026-09-13", "the chain walk has no Gabbro constructor"),
    "stmt:cas-loop": ("2026-09-13", "only the CAS step is covered (cas_success/failure)"),
    "stmt:compound-other": ("2026-09-13", "compound assignment is covered on locals only"),
    "stmt:store-array": ("2026-09-13", "schreibBytes and the byte writers, arena"),
    "stmt:struct-init": ("2026-09-13", "structLocal_rw has no Gabbro counterpart"),
    "stmt:call-indirect": ("2026-09-13", "callInd has no lemma"),
    "stmt:bind-call-foreign": ("2026-09-13", "bindAxiom has no lemma"),
    "stmt:asm": ("2026-09-13", "the stub body is a foreign step, outside the subset"),
    "stmt:watchdog": ("2026-09-13", "no run-time effect; the model has no form for it"),
    "stmt:break": ("2026-09-13", "the CAS loop's break"),
    "stmt:float": ("2026-09-13", "floating point is outside T4"),
    "stmt:store-deref": ("2026-09-13", "a store through a pointer parameter other than "
                         "the channel"),
    "stmt:store-field": ("2026-09-13", "a struct behind a pointer has no memory relation"),
    "stmt:walk": ("2026-09-13", "the walk has no Gabbro constructor (CFormenI CUTS)"),
    "stmt:trap-guard": ("2026-09-13", "the byte writers' bound check (T4 item 4)"),
    "expr:sat-i": ("2026-09-13", "the signed saturation helper (T4 item 4)"),
    "expr:byte-reader-other": ("2026-09-13", "only gabbro_le32 has a lemma"),
    "expr:volatile": ("2026-09-13", "device reads are per-step lemmas"),
    "expr:call": ("2026-09-13", "calls in expressions: bank/format accessors, port reads"),
    "expr:union-payload": ("2026-09-13", "see stmt:switch-tag"),
    "expr:neg": ("2026-09-13", "Expr.neg has no correspondence lemma"),
    "expr:array-read": ("2026-09-13", "constTab_read covers static const tables only"),
    "expr:field": ("2026-09-13", "device handles and views are per-step"),
    "expr:address-of": ("2026-09-13", "address-of outside the out-parameter call"),
}

CTYPE = r"(?:const\s+)?(?:uint8_t|uint16_t|uint32_t|uint64_t|int8_t|int16_t|int32_t|int64_t|bool|uintptr_t)"
IDENT = r"[A-Za-z_][A-Za-z0-9_]*"


def strip_comments(src):
    src = re.sub(r"/\*.*?\*/", " ", src, flags=re.S)
    return re.sub(r"//[^\n]*", "", src)


class Unit:
    """What the classifier needs to know about one emitted file."""

    def __init__(self, src):
        self.src = src
        self.defined = set()      # functions with a body
        self.declared = set()     # every prototype
        self.globals = set()      # file-scope objects
        self.enums = set()        # enum constants
        self.bodies = []          # (function name, has channel, [statements])
        self._scan()

    def _scan(self):
        for m in re.finditer(r"^\s*(" + IDENT + r")\s*(?:=\s*-?\d+)?\s*,\s*$", self.src, re.M):
            self.enums.add(m.group(1))
        for m in re.finditer(r"^(?:static\s+|extern\s+|_Noreturn\s+)*[A-Za-z_][A-Za-z0-9_ \*]*?\b("
                             + IDENT + r")\s*\([^;{]*\)\s*(?:__attribute__\S*\s*)*;", self.src, re.M):
            self.declared.add(m.group(1))
        for m in re.finditer(r"^static\s+(?:_Atomic\s+)?(?:const\s+)?(?:volatile\s+)?"
                             + IDENT + r"\s+(" + IDENT + r")\s*(?:\[[^\]]*\])?\s*(?:=|;)",
                             self.src, re.M):
            self.globals.add(m.group(1))
        for m in re.finditer(r"^_Atomic\s+" + IDENT + r"\s+(" + IDENT + r")", self.src, re.M):
            self.globals.add(m.group(1))
        lines = self.src.split("\n")
        depth = 0
        cur = None
        for ln in lines:
            s = ln.strip()
            if not s:
                continue
            if depth == 0:
                m = re.match(r"^(?:static\s+|_Noreturn\s+)*[A-Za-z_][A-Za-z0-9_ \*]*?\b(" + IDENT
                             + r")\s*\((.*)\)\s*(?:__attribute__\S*\s*)*\{$", s)
                if m and not s.startswith("typedef"):
                    cur = (m.group(1), "_grund" in m.group(2), [])
                    self.defined.add(m.group(1))
                    self.bodies.append(cur)
                    depth = 1
                    continue
                depth += s.count("{") - s.count("}")
                continue
            depth += s.count("{") - s.count("}")
            if depth <= 0:
                depth = 0
                cur = None
                continue
            if cur is not None:
                cur[2].append(s)


def split_statements(line):
    """Split a line at top-level `;` (a few emitted lines carry two statements)."""
    out, depth, start = [], 0, 0
    for i, ch in enumerate(line):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif ch == ";" and depth == 0:
            out.append(line[start:i + 1].strip())
            start = i + 1
    rest = line[start:].strip()
    if rest:
        out.append(rest)
    return [s for s in out if s]


def classify_stmt(s, unit, channel):
    """The statement form of `s`, or None."""
    if s in ("{", "}"):
        return "brace"
    if s.startswith("#"):
        return "stmt:preproc"
    if "__asm__" in s or s.startswith(":") or re.match(r'^"', s) or s == ");":
        return "stmt:asm"
    if s.startswith("static void (*const"):
        return "stmt:watchdog"
    if re.search(r"\b_(?:k|h|w)\d+(?:_hoch)?\b", s) or re.match(r"^const " + CTYPE + r" _r\d+ = ", s) \
            or s == "continue;":
        return "stmt:walk"
    if re.search(r"\b(double|float|isfinite)\b", s):
        return "stmt:float"
    if s == "__builtin_unreachable();":
        return "stmt:unreachable"
    if s == "} else {" or re.match(r"^\} else if \(", s):
        return "stmt:else"
    if s == "} break;":
        return "stmt:case-end"
    if s == "break;":
        return "stmt:break"
    if re.match(r"^case " + IDENT + r": \{$", s) or re.match(r"^case -?\d+u?: \{$", s):
        return "stmt:case"
    if re.match(r"^switch \(.*\.marke\) \{$", s):
        return "stmt:switch-tag"
    if re.match(r"^switch \(" + IDENT + r"\) \{$", s):
        return "stmt:switch-reason"
    if s == "for (;;) {":
        return "stmt:forever"
    if re.match(r"^for \(; !\(.*\) && _r\d+ < \d+u; _r\d+ \+= 1\) \{$", s):
        return "stmt:retry-header"
    if re.match(r"^for \(" + CTYPE + r" " + IDENT + r" = .*; " + IDENT + r" < .*; " + IDENT
                + r" \+= 1\) \{$", s):
        return "stmt:for-counting"
    if re.match(r"^for \(", s):
        return "stmt:for-chain"
    if re.match(r"^if \(_r\d+ >= \d+u && !\(.*\)\) \{ " + IDENT + r"\(\); \}$", s):
        return "stmt:retry-check"
    if re.match(r"^uint32_t _r\d+ = 0;$", s):
        return "stmt:retry-counter"
    if re.match(r"^if \(atomic_compare_exchange_(weak|strong)_explicit\(", s) or \
            re.match(r"^&" + IDENT + r", &_cx\d+", s) or re.match(r"^_ci\d+\+\+;$", s) or \
            re.match(r"^if \(_ci\d+ >= ", s) or re.match(r"^_cn\d+ = .*; goto _cn\d+_fertig;$", s) or \
            re.match(r"^_cn\d+_fertig: ;$", s) or re.match(r"^" + CTYPE + r" _c[xin]\d+ = ", s):
        return "stmt:cas-loop"
    if re.match(r"^" + IDENT + r" = atomic_compare_exchange_(strong|weak)_explicit\($", s):
        return "stmt:cas"
    if re.match(r"^if \(!" + IDENT + r"\(.*&" + IDENT + r", &" + IDENT + r"\)\) \{$", s):
        return "stmt:if-call-else"
    if re.match(r"^if \(.*\) return [^;]*;$", s):
        return "stmt:if-return"
    if re.match(r"^if \(.*\) (break|continue);$", s):
        return "stmt:cas-loop"
    if re.match(r"^if \(.*\) \{$", s):
        return "stmt:if"
    if s == "return;":
        return "stmt:return-void"
    if channel and s == "return true;":
        return "stmt:channel-return-true"
    if channel and s == "return false;":
        return "stmt:channel-return-false"
    if re.match(r"^return .*;$", s):
        return "stmt:return-expr"
    if re.match(r"^goto " + IDENT + r";$", s):
        return "stmt:goto"
    if re.match(r"^" + IDENT + r": ;$", s):
        return "stmt:label"
    if re.match(r"^\*_grund = " + IDENT + r";$", s):
        name = s[len("*_grund = "):-1]
        return "stmt:channel-grund-const" if name in unit.enums else "stmt:channel-grund-fwd"
    if s.startswith("*_wert = "):
        return "stmt:channel-wert"
    if re.match(r"^\(?\*\(volatile ", s) or re.match(r"^\*\(volatile ", s):
        return "stmt:reg-store"
    if re.match(r"^\*", s):
        return "stmt:store-deref"
    if re.match(r"^atomic_store_explicit\(", s):
        return "stmt:publish"
    if re.match(r"^\(void\)" + IDENT + r";$", s):
        return "stmt:void-expr"
    m = re.match(r"^\(void\)(" + IDENT + r")\(.*\);$", s)
    if m:
        return "stmt:call-unit" if m.group(1) in unit.defined else "stmt:call-foreign"
    if re.match(r"^if \(.*\) __builtin_trap\(\);$", s):
        return "stmt:trap-guard"
    m = re.match(r"^(" + IDENT + r")(?:->|\.)(" + IDENT + r")\(.*\);$", s)
    if m:
        return "stmt:call-indirect"
    m = re.match(r"^(" + IDENT + r")\((.*)\);$", s)
    if m:
        f = m.group(1)
        if re.search(r"_(nimm|gib)$", f) or re.search(r"_(lese|schreib)_(start|ende)$", f):
            return "stmt:call-lock"
        return "stmt:call-unit" if f in unit.defined else "stmt:call-foreign"
    m = re.match(r"^(" + CTYPE + r"|" + IDENT + r") (" + IDENT + r")( = (.*))?;$", s)
    if m:
        init = m.group(4)
        if init is None:
            return "stmt:decl-cell"
        if re.match(r"^\(" + IDENT + r"\)\{", init):
            return "stmt:struct-init"
        if re.match(r"^atomic_load_explicit\(", init):
            return "stmt:awaits"
        if re.match(r"^\(\*\(volatile ", init) or re.match(r"^\(+\*\(volatile ", init):
            return "stmt:reg-load"
        if ".last." in init:
            return "stmt:decl-union-payload"
        mc = re.match(r"^(" + IDENT + r")\((.*)\)$", init)
        if mc and mc.group(1) not in ("sizeof",):
            return "stmt:bind-call-unit" if mc.group(1) in unit.defined else "stmt:bind-call-foreign"
        return "stmt:decl-init"
    if re.match(r"^" + IDENT + r"(\[[^\]]*\]|\.buf\[)", s) and "=" in s:
        return "stmt:store-array"
    if re.match(r"^" + IDENT + r"->" + IDENT + r"\[[^\]]*\] = ", s) and "->slots[" not in s:
        return "stmt:store-array"
    if re.match(r"^" + IDENT + r"\.buf\[", s):
        return "stmt:store-array"
    if re.match(r"^" + IDENT + r"->slots\[[^\]]*\]\.[A-Za-z0-9_.]+ = .*;$", s):
        return "stmt:store-slot-ptr"
    if re.match(r"^" + IDENT + r"\.slots\[[^\]]*\]\.[A-Za-z0-9_.]+ = .*;$", s):
        return "stmt:store-slot-named"
    if re.match(r"^" + IDENT + r"(->|\.)slots\[[^\]]*\]\.[A-Za-z0-9_.]+ [-+*&|^]=", s) or \
            re.match(r"^" + IDENT + r"\+\+;$", s) or re.match(r"^" + IDENT + r" (\*|/|%|<<|>>|\^)= ", s) or \
            re.match(r"^" + IDENT + r"(->|\.)" + IDENT + r" [-+*&|^]= ", s):
        return "stmt:compound-other"
    m = re.match(r"^(" + IDENT + r") ([-+&|])= .*;$", s)
    if m:
        return "stmt:compound-local"
    m = re.match(r"^(" + IDENT + r") = (.*);$", s)
    if m:
        if m.group(2).startswith("atomic_load_explicit("):
            return "stmt:awaits"
        return "stmt:assign-global" if m.group(1) in unit.globals else "stmt:assign-local"
    if re.match(r"^" + IDENT + r"\.[A-Za-z0-9_.]+ = .*;$", s):
        return "stmt:struct-init"
    if re.match(r"^" + IDENT + r"->[A-Za-z0-9_.]+ = .*;$", s):
        return "stmt:store-field"
    return None


EXPR_RULES = [
    ("expr:slot-read", r"(?:->|\.)slots\["),
    ("expr:sizeof", r"\bsizeof\("),
    ("expr:ternary", r"\?[^:]*:"),
    ("expr:sat-u", r"\b_gabbro_sat_u\("),
    ("expr:sat-i", r"\b_gabbro_sat_i\("),
    ("expr:le32", r"\bgabbro_le32\("),
    ("expr:byte-reader-other", r"\bgabbro_(?:le16|le64|be16|be32|be64|u8|lese|schreib)\w*\("),
    ("expr:byte-guard", r"\(__builtin_trap\(\), 0\)"),
    ("expr:bnot", r"~"),
    ("expr:shift", r"<<|>>"),
    ("expr:cast", r"\((?:u?int(?:8|16|32|64)_t|bool)\)"),
    ("expr:land-lor", r"&&|\|\|"),
    ("expr:lnot", r"!\(|![A-Za-z_]"),
    ("expr:atomic-load", r"\batomic_load_explicit\("),
    ("expr:volatile", r"\*\(volatile "),
    ("expr:union-payload", r"\.last\."),
    ("expr:neg", r"(?:^|[=(,\s])-(?:[A-Za-z_(]|\d)"),
    ("expr:cell-read", None),      # decided by context: a name declared as a cell
    ("expr:reason-const", None),   # decided by context: an enum constant
    ("expr:call", None),           # decided by context: a call not covered above
    ("expr:array-read", None),
    ("expr:field", None),
    ("expr:address-of", None),
]

HELPERS = {"sizeof", "_gabbro_sat_u", "_gabbro_sat_i", "gabbro_le32", "atomic_load_explicit",
           "atomic_store_explicit", "atomic_compare_exchange_strong_explicit",
           "atomic_compare_exchange_weak_explicit", "__builtin_trap", "if", "for", "switch",
           "return", "while"}


def expression_part(s, form):
    """The part of a statement that is expression text."""
    if form in ("brace", "stmt:preproc", "stmt:asm", "stmt:else", "stmt:case-end", "stmt:case",
                "stmt:label", "stmt:goto", "stmt:watchdog", "stmt:decl-cell", "stmt:break",
                "stmt:retry-counter", "stmt:unreachable"):
        return ""
    if form == "stmt:if-call-else":
        return ""
    if form in ("stmt:retry-header",):
        m = re.match(r"^for \(; !\((.*)\) && _r\d+", s)
        return m.group(1) if m else ""
    if form == "stmt:retry-check":
        m = re.match(r"^if \(_r\d+ >= \d+u && !\((.*)\)\) \{", s)
        return m.group(1) if m else ""
    return s


def classify_exprs(text, unit, cells, form):
    found = []
    if not text:
        return found
    for name, rx in EXPR_RULES:
        if rx and re.search(rx, text):
            found.append(name)
    # calls inside the expression (a statement-level call is its statement form)
    body = text
    if form in ("stmt:call-unit", "stmt:call-foreign", "stmt:call-lock", "stmt:bind-call-unit",
                "stmt:bind-call-foreign", "stmt:call-indirect", "stmt:publish", "stmt:cas"):
        m = re.search(r"\((.*)\)", text)
        body = m.group(1) if m else ""
    for m in re.finditer(r"\b(" + IDENT + r")\(", body):
        f = m.group(1)
        if f in HELPERS or re.match(r"^u?int(8|16|32|64)_t$", f) or f == "bool" or \
                f.startswith("gabbro_") or f.startswith("_gabbro_"):
            continue
        found.append("expr:call")
        break
    for m in re.finditer(r"\b(" + IDENT + r")\b", text):
        w = m.group(1)
        if w in cells:
            found.append("expr:cell-read")
            break
    for m in re.finditer(r"\b(" + IDENT + r")\b", text):
        if m.group(1) in unit.enums:
            found.append("expr:reason-const")
            break
    t2 = re.sub(r"(?:->|\.)slots\[[^\]]*\]", "", text)
    if re.search(r"\b" + IDENT + r"\[", t2) and "expr:byte-guard" not in found:
        found.append("expr:array-read")
    t3 = re.sub(r"(?:->|\.)slots\[[^\]]*\](?:\.[A-Za-z0-9_]+)*", "", text)
    t3 = re.sub(r"\.last\.[A-Za-z0-9_]+", "", t3)
    if re.search(r"(?:->|\b" + IDENT + r"\.)(?!slots)[A-Za-z_]", t3) and "expr:volatile" not in found:
        if not re.search(r"\.marke\b", t3):
            found.append("expr:field")
    if re.search(r"(?:^|[(,=\s])&" + IDENT, text) and form not in ("stmt:publish", "stmt:awaits",
                                                                  "stmt:cas", "stmt:cas-loop"):
        found.append("expr:address-of")
    return found


def lemma_exists(name, sources):
    return re.search(r"^(?:theorem|def|lemma|abbrev)\s+" + re.escape(name) + r"\b", sources, re.M) is not None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--binary", default=str(W / "target" / "debug" / "gabbro"))
    ap.add_argument("--allow-stale", action="store_true")
    ap.add_argument("--forms", action="store_true", help="print every form, covered or not")
    ap.add_argument("--examples", type=int, default=3)
    args = ap.parse_args()

    binary = pathlib.Path(args.binary)
    if not binary.exists():
        print(f"ABBRUCH: no binary at {binary} -- build it (on ki-pc-fisch-101) or pass --binary")
        return 2
    stand = binary.stat().st_mtime
    newer = sorted(q for q in W.glob("crates/*/src/*.rs") if q.stat().st_mtime > stand)
    stale_note = ""
    if newer:
        msg = (f"the binary is OLDER than {len(newer)} source file(s) under crates/ "
               f"(first: {newer[0].relative_to(W)}) -- it measures another emitter")
        if not args.allow_stale:
            print("ABBRUCH: " + msg)
            print("  (build it, or pass --allow-stale to measure that binary anyway)")
            return 2
        stale_note = "  CAVEAT: " + msg
        print(stale_note)

    files = sorted(p for p in (W / "beispiele").glob("*.gab") if korpus.verfolgt(p, W))
    counts = collections.Counter()
    programs = collections.defaultdict(set)
    examples = collections.defaultdict(list)
    unclassified = collections.Counter()
    unclassified_ex = {}
    emitted = refused = 0
    for f in files:
        r = subprocess.run([str(binary), "emit", str(f)], capture_output=True, text=True, cwd=W)
        if r.returncode != 0 or not r.stdout.strip():
            refused += 1
            continue
        emitted += 1
        src = strip_comments(r.stdout)
        unit = Unit(src)
        for fname, channel, lines in unit.bodies:
            cells = set()
            for ln in lines:
                for s in split_statements(ln):
                    form = classify_stmt(s, unit, channel)
                    if form is None:
                        unclassified[s] += 1
                        unclassified_ex.setdefault(s, f.name)
                        continue
                    if form == "stmt:decl-cell":
                        m = re.match(r"^\S+ (" + IDENT + r");$", s)
                        if m:
                            cells.add(m.group(1))
                    if form != "brace":
                        counts[form] += 1
                        programs[form].add(f.name)
                        if len(examples[form]) < args.examples:
                            examples[form].append(f"{f.name}: {s[:110]}")
                    for ex in set(classify_exprs(expression_part(s, form), unit, cells, form)):
                        counts[ex] += 1
                        programs[ex].add(f.name)
                        if len(examples[ex]) < args.examples:
                            examples[ex].append(f"{f.name}: {s[:110]}")

    sources = "\n".join(p.read_text() for p in GRAMMATIK.glob("*.lean"))
    missing = []
    for form, (lemmas, _) in FORMS.items():
        for lm in lemmas:
            if not lemma_exists(lm, sources):
                missing.append((form, lm))

    print(f"pruefe-cformen: {emitted} programs emitted, {refused} refused by the emitter, "
          f"binary {binary}")
    covered = [(f, n) for f, n in counts.items() if FORMS.get(f, ([], ""))[0]]
    uncovered = [(f, n) for f, n in counts.items() if not FORMS.get(f, ([], ""))[0]]
    tot_cov = sum(n for _, n in covered)
    tot_unc = sum(n for _, n in uncovered)
    print(f"  forms seen: {len(counts)} ({len(covered)} covered, {len(uncovered)} uncovered); "
          f"occurrences: {tot_cov} covered, {tot_unc} uncovered, "
          f"{sum(unclassified.values())} unclassified statements")
    if args.forms:
        print("\n  COVERED FORMS (occurrences / programs / lemma)")
        for f, n in sorted(covered, key=lambda x: -x[1]):
            print(f"    {n:6d} {len(programs[f]):4d}  {f:28s} {', '.join(FORMS[f][0])}")
    print("\n  UNCOVERED FORMS (occurrences / programs / known since)")
    new_uncovered = []
    for f, n in sorted(uncovered, key=lambda x: -x[1]):
        known = KNOWN_UNCOVERED.get(f)
        tag = known[0] if known else "NEW"
        print(f"    {n:6d} {len(programs[f]):4d}  {f:28s} [{tag}] {FORMS.get(f, ([], '?'))[1]}")
        for e in examples[f][:args.examples]:
            print(f"                 e.g. {e}")
        if not known:
            new_uncovered.append(f)
    if unclassified:
        print(f"\n  UNCLASSIFIED STATEMENTS ({sum(unclassified.values())}): a shape the table does "
              "not know")
        for s, n in unclassified.most_common(40):
            print(f"    {n:4d}  {unclassified_ex[s]}: {s[:120]}")
    if missing:
        print("\n  NAMED LEMMAS THAT DO NOT EXIST in grammatik/Grammatik/*.lean:")
        for form, lm in missing:
            print(f"    {form}: {lm}")
    stale = [f for f in KNOWN_UNCOVERED if counts.get(f, 0) == 0]
    if stale:
        print("\n  KNOWN_UNCOVERED entries not seen in this run (may be removed): "
              + ", ".join(stale))
    bad = bool(missing or new_uncovered or unclassified)
    print("\n" + ("RED" if bad else "GREEN") + f": {len(new_uncovered)} new uncovered form(s), "
          f"{sum(unclassified.values())} unclassified statement(s), {len(missing)} missing "
          f"lemma(s)." + (" " + stale_note.strip() if stale_note else ""))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
