#!/usr/bin/env python3
"""**No emitted C form without its semantics** -- the guard of T4.

    ./instrumente/pruefe-cformen.py [--binary PATH] [--allow-stale] [--forms] [--examples N]

WHAT IT DOES
------------
It emits every tracked `beispiele/*.gab` with the built binary (`gabbro emit`), cuts the
function bodies of the emitted C into statements, and CLASSIFIES every statement and every
expression form in it against the table `FORMS` below. Each row of the table is one emitted
shape; a row is in one of THREE states:

  (i)   **lemma** -- the row names the correspondence lemma (the Lean theorem in
        `grammatik/` stating the shape's correspondence to Gabbro), and the guard
        checks by grep that every named lemma exists;
  (ii)  **named assumption** -- the form has no C meaning BY CONSTRUCTION and enters
        the closing theorem (PLAN-UEBERSETZUNGSVALIDIERUNG.md section 3) as a premise:
        inline asm (the syscall/port stub bodies), device register access (the hardware
        profile), syscall stubs (the kernel). Each such row names the Lean
        premise/assumption it maps to (`NAMED_ASSUMPTIONS` below), grep-checked like
        the lemma rows;
  (iii) **without semantics** -- a row with neither lemma nor named assumption.

It prints, per form, how often the corpus emits it and in how many programs; then the
assumption forms with their counts; then the uncovered forms with their counts; then
every statement it could not classify at all.

It FAILS (exit 1) when
  * a named lemma does not exist in `grammatik/Grammatik/*.lean`;
  * a named assumption does not exist there (a `def`/`theorem` at line start, or a
    premise binder `name :` -- the assumption rows name binders like `hdev`, which no
    `theorem` line would match);
  * an uncovered (state iii) form occurs that is not in `KNOWN_UNCOVERED` (a dated list,
    each entry with its reason) -- the emitter has started to emit a form nobody gave
    a meaning;
  * a statement matches no row at all -- a new shape, which is the same finding one step
    earlier: the classifier does not know it, so nothing can have proved it.
Only state (iii) forms outside the dated list turn the guard red: assumption forms are
measured, not excused -- their counts print every run.
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
* **Some lemmas are per-step or uninhabited** (the `note` column): `gcorr_onTag` is
  proved but its premise cannot hold (ValCorr has no case for a tagged union). That row
  is listed as KNOWN_UNCOVERED, not as covered. The device register forms (`regLies_step`,
  `regSchreib_step`) are per-step lemmas with the device window's liveness as a premise;
  the emitted register shapes are state (ii) -- named assumptions, not lemmas.
* **The count is of emitted occurrences in the corpus**, not of distinct programs; the
  program count is printed beside it.
* **An assumption row is a claim that the closing theorem carries the premise, not that
  the premise holds.** `AxCorr` holds per foreign function (the kernel behind the stub);
  `hdev`/`RegLokal` hold per device (the hardware profile). A program whose stub or
  device misbehaves is outside the theorem, not inside a proof.

THE C TYPE DECIDES, NOT THE STATEMENT TEXT (repaired 2026-09-15)
---------------------------------------------------------------
Until 2026-09-15 the classifier built its row key from the statement TEXT alone. `return
c.len;` and `return (Nachricht){ .marke = ... };` were the same row `stmt:return-expr`, and
`uint32_t c = f(k);` and `Completion c = f(k);` the same row `stmt:bind-call-unit` -- both
rows in state (i), naming a lemma. **But the certificate cannot carry an aggregate C value
at all:** `CSpeicher.lean` section 1 has `CTy := int (sgn) (w) | ptr` and section 2 has
`CVal := int | ptr | undef`, so every `CTy` in a `GRow` is a scalar. The named lemmas
(`scorr_ret`/`ergCorr_run`, `bsem_bindCall`) are about those scalars. *A guardian that books
a form under a lemma that does not cover it is worse than one that reports it uncovered.*

The classifier therefore now knows the unit's aggregate types (`typedef struct`/`typedef
union`; an `enum` typedef is a scalar and is NOT one), the C return type of every function,
and the aggregate-typed names in every body. **The rule is the DESTINATION of a value:** a
statement is aggregate-classified when it makes a C value of aggregate type FLOW --

  * into the return slot     -> `stmt:return-aggregate`
  * into a fresh local       -> `stmt:bind-aggregate` (`stmt:struct-init` keeps the
                                compound literal, which was already uncovered)
  * into memory or a variable-> `stmt:store-aggregate`
  * into a parameter         -> `stmt:call-aggregate-arg`

`(void)x;` on an aggregate is deliberately NOT in the list: it has no destination, the
certificate emits no row for it, and `cCorr_block` (`BlockCorr.pre`) is about the block, not
about the value. A POINTER to an aggregate (`&v`, `p->f`) is a scalar `CVal.ptr` and stays
where it was.
"""
import argparse
import collections
import pathlib
import re
import subprocess
import sys

W = pathlib.Path(__file__).resolve().parent.parent
GRAMMATIK = W / "grammatik" / "Grammatik"

# A hang looks like "still running", not like a finding: every `emit` runs under FRIST,
# and a run that misses it counts as refused (no emission to classify).
FRIST = 300

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
    # INTEGER `match` (lane 227 lowers it to a C `switch`). Lane 228 merged
    # `CFormMatch.lean` WITHOUT a correspondence lemma for these rows (review G07
    # F3, fix lane F1): its lemmas are over the scrutinee value and restate the
    # two `Exec` constructors of `CS.sw`; nothing ties `fallListe` to an emitted
    # `CS.sw`. Both rows stay state (iii), owner OPEN (TODO).
    "stmt:switch-int":         ([], "integer `match` switch (lane 227; lemma: open)"),
    "stmt:case-int":           ([], "integer `match` arm (lane 227; lemma: open)"),
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
    # statement forms without a lemma: state (ii) assumptions and state (iii) uncovered
    "stmt:switch-tag":         ([], "R5 proved (gcorr_onTag), not inhabitable"),
    "stmt:decl-union-payload": ([], "`T x = m.last.F;` (onTag payload)"),
    # AGGREGATE C VALUES: a whole struct/union moved by value. `CTy` is `int | ptr` and
    # `CVal` is `int | ptr | undef` (CSpeicher.lean 1 and 2), so NO `GRow` can carry one --
    # not `ret`, not `bindLet`, not `setVar`, not `call`'s destination or its arguments.
    # These four rows are the same absence at four destinations; see the module docstring.
    "stmt:return-aggregate":   ([], "`return e;` where the function returns a struct BY VALUE "
                                "(GRow.ret carries a CTy, and CTy has no aggregate)"),
    "stmt:bind-aggregate":     ([], "`T x = e;` with `T` a struct/union typedef "
                                "(GRow.bindLet carries a CTy)"),
    "stmt:store-aggregate":    ([], "a store whose right-hand side is a whole struct value "
                                "(GRow.setVar / the memory carry a CVal)"),
    "stmt:call-aggregate-arg": ([], "a call passing a struct BY VALUE (GRow.call's arguments "
                                "are CX, evaluated to CVal)"),
    # state (ii): named assumptions (see NAMED_ASSUMPTIONS) -- no C meaning by
    # construction, entering the closing theorem as a premise
    "stmt:reg-store":          ([], "H10 device write: assumption, not lemma (NAMED_ASSUMPTIONS)"),
    "stmt:reg-load":           ([], "H9 device read: assumption, not lemma (NAMED_ASSUMPTIONS)"),
    "stmt:asm":                ([], "inline asm (syscall/port stubs): assumption (NAMED_ASSUMPTIONS)"),
    # state (iii): without semantics (see KNOWN_UNCOVERED)
    "stmt:forever":            (["scorr_forever"], "F1: `for (;;) {` after the watchdog line"),
    "stmt:for-ever-other":     ([], "`for (;;) {` of the CAS loop or the walk"),
    "stmt:for-chain":          ([], "`for (v = a; v != N; v = next)` (chain walk)"),
    "stmt:cas-loop":           ([], "the `exchange update` CAS loop"),
    "stmt:cas":                (["cas_success", "cas_failure"], "H4 (one step)"),
    "stmt:compound-other":     ([], "compound assignment on a place or `x++`"),
    "stmt:store-array":        ([], "`A[i] = e;` (static array, byte view, arena)"),
    # Lane 259 (2026-09-26) lowers dynamic-arena stores through the reserved
    # base (`((T *)D_desc.base)[i] = e;`) and the commit through the runtime
    # (`if (gabbro_arena_grow(&D, n))`). Both are new shapes with no lemma:
    # the store joins the `store-array` bucket beside its static twin, the
    # commit call gets its own uncovered row -- booked, never silent.
    "stmt:grow-call":         ([], "`if (gabbro_arena_grow(&D, n))` (runtime commit "
                                "in a branch condition)"),
    "stmt:struct-init":        ([], "`T x = (T){ .f = v };` (M10 has no Gabbro form)"),
    "stmt:call-indirect":      ([], "`t->f(a);` (callInd)"),
    "stmt:bind-call-foreign":  ([], "`T x = ext();` (bindAxiom)"),
    "stmt:watchdog":           ([], "`static void (*const w)(void) = f;` (no run-time effect)"),
    "stmt:break":              ([], "`break;` outside a switch arm (CAS loop)"),
    "stmt:float":              ([], "floating point outside the rows below (`float`/binary32, "
                                "float memory, mixed forms)"),
    # floating point in `double` (binary64, the model's width): CFormenF.lean, under the
    # named assumption `gleitkomma_ieee` (C float ops are the IEEE ops of the model)
    "stmt:float-decl-arith":   (["gsem_gleit", "gleitkomma_ieee"], "F1: `double c = a op b;`"),
    "stmt:float-decl-lit":     (["gsem_gleitLit"], "F2: `double c = LIT;`"),
    "stmt:float-decl-conv":    (["gsem_gleitVon"], "F3: `double c = n;` (int to float)"),
    "stmt:float-narrow-range": (["gsem_gleitNarrow", "narrowCondF_ge_le"],
                                "F5: `if (!(x >= LO && x <= HI)) {`"),
    "stmt:float-narrow-finite": (["gsem_gleitNarrow", "narrowCondF_endlich"],
                                 "F6: `if (!isfinite(x)) {`"),
    "expr:float-cmp":          (["ecorr_fllt", "ecorr_flle", "ecorr_flgt", "ecorr_flge"],
                                "F4: `<`, `<=`, `>`, `>=` on doubles"),
    "expr:float-lit-inline":   ([], "a float literal or float `#define` inline in an "
                                "expression or `return` (per-program: klemmen_corr)"),
    "stmt:store-deref":        ([], "`*p = e;` other than the channel"),
    "stmt:decl-ptr":           ([], "`T *p = e;` (pointer local, no memory relation)"),
    "stmt:store-field":        ([], "`p->f = e;` on a struct that is not a table slot"),
    "stmt:walk":               ([], "the `descendants of` walk (`_k`, `_h`, `_w` locals)"),
    "stmt:trap-guard":         ([], "`if (!(i < N)) __builtin_trap();` (byte writer guard)"),
    "stmt:label-kind":         ([], "the region label a gate trap jumps to (lane 260: the "
                                "child entered by jump; no correspondence lemma -- the "
                                "jump rests on the checker (N448-N450) and the trap "
                                "construction, O21)"),
    # --- expressions ------------------------------------------------------------------
    "expr:slot-read":          (["ecorr_slotParam", "ecorr_slotNamed", "ecorr_durch"], "M1/E23"),
    "expr:sizeof":             (["ev_sizeofQuot", "hiSlots_ev"], "M5"),
    "expr:ternary":            (["ev_condT", "ev_condF", "cond_max"], "M4"),
    "expr:sat-u":              (["satU_run", "satU_zahl"], "E22"),
    "expr:le32":               (["ecorr_le32"], "H6"),
    "expr:byte-guard":         (["ecorr_byteGuard"], "H7"),
    "expr:bnot":               (["ecorr_bnot"], "E19"),
    "expr:shift":              (["ecorr_shl", "ecorr_shr", "wrapC_shl"], "E15/E16, `<<%`"),
    "expr:cast":               (["ecorr_cast"], "E20"),
    "expr:land-lor":           (["ecorr_und", "ecorr_oder"], "M3"),
    "expr:lnot":               (["ecorr_nicht"], "E18"),
    "expr:atomic-load":        (["bsem_awaits"], "H3"),
    "expr:cell-read":          (["ev_zs"], "a read of an address-taken local"),
    "expr:reason-const":       (["ecorr_grundLit"], "a reason constant `R_F`"),
    "expr:sat-i":              (["satI_run", "satI_zahl"], "S-I"),
    "expr:byte-reader-other":  ([], "byte readers other than `gabbro_le32`"),
    "expr:volatile":           ([], "device register read: assumption, not lemma (NAMED_ASSUMPTIONS)"),
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
    # Lane 227 (2026-09-17) lowers integer `match` arms to a C `switch`. Lane
    # 228 merged without the correspondence lemma (review G07 F3); coverage is
    # the checker's `N411` since fix lane F1 (2026-09-21). Both rows stay state
    # (iii) with the lemma OPEN -- booked, never silent.
    "stmt:switch-int": ("2026-09-17", "integer `match` switch (lane 227 emits it; "
                        "correspondence lemma open: CFormMatch.lean has value-level "
                        "lemmas only, no tie to an emitted CS.sw)"),
    "stmt:case-int": ("2026-09-17", "integer `match` arm: `case N:` / `case N: {` "
                      "(lane 227 emits it; correspondence lemma open, see switch-int)"),
    # The four aggregate rows. They are NOT new emitter shapes -- the emitter has written
    # them all along; they are newly VISIBLE, because until today the classifier read the
    # statement text and not the C type, and booked them under `scorr_ret`/`ergCorr_run`,
    # `bsem_bindCall`, `scorr_assignSlotParam` and `scorr_axiomCall`. Measured on the day
    # they were separated: 19 occurrences in 15 programs left state (i) for state (iii),
    # and 2 more moved from `stmt:bind-call-foreign` into `stmt:bind-aggregate`.
    # The absence is ONE absence at four destinations, and it is named in `OFFEN.md` O16.
    "stmt:return-aggregate": ("2026-09-15", "`GRow.ret` carries an `Option (CTy x CX)` and "
                              "`CTy` is `int | ptr` (CSpeicher.lean 1): a struct returned by "
                              "value has no row, and no ABI in the model to have one by"),
    "stmt:bind-aggregate": ("2026-09-15", "`GRow.bindLet x tc ce` carries a `CTy`: a local of "
                            "struct type is a stack BLOCK of `RecLay` shape with one store "
                            "per field, not one row"),
    "stmt:store-aggregate": ("2026-09-15", "the memory of `CSpeicher.lean` maps addresses to "
                             "`CVal = int | ptr | undef`: a whole struct stored in one "
                             "statement is n field stores, not one"),
    "stmt:call-aggregate-arg": ("2026-09-15", "`GRow.call`'s arguments are `CX`, evaluated to "
                                "`CVal`: a struct passed by value has no argument node"),
    "stmt:for-ever-other": ("2026-09-13", "the CAS loop and the walk (no lemma)"),
    "stmt:for-chain": ("2026-09-13", "the chain walk has no Gabbro constructor"),
    "stmt:cas-loop": ("2026-09-13", "only the CAS step is covered (cas_success/failure)"),
    "stmt:compound-other": ("2026-09-13", "compound assignment is covered on locals only"),
    "stmt:store-array": ("2026-09-13", "schreibBytes and the byte writers, arena"),
    "stmt:grow-call": ("2026-09-26", "the runtime commit call in a branch condition "
                       "(lane 259 emits it; no correspondence lemma: the commit "
                       "is a runtime effect outside the lowered shapes)"),
    "stmt:struct-init": ("2026-09-13", "structLocal_rw has no Gabbro counterpart"),
    "stmt:call-indirect": ("2026-09-13", "callInd has no lemma"),
    "stmt:bind-call-foreign": ("2026-09-13", "bindAxiom has no lemma"),
    "stmt:watchdog": ("2026-09-13", "no run-time effect; the model has no form for it"),
    "stmt:break": ("2026-09-13", "the CAS loop's break"),
    "stmt:float": ("2026-09-14", "`float` (binary32) forms and floats in memory: Ty.fl "
                   "carries no width, the model computes binary64 (CFormenF.lean CUTS)"),
    "expr:float-lit-inline": ("2026-09-14", "the model binds a float constant "
                              "(Block.gleitLit), C inlines it; covered per program "
                              "(CFormenFZeuge.lean klemmen_corr), not by a general lemma"),
    "stmt:store-deref": ("2026-09-13", "a store through a pointer parameter other than "
                         "the channel"),
    "stmt:decl-ptr": ("2026-09-14", "a pointer local (`Platz * tz = SPEICHER;`, "
                      "38-unveraenderlicher-zeiger.gab): corrW relates slots, not C "
                      "pointers; unclassified until today"),
    "stmt:store-field": ("2026-09-13", "a struct behind a pointer has no memory relation"),
    "stmt:walk": ("2026-09-13", "the walk has no Gabbro constructor (CFormenI CUTS)"),
    "stmt:trap-guard": ("2026-09-13", "the byte writers' bound check (T4 item 4)"),
    "stmt:label-kind": ("2026-09-26", "the region label a gate trap jumps to (lane 260; "
                        "no lemma: the jump rests on the checker and the trap, O21)"),
    "expr:byte-reader-other": ("2026-09-13", "only gabbro_le32 has a lemma"),
    "expr:call": ("2026-09-13", "calls in expressions: bank/format accessors, port reads"),
    "expr:union-payload": ("2026-09-13", "see stmt:switch-tag"),
    "expr:neg": ("2026-09-13", "Expr.neg has no correspondence lemma"),
    "expr:array-read": ("2026-09-13", "constTab_read covers static const tables only"),
    "expr:field": ("2026-09-13", "device handles and views are per-step"),
    "expr:address-of": ("2026-09-13", "address-of outside the out-parameter call"),
}

# Forms with no C meaning BY CONSTRUCTION (state ii). Each row names the Lean
# premise/assumption it maps to in the closing theorem
# (PLAN-UEBERSETZUNGSVALIDIERUNG.md section 3, stage b); the guard grep-checks
# every named assumption like the lemma rows. A name matches when it stands as a
# `theorem`/`def`/`lemma`/`abbrev` at line start (e.g. `AxCorr`, `RegLokal`) or as
# a premise binder `name :` (e.g. `hdev`, the assumption at the register in
# `regLies_step`, which no `theorem` line would match).
#
# What stays OUT, and why:
#   * `stmt:bind-call-foreign` (`T x = ext();`): a foreign call WITH an answer. Its
#     assumption shape would be the `bindAxiom` analogue of `AxCorr`, which does not
#     exist (CFormenH CUTS). Mapping it to `AxCorr` would claim a premise the closing
#     theorem cannot carry -- so it stays state (iii).
#   * `expr:call` (port reads among others): the bucket is too broad for one premise
#     (bank/format accessors beside port I/O); it stays state (iii).
NAMED_ASSUMPTIONS = {
    # The syscall/port stub bodies are inline asm by construction (the stub the
    # emitter prints for a foreign declaration); the stub's EFFECT enters the closing
    # theorem as the `AxCorr` premise of `scorr_axiomCall` (CFormenH.lean) and of
    # `bridge_syscallStub` (ErhaltungT4.lean: "the kernel behind the stub is the named
    # assumption"). `SysAbi.gut` (Syscall.lean) is the neighbouring well-formedness
    # premise for syscall declarations; the row maps to the effect assumption.
    "stmt:asm": (["AxCorr"],
                 "stub bodies are `__asm__`; the effect is the `AxCorr` premise"),
    # `T x = (*(volatile T *)(BASE + K));` -- the C device oracle's answer is linked to
    # Gabbro's register oracle by the `hdev` premise of `regLies_step` (CFormenH.lean:
    # "the assumption at the register"); `RegLokal` (ZielOrtGeraetSem.lean) is the
    # hardware class the closing theorem carries: the answer may depend only on the
    # device carriers `D.rtraeger r`.
    "stmt:reg-load": (["hdev", "RegLokal"],
                      "H9 device read: `hdev` links the oracles, `RegLokal` bounds them"),
    # `(*(volatile T *)(BASE + K)) = e;` -- a device write has no Gabbro trace
    # (`Orakel.regSchreib` returns `Unit`; `regSchreib_step` concludes the `.vwr`
    # observation without an `hdev` analogue). It enters the closing theorem under the
    # same hardware class; the store side is the documented gap beside `RegLokal`.
    "stmt:reg-store": (["RegLokal"],
                       "H10 device write: no Gabbro trace; hardware class `RegLokal`"),
    # `*(volatile ...)` read inside an expression: the same device read as reg-load.
    "expr:volatile": (["hdev", "RegLokal"],
                      "device read in an expression: same oracles as reg-load"),
}


def form_state(form):
    """The guardian state of a form: `lemma`, `assumption` or `uncovered`."""
    if FORMS.get(form, ([], ""))[0]:
        return "lemma"
    if form in NAMED_ASSUMPTIONS:
        return "assumption"
    return "uncovered"

CTYPE = r"(?:const\s+)?(?:uint8_t|uint16_t|uint32_t|uint64_t|int8_t|int16_t|int32_t|int64_t|bool|uintptr_t)"
IDENT = r"[A-Za-z_][A-Za-z0-9_]*"
# A C floating literal as the emitter prints it (`gleitkommatext`: a `.` or an exponent,
# an `f` suffix in `float` computations).
FLIT = r"-?\d+\.\d*(?:e[-+]?\d+)?f?|-?\d+e[-+]?\d+f?"


def float_atoms(text, unit):
    """Float literals, float macros and `double` names in `text`."""
    lits = re.findall(r"(?<![\w.])(?:" + FLIT + r")(?![\w.])", text)
    names = [w for w in re.findall(r"\b(" + IDENT + r")\b", text)
             if w in unit.floats or w in unit.fmacros]
    return lits, names


def classify_float(s, unit):
    """The float form of `s`, or None if `s` is not a float statement."""
    if re.match(r"^if \(!isfinite\(" + IDENT + r"\)\) \{$", s):
        return "stmt:float-narrow-finite"
    m = re.match(r"^if \(!\((" + IDENT + r") >= (\S+) && (" + IDENT + r") <= (\S+)\)\) \{$", s)
    if m and m.group(1) == m.group(3) and m.group(1) in unit.floats \
            and re.fullmatch(FLIT, m.group(2)) and re.fullmatch(FLIT, m.group(4)):
        return "stmt:float-narrow-range"
    m = re.match(r"^double (" + IDENT + r") = (.*);$", s)
    if m:
        rhs = m.group(2)
        if re.fullmatch(FLIT, rhs) or rhs in unit.fmacros:
            return "stmt:float-decl-lit"
        mb = re.fullmatch(r"(" + IDENT + r") ([-+*/]) (" + IDENT + r")", rhs)
        if mb and mb.group(1) in unit.floats and mb.group(3) in unit.floats:
            return "stmt:float-decl-arith"
        mc = re.fullmatch(r"(?:\(double\)\()?(" + IDENT + r")\)?", rhs)
        if mc and mc.group(1) not in unit.floats and mc.group(1) not in unit.fmacros:
            return "stmt:float-decl-conv"
        return "stmt:float"
    if re.search(r"\b(double|float|isfinite)\b", s) or re.search(r"(?<![\w.])\d+\.\d*f\b", s):
        return "stmt:float"
    return None


def strip_comments(src):
    src = re.sub(r"/\*.*?\*/", " ", src, flags=re.S)
    return re.sub(r"//[^\n]*", "", src)


# The head of a C function, definition or prototype: the optional storage class, then the
# return TYPE (group 1), then the name (group 2), then the parameter list (group 3).
FNHEAD = (r"(?:static\s+|extern\s+|_Noreturn\s+)*([A-Za-z_][A-Za-z0-9_ \*]*?)\b(" + IDENT
          + r")\s*\(")


class Body:
    """One emitted function body, with what the classifier needs about its C TYPES."""

    def __init__(self, name, channel, retty):
        self.name = name
        self.channel = channel    # the out-parameter channel (`_grund` in the parameters)
        self.retty = retty        # the C return type, as written
        self.lines = []
        self.aggnames = set()     # names bound here to a WHOLE struct/union (params, locals)


class Unit:
    """What the classifier needs to know about one emitted file."""

    def __init__(self, src):
        self.src = src
        self.defined = set()      # functions with a body
        self.declared = set()     # every prototype
        self.globals = set()      # file-scope objects
        self.floats = set()       # names of `double` parameters and locals (any function)
        self.fmacros = set()      # `#define NAME <float literal>`
        self.enums = set()        # enum constants
        self.aggregates = set()   # `typedef struct`/`typedef union` names (NOT enum)
        self.fnret = {}           # function name -> its C return type, as written
        self.bodies = []          # Body objects
        self._scan_aggregates()
        self._scan()

    def _scan_aggregates(self):
        """The unit's AGGREGATE type names: `typedef struct { ... } T;` and the union form.

        A `typedef enum { ... } T;` is NOT one -- an enum is an integer, which `CTy.int`
        carries; that is the whole reason a tagged union's `marke` field is fine and its
        `last` field is not. The scan counts braces because the emitter nests a union
        inside the tagged-union struct, so no single regular expression spans it.
        """
        depth, kind = 0, None
        for ln in self.src.split("\n"):
            s = ln.strip()
            if depth == 0:
                m = re.match(r"^typedef\s+(struct|union|enum)\b", s)
                if not m:
                    continue
                kind = m.group(1)
                depth = s.count("{") - s.count("}")
                if depth > 0:
                    continue
                # a one-line `typedef struct { ... } T;`
                mm = re.search(r"\}\s*(" + IDENT + r")\s*;", s)
                if mm and kind != "enum":
                    self.aggregates.add(mm.group(1))
                kind = None
                continue
            depth += s.count("{") - s.count("}")
            if depth > 0:
                continue
            depth = 0
            mm = re.match(r"^\}\s*(" + IDENT + r")\s*;", s)
            if mm and kind != "enum":
                self.aggregates.add(mm.group(1))
            kind = None

    def _scan(self):
        for m in re.finditer(r"^#define (" + IDENT + r") (" + FLIT + r")\s*$", self.src, re.M):
            self.fmacros.add(m.group(1))
        for m in re.finditer(r"\bdouble (" + IDENT + r")\s*[=;]", self.src):
            self.floats.add(m.group(1))
        for m in re.finditer(r"^\s*(" + IDENT + r")\s*(?:=\s*-?\d+)?\s*,\s*$", self.src, re.M):
            self.enums.add(m.group(1))
        for m in re.finditer(r"^" + FNHEAD + r"[^;{]*\)\s*(?:__attribute__\S*\s*)*;",
                             self.src, re.M):
            self.declared.add(m.group(2))
            self.fnret[m.group(2)] = m.group(1).strip()
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
                m = re.match(r"^" + FNHEAD + r"(.*)\)\s*(?:__attribute__\S*\s*)*\{$", s)
                if m and not s.startswith("typedef"):
                    ret, name, params = m.group(1).strip(), m.group(2), m.group(3)
                    cur = Body(name, "_grund" in params, ret)
                    for par in params.split(","):
                        pm = re.match(r"^\s*(?:const\s+)?double\s+(" + IDENT + r")\s*$", par)
                        if pm:
                            self.floats.add(pm.group(1))
                        # a PARAMETER of aggregate type: a struct passed by value
                        pa = re.match(r"^\s*(?:const\s+)?(" + IDENT + r")\s+(" + IDENT + r")\s*$",
                                      par)
                        if pa and pa.group(1) in self.aggregates:
                            cur.aggnames.add(pa.group(2))
                    self.defined.add(name)
                    self.fnret[name] = ret
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
                cur.lines.append(s)
                # a LOCAL of aggregate type, collected in the same pass so that a use of
                # the name later in the body knows the value is a whole struct
                for st in split_statements(s):
                    md = re.match(r"^(" + IDENT + r") (" + IDENT + r")\s*(?: = .*)?;$", st)
                    if md and md.group(1) in self.aggregates:
                        cur.aggnames.add(md.group(2))


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


def split_args(text):
    """Split a call's argument list at top-level commas."""
    out, depth, start = [], 0, 0
    for i, ch in enumerate(text):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif ch == "," and depth == 0:
            out.append(text[start:i].strip())
            start = i + 1
    rest = text[start:].strip()
    if rest:
        out.append(rest)
    return out


def aggregate_value(text, unit, body):
    """Does this C expression DENOTE a whole struct/union value?

    A field of one (`x.f`, `p->f`), an element of one and a POINTER to one (`&x`) are all
    scalars in the model's `CVal` and are NOT aggregate values -- only the whole thing is.
    Three shapes produce one: a name bound to a struct, a compound literal, and a call of a
    function whose C return type is a struct.
    """
    if body is None:
        return False
    t = text.strip()
    if re.fullmatch(IDENT, t):
        return t in body.aggnames
    m = re.fullmatch(r"\((" + IDENT + r")\)\{.*\}", t, re.S)
    if m:
        return m.group(1) in unit.aggregates
    m = re.fullmatch(r"(" + IDENT + r")\((.*)\)", t, re.S)
    if m:
        return unit.fnret.get(m.group(1)) in unit.aggregates
    return False


def classify_stmt(s, unit, channel, prev=None, body=None):
    """The statement form of `s`, or None. `prev` is the form of the statement before.

    `body` carries the C types of the enclosing function (return type, aggregate-typed
    names); without it the classifier falls back to the pre-2026-09-15 text-only rows.
    """
    retagg = body is not None and body.retty in unit.aggregates

    def agg(text):
        return aggregate_value(text, unit, body)

    def agg_args(text):
        return any(agg(a) for a in split_args(text))

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
    ff = classify_float(s, unit)
    if ff is not None:
        return ff
    if s == "__builtin_unreachable();":
        return "stmt:unreachable"
    if s == "} else {" or re.match(r"^\} else if \(", s):
        return "stmt:else"
    if s == "} break;":
        return "stmt:case-end"
    if s == "break;":
        return "stmt:break"
    if re.match(r"^case " + IDENT + r": \{$", s):
        return "stmt:case"
    # Lane 227: an integer `match` arm. Numeric labels (`case 3: {`) and the
    # stacked bare labels of an expanded range (`case 3:`) are never a reason
    # or tagged arm -- those spell names, never values (IDENT cannot be digits).
    # `(-9223372036854775807 - 1)` is how `-2^63` is spelled (fix lane F1; the
    # literal `-9223372036854775808` is unsigned in C and `cc -Werror` refuses it).
    if re.match(r"^case (-?\d+u?|\(-9223372036854775807 - 1\)): \{$", s) or \
            re.match(r"^case (-?\d+u?|\(-9223372036854775807 - 1\)):$", s):
        return "stmt:case-int"
    if re.match(r"^switch \(.*\.marke\) \{$", s):
        return "stmt:switch-tag"
    if re.match(r"^switch \(" + IDENT + r"\) \{$", s):
        return "stmt:switch-reason"
    # Lane 227: an integer `switch` over a scrutinee that is not a bare name
    # (`switch (s.len) {`). A bare-name integer switch reads as `switch-reason`
    # here and is reclassified by its first case in main() below; a complex
    # scrutinee never matches that row, so it lands here directly.
    if re.match(r"^switch \(.+\) \{$", s):
        return "stmt:switch-int"
    if s == "for (;;) {":
        return "stmt:forever" if prev == "stmt:watchdog" else "stmt:for-ever-other"
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
    # Opus agent C (2026-09-26): the continuation line of the split CAS call may name an
    # ELEMENT of an atomic array (`&REGEL[_ax1], &_cx1, …`, beispiele/140) -- the same
    # `stmt:cas-loop` row, which was the one unclassified statement on master.
    if re.match(r"^if \(atomic_compare_exchange_(weak|strong)_explicit\(", s) or \
            re.match(r"^&" + IDENT + r"(\[[^\]]*\])?, &_cx\d+", s) or re.match(r"^_ci\d+\+\+;$", s) or \
            re.match(r"^if \(_ci\d+ >= ", s) or re.match(r"^_cn\d+ = .*; goto _cn\d+_fertig;$", s) or \
            re.match(r"^_cn\d+_fertig: ;$", s) or re.match(r"^" + CTYPE + r" _c[xin]\d+ = ", s):
        return "stmt:cas-loop"
    if re.match(r"^" + IDENT + r" = atomic_compare_exchange_(strong|weak)_explicit\($", s):
        return "stmt:cas"
    if re.match(r"^if \(!" + IDENT + r"\(.*&" + IDENT + r", &" + IDENT + r"\)\) \{$", s):
        return "stmt:if-call-else"
    if re.match(r"^if \(.*\) return [^;]*;$", s):
        return "stmt:return-aggregate" if retagg else "stmt:if-return"
    # Lane 259: the commit call in a branch condition is its own row, never
    # the generic `stmt:if` below. Precedent: calls in conditions get their
    # own rows (`stmt:cas-loop`, `stmt:if-call-else`) -- a branch lemma
    # covers the jump, not the callee's effect, and the commit (bumping
    # `committed`, changing page protection) is all effect.
    if re.match(r"^if \(gabbro_arena_grow\(.*\)\) \{$", s):
        return "stmt:grow-call"
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
        # THE RETURN TYPE decides, not the returned text: a function returning a struct by
        # value has no `GRow.ret` (`ret` carries a `CTy`, and `CTy` is `int | ptr`).
        return "stmt:return-aggregate" if retagg else "stmt:return-expr"
    if re.match(r"^goto " + IDENT + r";$", s):
        return "stmt:goto"
    # Lane 260: the region label the gate trap jumps to (`emit.rs`
    # `kind_tor_falle`). Its own row, not `stmt:label`: the traverse/retry
    # lemmas behind that row cover loop exits, never a thread entered by
    # jump -- borrowing them would claim a proof that does not exist.
    if re.match(r"^gabbro_kind_\d+: ;$", s):
        return "stmt:label-kind"
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
    m = re.match(r"^\(void\)(" + IDENT + r")\((.*)\);$", s)
    if m:
        if agg_args(m.group(2)):
            return "stmt:call-aggregate-arg"
        return "stmt:call-unit" if m.group(1) in unit.defined else "stmt:call-foreign"
    if re.match(r"^if \(.*\) __builtin_trap\(\);$", s):
        return "stmt:trap-guard"
    m = re.match(r"^(" + IDENT + r")(?:->|\.)(" + IDENT + r")\(.*\);$", s)
    if m:
        return "stmt:call-indirect"
    m = re.match(r"^(" + IDENT + r")\((.*)\);$", s)
    if m:
        f = m.group(1)
        # AN ARGUMENT'S TYPE decides before the callee does: `GRow.call` evaluates its
        # arguments to `CVal`, which has no aggregate, so a struct passed by value has no
        # row whether the callee is in the unit or foreign.
        if agg_args(m.group(2)):
            return "stmt:call-aggregate-arg"
        if re.search(r"_(nimm|gib)$", f) or re.search(r"_(lese|schreib)_(start|ende)$", f):
            return "stmt:call-lock"
        return "stmt:call-unit" if f in unit.defined else "stmt:call-foreign"
    m = re.match(r"^(?:const\s+)?" + IDENT + r" \* " + IDENT + r" = .*;$", s)
    if m:
        return "stmt:decl-ptr"
    m = re.match(r"^(" + CTYPE + r"|" + IDENT + r") (" + IDENT + r")( = (.*))?;$", s)
    if m:
        init = m.group(4)
        # THE DECLARED TYPE decides: `GRow.bindLet x tc ce` carries a `CTy`, so a local of
        # struct type has no row -- whatever the initialiser looks like.
        declagg = m.group(1) in unit.aggregates
        if init is None:
            return "stmt:decl-cell"
        if re.match(r"^\(" + IDENT + r"\)\{", init):
            return "stmt:struct-init"
        if re.match(r"^atomic_load_explicit\(", init):
            return "stmt:awaits"
        if re.match(r"^\(\*\(volatile ", init) or re.match(r"^\(+\*\(volatile ", init):
            return "stmt:reg-load"
        if declagg:
            return "stmt:bind-aggregate"
        if ".last." in init:
            return "stmt:decl-union-payload"
        mc = re.match(r"^(" + IDENT + r")\((.*)\)$", init)
        if mc and mc.group(1) not in ("sizeof",):
            if agg_args(mc.group(2)):
                return "stmt:call-aggregate-arg"
            return "stmt:bind-call-unit" if mc.group(1) in unit.defined else "stmt:bind-call-foreign"
        return "stmt:decl-init"
    if re.match(r"^" + IDENT + r"(\[[^\]]*\]|\.buf\[)", s) and "=" in s:
        return "stmt:store-array"
    # Lane 259: the dynamic-arena store through the reserved base. Same bucket
    # as its static twin above: no lemma covers either, so no new claim --
    # the shape joins the recorded uncovered row instead of standing beside it.
    if re.match(r"^\(\([A-Za-z0-9_]+ \*\)" + IDENT + r"\.base\)\[[^\]]*\] =", s):
        return "stmt:store-array"
    if re.match(r"^" + IDENT + r"->" + IDENT + r"\[[^\]]*\] = ", s) and "->slots[" not in s:
        return "stmt:store-array"
    if re.match(r"^" + IDENT + r"\.buf\[", s):
        return "stmt:store-array"
    # THE STORED VALUE'S TYPE decides: a slot field that takes a WHOLE struct is not the
    # scalar slot store `scorr_assignSlotParam`/`scorr_assignSlotNamed` speaks about --
    # the memory of `CSpeicher.lean` holds `CVal`, which has no aggregate.
    m = re.match(r"^" + IDENT + r"(?:->|\.)slots\[[^\]]*\]\.[A-Za-z0-9_.]+ = (.*);$", s)
    if m and agg(m.group(1)):
        return "stmt:store-aggregate"
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
        if agg(m.group(2)):
            return "stmt:store-aggregate"
        return "stmt:assign-global" if m.group(1) in unit.globals else "stmt:assign-local"
    m = re.match(r"^" + IDENT + r"(?:->|\.)[A-Za-z0-9_.]+ = (.*);$", s)
    if m and agg(m.group(1)):
        return "stmt:store-aggregate"
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
           "return", "while", "isfinite"}


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
                "stmt:bind-call-foreign", "stmt:call-indirect", "stmt:publish", "stmt:cas",
                # the aggregate rows are the same statement-level calls under another row:
                # without them the call would be counted a second time as `expr:call`, and
                # the repair would look as if it had found expressions it did not find
                "stmt:call-aggregate-arg", "stmt:bind-aggregate"):
        # `(void)f(a);` is the same call with its answer discarded (C11 6.3.2.2): the cast
        # is not the argument list. Found 2026-09-15: without this the `(void)` parenthesis
        # was read as the arguments and `f(` itself as a call INSIDE an expression, which
        # put `beispiele/104`'s `(void)lies(k, i);` into state (iii) (`expr:call`).
        m = re.search(r"\((.*)\)", re.sub(r"^\(void\)", "", text))
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
    # floats: a comparison with a float operand, and a float literal / float macro that
    # stands inline (the narrow check and `double c = LIT;` carry theirs in their own row)
    lits, fnames = float_atoms(text, unit)
    if lits or fnames:
        atom = r"(?:" + IDENT + r"|" + FLIT + r")"
        for m in re.finditer(r"(" + atom + r") (<=|>=|<|>) (" + atom + r")", text):
            if any(re.fullmatch(FLIT, g) or g in unit.floats or g in unit.fmacros
                   for g in (m.group(1), m.group(3))):
                found.append("expr:float-cmp")
                break
        if form not in ("stmt:float-narrow-range", "stmt:float-decl-lit", "stmt:float") and \
                (lits or any(n in unit.fmacros for n in fnames)):
            found.append("expr:float-lit-inline")
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


def assumption_exists(name, sources):
    """Does the named assumption occur in the Lean sources -- as a `theorem`/`def`/
    `lemma`/`abbrev` at line start, or as a premise binder `name :`?

    The binder half is what the assumption rows need: `hdev` is a premise of
    `regLies_step`, not a declaration of its own. Requiring only the declaration form
    would make every binder row permanently red -- a guard that cries wolf about its own
    table instead of about the tree.
    """
    if lemma_exists(name, sources):
        return True
    return re.search(r"[(|{]\s*" + re.escape(name) + r"\s*:", sources) is not None


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
        try:
            r = subprocess.run([str(binary), "emit", str(f)], capture_output=True,
                               text=True, cwd=W, timeout=FRIST)
        except (OSError, subprocess.TimeoutExpired):
            refused += 1
            continue
        if r.returncode != 0 or not r.stdout.strip():
            refused += 1
            continue
        emitted += 1
        src = strip_comments(r.stdout)
        unit = Unit(src)
        for body in unit.bodies:
            cells = set()
            prev = None
            trail = []
            for ln in body.lines:
                for s in split_statements(ln):
                    form = classify_stmt(s, unit, body.channel, prev, body)
                    prev = form
                    trail.append((form, s))
            # Lane 227: an integer `switch` over a bare name shares its header
            # text with a reason `switch` (`switch (x) {`) -- the cases tell
            # them apart. A header whose immediately following case is numeric
            # is an integer switch, not a reason one. Both lowerings place the
            # first case directly under the header, so anything else in between
            # keeps the provisional row (conservative: a merged header is a
            # wrong lemma claim, an unmerged one is at most an extra row).
            for i, (form, s) in enumerate(trail):
                if form == "stmt:switch-reason" and i + 1 < len(trail):
                    if trail[i + 1][0] == "stmt:case-int":
                        trail[i] = ("stmt:switch-int", s)
            for (form, s) in trail:
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
    missing_assumptions = []
    for form, (names, _) in NAMED_ASSUMPTIONS.items():
        for nm in names:
            if not assumption_exists(nm, sources):
                missing_assumptions.append((form, nm))

    print(f"pruefe-cformen: {emitted} programs emitted, {refused} refused by the emitter, "
          f"binary {binary}")
    lemmas = [(f, n) for f, n in counts.items() if form_state(f) == "lemma"]
    assumed = [(f, n) for f, n in counts.items() if form_state(f) == "assumption"]
    uncovered = [(f, n) for f, n in counts.items() if form_state(f) == "uncovered"]
    tot_lem = sum(n for _, n in lemmas)
    tot_asm = sum(n for _, n in assumed)
    tot_unc = sum(n for _, n in uncovered)
    print(f"  forms seen: {len(counts)} ({len(lemmas)} lemma, {len(assumed)} named assumption, "
          f"{len(uncovered)} without semantics); occurrences: {tot_lem} lemma, {tot_asm} "
          f"named assumption, {tot_unc} without semantics, "
          f"{sum(unclassified.values())} unclassified statements")
    if args.forms:
        print("\n  LEMMA FORMS (occurrences / programs / lemma)")
        for f, n in sorted(lemmas, key=lambda x: -x[1]):
            print(f"    {n:6d} {len(programs[f]):4d}  {f:28s} {', '.join(FORMS[f][0])}")
    print("\n  NAMED-ASSUMPTION FORMS (occurrences / programs / Lean premise)")
    for f, n in sorted(assumed, key=lambda x: -x[1]):
        names, _note = NAMED_ASSUMPTIONS[f]
        print(f"    {n:6d} {len(programs[f]):4d}  {f:28s} {', '.join(names)}")
        for e in examples[f][:args.examples]:
            print(f"                 e.g. {e}")
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
    if missing_assumptions:
        print("\n  NAMED ASSUMPTIONS THAT DO NOT EXIST in grammatik/Grammatik/*.lean:")
        for form, nm in missing_assumptions:
            print(f"    {form}: {nm}")
    stale = [f for f in KNOWN_UNCOVERED if counts.get(f, 0) == 0]
    if stale:
        print("\n  KNOWN_UNCOVERED entries not seen in this run (may be removed): "
              + ", ".join(stale))
    bad = bool(missing or missing_assumptions or new_uncovered or unclassified)
    print("\n" + ("RED" if bad else "GREEN") + f": {len(new_uncovered)} new uncovered form(s), "
          f"{sum(unclassified.values())} unclassified statement(s), {len(missing)} missing "
          f"lemma(s), {len(missing_assumptions)} missing assumption(s)."
          + (" " + stale_note.strip() if stale_note else ""))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
