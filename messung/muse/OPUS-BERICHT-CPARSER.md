# A2 — a Lean parser for the emitted C subset

*Opus agent, 2026-09-15, branch `opus/cparser` off `cf9cb77c`. Task: replace assumption A2
("the emitted TEXT means `kProg zert`" — a hand transcription) by a Lean parser and a
kernel-checked pin, for the programs the chain covers. Everything below is measured on
`ki-pc-fisch-101` (110 GB, 16 cores, Lean 4.33.1) with a binary built from this tree, with
other agents' lanes running beside it.*

---

## 0. The verdict in one paragraph

`parseC : List Char → Option (List CFun)` reads the emitted C subset in Lean, and for the
two closed chains

```
a2_104 : parseC ctext104 = some (kFuns zert104)      -- `rfl`, kernel:  11 s, 2,7 GB
a2_108 : parseC ctext108 = some (kFuns zert108)      -- `rfl`, kernel:  17 s, 3,0 GB
```

hold, with `ctext104`/`ctext108` pinned line by line and byte-identical to `gabbro emit`
(a new guardian re-emits and compares: **2 of 2 pins, 2733 bytes**). From them follows
`cProgC ctext = kProg zert`, and `schlusssatz_text` — the closing theorem with its A1
premise stated about the C unit of the TEXT. **A2 is no longer an assumption of these two
chains.** What remains is *"the C compiler's front end reads this subset as `parseC` does"*,
which is part of A1.

Standards: no `sorry`, no `native_decide`, no new `axiom`; every new theorem prints the
standard three axioms (two print fewer); every theorem with a ∀-over-syntax premise has a
witness; `lake build` of the whole library: **247 jobs, green, peak 2,9 GB**.

---

## 1. The subset, measured first

### 1.1 What the two chain programs emit

`gabbro emit beispiele/104-referenz.gab` is 1419 bytes / 45 lines,
`beispiele/108-disjoint-start-locks.gab` 1314 bytes / 40 lines. Every construct in them:

| # | Top-level construct | 104 | 108 | `parseC` |
|---|---|---|---|---|
| 1 | `/* … */` block comment (licence header, prelude note) | 2 | 3 | skipped |
| 2 | `#include <stdint.h\|stdbool.h\|stdatomic.h\|math.h>` | 4 | 4 | checked, skipped |
| 3 | `_Static_assert((-1 >> 1) == -1, "…");` | 1 | 1 | **required** |
| 4 | `_Static_assert((int)0xFFFFFFFFu == -1, "…");` | 1 | 1 | **required** |
| 5 | `#define NAME <integer>` | 1 | 1 | value recorded |
| 6 | `#define NAME (<integer or macro>)` | 1 | 1 | value recorded |
| 7 | `typedef struct { <scalar fields> } T_slot;` | 1 | 1 | the record's fields |
| 8 | `typedef struct { T_slot slots[N]; } T;` | 1 | 1 | table + `natLay` geometry |
| 9 | `static T T_speicher;` | — | 1 | the table block object |
| 10 | `void f(void);` (foreign: the lock primitive) | 2 | — | noted, never callable |
| 11 | `static <ret> f(<params>) __attribute__((word))…;` | 2 | 2 | function number |
| 12 | `static <ret> f(<params>) <attrs> { <body> }` | 2 | 2 | the body |

| # | Statement / expression (census name) | 104 | 108 | `parseC` node |
|---|---|---|---|---|
| 13 | `(void)x;` — `stmt:void-expr` | 1 | — | `.expr (.var k)` |
| 14 | `p->slots[i].f = e;` — `stmt:store-slot-ptr` | 1 | — | `.store (.slotA (.var kp) …)` |
| 15 | `(void)f(a, b);` — `stmt:call-unit` | 1 | — | `.call n args none` |
| 16 | `return e;` — `stmt:return-expr` | 1 | 2 | `.ret (some (τ, e))` |
| 17 | `p->slots[i].f` — `expr:slot-read` (pointer) | 1 | — | `.ld (.slotA (.var kp) …) τ` |
| 18 | `T_speicher.slots[k].f` — `expr:slot-read` (named) | — | 2 | `.ld (.slotA (.addr (.tab t)) …) τ` |
| 19 | integer literal `100` — `czahl` | 1 | — | `.lit` |
| 20 | a parameter read (`i`, `k`) | 4 | — | `.var` |

Nothing else occurs in these two files. Types: `void`, `uint32_t`, `Konto */T *` with
`restrict` and `const`. Parameter forms: `(void)`, `T *restrict x`, `const T *restrict x`,
`uint32_t x`.

### 1.2 What the corpus emits, and how much of it that is

113 of 113 tracked programs emit (0 refusals), **8512 lines** of C. Top-level constructs over
all of them, counted at brace depth 0 (`/* */` header excluded from the classification):

| occurrences | programs | top-level form | in the subset |
|---|---|---|---|
| 453 | 113 | `#include <…>` | the four known headers |
| 329 | 109 | `static … f(…) {` — a function definition | yes, for the parameter forms above |
| 300 | 105 | `static … f(…);` — a declaration | yes |
| 228 | 113 | `_Static_assert(…)` | only the two pins |
| 182 | 58 | a non-`static` declaration (`void K_nimm(void);`, `bool f(uint64_t*, …);`) | only `void f(void);` |
| 170 | 73 | `typedef struct {` | only the two table shapes |
| 146 | 6 | `static inline … { … }` one-line byte helper | no |
| 129 | 72 | `#define NAME <int>` | yes |
| 71 | 38 | `static … x … = …;` (initialised global) | no |
| 52 | 37 | `#define NAME (…)` | only integer/macro |
| 29 | 22 | `static T T_speicher;` | yes |
| 28 | 20 | one-line `typedef struct { … } T;` (device handle, byte view) | no |
| 26 | 20 | `typedef enum {` | no |
| 19 | 11 | a global declaration (`_Atomic bool G;`) | no |
| 9 | 7 | a non-`static` definition | no |
| 5 | 2 | `static _Atomic T a[N];` | no |
| 3 | 3 | forms no rule of this census matched (function-pointer parameters, a multi-line `_Static_assert`) | no |

Inside function bodies the census `instrumente/pruefe-cformen.py` is the register: **77 forms
seen, 51 with a correspondence lemma, 4 named assumptions, 22 without semantics; 1905 / 187 /
400 occurrences.** The five biggest are `stmt:return-expr` (287 in 90 programs),
`expr:slot-read` (182/51), `stmt:if` (122/40), `stmt:call-lock` (92/21), `expr:cell-read`
(88/17). `parseC` reads four of the 77 (`stmt:return-expr`, `stmt:return-void`,
`stmt:store-slot-ptr`/`-named`, `stmt:void-expr`, `stmt:call-unit`, `expr:slot-read`) and
refuses the rest.

### 1.3 How far the parser reaches, measured over the corpus

`parseC` run (compiled, `#eval`) over the emitted C of all 113 programs:

> **4 of 113 are inside the subset**: `104-referenz`, `108-disjoint-start-locks`,
> `118-sperrinvariante-erhaltung` (TWO table types, two pointer parameters, four stores)
> and `52-baugatter` (a store of a parameter's value). The two chain programs are among
> them. Read out of the parser (`#eval`), 118 gives two functions of two pointer parameters
> with the geometry `2 4 0` at each store — the second table type is registered and numbered
> even though its rows reach it through a parameter.

That is the honest size of the subset, and it is not the bottleneck: sieve (a) — the Lean
Gabbro parser and elaborator — stops 109 of 111 tracked programs before the C side is ever
reached (PLAN §6.3). **A wider C parser buys no chain today**; what a wider chain will need
is in §5.

**THE CHAIN COUNT DOES NOT MOVE, and must not**: it stays at **2** (104, 108). A2 is not one
of `zaehle-kette.py`'s five sieves — the counter asks for a Lean-checked instance of
`schlusssatz`, and both programs had one before this lane. What changed is what that
instance ASSUMES, not how many there are. *A lane that discharges an assumption and reports
a bigger headline number would be reporting the wrong thing.*

---

## 2. What is proved

| theorem | file | content |
|---|---|---|
| `lexC_total`, `parseC_total` | `CParser/CLexer.lean`, `CParse.lean` | the lexer and the parser are TOTAL functions — every text has an outcome, and a text outside the subset has the outcome `none` |
| 14 lexer probes | `CLexer.lean` | one per lexer decision, including four refusals (`0b101`, `2ux`, an unterminated comment, a character outside the subset) |
| 7 parser refusals | `CParser/CProben.lean` | `if`, arithmetic, `let`, a volatile access, a missing prelude pin, a declared-but-undefined function, and the smallest accepted unit |
| `kProg_kFuns`, `a2_kProg` | `CParser/Bruecke.lean` | the certificate's unit as a list, and `A2 s c → cProgC s = kProg c` |
| `a2_hA1`, **`schlusssatz_text`** | `CParser/Bruecke.lean` | the closing theorem with its A1 premise stated about the TEXT — the conclusion written out, so a change to `schlusssatz` breaks the build |
| **`a2_104`**, `cprog_104` | `CText104.lean` | A2 for 104, by kernel reduction |
| **`a2_108`**, `cprog_108` | `CText108.lean` | A2 for 108 |
| `kette_104_binaer_text`, `kette_108_binaer_text` | `Kette104Satz.lean`, `CText108.lean` | part 6 of the closing theorem (every run of the binary) with the C unit read from the text |
| `kette_104_zeuge_text`, `kette_108_zeuge_text` | same | the witnesses of §6.3 again, through the text: the slot `0 -> 100` in Gabbro and in EVERY C run; `read_a()` returns `42` both ways |
| `a2_104_gegenprobe_*`, `a2_108_gegenprobe*` | `CText104Zeuge.lean`, `CText108.lean` | the negative witnesses, §3 |

**What the pin checks that a transcription cannot.** The table geometry `2 4 0` (two slots, a
4-byte record, the field at offset 0) is COMPUTED by `natLay` from `#define NKONTO 2u` and the
two `typedef struct`s; the C function numbers come from the order of the `static`
declarations; the C locals come from the parameter lists; 108's table block number comes from
the order of the table typedefs. All four are things the certificate ASSERTS and the text
now has to agree with.

### 2.1 Negative witnesses — one line changed

| text | answer | and then |
|---|---|---|
| 104, store value `100` → `99` | a DIFFERENT program (`zert104_wert`) | `korrOk … = false` |
| 104, `#define NKONTO 2u` → `3u` | a DIFFERENT program (`3 4 0`) | `korrOk … = false` |
| 104, second `_Static_assert` deleted | `none` | — |
| 104, `stand` → `fehlt` at the read | `none` | — |
| 108, `slots[0]` → `slots[2]` in `read_a` | a DIFFERENT program | `korrOk … = false` |
| 108, `T_slot slots[4]` → `[5]` | a DIFFERENT program | `korrOk … = false` |
| 108, `static T T_speicher;` deleted | `none` | — |

Plus the seven refusals of `CProben.lean` on short texts: a parser that accepted anything
could not pass these.

### 2.2 The guardian

`instrumente/pruefe-ctext.py` reads every `CTEXT-PIN <program> <name>` marker, decodes the
Lean literals of the `CTEXT-BEGIN`/`END` block, re-emits with the built binary
(`LC_ALL=C`, deadline 120 s) and compares byte for byte. Speech test in both directions
(a planted block reads as its bytes; the same block with ONE byte changed does not; an
unknown escape is refused, not guessed; a missing block is no text). Exits 0 / 1 / 2 with
the work count beside the verdict. Green: `2 of 2 pins byte-identical, 2733 bytes compared`.
`pruefe-waechter.py` reports it `ok` (no missing requirement) and its tool count moves
84 → 85.

---

## 3. The cost — the finding this lane did not expect

The first version of the pin, written the obvious way (`parseC : String → …`, the text one
string literal), needed **44,6 GB and 364 s just to LEX**, and the full file was OOM-killed at
43,6 GB. Cutting it apart:

| what the kernel was asked to reduce | wall clock | peak resident |
|---|---|---|
| `lexC` over the 1419-byte text as ONE `String` literal | 364 s | **44,6 GB** |
| `(String.toList s).length = 1419`, same literal | 235 s | **38,2 GB** (OOM) |
| `(String.toList s).isEmpty = false` — the FIRST character only | 217 s | **33,7 GB** |
| the same text as 45 short `String` literals joined by `++` | 449 s | 34,6 GB |
| the same text as a `List Char` of 45 short `"…".toList` pieces, lexed AND counted | 20 s | **3,3 GB** |
| `a2_104` (the whole parse, against the certificate) | 11 s | **2,7 GB** |
| `a2_108` | 17 s | 3,0 GB |
| `CText104Zeuge.lean` (4 further parses + 2 `korrOk` decides) | 19 s | 3,2 GB |
| `korrOk … = false` by `decide`, alone | 1,8 s | 0,7 GB |
| the whole `Grammatik` library, incremental | 30 s | 2,9 GB |

**Forcing ONE character of a long string literal costs 33,7 GB.** In Lean 4.33 a `String` is an
array underneath — `String.toList s = (String.Internal.toArray s).toList`, and
`String.length s = s.toList.length` — so `lex s = scan s.toList (s.length + 1)`, the shape of
`Parser/Lexer.lean` and of every `src…real` pin, pays that conversion twice over. Splitting
the literal at the `String` level does not help: `String.append` goes through the array too.
What helps is pinning the text as a `List Char` of short `"…".toList` pieces and letting the
lexer take `List Char`. Factor 13 in memory, 18 in time, same theorem.

**This is very probably what O13's 72 GB is**, and `dokumente/OFFEN.md` O13 now carries the
table with the cheapest next experiment named: give `lex` a `List Char`, pin `src104real` as
its lines, re-measure. Nobody has done it — the claim here is about the C side, where it is
measured.

**A second pathology, found by a runaway probe.** A MUTUAL recursion through a fuel argument
compiles to a mutual `Nat.brecOn`, and reducing that in the kernel is EXPONENTIAL in the
fuel. With the fuel taken from the token count (~70), the seven-token probe
`return x + 1;` had reached **112 GB** when it was killed; the machine's other Lean jobs went
with it. The same parser with the expression functions made NON-recursive (the subset nests
one level) costs 0,9 GB for the same probe. *Fuel that comes from a token count must never
reach a mutual recursion* — both files say so at the definition.

---

## 3a. Guardians, before and after

`abnahme.py --schnell` was run twice on `ki-pc-fisch-101`, in a tree at `cf9cb77c` and in
this one, with the same binary and the same Lean cache. **The two outputs differ in exactly
one line**, and that line is a number my change moved:

| guardian | base | this branch | booked |
|---|---|---|---|
| `pruefe-todo.py` | 13 findings | 14 — `README: '41' als Waechter -- es sind 42` | README §Guardians `41 → 42`, with the reason; back to **13**, output byte-identical to the base |
| `pruefe-ctext.py` (new) | — | **green**: 2 of 2 pins byte-identical, 2733 bytes | — |
| `pruefe-waechter.py` | the new instrument would be flagged if it lacked a requirement | `ok` for `pruefe-ctext.py`; tool count 84 → 85, static requirements 67/70 → 68/71 | — |
| `pruefe-cformen.py` | GREEN | GREEN (unchanged: `emit.rs` is untouched) | — |
| `pruefe-zahlen.py` | 27 findings | **23** | four stale figures re-measured and booked: README `65 of 68 → 68 of 71`, RUECKLAUFWERTE `61 von 66 → 65 von 71` and `376 → 409`. **Three of those four instruments came from lanes BEFORE this one** and stood unbooked — the note says so; a figure that books only its own share stays wrong and looks booked |
| every other guardian | — | identical, including the pre-existing reds | — |

`zaehle-kette.py` without `--lean` reports 0 (unmeasured counts as not passed) in both trees;
the chain count of record stays 2 (§1.3).

---

## 4. What A1, A2, A3 still assume

| | before | after |
|---|---|---|
| **A1** | every run of the compiled binary of `f` is a run of the C semantics of `kProg zert` at the emitter's layout and the call depth its call tree needs | unchanged in substance, but it is now about the C unit of the EMITTED TEXT (`cProgC ctext104`) — and it therefore CONTAINS the old A2 as "the compiler's front end reads this text as `parseC` does" |
| **A2** | *the emitted TEXT means `kProg zert`* — a hand transcription, checked by nobody | **discharged for `beispiele/104` and `beispiele/108`**: `parseC ctext = some (kFuns zert)`, by kernel reduction, over a text a guardian re-emits. NOT discharged for `beispiele/124` (stage (b), §7.6 item 6) and not for any program outside the subset |
| **A3** | the `_Static_assert` pins hold and the C semantics reads a `RecLay` only through the pinned numbers | unchanged. The parser now REQUIRES both pins to be present in the text (a text without them is `none`), so A3's premise is checked to be *stated*; that the compiler accepts them is still A1's business. The missing lemma (the C semantics reads a `RecLay` only through the pinned numbers) is untouched |
| **A4** | the real runtime starts in a `LaufzeitStart`/`EinFadenStart` shape | untouched |
| **A5** | the Lean kernel, and the definitions PLAN §3 lists for human review | untouched, plus the two new definitions this lane adds to that list: **`parseC` and `lexC` — that they read the C subset as a C compiler reads it is exactly what a reviewer must judge** |

**The honest shape of the new trusted piece.** `parseC` is a DEFINITION, not a theorem. It
says how the emitted C text is to be read. If it read `k->slots[i].stand` as slot `i+1`, the
pin would still hold and the chain would be wrong. Two things bound that risk and neither
removes it: the negative witnesses (§2.1) show the parser distinguishing texts that differ
by one token, and the geometry is computed from the declarations rather than asserted.
**A third would remove much more of it and does not exist: a printer with
`parseC (printC p) = some p`, proved by induction** — then a reviewer would read the printer
next to `emit.rs` instead of the parser next to C11.

---

## 5. What a wider chain needs, named

1. **Arithmetic** (`expr:cast` 71/29, the `bin`/`cmp` forms). `CX.bin` carries a C computation
   type; C only implies it through the usual arithmetic conversions. The parser must infer it
   — it refuses instead. This is the single biggest missing piece of the C side.
2. **`if` (122/40) and the loops** (`stmt:for-counting` 17/11, `stmt:forever` 11/7): one arm
   each, and the loop marks (`m_weiter`, `m_ende`) must become labels the parser reads.
3. **Locals that are not parameters** (`stmt:decl-init` 84/26, `stmt:decl-cell` 68/17): a C
   local number for them. The certificate's `vm` says which Gabbro variable lives where; the
   parser would have to agree with the exporter's rule, and that rule is pinned nowhere today.
   This is the one place where widening needs a DECISION, not just work.
4. **The lock primitive** (`stmt:call-lock` 92/21) as `CS.ext`, and with it the foreign-call
   numbering.
5. **Globals, arrays, unions, atomics, volatile registers, `switch`, `goto`, asm**: each is a
   named form in the census, each is a refusal today.
6. **Stage (b)**: 124's text is a `CEinheit` of the concurrent semantics, not a `KCert`; a
   `parseC`-to-`CEinheit` bridge is missing on top of the forms above.
7. **The prelude is pinned exactly.** Two `_Static_assert` spellings and four headers are
   hard-wired. A unit that needs `<float.h>` (26-gleitkomma) is refused for that reason alone.

---

## 6. Files

New: `grammatik/Grammatik/CParser/{CLexer,CParse,CProben,Bruecke}.lean`,
`grammatik/Grammatik/{CText104,CText104Zeuge,CText108}.lean`, `instrumente/pruefe-ctext.py`,
this report. Changed: `grammatik/Grammatik.lean` (imports), `grammatik/Grammatik/Kette104Satz.lean`
(the two text theorems), `dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md` (§5, §6.4, §6.5, new
§6.6, §7.6 item 6), `dokumente/SATZKARTE.md` (§28), `dokumente/OFFEN.md` (O13), `README.md`
and `messung/RUECKLAUFWERTE.md` (the four booked figures of §3a).
Untouched, on purpose: `KorrespondenzAllg.lean`, `Parser/`, `emit.rs`, `pruefe-emission.sh`,
the MARKE counters.
