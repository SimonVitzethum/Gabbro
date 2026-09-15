# Grammar into the emitter -- the expression/statement/type/device half

**Lane: Opus, stage (b). 2026-09-15.** Branch `worktree-agent-ab47a16ebeff99280`, base
`1434efba`. Every number below was measured on `ki-pc-fisch-101` (`cargo`, `pruefe-emission.sh`)
or locally with an already-built binary (single `gabbro` runs, `cc` on one file), as `CLAUDE.md`
splits the load.

---

## 0. What the lane was asked, and what it turned out to be about

The assignment began at `./instrumente/miss-grammatikdeckung.py` with 37 named forms and was
re-aimed mid-lane at the **Lean specification of the syntax** -- `grammatik/Grammatik/Syntax.lean`
and its `Ty`, `Expr`, `Stmt`, `Block`, `Endblock`, `Regklasse` -- as the authority, with the
327-form census demoted to a secondary check.

That re-aiming is the reason this lane found what it found. **The five defects below were all
found the same way: by walking the constructors of `Syntax.lean` one by one and COMPILING what
came out of the emitter.** Three of them were zero checker errors, `gabbro emit` returning 0,
and `cc -std=c11 -Wall -Wextra -Werror` refusing at BOTH -O0 and -O2 -- forms that pass every
gate this tree has and produce C that does not build. *None of them is visible to a census that
asks whether the C DIFFERS; all of them are visible to one that asks whether the C COMPILES.*

---

## 1. The five things the lane changed

| # | form (Lean constructor) | before | after | commit |
|---|---|---|---|---|
| 1 | `Ty.ptr` at `mmio`/`dma` | C byte-identical to `normal` | `volatile` on the C pointer type | `3db9cbb7` |
| 2 | `Stmt.retGrund` | `-Werror=unused-parameter` on `_wert` | `(void)_wert;` beside the existing `(void)_grund;` | `89fa78a6` |
| 3 | `Expr.leseBytes` via `->` | `'F' has no member named 'a'` | the generated reader, as for `.` | `89fa78a6` |
| 4 | a place over a `table`, first suffix not `slots` | `'T' has no member named 'wert'` | named refusal with the repair | `89fa78a6` |
| 5 | `own@m` (no Lean constructor) | parsed, read by nobody, silent | named refusal with the repair | this lane |

### 1.1 `mmio` and `dma` lower to `volatile` -- because `R008` already said so

`R008` in `m3.rs` prints, of itself:

> *"the address space is part of what a pointer IS -- `mmio` is volatile and device-mapped,
> `normal` is not, **and the emitter lowers them differently**"*

**And it did not.** `messung/ADRESSRAEUME.md` measured on 2026-08-31 that six programs differing
in nothing but the space word emit six byte-identical C files, and concluded `ctyp` reads
`z.raum` for *no* space. *A refusal that names a lowering the generator does not write is the
worse half of `W16`: the sentence reads like a measurement.*

`emit::raumqualifizierer` is now the one home, with the reason per space: `mmio` and `dma` earn
`volatile` (a load IS the device access; folding two reads into one, hoisting one out of a loop
or deleting a store are three different programs at the device, and none of them is a
diagnostic), `normal`/`boot`/`code`/`port`/a named space earn nothing, each for a written reason.

**Two targets keep the qualifier off, and the rule is one sentence: it goes where the emitter
writes the access itself.** A `device` handle and a `format` handle are dereferenced by a
GENERATED ACCESSOR, never by the caller, and the accessor is generated once per declaration
rather than once per space. `beispiele/gift/416` writes the device half down word for word:
*"the space at the POINTER does not decide the access form -- the `device` declaration does"*.
Measured without the exception: `-Werror=discarded-qualifiers` at every generated setter call
in `messung/treiber/virtio-net.gab` and `messung/proben/probe-netz-rahmen-und-ergebnis.gab`.

**What stays open and is named in the code rather than papered over:** a `format` in `dma` is a
byte view of memory a device writes, and its accessor does not qualify its own loads and stores.

Re-measured the way `ADRESSRAEUME.md` §2 measured it: the six programs now give **two distinct C
files plus one named refusal**, where §2 found one file six times. That document keeps its 2026-08-31
measurement word for word -- it was right, and its finding (*"`mmio` arrives only because every
clean `ptr<mmio, …>` in the corpus points at a `device` type"*) is what made the repair land where
it did -- and gains a dated block saying which half no longer holds.

### 1.2--1.4 Three forms the checker passes and `cc` does not

```text
fn f() -> u32 or R ... { return R::Leer; }
  -> static bool f(uint32_t *_wert, R *_grund) { *_grund = R_Leer; return false; }
  cc: error: unused parameter '_wert' [-Werror=unused-parameter]

impl fn f(m : ptr<normal, r> F) ... { return m->a; }      -- F is a `format`
  -> return m->a;   into   typedef struct { uint8_t *bytes; uint32_t len; } F;
  cc: error: 'F' has no member named 'a'

impl fn f(q : ptr<normal, r> T, ...) ... { return q->wert; }   -- T is a `table`
  -> return q->wert;   into   typedef struct { T_slot slots[4]; } T;
  cc: error: 'T' has no member named 'wert'
```

The first two are now lowered; the third is a named refusal that prints the repair
(`q.slots[i].wert`). `rumpf_gibt_wert` is the MIRROR of `rumpf_scheitert` and not its negation:
a body may write both channels or neither, and the two are independent questions.

The table refusal is **coarse in the safe direction (`W9`)**: it asks only whether the first
suffix is `slots`, the one member a table handle has. *The exact question -- is this a declared
slot field? -- belongs to the checker, and that the checker gives no answer to `q->wert` is a
second finding, entered in §5 rather than papered over in the generator.*

### 1.5 `own@m` -- a form the grammar admits and no side of the compiler answers for

`parse::right` reads `own [ "@" ident ]` and builds `Recht::Eigen(Some(marke))`. **That line is
the last one in the repository that looks inside the `Some`**: `grep -rn "Eigen(Some" crates/`
names `parse.rs:1418` and nothing else. Every other reader -- `m3.rs` twice, `alias.rs`,
`lean_g.rs` twice, `emit.rs` -- matches `Recht::Eigen(_)` and drops the mark.

* `ptr<normal, own@m> u32` and `ptr<normal, own> u32` emit the same C to the byte,
* they book the same obligations (none), and no pass refuses either,
* **`Ty.ptr` in `Syntax.lean` carries `(t : Nat)` and `(rw : Bool)` and no mark**, and
* the corpus asks for it **zero** times (`grep -rn "own@" --include=*.gab` is empty).

Refused by name, not built: the mark would mean a linearity statement the checker would have to
hold at every call site, and Rule A does not build a construct without a measured need. The
refusal prints the repair (`own`, plus `effects { consumes m }`). It holds at the SIGNATURE like
the `ptr<port, …>` refusal beside it, and for the same reason (`W10`).

---

## 2. The constructor census -- `Syntax.lean` against `emit.rs`, `parse.rs` and `gbodyOk`

The three questions, per constructor: does the emitter produce C for it and does that C compile;
does the Rust parser admit a form Lean has no constructor for; does a Lean constructor exist that
the emitter never produces. Measured with small programs through `gabbro pruefe` / `emit` and
`cc -std=c11 -Wall -Wextra -Werror` at -O0 and -O2.

**The correspondence predicate is `gbodyOk` in `grammatik/Grammatik/Korrespondenz.lean`** (the
coordinator's `korrOk` in `KorrespondenzAllg.lean` does not exist under those names in this tree
-- `grep -rn "korrOk\|KorrespondenzAllg"` over the whole repository is empty). Its row family is
`GRow`: `void`, `storeSlot`, `storeNamed`, `storeGlob`, `setVar`, `setOp`, `bindLet`, `ite`,
`call`, `ret`, `forTrav`; its expression gate is `exprOk`.

### 2.1 `Expr` -- 42 constructors

CARRIES with compiling C: `lit`, `wahr`, `falsch`, `var`, `glob` (plain and
`atomic_load_explicit`), `slot`, `durch`, `fnref` (in a record field), `weiter` (no cast: the
inner text stands verbatim), `add`, `sub`, `mul`, `div`, `rem`, `sdiv`, `srem`, `leseBytes`,
`band`, `bor`, `bxor`, `shl`, `shr`, `lt`, `le`, `eq`, `fllt`, `flle`, `und`, `oder`, `nicht`,
`none`, `some`, `fall`, `grund`, `Args.nil`, `Args.cons`, `NutzlastExpr.keine`/`.zahl`.

**LEAN HAS IT, THE EMITTER NEVER PRODUCES IT (7):**

| constructor | blocker |
|---|---|
| `neg` | emitter `C001`, unconditional -- *"unary minus -- in C `-x` on an unsigned operand stays UNSIGNED … No corpus site needs it"*. Measured with `i32` and `i64` operands too: same refusal. |
| `ptrOf` | **no surface syntax**: `&path` parses only as `ExprArt::FnWert`, and `&T` is checker `M127` (*"`&` makes a FUNCTION into a value; there is no address-of for a variable or a type in Gabbro"*). Pointers reach a body only as parameters. |
| `istSome` | **no surface syntax**: `.is_some()` is `M129`, and the token exists nowhere in `crates/` or the corpus. The discriminating C exists only under `Stmt.onOption`. |
| `altGlob` | C only inside `exchange … when old(X) == e` (the `&_cx1` argument). Elsewhere `C001`. |
| `altSlot` | no C at all: contract-only, `C001` outside a contract. |
| `forallSlots`, `existsSlots`, `reaches` | 0 checker errors and **no C**: contracts are not lowered (`W6`). |
| `none`/`some` | **partial**: produced in assignment and `return` position only. In a `let` with a declared `option` type: `C001`, *"`option` has no representation yet"*. |

**RUST ADMITS, LEAN HAS NO CONSTRUCTOR (13), and only two of them are refused:**

| Rust form | checker verdict | Lean |
|---|---|---|
| `+%` `-%` `*%` `<<%` `+|` (wrapping/saturating) | **silently accepted**, C compiles | `Zahl.addW`/`subW`/`mulW`/`shlW`/`addS` are VALUE ops in `Ueberlauf.lean`; **no `Expr` constructor** |
| `count k in D : p` (`ExprArt::Zaehle`) | **silently accepted**, lowers to a generated counter call | none; `SYNTAX.md` calls it sugar for `Block.bindCall` |
| float literal (`ExprArt::Gleitkomma`) | accepted, `double r = 1.5;` | only `Block.gleitLit` -- no `Expr` node |
| float arithmetic `x + y` on `f64` | accepted, `double r = x + y;` | only `Block.gleit` -- no `Expr` node |
| a call in value position, `u64(a)`, `u32::max` | accepted | **no call `Expr`** at all; a call is `Block.bindCall` |
| `!=`, `>`, `>=` | accepted | derived from `lt`/`eq`; `exprOk` covers `gt` but **not `ne`/`ge`** |
| `~` (`UnOp::BitNicht`) | accepted, `(uint32_t)~(uint32_t)(w)` | `Expr.bxor w`, but the C is `CX.cpl`, not `.bin bxor` |
| `sizeof`/`aligned`/`lenof` | accepted; emitter `C001` | sugar for `Expr.lit`; no constructor |
| `result` | accepted, no C | the `ErgCtx` head variable, not a constructor |
| `[e0, e1]` (const initializer) | accepted, `static const uint32_t A[4]` | none; checker-evaluated |
| `@lib#fn(…)` | **refused, `N057`** | none |
| `&f` at an `fn(…)`-typed local | **accepted, C does not compile** -- see §5 | `fnref` |

**`exprOk` is narrower than the T4 lemma stock it gates.** `ecorr_div/rem/sdiv/srem/band/bor/
bxor/shl/shr/nicht/und/oder/bnot/cast` all exist in `CFormenI.lean`/`CFormenM.lean`, and
`exprOk` admits only `lit`, `var`, `bin add|sub|mul`, `cmp lt|le|eq|gt`, two slot-load shapes and
a plain global load; everything else is `_ => false`. *Widening `exprOk` to the lemmas already
proved moves about thirteen constructors from "outside the certificate" to "inside" without a
new proof, and `cmp ne`/`cmp ge` are the cheapest two.* **That is the single largest lever for
the translation-validation lane that follows.**

### 2.2 `Stmt`, `Block`, `Endblock` -- 50 constructors

CARRIES with compiling C: `assignSlot`, `assignDurch`, `assignGlob`, `schreibBytes`, `assignVar`
(plain and the four compound forms), `ite`, `onOption`, `onTag`, `onGrund`, `call`, `callInd`,
`locks` (plain and `shared`), `breaking`, `traverse`, `retry`, `forever`, `axiomCall`,
`regSchreib`, `transition`, `publish`, `ret`, `retGrund` (**since this lane**), `leave`
(`goto m_ende;`), `next` (`goto m_weiter;`), and every `Block` constructor except three.

**LEAN HAS IT, THE EMITTER NEVER PRODUCES IT (6):**

| constructor | blocker |
|---|---|
| `Stmt.uebergang` | **no surface statement** (`P017`); the `state` item itself is `C001` and `N055` |
| `Stmt.advances` | **no surface statement**; the head clause checks green but is GHOST -- the phase parameter is dropped from the C signature |
| `Stmt.retires` | same; the only green corpus site is a bodiless declaration |
| `Block.pruefung` | no surface form reaches C. A `format` field's `where` lands in a generated `F_gueltig` that **nothing calls**; the reading accessor carries no check |
| `Block.gleitVon` | `let y = f64(n);` draws `H021`+`E009`: `aufrufgraph.rs:410` registers the **eight integer** conversions only -- `f32`/`f64` are absent from the list |
| the `axiom` keyword | `aufrufgraph.rs` has no `axiom` handling at all, so every call of an `axiom`-declared name draws `H021`+`E009`. The two constructors stay reachable through `extern fn`/`prim fn`. |

**RUST ADMITS, LEAN HAS NO CONSTRUCTOR -- and the arena is the sharp one:**

| Rust form | checker | emitted | Lean |
|---|---|---|---|
| `let i = alloc A (v) [else …];` | **silently accepted (0 codes)** | `A_arena_speicher.buf[A_arena_speicher.used++] = (v);`, cc OK | **NONE.** `SYNTAX.md`:934 says so verbatim (*"no `Stmt` constructor -- the generation is checker state"*); `Arena.lean` carries only the MODEL |
| `reset A;` | **silently accepted (0 codes)** | `A_arena_speicher.used = 0;`, cc OK | **NONE** |
| compound assignment on a **global / slot / register** | accepted, cc OK | `Z += 0;`, `g->slots[i].w += 0;` | representable only as `assignGlob`/`assignSlot` + `Expr.add`; `Zucker`'s four sugars are `Var Γ`-only, and `storeSlot`/`storeGlob` elaborate to a plain `=` -- so these are **outside `GRow`** |
| `let i = o else (e) { … }` over a PLACE («B14b») | accepted | `C001` by name | none (`onOption` binds no reason) |
| `traverse … by consuming` | `S008` / `C001` by name | -- | none (`Stmt.traverse` has no mode) |
| `traverse … touches/decreases/invariant`, `forever … leaves/progress` | accepted, **erased** (byte-identical C) | -- | no field in the constructor |
| `exchange … when … returns r` | accepted | CAS | **shape mismatch**: `Block.exchange` binds the OLD value, the surface binds a `bool` |
| `breaking a, b { }` | accepted | -- | `Stmt.breaking` carries ONE `D.Inv` |
| `accumulates Q …; Q = v;` | accepted | per-CPU atomic fold `Q_melde(v)` | no matching constructor |
| `@lib#fn(…) { }` | **refused, `N057`** + `C001` | -- | none |

> **The two arena statements are the direction-2 finding that matters**: they are admitted, they
> emit C, they compile, and the specification has no constructor for them. Every program using
> one can therefore never close a correspondence chain -- and nothing says so at the site.
> `SYNTAX.md` names the gap; the compiler does not.

### 2.3 `Ty`, `Regklasse`, devices, registers, trees, domains, slots

* **`Ty.ptr (t : Nat) (rw : Bool)` carries NO SPACE.** The surface has six spaces plus named
  ones; `gabbro lean-g` prints *"pointer address spaces"* in its own "NO FORM in G (accepted and
  dropped, each named)" header, so the drop is named rather than silent. Since this lane the
  space is nonetheless in the artefact for two of the six (§1.1), which is a stronger answer than
  the census asked for.
* **`Ty.ptr` carries no `own`, no `x` and no owner mark.** `own` and `x` are carried by the
  checker (`R002`/`R003`/`R004`); the mark was carried by nobody and is now refused (§1.5).
* **`Regklasse.w1c` and `.rw` are indistinguishable IN THE SPECIFICATION**: `lesbar` and
  `schreibbar` agree on both. On the Rust side `R012` separates them (a read-modify-write of one
  bit of a `w1c` or `rc` word), and the emitter separates neither. *A constructor of the
  specification with no predicate that tells it from its neighbour is worth naming.*
* **`Ty.sum cases : List (Option (Int × Int))`** admits at most ONE integer payload per case.
* **Trees and domains have no `Ty`/`Expr` of their own**: a tree edge is a field with
  `Expr.reaches` over it, and `descendants`/`ancestors`/`chain` are `forallSlots` with `reaches`
  as a filter. Neither reaches C, and both are carried by refusals (§3).
* **A `device` with no parameter list** still emits `typedef struct { volatile uint8_t *basis; }`
  -- a member the declaration never named. Open; see §5.

---

## 3. The secondary measure -- `miss-grammatikdeckung.py`, 327 forms

### 3.1 The instrument itself was measuring the wrong thing, and it said so in its own header

Line 51 of `miss-grammatikdeckung.py`:

> *"The run therefore also records whether a deliberately broken variant is refused
> (`gegenprobe`), and prints that column beside the verdict."*

**It did not.** No table of broken twins, no run, no column -- the word stood twice in prose and
nowhere in code. *A documented column that was never built is the same shape as the `when` clause
this instrument was written to catch.*

What it cost: `GUARDS` was decided by asking whether the form's word stands inside backticks in
some checker refusal, read off STATIC string literals. **A refusal that names the form through an
interpolated `{}` is invisible to that**, and the checker is full of them:

```text
D007:  "`tree {wort} {}` is not `option index into {}`"   prints  tree parent elter
R006:  "`{}` is written, but `{}` is `class {}`"          prints  class rc
R008:  "`{}` passes `{}` in space `{}` to ..."            prints  space mmio
D018:  "`{form} {}` needs {}, and `{}` is {}"             prints  queue, elems, mappings
```

Seven form families of this half read `UNCOVERED` -- the class the instrument calls the dangerous
one -- while a checker rule about each exists, fires, and prints the form's own word. *The
instrument was not measuring the language; it was measuring how the sentence happened to be
spelled.*

**The gegenprobe is now built**: per form a deliberately broken twin and the words its refusal
must name, run through `pruefe` or through `emit` (both count; the verdict says which), with the
result consulted before the static word list.

**The one trap, and it caught the first draft:** a diagnostic ECHOES THE SOURCE LINE, and the
source line contains the form's word trivially. The first draft matched over the whole output and
reported seven domains as guarded on programs the checker had ACCEPTED. `absagetext` keeps only
the `error:`/`hint:` lines and their `=` notes, and the **fourth direction of the new speech test
holds it there** -- a word that stands only in the echoed source must not count. Notes DO count:
they are written by the same pass at the same site, and this folder puts the naming half there on
purpose (`M108` names `backed` in its note and not in its sentence).

### 3.2 Before and after, over all 327 forms

| class | before | after | Δ |
|---|---:|---:|---:|
| CARRIES | 128 | 140 | **+12** |
| GUARDS | 43 | 60 | **+17** |
| REFUSES | 49 | 52 | **+3** |
| DEMANDS | 6 | 6 | 0 |
| BASIS-C001 | 32 | 32 | 0 |
| NICHT-C | 4 | 4 | 0 |
| BASE-RED | 2 | 2 | 0 |
| **UNCOVERED** | **52** | **27** | **−25** |
| **NOT-PROBED** | **11** | **4** | **−7** |
| *open (UNCOVERED + NOT-PROBED)* | *63* | *31* | *−32* |

Headline: *the LANGUAGE carries* 171 of 282 measured (60.6 %) → **200 of 289 (69.2 %)**; of all
327 forms, 52.3 % → **61.2 %**.

**Every form that moved is one of the 37 assigned to this lane.** Verified by joining the two TSVs:
32 rows changed class, all 32 in the assigned set; no form of the parallel lane moved. The
gegenprobe is keyed per form, so a form with no entry cannot change class through it.

### 3.3 The 37, one by one

| form | before | after | what did it |
|---|---|---|---|
| `space.mmio` | UNCOVERED | **CARRIES** | `volatile` on the C pointer type (§1.1) |
| `space.dma` | UNCOVERED | **CARRIES** | same |
| `space.normal` | UNCOVERED | **CARRIES** | its probe holds it against an `mmio` base |
| `space.code` | UNCOVERED | **GUARDS** | gegenprobe `R008` names the space |
| `space.boot` | UNCOVERED | **GUARDS** | gegenprobe `R008` names the space |
| `device.mirrors` | UNCOVERED | **CARRIES** | probe repair: the mirror is read at a `transition`, and the host had none |
| `letform.:` | UNCOVERED | **CARRIES** | probe repair: the pair held `u32` against an inferred `u32` -- the same program. A `u64` annotation is what a declared type BUYS |
| `orexpr.\|\|` | UNCOVERED | **CARRIES** | probe repair: it had the host of `orpred.\|\|`, a predicate, where no C is written |
| `range...<` | UNCOVERED | **CARRIES** | probe repair: on the `typ` host a range moves the checks, not the storage; a `narrow` is where a bound reaches the artefact |
| `verbund_oder_varianten.(` | UNCOVERED | **CARRIES** | probe repair: the type was declared and never used |
| `primary.Some` | NOT-PROBED | **CARRIES** | new host: the one position the emitter lowers an `option` constructor in |
| `primary.None` | NOT-PROBED | **CARRIES** | same |
| `stmt.leave` | NOT-PROBED | **CARRIES** | the entry was a BUG: base and variant came from the same `{X}`. A `forever` cannot carry them (`S009`); a `retry … until` can |
| `stmt.next` | NOT-PROBED | **CARRIES** | same |
| `primary.Self` | NOT-PROBED | **REFUSES** | new host: `Self` in value position is an ordinary name, declared nowhere (`M119`) |
| `typ_oder_ort.{` | NOT-PROBED | **REFUSES** | new host: the record spelling of the decision `typ_oder_ort.intty` probes, same `C001` |
| `right.@` | UNCOVERED | **REFUSES** | the new named refusal (§1.5) |
| `slottype.wrapping` | NOT-PROBED | **GUARDS** | new host; `wrapping` is in the static word list already |
| `treedecl.parent` | UNCOVERED | **GUARDS** | gegenprobe `D007` prints the edge word |
| `treedecl.child` | UNCOVERED | **GUARDS** | same |
| `treedecl.sibling` | UNCOVERED | **GUARDS** | same |
| `regklasse.rc` | UNCOVERED | **GUARDS** | gegenprobe `R006`/`R012` name `class rc` |
| `regklasse.w1c` | UNCOVERED | **GUARDS** | gegenprobe `R012` -- the ONLY rule that separates `w1c` from `rw` |
| `table.backed` | UNCOVERED | **GUARDS** | gegenprobe `M108` names `backed` in its note |
| `typedecl.order` | UNCOVERED | **GUARDS** | gegenprobe `O001` |
| `domain.slots` | UNCOVERED | **GUARDS** | gegenprobe `D018` |
| `domain.queue` | UNCOVERED | **GUARDS** | gegenprobe `D018` |
| `domain.elems` | UNCOVERED | **GUARDS** | gegenprobe `D018` |
| `domain.mappings` | UNCOVERED | **GUARDS** | gegenprobe `D018` |
| `domain.chain` | UNCOVERED | **GUARDS** | gegenprobe `D015` |
| `domain.descendants` | UNCOVERED | **GUARDS** | gegenprobe at `emit` -- the refusal `beispiele/gift/195` was written for |
| `domain.ancestors` | UNCOVERED | **GUARDS** | same (`gift/196`) |
| `device.(` | UNCOVERED | **UNCOVERED** | open -- §5 |
| `regklasse.rw` | UNCOVERED | **UNCOVERED** | open -- §5 |
| `table.pub` | UNCOVERED | **UNCOVERED** | open -- §5 |
| `typedecl.(` | UNCOVERED | **UNCOVERED** | open -- §5 |
| `typedecl.=` | UNCOVERED | **UNCOVERED** | open -- §5 |

**32 of 37 closed; 5 stay open and are named in §5.** Of the 32: **12 CARRIES, 17 GUARDS,
3 REFUSES**. Seven of them were `NOT-PROBED` before, and in every one of those seven the cause was
the probe table rather than the language -- twice an entry whose base and variant were the same
program by construction (`stmt.leave`, `stmt.next`).

---

## 4. The guardians, before and after

Base measured on a clean tree at `1434efba` (the lane's changes stashed), not guessed.

| guardian | before | after | verdict |
|---|---|---|---|
| `pruefe-kennungen.py` | ALL PASS, 408 identifiers, 798 files | ALL PASS, **408**, 798 | unchanged -- every refusal this lane added is `C001`, which already has its identifier and its sentence |
| `pruefe-saetze.py` | (abort: binary older than `emit.rs`) | 408 identifiers, 163 sentences, **55 without a sentence**, 0 invented | the ratchet is `55`; no new identifier, so nothing to raise |
| `pruefe-zahlen.py` | **27** BEFUNDE | **27** BEFUNDE | unchanged |
| `pruefe-todo.py` | **14** BEFUNDE | **14** BEFUNDE | unchanged |
| `pruefe-englisch.py` | 7941 / 36968 German comment lines; ratchets 29/26 and 5/2 already broken | **7942 / 37124**; the same two ratchets, same numbers | +1 German line, mark `MARKE_KOMMENTARE = 7949` NOT reached; the two broken ratchets are the base state and did not move |
| `pruefe-emission.sh` | ALL PASS, 262 of 262 compile | **ALL PASS, 264 of 264 compile**, 37 driven through, 2 reverse probes | `MARKE_EMIT` 111 → 113, booked in the script with the date and the reason |
| `cargo test --no-fail-fast` | green, 40 collections | **green, 40 collections** | |
| `mutiere-pruefer.py --anker` | 388 of 416 anchors bite | **393 of 421** | +5 mutations, all five bite |

**Two numbers moved and are NOT booked in `README.md`/`TODO.md`, deliberately.** The mutation
catalogue is 416 → 421 and the biting anchors 388 → 393; both registers were already findings
before this lane (`README.md` carried 413, `TODO.md` 386) and the parallel lane adds mutations to
the same catalogue. *A number two lanes move at once belongs to the merge, which re-measures it --
booking it here would put a third wrong value in a register that already has two.*

`MARKE_EMIT` is booked by the lane and not by the merge, against the rule written beside it, and
the reason stands in the script: both new examples exist to PIN a lowering this lane changed, and
a pin whose file the mark does not count is not a pin -- stage 9 would skip it and the guardian
would be green over the very regression it exists for.

---

## 5. What stays open, and what blocks each

### 5.1 The five forms of the 37 that did not close

| form | what blocks it |
|---|---|
| `device.(` | A `device D at mmio` with NO parameter list emits the same handle as `device D(basis : Pa) at mmio`: `typedef struct { volatile uint8_t *basis; } D;` -- **a member the declaration never named**, with no type and no name of its own. The honest close is a named refusal ("a device at a memory space has a base, and the parameter list is where its type is declared"), which this lane did not build: the two corpus sites are gift files (`07`, `416`) whose expectations would have to be re-measured, and `at port` may legitimately want base 0. |
| `regklasse.rw` | **Nothing to refuse, and that is the finding.** `rw` is the permissive class, defined by what the other four forbid relative to it; there is no program a pass rejects for using an `rw` register. `Syntax.lean` cannot tell `.rw` from `.w1c` either (`lesbar`/`schreibbar` agree). An invented gegenprobe would be a twin broken for some other reason. |
| `table.pub` | A table-level `const` lowers to **nothing at all** (`table.const` is GUARDS, no C of its own) and cannot be named from another module in any spelling measured (`p::T::K` → `K190`+`M119`; `T::K` after a `use` → `K190`+`M126`). So `pub` on it changes nothing, anywhere, in any pass. *A form the grammar admits whose presence and absence are indistinguishable everywhere.* The honest close is a refusal at the declaration; it needs a checker rule, an identifier and a sentence, which is the parallel lane's surface. |
| `typedecl.(` | `type Q(Subject)` is the subject list of a ghost mark (`linear ghost type Duty(farbtest)`, three corpus sites, all ghost). It reaches no C by rule `G001` and is named by `LG001` at the G translation (*"type Q has no G form"*). What it does NOT have is a rule at the declaration -- the subject is never held against anything. |
| `typedecl.=` | A type alias is TRANSPARENT by design: `fn f(x : Q)` with `type Q = u32` emits `uint32_t x` exactly as `fn f(x : u32)` does. The C could differ if the emitter wrote a `typedef` per named alias, which would also make the generated C readable; it would change the C of every corpus file and was not attempted in this lane. |

### 5.2 Emitter defects found and NOT repaired

**`&f` at an `fn(…)`-typed local or return value.** `let r : F = &h;` with `type F = fn(x : u32)
-> u32 …` passes the checker with 0 errors and emits

```c
uint32_t (*)(uint32_t) r = &h;
```

-- an abstract declarator where a named one belongs; `cc` says `expected identifier or '(' before
')'` twice. The corpus only ever writes `&f` into a record field, where it is fine. The repair is
`fnzeiger_deklarator(z, name, u)` instead of `(z, "", u)` at the `let` site, or a named refusal.
*Left open because it is a fourth form of the same class and the lane had already moved three;
one more untested lowering in the same commit is one more thing the guardians cannot separate.*

**The checker accepts `q->wert` over a table.** This lane made the EMITTER refuse it. The checker
still says nothing: it never asks whether a field named through a pointer belongs to the target
type. The emitter's cut is coarse (first suffix must be `slots`); the exact rule is a checker rule.

### 5.3 For the translation-validation lane that follows

The binding sieve was named as (a): 109 of 111 corpus programs stop at the Lean parser or
elaborator, and the next gains come from widening `gbodyOk`'s covered forms. What this census adds
to that list, in the order of cheapness:

1. **`exprOk` is narrower than its own lemma stock.** `ecorr_div`, `rem`, `sdiv`, `srem`, `band`,
   `bor`, `bxor`, `shl`, `shr`, `nicht`, `und`, `oder`, `bnot`, `cast` are all proved in
   `CFormenI.lean`/`CFormenM.lean` and all fall through `exprOk`'s `_ => false`. About thirteen
   constructors move inside the certificate with no new proof.
2. **`cmp ne` and `cmp ge`** are the two cheapest of all: `CCmp` already carries them, the Rust
   side emits `!=`/`>=` freely, and `exprOk` admits `gt` but not those two.
3. **Compound assignment on a global, a slot or a register** is accepted, emits, compiles, and is
   outside `GRow`: `storeSlot`/`storeGlob` elaborate to a plain `=`, and `setOp` is `Var Γ`-only.
   `Zucker` has the four sugars for locals and none for the other three carriers.
4. **`Stmt.assignDurch` has no row premised on it.** Its C form IS `GRow.storeSlot`, and
   `RBlock`/`REnd` premise that row on `assignSlot` only -- although `GenOblig104.lean:134` uses
   `assignDurch` for exactly this surface.
5. **`retGrund`, `leave` and `next` have no `REnd` row**, though all three now emit compiling C.
6. **Floats can never enter a `GRow`**: `CX` has no float, and `fllt`/`flle`/`gleit*` have no
   `ecorr_*`.
7. **The arena statements have no constructor at all** (§2.2), so no program using `alloc`/`reset`
   can ever close a chain -- and nothing says so at the site.

---

## 6. What was measured where

* **`ki-pc-fisch-101`, directory `gabbro-opus-sb`:** every `cargo build`, `cargo test
  --no-fail-fast` and `./instrumente/pruefe-emission.sh`.
* **Locally:** single `gabbro pruefe`/`emit`/`lean-g` runs over an already-built binary, `cc` on
  one file at a time, and the text guardians -- the split `CLAUDE.md` draws.
* **`miss-grammatikdeckung.py`** runs locally by the same rule: it is `gabbro` plus `cc`, once per
  form, over a binary somebody else built.

Nothing was merged and nothing was pushed.
