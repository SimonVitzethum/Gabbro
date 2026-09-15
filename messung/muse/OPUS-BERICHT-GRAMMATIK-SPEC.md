# The specification half of the grammar, against the Lean specification

*Lane: Opus stage (a), 2026-09-15. Worktree `agent-a40cf5b762e63d298`, server directory
`gabbro-opus-sa` on `ki-pc-fisch-101`. Nothing merged, nothing pushed.*

**The authority of this report is `grammatik/Grammatik/Syntax.lean`** -- the typed family
that says what a sentence of Gabbro IS -- together with the surface readers under
`grammatik/Grammatik/Parser/`. The derived-form census
(`instrumente/miss-grammatikdeckung.py`) is the SECONDARY measure and is reported at the
end; it checks that nothing was missed, it is not what was optimised.

Three questions per constructor, and each answer is a measurement, not a reading:

1. **Does the Rust checker handle it** -- which pass, which rule, or nothing at all?
2. **Does the Rust surface parser admit a form the Lean specification cannot express?**
   That is a hole in the bridge between the two checkers.
3. **Does a Lean constructor exist that the Rust side never produces?** Then either the
   exporter must produce it, or its absence is named with a reason.

Everything below was run. The commands are named at each table.

---

## 0. The three measurements this report rests on

| what | how | where |
|---|---|---|
| the Rust checker | `gabbro pruefe` over a differential pair per form | server `gabbro-opus-sa` |
| the Lean surface reader | `lex` then `parseTopTief` on one source line per form, `lake env lean` | `Grammatik.Parser.ElementTief`, built in 4.8 s |
| the Lean bridge | `gabbro lean-g` over a differential pair, G term compared BYTE-WISE after the source path is normalised away | `crates/gabbro-check/src/lean_g.rs` |

**The third column is the one the census does not have.** `miss-grammatikdeckung.py` reads
two registers -- the emitted C and `gabbro pflichten` -- and a form that reaches the *G
program term* and neither of those comes out `UNCOVERED`. `andpred.&&` and `orpred.||` are
exactly that case: the bridge carries both (`Expr.und`, `Expr.oder`, measured: the G term
grows by 55 and 56 bytes), and the census reads them as forms nothing answers for. *The
census is right about what it measures and the sentence it invites is wrong.*

**And `gabbro lean-g` reports exactly ONE refusal per file and stops.** Measured over the
corpus: 111 files, 10 export, 101 refused -- and of the 101, **exactly one** reaches a
contract-level refusal (`[LG003] requires-clause in setze`). Everything else is stopped
earlier by `LG001`/`LG002` at a declaration (a `static`, an opaque type, an `assume`, a
`device`). *A corpus census of the bridge therefore cannot see the predicate half at all*;
it answers "does at least one form stop this file", not "which forms stop it" -- the same
shape as the `panic!` instrumentation of 2026-08-31. Every row below was therefore measured
on an ISOLATED pair over a host that exports, not on the corpus.

---

## 1. `Expr` -- the specification-only arms (`Syntax.lean` §3, `SYNTAX.md` §4/§5)

| Lean constructor | surface | 1. Rust checker | 2. Lean surface reader | 3. Lean bridge (`lean-g`) |
|---|---|---|---|---|
| `Expr.und` | `p && q` | accepted, no rule names `&&` | **ok** (`SExpr.bin "&&"`) | **carried** -- G term differs |
| `Expr.oder` | `p \|\| q` | accepted, no rule names `\|\|` | **ok** (`SExpr.bin "\|\|"`) | **carried** -- G term differs |
| `Expr.nicht` | `!p` | accepted, no rule names `!` | **ok** (`SExpr.un "!"`) | **REFUSED** `[LG003] ensures-clause has no G form` |
| *(none)* | `p => q` | accepted, no rule names `=>` | **PARSE-ERROR** (`fn without body`) | **REFUSED** `[LG003]` |
| *(grouping)* | `(p)` | accepted | **ok** | **REFUSED** `[LG003]` |
| `Expr.forallSlots` | `forall i in D : p` | accepted, **no rule names `forall`** | **PARSE-ERROR** `reserved head forall` | **REFUSED** `[LG003]` |
| `Expr.existsSlots` | `exists i in D : p` | accepted, **no rule names `exists`** | **PARSE-ERROR** `reserved head exists` | **REFUSED** `[LG003]` |
| `Expr.reaches` | `a reaches b via f` | accepted, **no rule names `reaches`** | **PARSE-ERROR** | not reached (`LG003` before it) |
| *(none)* | `e in domain` | `M111` refuses it outside a domain | **PARSE-ERROR** | -- |
| `Expr.altGlob`/`altSlot` | `old(place)` | accepted, **no rule names `old`** | **ok** (`SExpr.alt`) | **carried** -- G term differs |
| *(none)* | `result` | `M1` names `result` in an error | **ok** (`SExpr.ergebnis`) | carried (`USide.erg`) |
| *(place head)* | `Self` | `m1.rs`: ``` `Self` in `ensures` of `{}` names no carrier ``` | **ok** | not reached |

**Reading of the table.**

* **`=>` is the one arm with no Lean constructor at all** (question 2). Implication is not
  in `Expr`; the Lean reader has no shape for it, and `lean_g.rs` refuses it. 4 corpus
  files carry an implication outside a `match` arm. *The repair is a desugaring
  (`nicht a oder b`) plus a reader -- it belongs on the Lean side, not in a refusal.*
* **`forall`, `exists`, `reaches` are the mirror case** (question 3): the constructors
  exist in `Syntax.lean` and **nothing on the Rust side ever produces them**, because the
  Lean surface reader cannot even parse them. `ElementTief.lean` CUT 1 books this
  honestly: *"No `pred` reader (SYNTAX.md section 5)"*. **14 of 111 corpus files carry a
  quantifier or an implication** -- that is the size of the hole.
* **`old` and `!` split the difference**: `old` reaches the G term, `!` does not, although
  `Expr.nicht` exists. `!` is therefore a pure exporter gap, one `UEns.nicht` arm wide
  (`Uebersetze.lean` already has the arm; `lean_g.rs` does not produce it).
* **Four spec-only forms have no Rust checker sentence at all**: `forall`, `exists`,
  `reaches`, `old`. No `Absage::fehler` text names any of them. See §6.

---

## 2. The contract clauses (`Signatur`, `Programm`, `Syntax.lean` §1/§5)

| Lean field | surface | 1. Rust checker | 2./3. Lean side |
|---|---|---|---|
| `Programm.requires` | `requires p` | `namen`/`m1`, error text names `requires` | reader ok; bridge refuses a non-comparison (`LG003`) |
| `Programm.ensures` | `ensures p` | books an obligation (`DEMANDS`) | reader ok; bridge carries a COMPARISON only -- `ensures result == a + b` is `[LG003] comparison has no G form` |
| `Signatur.haelt` | `requires Held(L)` | `H003`/`H006`, interprocedural | reader ok (`ruf "Held"`); carried |
| `Signatur.erg` | `-> T` | carried into the C | carried |
| `Signatur.gruende` | `or R` | carried into the C | **elaborator: "Klausel ohne G-Form"** |
| `Signatur.schreibt`/`gschreibt` | `effects { writes … }` | error text names `writes` | carried |
| `Signatur.konsumiert` | `effects { consumes m }` | `m2.rs` names `consumes` | **elaborator: "Effekt ohne G-Form"** although `konsumiert` EXISTS |
| `Signatur.produziert` | `effects { allocs … }` | error text names `allocs` | same |
| `Signatur.boden` | *(computed)* | `H006`/`H003` walk | computed, never written |
| *(no field)* | `effects { reads … }` | error text names `reads` | **dropped, and NAMED** in the exporter's NO-FORM ledger |
| *(no field)* | `effects { diverges }` | **a HINT only** (`wirkungen.rs`), no error | **dropped SILENTLY** by the elaborator (`weichtAb` is skipped) |
| *(no field)* | `costs <= N ops` | `K001`, `kosten.rs` | **dropped, and NAMED** ("static annotations") |
| *(no field, `decreases` = recursion depth)* | `decreases e` | error text names `decreases` | **bridge: `[LG001] carries a form with no G counterpart`** |
| *(no term)* | `by induction over …` | error text names `by` | same |
| *(no field)* | `section "…"` | **nothing, until this lane** | dropped SILENTLY and not in the ledger |
| *(no field)* | `arch X` | `namen.rs` names `arch` | `[LG001] no G counterpart` |
| *(no field)* | `when X` | carried (the C differs) | `[LG001] no G counterpart` |
| `Stmt.advances` | `advances a -> b` | `O001`, `phasen.rs` | `[LG001] no G counterpart` |
| `Stmt.retires` | `retires t from …` | `O011`/`O013` | `[LG001] no G counterpart` |
| folded into `ensures` | `refines s` | books an obligation | elaborator: "Klausel ohne G-Form" |
| folded into `Inv` | `maintains I` | `m1.rs` names `spec fn` | elaborator: "Klausel ohne G-Form" |

**The row that matters most is `section`, and it is the reason for the one new refusal in
this lane.** Three registers, all empty: the emitted C of a function WITH the clause is
byte-identical to the C without it (`miss-grammatikdeckung.py --nur fndecl.section`), no
pass names the word, and `gabbro lean-g` exports the unit with a **byte-identical G term**
-- *and does not name the drop in the NO-FORM ledger it writes into its own header.* A
clause that changes neither the artefact nor an obligation nor the model is a promise
nobody keeps. `SPRACHE.md` §S2 asks for exactly this placement (`raw fn` in
`section ".boot"`) and says in the same row that it is **not enforced**;
`messung/BOOT-S3.md` item 4 books it as open. **`N320` now refuses it by name** -- the
honest interim state, and the rule goes the day the emitter writes the attribute.

**`pub` was the second silent drop.** `pub const Q` and `const Q` export a byte-identical
G term, and `pub` was in no ledger. It is now named in both the module header and the
generated header of `lean_g.rs`.

---

## 3. `Regklasse`, ghost carriers, `spec`, the axiom arrow

| Lean | surface | 1. Rust checker | 2./3. Lean side |
|---|---|---|---|
| `Regklasse.r/w/rw/w1c/rc` | `class …` | `R005`/`R006`, `regklasse.*` all CARRIES | all five exist; a device is `[LG001]`, so the classes never reach the term |
| `Regklasse.lesbar`/`schreibbar` | -- | derived in both | agree by construction |
| `Deklaration.geist`/`ggeist` | `ghost table` / `ghost static` | `G001`, `geister_haben_keinen_speicher` | reader ok; carriers are `LG001` |
| *(inlined, §6: `spec fn` = eingesetzt)* | `spec fn` | `m1.rs`, three error texts name `spec fn` | reader ok; **bridge: `[LG001] function q is not `impl`** |
| `Deklaration.aerg` + `Block.bindAxiom` | `axiom X() -> T` | accepted; no rule names the arrow | reader **ok**; **bridge: `[LG001] axiom has no G form`** |
| `Deklaration.Annahme` | `assume A …` | `namen.rs` names `arch` at an assumption | reader ok; `[LG001] assume has no G form` |
| `Deklaration.Inv`, `Programm.invariante` | `invariant … runs offline` | `D013` etc. | reader ok; **`[LG001] table T carries a form with no G counterpart`** |
| *(no field)* | `invariant … runs online` | **nothing names `online`** | reader ok; same refusal |
| *(no field)* | `invariant … by induction over` | error text names `by` | **PARSE-ERROR** `wanted :` |
| *(no form)* | `check … floor e` | `namen.rs` names `floor` | reader ok; check is `LG001` |
| `Signatur` via `sigNr` | `fn(…) -> T effects {…} costs <= n` | `N035`, `N036`, `M128`, `M141`, `N295`, `N297` | **PARSE-ERROR** `wanted ;` -- see below |
| *(§1: names are static)* | `use q::r;` | **nothing names `use`** | reader ok; `[LG001] use has no G form` |
| *(no notion)* | `pub` | `namen.rs` names `pub` | reader **drops it** (CUT 5); bridge drops it |

**The function-pointer type does not parse in Lean at all, and the CUT understates it.**
`ElementTief.lean` CUT 2 says `fnptr` "rides `roh`, balanced but uninterpreted". Measured:
`type F = fn(x : u32) effects { pure } costs <= 1 ops;` is a **PARSE-ERROR (`wanted ;`)**
-- the `fn(…)` parameter group rides `roh`, but the CONTRACT TAIL after it is not consumed,
so **no function-pointer type parses**, with or without `->`, `requires`, `ensures`,
`effects` or `costs`. That is five rows of the census in one reader gap, and it is a
correction to a booked CUT rather than a new one.

---

## 4. The one thing this lane repaired that nobody was looking for

**A single missing backtick in `m1.rs` had scrambled the checker's word register, and
every guardian that reads it stayed green.**

`pruefe-grammatiktafel.prueferworte()` collected every `Absage::fehler` text, **joined them
into one string, and only then paired the backticks**. One text -- `M159`, the `rotl`/`rotr`
range -- carried an odd number of backticks:

```
"`{name}` rotates a whole word and needs the exact full range `u{w} in 0 .. {}, and `{}` is not it"
                                                              ^ never closed
```

From that point on the pairing was inverted for **every file sorted after `m1.rs`**.
Measured:

| | |
|---|---|
| register size, joined (the state until today) | **531 words** |
| register size, paired per text (the truth) | **209 words** |
| real form words LOST | **80** -- `arch`, `costs`, `impl`, `pub`, `spec`, `Self`, `consumes`, `floor`, `ensures`, `refines`, `progress`, `traverse`, `touches`, `assume`, `axiom`, `asm`, `let`, `measures`, `raw`, `dma`, `order`, … |
| PHANTOM words gained out of the prose between the groups | **~450** -- `the`, `is`, `not`, `already`, `anything`, `bits`, … |

Both directions were wrong and both were silent. The consequence in the census:
**eleven forms read `UNCOVERED` that a real rule covers, and four read `GUARDS` that no
rule covers** (`domain.fields`, `item.opaque`, `regdecl.fields`, `typedecl.opaque` -- the
words `fields` and `opaque` are named by no checker error; they were phantoms).

The repair is in three parts, and only the first is the typo:

1. `crates/gabbro-check/src/m1.rs` -- the closing backtick.
2. `instrumente/pruefe-grammatiktafel.py` -- `_in_ruecken_je()`: pair **per text**, for the
   checker register and for the emitter register. *A register that pairs per text cannot be
   scrambled by its neighbour.*
3. the same file -- a **sixth direction of the speech test**, placed FIRST because every
   other direction reads the register it guards: *no diagnostic text may carry an odd
   number of backticks*, for the checker and for the emitter apart. The next typo is loud.

There is a **third blind spot of the register, and it is not repaired, it is named**: a
word that reaches the message through a VARIABLE is invisible, because the register reads
the literal of `Absage::fehler`. `N035` said ``"`{}` declares no {fehlt}"`` with `` `effects` ``
and `` `costs` `` inside `fehlt` -- the rule existed, the words did not. The three branches
now carry their own format literal (at most one fires, so the refusal count is unchanged),
and `fnptr.effects`/`fnptr.costs` became `GUARDS`. **Every other rule that builds a form
word into a variable is still invisible to the register**; this lane did not sweep for them.

A fourth limit, named and NOT repaired: `_in_ruecken` takes only
`[A-Za-z_][A-Za-z0-9_]*` inside backticks, so **an operator form can never score `GUARDS`**
-- `andpred.&&`, `orpred.||`, `notpred.!`, `notpred.=>`, `atompred.(`, `axiom.->`,
`fnptr.->` are structurally excluded no matter what the checker says. Extending the pattern
would pull the format placeholders (`{}`, `{} .. {}`, `0`, `-1`) into the register, so the
extension needs a design and not a one-line change. For those seven forms `UNCOVERED` is a
statement about the instrument as much as about the tree, and §1 above says what is really
true of each.

---

## 5. The 26 assigned forms -- before, after, and what did it

Measured with `./instrumente/miss-grammatikdeckung.py` at `master` (base) and after the
change, both on `ki-pc-fisch-101` with a freshly built binary.

| form | before | after | what did it |
|---|---|---|---|
| `assume.arch` | UNCOVERED | **GUARDS** | register repair -- `namen.rs` names `arch` at an assumption |
| `check.floor` | UNCOVERED | **GUARDS** | register repair -- `namen.rs`: *"compared one-sidedly and no `floor` names it"* |
| `eff.consumes` | UNCOVERED | **GUARDS** | register repair -- `m2.rs`: *"listed under `consumes` but consumed on no path"* |
| `fndecl.arch` | UNCOVERED | **GUARDS** | register repair -- `namen.rs`: *"`arch {}` names a machine this unit never declares"* |
| `fndecl.costs` | UNCOVERED | **GUARDS** | register repair -- `namen.rs`: *"has an `asm` body but no `costs`"* |
| `fndecl.impl` | UNCOVERED | **GUARDS** | register repair -- `m1.rs`: *"carries `refines` but is not an `impl fn`"* |
| `item.pub` | UNCOVERED | **GUARDS** | register repair -- `namen.rs`: *"`{ziel}` is not `pub`"* |
| `item.spec` | UNCOVERED | **GUARDS** | register repair -- `m1.rs`, three texts name `spec fn` |
| `place.Self` | NOT-PROBED | **GUARDS** | new host (a table invariant, the only place that can name its carrier) -- `m1.rs`: *"`Self` in `ensures` names no carrier"* |
| `fnptr.effects` | NOT-PROBED | **GUARDS** | new host (`beispiele/49` shape) + `N035` carries the word in its own literal |
| `fnptr.costs` | NOT-PROBED | **GUARDS** | same |
| `fndecl.section` | UNCOVERED | **REFUSES `N320`** | new rule + `beispiele/gift/980` + sentence + mutation |
| `atompred.reaches` | NOT-PROBED | UNCOVERED | new host -- and the honest verdict: **no checker error names `reaches`** (the old `GUARDS`-adjacent reading came from a phantom) |
| `andpred.&&` | UNCOVERED | UNCOVERED | **carried by the bridge** (`Expr.und`); invisible to the census, see §4 |
| `orpred.\|\|` | UNCOVERED | UNCOVERED | **carried by the bridge** (`Expr.oder`); same |
| `primary.old` | UNCOVERED | UNCOVERED | **carried by the bridge** (`Expr.altGlob`/`altSlot`); no checker rule names `old` |
| `notpred.!` | UNCOVERED | UNCOVERED | `Expr.nicht` exists, the exporter never produces it |
| `notpred.=>` | UNCOVERED | UNCOVERED | **no Lean constructor**, no Lean reader, no checker rule |
| `atompred.(` | UNCOVERED | UNCOVERED | grouping; needs no constructor, refused by the bridge |
| `atompred.forall` | UNCOVERED | UNCOVERED | `Expr.forallSlots` exists, **the Lean reader refuses the word** |
| `atompred.exists` | UNCOVERED | UNCOVERED | `Expr.existsSlots` exists, same |
| `axiom.->` | UNCOVERED | UNCOVERED | `Deklaration.aerg` + `Block.bindAxiom` exist, every axiom is `LG001` |
| `fnptr.->` | UNCOVERED | UNCOVERED | `(D.sigNr n).erg` exists, no fn-pointer type parses in Lean |
| `eff.diverges` | UNCOVERED | UNCOVERED | **a hint, not an error**; no `Signatur` field; the elaborator skips it silently |
| `invariant.online` | UNCOVERED | UNCOVERED | nothing names `online`; no Lean field |
| `item.use` | UNCOVERED | UNCOVERED | nothing names `use`; §1 says names are static, so there is no Lean form to want |

**12 of 26 closed** (11 `GUARDS`, 1 `REFUSES`), **1** moved from unmeasured to an honest
`UNCOVERED`, **13 stay open** with the reason named above and in §6.

### The census as a whole

| class | before | after |
|---|---|---|
| CARRIES | 128 | 128 |
| GUARDS | 43 | **53** |
| REFUSES | 49 | **50** |
| DEMANDS | 6 | 6 |
| BASIS-C001 | 32 | 32 |
| NICHT-C | 4 | 4 |
| BASE-RED | 2 | 2 |
| **UNCOVERED** | **52** | **45** |
| **NOT-PROBED** | **11** | **7** |
| open (UNCOVERED + NOT-PROBED) | **63** | **52** |

**Three of the gains and all four of the losses are outside this half**, and they are
listed here so the parallel lane does not count them twice:

* gained by the register repair, not by this lane's work: `space.dma`, `table.pub`,
  `typedecl.order` (UNCOVERED -> GUARDS).
* **lost** by the register repair, and the loss is the truth: `domain.fields`,
  `item.opaque`, `regdecl.fields`, `typedecl.opaque` (GUARDS -> UNCOVERED). No checker
  error names `fields` or `opaque`; they were covered by a phantom. *These four are new
  work, not a regression.*

---

## 6. What stays open, and what blocks it

**On the Rust checker side -- five forms of this half have no diagnostic at all**, and
none of them can be refused, because the corpus writes all five:

| form | corpus sites | why no rule was written |
|---|---|---|
| `forall` | 11 files | the obvious rule (a binder the body never names) needs an AST walk over predicates; the text scan that would have justified it is not accurate enough to claim the corpus is clean |
| `exists` | 2 files | same |
| `reaches` | 3 files | same |
| `old` | 4 files | candidate rule: *`old` names a place this function never writes*. Sound in principle; the four corpus sites are `old(BESITZER)` / `old(k.slots[i].stand)` and would need the write-set per function to be certain. Not written without that measurement. |
| `invariant … runs online` | 3 files | candidate rule: *`runs online` on a table with no `ops`*. **Measured and DROPPED**: `beispiele/07-eintritt-und-boot.gab` has `runs online` and no `ops`, so the rule would fall on a corpus program. |
| `diverges` | 17 files | candidate rule: *`diverges` on a function that does not answer `never`*. **Measured and DROPPED**: 42 heads carry `-> never`, **11 do not** (`54-divergenz-leckt-nicht`, `39-auftragsdienst`, `42-zaehlwerk`, …), and `wirkungen.rs` says in so many words that `diverges` does not travel upwards. |
| `use` | 1 file | the rule would be *a `use` the unit never mentions* -- and `namen.rs` says in its own header that module RESOLUTION does not exist yet. A rule on top of a resolution that is not built measures nothing. |

*Two candidate rules were measured against the corpus and dropped before they were
written. That is the cheaper half of the day and it belongs in the report: a rule that
would have fallen on `beispiele/07` is not a near miss, it is a wrong rule.*

**On the Lean side -- the next lane's input, named precisely.**

1. **`Parser/Ausdruck.lean` has no `pred` reader at all** (`ElementTief.lean` CUT 1). The
   missing shapes are `forall i in D : p`, `exists i in D : p`, `a reaches b via f`,
   `e in domain`, `p => q`, and a two-argument `Held(L, shared)`. `forall`/`exists` are
   even listed in `keinPlatzTafel` as words that never start a place, so they are refused
   rather than misread -- **`reserved head forall`** is the measured message.
   **14 of 111 corpus files carry at least one of these**, and every corpus table
   invariant quantifies. *This is the single largest item between the two checkers.*
2. **`p => q` needs a constructor or a desugaring on the Lean side.** `Expr` has `und`,
   `oder`, `nicht` and no implication. A desugaring `nicht a oder b` in the reader costs
   nothing in `Syntax.lean` and closes the row.
3. **`Parser/ElementTief.lean` does not read a function-pointer type.** Not "uninterpreted"
   as CUT 2 says -- `type F = fn(x : u32) effects { pure } costs <= 1 ops;` is a
   PARSE-ERROR. The parameter group rides `roh`; the contract tail after it is not
   consumed. Five census rows hang on this one gap.
4. **`invariant … by induction over …` is a PARSE-ERROR** (`wanted :`) on a table
   invariant.
5. **`Uebersetze.elabU` silently skips three effect arms** -- `reads`, `pure` and
   **`diverges`** -- and errors on `locks`, `masks`, `allocs`, `consumes`, `publishes`.
   `consumes` is the sharp one: **`Signatur.konsumiert` exists in `Syntax.lean`** and
   neither the Rust exporter nor the Lean elaborator ever produces it.
6. **`costs`, `section` and `payload` "travel nowhere and are ignored"** in `elabU`, and
   `Signatur` has no cost field at all. The cost half of the goal lives in `KostenG.lean`
   over the machine, not in the declaration -- that is a decision, and it should be stated
   in `Syntax.lean` §6 (which today lists `decreases`, `refines`, `by induction` and
   `spec fn`, and does not mention `costs`, `arch`, `section` or `when`).
7. **`gabbro lean-g` stops at the first refusal.** Until it collects them, no corpus census
   of the bridge can see past the declaration layer. That is the cheapest single change to
   the next lane's measuring apparatus.

---

## 7. The guardians, before and after

All on `ki-pc-fisch-101:gabbro-opus-sa`, freshly built binary, `cargo test --no-fail-fast`.

| guardian | before | after | booking |
|---|---|---|---|
| `cargo test --no-fail-fast` | (base) | **1003 passed, 0 failed** | -- |
| `pruefe-kennungen.py` | exit 0, **408** codes | exit 0, **409** codes | `N320` |
| `pruefe-saetze.py` | exit 0, 408 codes / **163** sentences / 55 without | exit 0, 409 / **164** / 55 | `namen.section_an_funktion` |
| `pruefe-zahlen.py` | exit 1, **28** findings | exit 1, **28** findings | it stood at 29 between the rule and the booking; the one new finding is booked in `TODO.md`, see below |
| `pruefe-todo.py` | exit 1, 14 findings, README 6 | exit 1, 14 findings, README 6 | unchanged |
| `pruefe-englisch.py` | exit 1 (aborts at *Quellsprache*) | exit 1, same abort | unchanged |
| `pruefe-grammatiktafel.py` | exit 0, **0 of 240 UNGEDECKT**, 5 directions | exit 0, **0 of 240 UNGEDECKT**, **6 directions** | the pairing direction is new and green |
| `miss-grammatikdeckung.py` | 63 open | **52 open** | §5 |

The mutation is measured and not assumed: applied on the server copy, built, `gift/980`
stops reporting `N320` (0 occurrences) and `cargo test --test beispiele` goes
**FAILED, 24 passed / 1 failed**; the source was restored and compared by `md5sum` against
the worktree. Anchors: **389 of 417 grip** (before: 388 of 416); the 28 that grip into
nothing are the pre-existing backlog, untouched.

`pruefe-zahlen.py` moved five numbers, four of which were **already stale before this
lane** and stay in the backlog with their old entries (`Absagekennungen` 393→408→409;
`Mutationsanker` 386→388→389; `Mutationen im Katalog` 413→416→417; `Zeilenfortsetzungen`
3183→5324→5341). **Exactly one number was correct before and is moved by this lane, and it
is booked in `TODO.md` with its reason**: *„Absagen, die sich ueber die DARSTELLUNG
begruenden"* **8 → 9**. `N320` justifies itself through the artefact (`byte-identical C`)
and the guardian is right to flag it -- here that is the sentence and not a slip, because
the rule's whole content is that the clause reaches no register at all. A justification out
of the promise would have been the dishonest one.

Two further numbers moved inside `pruefe-grammatiktafel.py` and are read by no guardian:
the speech test's first candidate word (`Self` → `acquire`, because `Self` is now covered by
the checker as well), and **EMPFINDLICHKEIT 6 → 3** words that hang on a single file --
the repaired register covers three of them a second way.

---

## 8. What was changed

| file | change |
|---|---|
| `crates/gabbro-check/src/m1.rs` | the missing closing backtick in the `M159` text (one character) |
| `crates/gabbro-check/src/namen.rs` | `N320` -- `section` at a function; and `N035` carries `effects`/`costs` in its own format literal |
| `crates/gabbro-check/src/saetze.rs` | the sentence `namen.section_an_funktion` |
| `crates/gabbro-check/src/lean_g.rs` | `pub` named in the NO-FORM ledger, in the module header and in the generated header |
| `beispiele/gift/980-section-an-einer-funktion.gab` | the probe, `-- erwartet: N320 allein` |
| `instrumente/mutiere-pruefer.py` | one mutation on the new rule |
| `instrumente/pruefe-grammatiktafel.py` | per-text backtick pairing; the sixth speech-test direction |
| `instrumente/miss-grammatikdeckung.py` | hosts for `atompred.reaches`, `place.Self`, `fnptr.effects`, `fnptr.costs` |
| `TODO.md` | the one number this lane moved, with its reason |

Not touched, by instruction: `emit.rs`, `instrumente/pruefe-emission.sh`, the `beispiele/*.gab`
examples (only a new `gift/`), MARKE counters.
