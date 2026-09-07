# The grammar derived from the checker — and what plumbing a user still carries

**Base:** `master` at `99ac2e6`. Server directory `gabbro-grammatik`. Binary: `cargo build`
on `ki-pc-fisch-101`, debug.

**The brief, in the owner's words:** *derive the grammar and syntax FROM THE CHECKER'S CODE,
and against that derived grammar determine what plumbing a user still carries.* The word
that carries it is **derive**. The documents are not the source here — they are the
comparison.

Every number below carries the command that produced it. Where an instrument measures
something other than its object, that is said at the number and not in a footnote.

---

## 0. Why the GRAMMAR is the right population, and why this lane exists

Every previous attempt at the plumbing question measured over a **corpus**, and every one ran
into **trap 80** — measuring against a corpus written while looking at it. `gabbro
blindstellen` says so about itself: *"der Korpus ist von der Sprache nach außen geschrieben."*
A corpus cannot answer completeness, because completeness is a statement about the language
and the corpus is a statement about what somebody wrote.

**The grammar is the language's own population.** It is not written from the language
outwards; it *is* the language. That is the one denominator trap 80 cannot reach, and it is
the methodological reason this lane was opened.

But there are two grammars, and until today only one of them had a population.

### The defect this lane was aimed at, and it is real

`instrumente/pruefe-grammatiktafel.py` is the tree's grammar register. It computes
FORM × ZUSTÄNDIGKEIT and demands that `UNGEDECKT` be empty. **Its population is read out of a
DOCUMENT** — its own line 8:

> *"The population here is the **grammar**: the rules and terminals `dokumente/SYNTAX.md`
> carries, and that is the set „beliebig" means."*

Mechanically, `terminale()` (line 246) loads `pruefe-wortschatz.py` and takes its `term` —
the quoted word-shaped terminals of the EBNF blocks of `dokumente/SYNTAX.md`. So the
population is **218 words out of a document**, and a form the parser accepts that the
document does not carry is in no population, gets no state, and an empty `UNGEDECKT` says
nothing about it.

**The table says this about itself, and says it correctly:**

> *"ein Terminal ist nicht dasselbe wie eine Form — eine Regel, die aus lauter gedeckten
> Woertern eine ungedeckte Kombination baut, faellt hier nicht auf."*

That is not a criticism of the table. It is the reason the second population had to be built,
and §1 builds it.

```bash
ssh ki-pc-fisch-101 'cd gabbro-grammatik && python3 instrumente/pruefe-grammatiktafel.py'
# == GRAMMATIKTAFEL GRUEN: 0 von 218 Terminalen UNGEDECKT ==     exit 0
```

**The table is green, and it stays green in this report.** Nothing below lowers it. What
follows is a second question over a second population, not a second answer to its question.

---

## 1. THE DERIVED GRAMMAR — 105 productions, 320 forms

`instrumente/leite-grammatik.py` reads `crates/gabbro-syntax/src/parse.rs`, `kw.rs` and
`lex.rs` and prints the grammar the reader implements.

```bash
./instrumente/leite-grammatik.py            # the derived grammar, rule by rule
./instrumente/leite-grammatik.py --formen   # one line per form -- the population
./instrumente/leite-grammatik.py --zahl
# == 105 rule functions · 320 FORMS (179 WAHL, 141 OPTION) ==
#    11 rules decide by LOOKAHEAD and not by a word
#    vocabulary: 221 words, 17 reserved
```

**It is a derivation and not a transcription, and that is possible because `parse.rs` says
so of itself:** *"laid rule by rule against SYNTAX.md: every EBNF rule has a function carrying
its name."* One rule function, one production.

### What a FORM is here, and why the denominator is defensible

A production is not yet something a user chooses — `fndecl` is one function and eighteen
decisions. So the population is the set of **decision points**, and there are exactly two
kinds, both mechanically visible in the source:

| | |
|---|---|
| **WAHL** (179) | an alternative arm keyed on a token: `Art::Wort(Kw::X) =>` / `Art::Zeichen(Z::Y) =>`. The user picks one arm. |
| **OPTION** (141) | a clause the user may write or omit: `friss_kw(Kw::X)` / `ist_kw(Kw::X)` / `friss_z` / `ist_z` guarding an `if`. |

An `erwarte_kw(Kw::X)` is **neither** — it is a DEMAND. The user does not choose it; it is
the skeleton the chosen form is made of, and counting demands would count the same form once
per word it is spelled with. *The denominator is what a user decides, not what the parser
consumes.*

Three exclusions, each with its reason in the tool:

* **List punctuation is not a form.** `if !self.friss_z(Z::Komma) { break; }` is how a
  repetition ends. Counting it would put `,` `}` `)` `]` `;` in the denominator once per list
  in the language. 47 decision points fall out here.
* **The eight integer words are counted ONCE**, at `intty`, which builds the type. Five other
  rules test `k.ist_intty()` — two to delegate, three to tell a type or a path from a name —
  and there the predicate is one decision, not eight.
* **Eleven rules decide by LOOKAHEAD and not by a word** and are one form here and several to
  a user. They are printed under `ZWEIDEUTIG` and named, not counted away: `letform`,
  `primary`, `zuweisung_oder_ruf`, `stmt`, `verbund_oder_varianten`, `fnptr_params`,
  `typ_oder_ort`, `bitpos`, `atompred`, `bootdecl`, `slottype`.

### The trap that would have made the whole derivation wrong

**Keywords are CONTEXTUAL.** As of `77c4061` reserved words went from **212 to 17**, and 204
of 221 vocabulary words are ordinary names wherever the grammar expects a name. A derived
grammar treating the old 212 as terminals would be wrong about almost every position in the
language. The seventeen, from `kw.rs`:

```
const static extern if else return bool          -- break the emitted C as an ordinary local
sizeof lenof aligned forall exists               -- head an expression or a predicate
true false Self Some None                        --   unconditionally
```

The two reasons are different kinds of reason, and `parse.rs::erwarte_ident` prints the right
one per word.

### Register reconciliation — which register is this one? (`W7`)

| register | population | unit | today |
|---|---|---|---|
| `pruefe-grammatiktafel.py` | `SYNTAX.md` EBNF | **218 terminals** (words) | 0 UNGEDECKT |
| `leite-grammatik.py` | **`parse.rs`** | **320 forms** (decision points) | this document |
| `fuzze-grenzen.py` / `fuzze-erzeuger.py` | a hand-written template dict | 63 / 64 **declaration forms** × value rungs | see `messung/ERZEUGERREST.md` |
| `gabbro blindstellen` | a corpus | form × position | says of itself it cannot answer completeness |

**These are four registers over four different things and none of them is a copy of another.**
The sweeps ask *"for this form, at extreme values, does the pipeline hold?"*; this one asks
*"does this form exist, and who carries it?"* The sweeps' 63/64 forms are a **hand-written
dict** (`fuzze-grenzen.py:280 FORMEN = {`), which is the same shape of defect one level up —
the derived list in §1 is what that list can now be held against. **That comparison is NOT
run in this document** and is named in §5.

---

## 2. THE COMPARISON — 32 measured divergences, both directions

Against `dokumente/SYNTAX.md`, and specifically against the population
`pruefe-grammatiktafel.py` reads. **A divergence claimed from reading two texts is a
hypothesis; a divergence with a program under it is a measurement.** Every row below was run
against this binary and the output is quoted literally.

### 2.1 The word-level comparison finds NOTHING, and that is the point

```
EBNF terminals (the grammar table's population):        218
derived forms:                                          320   (258 word-keyed, 62 punctuation-keyed)
distinct words the parser DECIDES on:                   191
a word the parser decides on that the EBNF lacks:         3   -- `r` `w` `x`, and by RULE
EBNF terminals at no parser decision point AND no `erwarte_kw`: 0
```

The three are single lowercase letters, which `pruefe-wortschatz.py:95` excludes from the
terminal set by construction (`len(t) > 1 or t.isupper()`). So **every word of the document
is implemented and every word the parser reads is in the document.** At the level of words
the two grammars agree completely.

> **And that is exactly why the defect is real.** The population is a set of WORDS. A
> divergence between two grammars lives in the COMBINATIONS, and a word-keyed table has no
> cell for a combination. All 32 divergences below are invisible to it, and not one of them
> lowers its green.

### 2.2 (A) The parser accepts what the document does not carry — 20 measured

Each was run as `gabbro pruefe` on a minimal file; `0 errors` means the form went through
the reader **and** every built pass.

| # | rule | probe | result |
|---|---|---|---|
| A1 | `SM:173/174` `hex`/`bin` need a digit before any `_` | `const X : u32 = 0x_FF;` | **0 errors** |
| A2 | `SM:188` `pathseg = ident \| intty \| opname` | `use a::return;` · `use a::bool;` | **0 errors** — a RESERVED word after `::` |
| A3 | `SM:208` `regbind = ident ":" ident` | `regs in { r0 : Self }` | **0 errors** |
| A4 | `SM:381/463` `typelist` cannot be empty | `type T();` | **0 errors** |
| A5 | `SM:404` `typeexpr` has no `Self` | `type T = { a : Self, };` | **0 errors** |
| A6 | `SM:414` `fexpr = float [rounded] \| ident \| int` | `const A : f32 in 0.0 - 1.0 .. 1.0 = 0.5;` | **0 errors** — arithmetic in a float range |
| A7 | `SM:430` `field = ident ":" fieldty` | `type T = { bool : u32, };` | **0 errors** |
| A8 | `SM:441` `variants` carries no trailing comma | `tagged type K = { A, B, };` | **0 errors** |
| A9 | `SM:635` `primary` has no `float` | `const X : f32 = 1.5;` | **0 errors** |
| **A10** | `SM:427` an INTEGER `range`, and `primary` has no float | `type T = u32 in 0.5 .. 1.5;` | **0 errors, and it EMITS C that compiles** |
| A11 | `SM:638` `reasonval = ident "::" ident` — exactly two | `const X : u32 = A::b::c;` | parses; `M134` at the pass |
| A12 | `SM:711` `placesuffix = "." ident` | `type S = { return : u32, }; … s.return` | **0 errors** |
| A13 | `SM:711` `placesuffix = "->" ident` | `… s->if` | **0 errors** |
| **A14** | `SM:709` `oldexpr` — *"nur in ensures"* | `fn f(a : u32) requires old(a) == 1 …` | **0 errors** — `old` in `requires` |
| A15 | `SM:683` `arglist = arg { "," arg }` | `g(1, 2,);` | **0 errors** |
| A16 | `SM:702` `arg = [ ident ":" ] expr` | `P(bool: 1)` | **0 errors** — a reserved word as a label |
| A17 | `SM:764` `reach … "via" ident` | `a reaches b via return` | **0 errors** |
| A18 | `SM:855/857` `identlist` is ≥ 1, no trailing comma | `asm { "nop" clobbers { } }` · `in { }` · `clobbers { rax, }` | all three parse |
| A19 | `SM:992/993/1009` `awaitload`/`exchstmt`/`let…else` write bare `"let" ident "="` | `let mut x : u32 = q() else (e) { … }` | **0 errors** — `mut` and a type on all three |
| A20 | `SM:1013` `matchstmt` arms are `ident` | `match o { Some(x) => { } None => { } }` | **0 errors** — two of the seventeen |

Six more of the same class, measured, that the EBNF is simply behind on and the prose is not:

* `SM:1040` `traverse` carries no `[ "invariant" pred ]`; the parser reads one at all three
  loop forms (`schleifeninvariante`), and `SM:1065` says so in prose.
* `SM:1331` `reason … [ "exhaustive" ]` stands after the cases, once — the parser takes it
  **anywhere in the body and repeatedly**: `reason R { exhaustive a = 1 "x" }` and
  `reason R { a = 1 "x" exhaustive exhaustive }` both give **0 errors**.
* `SM:1345` `device` body is `"{" [ mirrors ] { regdecl | bank | transition } "}"` — the
  parser takes `mirrors` at any position, and the document's own example at `SM:1408` writes
  it after three `reg`s, so the example contradicts the production, not the parser.
* `SM:1493` `rcudecl … "{" placelist "}"` with `placelist` ≥ 1: `rcu R protects { };` and
  `rcu R protects { Z, };` both give **0 errors**.
* `SM:1589` `axiom … [ "requires" pred ]` — at most one; the parser loops
  (`while self.friss_kw(Kw::Requires)`), and two clauses give **0 errors**.
* `SM:269` `buildgate = "when" "TESTBUILD"` — the parser takes any expression. **This one is
  not a finding**: `G002` refuses it by name (`a `when` condition other than `TESTBUILD``)
  and `SM:271` says the reader is deliberately the wider of the two. *It is the shape the
  other nineteen should have and do not.*

**A10 is the sharpest.** `type T = u32 in 0.5 .. 1.5;` — an integer type whose range bounds
are floating-point literals — is accepted by the reader, by all built passes, by the emitter,
and its C compiles at `-O0` and `-O2`. Nothing anywhere says a word about it.

### 2.3 (B) The document carries what the parser refuses — 12 measured

| # | rule | probe | refusal |
|---|---|---|---|
| B1 | `SM:167` `ident = ( letter \| "_" ) { … }` | `const _ : u32 = 0;` | `P034` |
| B2 | `SM:175/172` the exponent is a `dec`, and `dec` carries `_` | `const X : f64 = 1.0e1_0;` | `P001` |
| **B3** | `SM:413` `frange = fexpr ( ".." \| "..=" \| "..<" ) fexpr` | `const A : f64 in 0.0 ..= 1.0 = 0.5;` | `P011` — **`..=` is not a token in `lex.rs`** |
| B4 | `SM:429` `structty = "{" { field } "}"` | `type T = { };` | `P035`, deliberately |
| B5 | `SM:461` `fncontract` demands `effects` and `costs` | `type F = fn(u8);` | parses; `N035` at the pass |
| B6 | `SM:707` `builtin` takes a `typeexpr`, and `indexty` is one | `sizeof(index into T)` | `P001` at `into` |
| B7 | `SM:296` `bootstep = "step" ( call \| … )`, `SM:672` `call = ( path \| place ) "("…` | `step t.f();` | `P001` — `=` expected |
| B8 | `SM:994` `exchange … publishes ( placelist \| "nothing" )` — no braces | `… publishes Z;` | `P001` — and `SM:1484` says the opposite in the same document |
| B9 | `SM:1245` `slotdecl` — the trailing comma is OPTIONAL, and `SM:211` names `slotdecl` in the "one comma rule" box | `slot { used : u32 }` | `P001` — the parser DEMANDS it |
| B10 | `SM:1130` the `table` body is a repetition over `slotdecl` | two `slot` words | `P020`, deliberately |
| **B11** | `SM:1489` `lockdecl … "{" placelist "}"` — the SAME text as `rcudecl` | `lock L protects { Z, }` · `lock L protects { }` | `P003` for both, while `rcu` accepts both |
| B12 | `SM:211` "one comma rule … trailing comma optional", `entrydecl` named | `preserves { rbx, }` | `P003` |

**B11 is two behaviours for one EBNF text.** `lockdecl` calls `placelist()` (which demands
≥ 1 and no trailing comma); `rcudecl` writes its own loop (which allows both). The document
gives them the same right-hand side.

### 2.4 The one that contradicts the headline of `77c4061`

`SYNTAX.md:126` states the rule the contextual-keyword change was made to establish:

> *"At every position where the grammar writes `ident`, every word of this table is a name."*

**Measured, and it is not true at two positions:**

```
retry lauf  bounded 4 ops on_exceeded x { }     -- 0 errors        (the control)
retry node  bounded 4 ops on_exceeded x { }     -- P001: `bounded` expected, `node` found
retry index bounded 4 ops on_exceeded x { }     -- P001: `bounded` expected, `index` found
forever stack per_pass bounded 4 ops …          -- P001: `per_pass` expected, `stack` found
```

The cause is exact and there are exactly two of it. Every position in the parser that admits
an optional name tests the token kind, and only these two test for a **bare** identifier:

```
crates/gabbro-syntax/src/parse.rs:3293   retry    let marke = if matches!(self.blick().art, Art::Ident) {
crates/gabbro-syntax/src/parse.rs:3335   forever  let marke = if matches!(self.blick().art, Art::Ident) {
```

```bash
grep -n 'matches!(self.blick().art, Art::Ident)' crates/gabbro-syntax/src/parse.rs
```

The other three hits of `Art::Ident` in the file are not this class: `:324` is the `_` rule,
`:2224` is the `Held` special form (an uppercase name, no vocabulary word can reach it), and
`:2798` is the abolished-forms table (`while`, `for`, `goto` — none is a vocabulary word).

**So the loop label of `retry` and `forever` is the whole residue of the old rule, and it
costs 204 of the 221 words.** The words it costs are from the half `77c4061` measured as the
colliding half: `node`, `index`, `next`, `stack`, `step`, `count`, `entry`, `table`, `slot`,
`state`. *A loop label is exactly the place a kernel programmer writes `node` or `next`.*

**Reported, not repaired** — `crates/gabbro-syntax/src/parse.rs` is a checker source and this
is a measuring lane. The repair is two lines and it is the same one both times: test
`Art::Ident | Art::Wort(k) if !k.reserviert()`, or reuse the `wort_ist_anweisungskopf`
lookahead (the token after a label is always `bounded`, `until` or `per_pass`, and no name
can be one of those in that position).

### 2.5 Two silent blind spots in the grammar table itself

Both are in `instrumente/pruefe-grammatiktafel.py`, both are stale since `77c4061`, and both
show up in the run's own output. **Reported, not repaired.**

**(a) `:253` drops one word to a whitespace-sensitive regex.**

```python
def kontextuell():
    return {t for t, k in re.findall(r'=>\s*"([^"]+)",\s*(res|ctx);', KW.read_text()) if k == "ctx"}
```

`kw.rs` writes `Ancestors     => "ancestors"  ,   ctx;` with spaces before the comma. The
regex demands `",` and silently drops it:

```bash
python3 -c 'import re,pathlib; kw=pathlib.Path("crates/gabbro-syntax/src/kw.rs").read_text();
print(len(re.findall(r"=>\s*\"([^\"]+)\",\s*(res|ctx);",kw)),
      len(re.findall(r"=>\s*\"([^\"]+)\"\s*,\s*(res|ctx);",kw)))'
# 220 221
```

**The consequence is visible in the run:** the table prints `200 KONTEXTUELLE Woerter` and
`ancestors` is not among them — so today the table calls `ancestors` a reserved word. Its
`gesenkt` state is therefore read as exact where it is an upper bound. *A guard that reads a
source file reads its whitespace too.*

**(b) `:828` prints a hard-coded number that was true until 2026-09-05.**

```python
print("   die anderen 213 sind reserviert, und dort ist ein Vorkommen ein Wort.")
```

**213 became 17 at `77c4061`.** The line is printed under a heading that computes `200` from
the source, so the run prints `200` and `213` side by side over a set of 218. *A false
sentence beside a right number is the most durable form of an error, because every check that
points at the number confirms it* — which is `W25`, invented in this very file's docstring
for this very shape.

Worse than the number: **the sentence the table rests on.** Its head says

> *"Und es ist tragfaehig, weil der Wortschatz GESCHLOSSEN ist. `kw.rs` fuehrt 213 der 222
> Woerter als `res` — reserviert, nirgends ein Bezeichner. **Ein Vorkommen IST damit ein
> Schluesselwort.**"*

That inference is now false for 204 of 221 words. It does not make the table wrong — its
`gesenkt` state was always measured by running the emitter and the C compiler, not by
counting occurrences — but the *justification printed beside the measurement* no longer
holds, and the run says `Fuer sie ist gesenkt eine OBERE Schranke` about 200 words while
calling 213 others exact.

### 2.6 A hole found in the parser that no document could have shown

`item()` at `parse.rs:280` handles `Art::Wort(Kw::Group)`. `faengt_item_an()` at
`parse.rs:4598` — the function recovery uses to find the next item after a refusal — lists 33
words and **omits `Kw::Group`**.

**Measured, three files identical but for the last declaration, each after the same reader
refusal:**

```
module p { atomic A : u32 seq;  fn kaputt(] -> u32 { return 0; }  <LAST> }

<LAST> = group N over { A, A };        ->  P003, "2 items"     <- the group is SWALLOWED
<LAST> = lock  N protects { A } rank 0; ->  P003, "3 items"
<LAST> = rcu   N protects { A };        ->  P003, "3 items"
```

After any earlier refusal in the same file, a `group` declaration is skipped by
`synchronisiere` and never parsed — so `U001`, `U003`, `U005` and `U006` never see it.
`SYNTAX.md:264` lists `gruppedecl` in `item`, the parser implements it, and only the recovery
function disagrees. **A document comparison cannot find this; only the code can.**

The same omission has a second face one line up: the `P006` note at `parse.rs:294` names
twenty item kinds and leaves out **`rcu`, `group` and `entrust`** — so the refusal that says
*"`item` knows: …"* does not know three of the things it knows.

```bash
./target/debug/gabbro pruefe <a file whose first item is broken and whose second is a `group`>
```

**Reported, not repaired.**

---

## 3. THE PLUMBING VERDICT, per form — `instrumente/miss-grammatikdeckung.py`

```bash
ssh ki-pc-fisch-101 'cd gabbro-grammatik && python3 instrumente/miss-grammatikdeckung.py'
```

### 3.1 The test is DIFFERENTIAL, and that is the whole instrument

A form is measured by **two programs that differ in exactly it**: a BASE without it and a
VARIANT with it. Four runs on each — `gabbro pruefe`, `gabbro emit`,
`cc -std=c11 -Wall -Wextra -Werror` at `-O0` **and** `-O2`, and `gabbro pflichten`.

**Why a pair.** `gabbro emit` succeeding says the emitter did not refuse. It does **not** say
the emitter READ the form. Only the difference to a program without the form says that, and
only a byte comparison of the C says it without writing a second emitter beside the emitter
(`W7`).

**This generalises a defect the tree has already paid for.** `SYNTAX.md` said of `when` for
months that it lowers to `#if`; the emitter never read the field, and an item with `when`
produced exactly the same C as one without. *A clause that changes neither the artefact nor
the obligation register is a promise nobody keeps — and it looks kept.* Today `when` is
carried, and this instrument confirms it (`item.when` → CARRIES).

### 3.2 The five verdicts, and why there are five and not four

| verdict | test |
|---|---|
| **REFUSES** | the variant is refused by name — `C001` at the emitter, or a checker error |
| **DEMANDS** | accepted, and `gabbro pflichten` books an obligation the base does not |
| **CARRIES** | the variant's C differs from the base's, and that C compiles at both levels |
| **GUARDS** | no C of its own and no obligation — but a **checker error text names the word** |
| **UNCOVERED** | accepted, lowered, compiles, C byte-identical, no obligation, **and no checker error names it** |

**`GUARDS` is the fifth cell the four-way table was missing, and it is not a softening of
`UNCOVERED`.** `requires` generates no C and books its obligation at the CALL SITE, not at the
declaration; a pointer SPACE has no counterpart in C at all. Judging those `UNCOVERED` because
the artefact does not move would say the language does nothing with a `requires`. *The
generator is one of two ways a language can carry a form; the other is a refusal.*

The word register behind `GUARDS` is **read and not copied** (`W7`): `prueferworte()` out of
`pruefe-grammatiktafel.py`, which already computes *"which words does a checker error name"*
for its own `vom Pruefer` state.

### 3.3 The result

```
   BASIS-ROT       6     1.9 %      the base program itself does not check
   NICHT-GEPROBT 102    32.1 %      no minimal host in this file isolates the form
   NICHT-C         2     0.6 %      it emits, and `cc -Werror` refuses the result
   REFUSES        49    15.4 %
   UNCOVERED      33    10.4 %
   GUARDS         30     9.4 %
   DEMANDS         4     1.3 %
   CARRIES        92    28.9 %

== of 318 derived forms, 210 were measured and 108 could not be ==
   the LANGUAGE carries   122  (58.1 % of the 210 measured, 38.4 % of all 318)
   the USER carries        86  (41.0 % of the 210 measured)
```

**The headline, with its denominator (`W25`):**

> **Over the derived grammar, the language carries 122 of the 210 forms this run could
> measure — 58.1 %. The user carries 86 — 41.0 %. The denominator is 210, not 320: 108 forms
> have no probe in this file yet and 2 more emit C that `cc -Werror` refuses.** Against the
> full derived population of 320 the carried share is **38.4 %**, and the gap between the two
> numbers is this instrument's own incompleteness, not the language's.

`NICHT-GEPROBT` stays in the denominator on purpose. *A denominator that drops what could not
be measured is `W25`.*

The probe population reconciles against the derived one:

```bash
# 320 derived forms, 318 probe entries; 3 forms have no probe, 0 probes name a non-form
# (matchstmt.Some, matchstmt.None, typeexpr_innen.index)
```

### 3.4 `UNCOVERED` — 33 forms nothing in the tree has an answer for

```
andpred.&&  atompred.(  atompred.exists  atompred.forall  axiom.->  eff.allocs  eff.diverges
eff.writes  fndecl.section  intty.in  invariant.online  item.opaque  item.tagged  item.use
letform.:  notpred.!  notpred.=>  orexpr.||  orpred.||  primary.old  range...<  regdecl.fields
right.@  space.boot  space.code  space.mmio  table.backed  table.const  typedecl.=
typedecl.opaque  typedecl.tagged  typeexpr_innen.in  verbund_oder_varianten.(
```

**This cell is a QUESTION LIST and not yet a defect list**, and the distinction is the honest
half of it. Three kinds sit in it and the run does not separate them:

1. **forms whose work is genuinely elsewhere and my probe's single file cannot see it** —
   `primary.old` and `axiom.->` book their obligation at a call site, `space.mmio` is checked
   against a `device` this probe has none of;
2. **forms whose word is spelled differently in the refusal than in the grammar**, so
   `prueferworte()` misses the link — `range...<`, `verbund_oder_varianten.(`;
3. **forms that really are read by nobody.** `intty.in` and `typeexpr_innen.in` — the range
   on an integer type — sit here, and `table.backed` sits here, and those three deserve a
   probe each before anyone calls them either way.

*Naming which of the three each one is takes one program per form and is the next step, not
this one.*

### 3.5 `C001` — 16 forms the checker accepts and the emitter refuses BY NAME

This is the blind spot the brief names, and the run finds sixteen instances:

```
bitpos.[  field_innen.@  field_innen.reserved  field_innen.where  fieldty.embeds  fieldty.scale
format.@  item.format  item.walk  primary.lenof  primary.rounded  primary.sizeof  space.port
typ_oder_ort.intty  typeexpr_innen.never  walkdecl.invariant
```

**`gabbro pruefe` reports zero errors on every one of them and `gabbro emit` refuses by
name.** Two of them are whole item kinds — `format` and `walk`. That `S11 walk.mappings` is a
known half-truth (`emit.rs:2365` generates `walk`, `emit.rs:8666` refuses `mappings of`) is
one instance of a shape this run finds sixteen of.

### 3.6 `DEMANDS` — 4

```
device.transition   fndecl.ensures   table.invariant   transition.requires
```

Four forms that put a new line in `gabbro pflichten` from a single file. It is a low number
and it is a statement about the probe, not about the language: the 84 obligations
`gabbro pflichten` books over the 70 tracked examples arise overwhelmingly **at call sites**,
and a one-file probe has none. **This is the weakest column of the run and is named as such.**

---

## 4. What this document does NOT say

* **A C difference is not a CORRECT lowering.** `cc -Werror` checks the language, not the
  meaning — the grammar table carries the same caveat, in the same words, for the same reason.
* **`CARRIES` means the artefact moved**, not that it moved rightly.
* **`UNCOVERED` is a question, not a verdict** — §3.4.
* **The 108 unmeasured forms are the instrument's debt**, not the language's credit.
* **Nothing here lowers the grammar table's green.** It answers a different question over a
  different population, and both answers stand.

---

## 5. Runs behind this document — and what was NOT run

| run | where | result |
|---|---|---|
| `cargo build` | `ki-pc-fisch-101:gabbro-grammatik` | exit 0 |
| `pruefe-grammatiktafel.py` | server | **GRUEN, 0 von 218 UNGEDECKT**, exit 0 |
| `leite-grammatik.py --zahl` | local (`free -g`: 15 GB available) | 105 rules, 320 forms |
| `leite-grammatik.py --formen` | local | the population, joined against the probe table |
| 32 divergence probes (§2.2, §2.3) | local, one `gabbro pruefe` each | output quoted literally above |
| the `group` recovery triple (§2.6) | local | 2 items against 3 and 3 |
| the `retry`/`forever` label quadruple (§2.4) | local | control green, three `P001` |
| `miss-grammatikdeckung.py` | server, 318 probes × 2 programs × 5 runs | the table of §3.3 |

**NOT run, and each is a real gap:**

* **`cargo test --no-fail-fast`.** This lane wrote no `crates/` code, so nothing it did could
  move a test — but that is an argument and not a run.
* **`abnahme.py`**, in any form. The two new instruments are not in `pruefe-waechter.py` and
  no acceptance run has ever seen them.
* **`pruefe-emission.sh`**, `mutiere-pruefer.py`, `isabelle build`. Untouched, unmeasured.
* **The derived form list against `fuzze-grenzen.py:FORMEN`.** §1 names this as the obvious
  next comparison — a hand-written 63-form dict against a derived 320-form population — and it
  is **not** done here.
* **Probes for the 108 unmeasured forms**, and the three-way split of the 33 `UNCOVERED`
  (§3.4). Both are the next day's work.
* **Any repair.** Five defects are named in §2.4, §2.5 and §2.6 and **not one line of
  `crates/` or of an existing instrument was changed.** This is a measuring lane; the repairs
  are described where they are found and left there.
