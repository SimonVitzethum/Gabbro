# A record as a VALUE: the product former was PRICED and REFUSED — it gains ZERO programs

**Opus lane `produkt`. 2026-09-15.** Branch `worktree-agent-a3a844d2c55c4283b`, base
`2648c09b`. Every `cargo build`, `cargo test --no-fail-fast`, `gabbro lean-g`, `gabbro emit`,
`gabbro obligations`, `lake env lean` and every guardian run below was measured on
`ki-pc-fisch-101`, directory `gabbro-opus-prod`.

**Assignment:** decide whether to give a record-as-a-value a form in the specification —
*"measure the decision before making it … if the honest answer is 'it gains little', say so
and stop."* **The honest answer is ZERO, and this lane stopped.** No Lean was written, no
Rust was changed, and the specification is unchanged.

## Files touched

| file | why |
|---|---|
| `dokumente/OFFEN.md` | the new named absence **O15**: a record as a VALUE has no `Ty`, priced and refused, with the measured number |
| `dokumente/SYNTAX.md` | §2 "Attributes and Lean": the type table said a compound is a table with `count 1` and said nothing about the VALUE position. It now does, and names `O15` |
| `dokumente/PLAN-ZIELSATZ.md` | §8: the first extension the rule refused, with the booked before/after obligation number |
| `messung/muse/OPUS-BERICHT-PRODUKT.md` | this report |

**Nothing else.** In particular **`grammatik/`, `crates/`, `instrumente/`, `beispiele/` and
`MARKE_EMIT` were NOT touched.** The probe of §1 was applied to
`crates/gabbro-check/src/lean_g.rs`, measured, and **restored byte for byte** — SHA-256
`a33545f2dc5555245dc4431e527f1d7d68f7c6d1f621d78d1119b300e29fc4a0` before and after, and
`git status` clean on `crates/`. No diagnostic code was needed and none is reserved.

---

## 1. THE MEASUREMENT THAT DECIDED IT

> **A product former in `Ty` would gain ZERO of 113 corpus programs at sieve (b).**

### 1.1 Method — the same one that measured `linear`, and it is not a first-refusal count

The exporter stops at its FIRST refusal, so its census counts *which wall a program hits
first*. `OPUS-BERICHT-LINEAR.md` §9 measured that sieve (b) is itself multiplicative: a
refused program is usually refused by three or four groups at once and only the first is
visible. So the census row is not the answer; the sweep with the refusal skipped is.

Two probes were applied to `lean_g.rs`, both behind environment variables, both reverted:

| probe | what it skips | why |
|---|---|---|
| `GABBRO_PROBE_SKIP_PRODUCT` | the three `refuse_record_value` sites — a record as a RESULT, as a PARAMETER, as a `let` annotation | exactly what a `Ty.prod` would close |
| `GABBRO_PROBE_SKIP_FIELD` | a record FIELD with no `Ty` | **generous on purpose**: those six are arrays and function pointers, which a product former would NOT close. Skipping them bounds the whole record group from above |

Each skip substitutes a placeholder `int 0 0`, so the traversal continues and the NEXT wall
becomes visible. The whole 113-program sweep (`gabbro lean-g` per program, exit 0 and
non-empty output) was run three times: baseline, strict probe, generous probe.

### 1.2 The result

| run | sieve (b) |
|---|---|
| baseline (`2648c09b`) | **15 of 113** |
| with the product-shaped refusals skipped | **15 of 113** |
| with the record FIELD refusals skipped too (generous) | **15 of 113** |

**Seven programs reach a product-shaped refusal. None of them exports once it is skipped.**

| program | first refusal (baseline) | the wall AFTER the skip | product-shaped? |
|---|---|---|---|
| `21-verbundwert` | the result of `fertig` is the record `Completion` | `call in fertig has no G form here` — the constructor; then §1.3 | see §1.3 |
| `111-rufzulassung` | field `senden` of record `Treiber` has no `Ty` (a fn pointer) | `call in baue has no G form here` | NO |
| `126-vergleichssortierung` | field `cmp` of record `Vergleich` (a fn pointer) | `comparison in kleiner has no G form` | NO |
| `127-treiberrueckruf` | field `cb` of record `Rueckruf` (a fn pointer) | `` `narrow` in schreibe has no G form in this fragment `` | NO |
| `49-dispatch-tabelle` | field `bereit` of record `Treiber` (a fn pointer) | `unknown name AUS_BEREIT in hart_bereit` | NO |
| `32-zeichenkette` | field `bytes` of record `Text` (an array) | `place s.len in byte_an has no G form` | NO |
| `56-auftragsring` | field `plaetze` of record `Ring` (an array) | `place r.plaetze[…] in einreihen has no G form` | NO |

An eighth program, `40-werte-und-griffe`, uses a record as a value
(`extern fn gemessene_spanne(i) -> Spanne`, `let s : Spanne = …`) and **never reaches the
refusal**: it stops earlier at `static GERAETEBASIS carries a section, which is a PLACEMENT`,
in both runs. A static census over the corpus (`.claude/kratz-prod/zensus.py`) finds **six**
programs using a record in a value position at all — the upper bound, and the probe confirms
it from the other side.

### 1.3 `21-verbundwert` is the pure case, and it has FOUR walls

It is the one program whose records are all-scalar (`Completion { id : u32, len : u32 }`,
`Marke { wer : Zaehler, fertig : bool }`), so the product former is the whole of its type
problem. It was measured by exporting a record-free rewrite of the same program, one wall at
a time (`.claude/kratz-prod/21-ersatz*.gab`, scratch, never in `beispiele/`):

| # | wall | closed by a product former? |
|---|---|---|
| 1 | `impl fn fertig(k, n) -> Completion` — the result type | **yes** |
| 2 | `return Completion(id: k, len: n);` — the constructor expression | **yes** (it is the former's `Expr`) |
| 3 | `let c = fertig(k, 7);` — *"`let` of a call at the top level has no G form"* | **NO** |
| 4 | `return fertig(k, 7);` — *"call in value position"* | **NO** |

With 1–4 all removed the rewrite exports (exit 0, 199 lines). **Walls 3 and 4 are the
`Endblock`-binder wall, and it is already a named absence:** `OFFEN.md` `O14` (2) says it in
as many words — *"`Block.arenaAlloc` is a `Block` former and a body is an `Endblock` — the
same wall `let x = f()` and `let … else` hit there … closing it needs an `Endblock` form for
the `Block` binders, which is a change to `Syntax.lean`"*. `beispiele/98` and `99` stop at the
same place.

> **The binding constraint on the one program a product would serve is not the product.**

### 1.4 And the chain count could not move either

Sieve (a) — the Lean parser and elaborator (T3) — passes **2 of 113** and binds
multiplicatively (`OPUS-BERICHT-LINEAR.md` §0). A rising sieve-(b) number does not move the
chain count, and here sieve (b) does not rise at all.

**DECISION: do not build it.** A specification extension that pays for nothing is worse than a
named absence, and the absence is now named with its number (`OFFEN.md` `O15`).

---

## 2. What the extension WOULD cost — read from the sources, so the next lane starts from a price

*This section is an argument from the sources, not a measured build failure: no `Ty`
constructor was added and no Lean was compiled with one. It is written down because §8 asks an
extension to be priced, and because the price is the second half of the decision.*

**`Ty` is today entirely NON-RECURSIVE.** All nine constructors take first-order data:
`int (lo hi : Int)`, `bool`, `opt (n : Int)`, `sum (cases : List (Option (Int × Int)))`,
`grund (n : Nat)`, `never`, `fl (lo hi : Int × Int)`, `fnptr (sig : Nat)`,
`ptr (t : Nat) (rw : Bool)`. *That is why the specification has a SUM and no PRODUCT:* a sum's
payload list is `Option (Int × Int)` — data, not types — so `Val … | .sum cs => Σ i : Fin
cs.length, Nutzlast (cs.get i)` is a plain case split. A `prod (fs : List Ty)` makes `Ty` a
NESTED inductive, and then:

| what | where | what changes |
|---|---|---|
| `Val` | `Typen.lean` §2 | a case split becomes a nested recursion (a `ValList` helper or a mutual inductive); `deriving DecidableEq, Repr` re-derived over the recursion |
| `einpassen` | `Semantik.lean` (`(τ : Ty) → Int → Option (Wert D τ)`) | a `.prod` arm decoding a tuple from **ONE raw `Int`**. Constructible as mixed radix over finite component ranges — the `.sum` arm already packs the emitter's C as `roh = marke + \|cases\| * last` — **and it must stay TOTAL** (SATZKARTE §24) |
| `einpassen_voll` | `EinpassenVoll.lean` | every product value is the decoding of some raw word: an encoder and a round-trip proof |
| `antwortTyB` / `antwortTyB_iff` | `EinpassenVoll.lean` | a product is answerable iff every component is — the component `antworten` of `AkzeptiertSpec` (W1) rests on it |
| the `Ty` case splits | **17 arms in 8 files**: `MitRuhe.lean` (6), `EinpassenVoll.lean` (3), `Semantik.lean` (2), `Zielsatz/Ruhe.lean` (2), `Typen.lean`, `MitRuheSemantik.lean`, `CFormenI.lean`, `Parser/Uebersetze.lean` (1 each) | one arm each |
| the two `Expr` formers | `Syntax.lean` | construction and projection, with their typing and their `Expr` semantics |
| the checker Bool | `Zielsatz/Akzeptiert.lean` | the new `Expr` forms in every component that walks an expression — **and `Akzeptiert` is settled by `decide`, so the kernel reduces over the new recursion** |
| the goal theorem | `Zielsatz/Beweis.lean` | every leg of `Ziel` gains a case |

**`gabbro_ziel` would not be WEAKENED by it.** The statement quantifies over all declarations,
so a new `Ty` constructor *enlarges* the set it speaks about — it cannot make the statement say
less. It can make it unprovable until every leg has its case, and `#print axioms` must come out
`propext`, `Classical.choice`, `Quot.sound` again. **That is a re-proof of the goal theorem
bought for zero programs**, and it is the reason the answer is "not now" rather than "later,
cheaply".

---

## 3. The C side — what corresponds, and whether `korrOk` can carry it

*Another Opus agent holds `KorrespondenzAllg.lean`; nothing here touches it. This section says
what that lane would face.*

### 3.1 The C shape, measured

`gabbro emit beispiele/21-verbundwert.gab` writes (verbatim, trimmed):

```c
typedef struct { uint32_t id; uint32_t len; } Completion;

static Completion fertig(uint32_t k, uint32_t n) {
    return (Completion){ .id = k, .len = n };
}
static uint32_t laenge_von(uint32_t k) {
    Completion c = fertig(k, 7);
    return c.len;
}
```

So the correspondence would be: **a plain C struct, one member per field in declaration
order** (no padding beyond natural alignment — the emitter writes no `_Alignas` and no packed
struct); construction is a **compound literal with designated initialisers**, labels
mandatory, which is «B7» and `M106` (`deckt fs zs ↔ map fst zs = fs`,
`beweise/Verbund_Konstruktor.thy`); a local of record type is `Completion c = …` **by value**;
the field read is `c.len` — a dot, not a `->`; and the function **returns the struct by
value**.

### 3.2 `korrOk` cannot carry it today, and the reason is one line deep

`CTy` is `int (sgn : Bool) (w : CWidth) | ptr` (`CSpeicher.lean` §1) and `CVal` is
`int | ptr | undef` (§2). **A C cell in this model holds a scalar.** Every place a C type
appears in the certificate's row language takes a `CTy`:

| `GRow` | what it would have to carry |
|---|---|
| `setVar (x) (tc : CTy) (ce : CX)` / `bindLet (x) (tc : CTy) (ce)` | `Completion c = …;` — `tc` has no aggregate |
| `call (fc) (cargs) (dst : Option (Nat × CTy))` | `Completion c = fertig(k, 7);` — the destination has no aggregate |
| `ret (cr : Option (CTy × CX))` | `return (Completion){ … };` — the returned value has no aggregate |

What the C side *does* already have is the carrier machinery: `RecLay` (a typed record
layout — `count` records of `nf` scalar fields at byte offsets), `CX.fld p off` (`&p->f` /
`&x.f`) and `CX.addrL x`, whose own comment says *"a by-value struct local `x.f`"*. So the
honest answer is:

> **A record VALUE corresponds, at the level `korrOk` speaks, to a stack BLOCK of layout
> `RecLay { count := 1, nf := #fields, … }` with `nf` field stores and `nf` field loads — not
> to one row.** Neither `GRow.setVar` nor `GRow.ret` can carry it. A struct RETURN has no shape
> at all: it is the SysV ABI's business (two registers, or a hidden pointer), and the model has
> no ABI.

### 3.3 And this is ALREADY owed — by a form the specification HAS

`beispiele/120-tagged-construction` is **one of the 15 programs that export today**, and its
emitted C is

```c
static Nachricht baue(bool kurz, uint32_t x) {
    if (kurz) { return (Nachricht){ .marke = Nachricht_Kurz, .last.Kurz = x }; }
    return (Nachricht){ .marke = Nachricht_Leer };
}
```

— a struct returned by value, for a `Ty.sum`. **The aggregate-value problem on the C side is
not the product's; the product would only be the second G form to owe it.** That is an
argument about ORDER, and it points the same way as §1: the C side of aggregate values pays
for `Ty.sum`, which exports, before it pays for a product, which exports nothing.

### 3.4 A guardian that cannot see the difference — found on the way

`instrumente/pruefe-cformen.py` builds its row key from the statement TEXT; the declared C
type is not part of it. **Measured**, by calling the guardian's own `classify_stmt`
(`.claude/kratz-prod/klass.py`), not by reading it:

| emitted line | row | state |
|---|---|---|
| `Completion c = fertig(k, 7);` | `stmt:bind-call-unit` | **lemma** (`bsem_bindCall`, M7) |
| `uint32_t c = fertig(k, 7);` | `stmt:bind-call-unit` | lemma — *the same row* |
| `return (Completion){ .id = k, .len = n };` | `stmt:return-expr` | **lemma** (`scorr_ret`, `ergCorr_run`, S5) |
| `return c.len;` | `stmt:return-expr` | lemma — *the same row* |

Neither lemma is about an aggregate (§3.2). How much is in there, measured over the emitted C
of all 113 programs (`.claude/kratz-prod/aggregat.py`):

| shape | occurrences | programs |
|---|---|---|
| `return (T){ … };` with `T` a `typedef struct` | **8** | 6 (`111`, `120`, `126`, `127`, `21`, `49`) |
| `T x = f(…);` with `T` a `typedef struct` | **3** | 2 (`21`, `40`) |
| `static T f(…)` returning a `typedef struct` | **28** | 13 |

The rows `stmt:return-expr` (287 occurrences) and `stmt:bind-call-unit` (6) include them.
*This is the class `OPUS-BERICHT-LINEAR.md` §4 found in the footprint mirror and the exporter
lane found when it first compiled every export: a measuring instrument that cannot see the
distinction books the claim it cannot check.* **It is reported, not repaired** — it belongs to
`instrumente/`, which a parallel lane holds, and repairing it here would have been a second
topic in one lane.

---

## 4. The numbers `PLAN-ZIELSATZ.md` §8 demands

§8: *"The measure … is `gabbro obligations`: how many of the obligations the extension
generates the checker discharges, and how many it hands to the user. The number is booked
BEFORE and AFTER each extension, on its examples and on the corpus."*

| | BEFORE | AFTER |
|---|---|---|
| `gabbro obligations beispiele/21-verbundwert.gab` | **1** (1 precondition, `open`; 0 refinement, 0 preservation, 0 postcondition, 0 foreign, 0 device, 0 loop invariant, 0 unowned invariant, 0 lock invariant, 0 contract refinement) | **1** — nothing was built |
| the same over the corpus (113 programs, summed closing counts) | **126** | **126** |
| sieve (b), `gabbro lean-g` accepts | **15 of 113** | **15 of 113** |
| CHAIN COUNT | 2 of 113 (`OPUS-BERICHT-LINEAR.md` §0; sieve (a) binds) | unchanged, and untouchable from here |

The before number is written down in `OFFEN.md` `O15` and in `PLAN-ZIELSATZ.md` §8 so the next
lane measures a movement instead of remembering one. *§8's measure could not decide this case
on its own, and that is worth saying: **an extension nothing reaches generates no obligations
at all**, so the deciding number came one step earlier — the sweep of §1.*

---

## 5. Standards, and where each was measured

All on `ki-pc-fisch-101`, directory `gabbro-opus-prod` (seeded with
`cp -a ~/gabbro-muse/stage/lake3 grammatik/.lake`, cargo with `PATH=$HOME/.cargo/bin:$PATH`):

| standard | result |
|---|---|
| `cargo test --no-fail-fast` | **60 suites `ok`, 0 `FAILED`** |
| `instrumente/pruefe-exportlean.py --dateien beispiele/*.gab` | **EXPORTLEAN: GRUEN** — 15 of 113 accepted by each of the two generators, **30 of 30 exports elaborate, 0 Lean errors**, 1 pasted block byte-identical, 263 568 bytes elaborated |
| `instrumente/pruefe-genlean.py` | **GENLEAN: GRUEN** — 2 of 2 generated files byte-identical, 18 927 bytes compared |
| `instrumente/pruefe-cformen.py` | **GREEN** — 0 new uncovered forms, 0 unclassified statements (and §3.4 on what "covered" means for an aggregate) |
| `instrumente/pruefe-kennungen.py` | ALL PASS, 825 files, no new diagnostic code |
| `instrumente/pruefe-widerruf.py` | ALL PASS |
| `sorry` / `admit` / `native_decide` / new `axiom` | **none — this lane wrote no Lean and no Rust at all** |
| `#print axioms gabbro_ziel` | unchanged by construction: `grammatik/` is untouched (`git status` clean there) |
| witnesses | none owed: no theorem was stated |

### 5.1 Guardian figures that moved, with their reason

Measured by running the guardians on the server tree before the three document edits and after.

The baseline was taken by hiding the three edited documents and this report
(`git stash` plus a move out of the tree), re-syncing and re-running — *not by memory.*

| figure | before | after | reason |
|---|---|---|---|
| `pruefe-widerruf.py` / files the guardian reads | 554 | **555** | this report |
| `pruefe-zahlen.py` / unguarded bold cells OUTSIDE the five guarded documents | 512 cells in 104 files | 520 cells in 105 files | this report's eight `\| **n** \|` cells (measured file by file with the guardian's own `KENNZAHL` pattern, `.claude/kratz-prod/kennzahl.py`: the three documents move it by nothing). *The 518 first measured was this table one row shorter — the reckoning counts the report that reports it, and that is not a paradox, only a fixpoint worth naming* |
| `pruefe-zahlen.py` / findings | 27 | **27** | unchanged |
| `pruefe-zahlen.py` / `Kennzahlen mit Befehl` · guarded bold cells | 87 · 152 | **87 · 152** | unchanged — none of the four files is in `BEWACHTE_DATEIEN` |
| `pruefe-todo.py` | 14 findings | **14** | unchanged; the stale README numbers (EBNF rules 170 vs 177, terminals 233 vs 240) were already red at the baseline and are not this lane's |
| `pruefe-englisch.py` / German comment lines in the checker (a RATCHET) | 7958 (booked 7949) | **7958** | unchanged — no checker source was touched |
| `pruefe-englisch.py` / German feeders · German messages at a sink | 30 (booked 26) · 5 (booked 2) | **30 · 5** | unchanged, same reason |
| `pruefe-grammatiktafel.py` | GRUEN, 0 of 240 terminals uncovered | **GRUEN, 0 of 240** | the new SYNTAX.md row is a table row, not an EBNF production |

**The English ratchet was already red at the baseline `2648c09b`**, at exactly these numbers,
and this lane did not move it and did not re-cut the ledger. *Booking 7958 into
`messung/KENNZAHLEN.md` would book a jump whose history this lane did not measure* — the same
call `OPUS-BERICHT-LINEAR.md` §7.1 made, for the same reason. `KENNZAHLEN.md` is untouched.

### 5.2 The probe, and that it left nothing behind

`crates/gabbro-check/src/lean_g.rs` was edited at four sites, built, swept three times and
restored from a copy taken before the first edit. **SHA-256 identical before and after**
(`a33545f2…29fc4a0`), `git status` clean on `crates/`, and the server tree was re-synced and
rebuilt from the restored source before `cargo test`, `pruefe-exportlean.py` and
`pruefe-genlean.py` were run. *A probe measured on a tree that was never restored is a
measurement of the probe.*

Scratch (the probe backup, the sweep scripts, the three `21-ersatz*.gab` rewrites, the census
and classification scripts, the three sweep tables) lives in the worktree's gitignored
`.claude/kratz-prod/`, never in `beispiele/` — *a scratch file inside the measured tree is a
corpus file.*

---

## 6. What this lane did NOT do, by name

* **The product former.** Not built, and §1 is the argument rather than a preference.
* **The `Endblock` binder** (`O14` (2)) — it is what `21-verbundwert` actually needs, it is
  already a named absence, and it is a `Syntax.lean` change, not this lane's.
* **The C side of aggregate values.** `KorrespondenzAllg.lean` and `CFormen*` belong to a
  parallel Opus lane; §3 is written for it and touches nothing.
* **The `pruefe-cformen.py` row key** (§3.4). Reported. `instrumente/` is another lane's.
* **The function-pointer record field.** Four of the seven programs stop there, and `Ty.fnptr`
  **is in the specification** — what is missing is the exporter building `D.sig`/`D.sigNr` for
  a field. That is an exporter lane, not a `Spec.lean` review, and it is the bigger of the two
  record rows.

## 7. The one sentence to carry forward

**Measure what an extension would gain before deciding whether the specification should carry
it — and measure it by re-running the sweep, not by reading the census row.** The census said
"fourteen programs hang on records"; the sweep says a product former gains none of them, and
that the one program it would serve is held by a wall that was already written down as `O14`.
*The cheapest work an extension can do is the work it makes unnecessary.*
