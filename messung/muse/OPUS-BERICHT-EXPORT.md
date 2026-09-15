# Widening the exporter — sieve (b) of the chain

**Opus lane `export`. 2026-09-15.** Branch `worktree-agent-af1187a723d6822c3`, base `6479ea5b`.
Every `cargo build`, `cargo test --no-fail-fast`, `pruefe-emission.sh`, `lake build` and every
`gabbro lean-g` run below was measured on `ki-pc-fisch-101`, directory `gabbro-opus-exp`.

**Assignment:** `instrumente/zaehle-kette.py --lean` measures five sieves per corpus program;
sieve (b) is `gabbro lean-g`, and it covered **10 of 113** programs. Every program the exporter
refuses can never close a chain.

## 0. THE HEADLINE, in the two numbers that must not be confused

| | before | after |
|---|---|---|
| **sieve (b)**, `gabbro lean-g` accepts | **10 of 113** | **12 of 113** |
| exports that COMPILE under Lean | **8 of 10** (never measured before) | **12 of 12** |
| **CHAIN COUNT** | **2 of 113** | **2 of 113** |

**The chain count did not move and could not.** Sieve (a) — the Lean parser and elaborator
(T3) — passes 2 of 113, and it binds; this lane touched only sieve (b). *An export is not a
chain: a program that exports still has to pass the checker Bool, the user's duty and the
certificate, and 111 of 113 still stop at sieve (a), which two Muse lanes are widening.*
Official run, `zaehle-kette.py --lean` on `ki-pc-fisch-101`, 113 tracked programs:

```
sieve totals: (a) 2  (b) 12  (c) 15  (d) 60  (e) 2 of 113
first stopping sieve of the programs without a closed chain: (a) elab: 91, (a) parse: 20
== CHAIN COUNT: 2 of 113 programs have a CLOSED chain ==
```

The booked figure it replaces (`PLAN-UEBERSETZUNGSVALIDIERUNG.md` §6.5, 111 programs):
(a) 2, (b) **10**, (c) 15, (d) 60, (e) 2.

### Files touched

| file | why |
|---|---|
| `crates/gabbro-check/src/lean_g.rs` | every change below |
| `crates/gabbro-check/tests/lean_g.rs` | 11 new probes, both directions |
| `dokumente/OFFEN.md` | **O14** rewritten: what closed, what is still open and why it is a decision |
| `dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md` | §6.5 arena bullet, and the re-measured sieve totals beside the old ones |
| `messung/muse/OPUS-BERICHT-EXPORT.md` | this report |

Nothing else. In particular **`GenOblig104.lean`, `Pflicht104.lean`, the generated obligation
files, `Parser/`, `m1.rs`, `saetze.rs` and `MARKE_EMIT` were NOT touched.** No new diagnostic
code was needed: **`N360`–`N369` and gift numbers `1020`–`1029` are returned unused** — every
refusal added here is an existing `LG00x` with a message that names the form.

---

## 1. THE MEASUREMENT, first — every refusal, grouped by cause

`gabbro lean-g` was run over all **113 tracked** `beispiele/*.gab` (the population
`zaehle-kette.py` uses: `git ls-files` restricted to the top level, not the 797 files the
recursive glob would catch). **10 export, 103 refuse.**

The exporter stops at its FIRST refusal, so this table is *"which sieve stops the program
first"*, not *"everything wrong with it"* — closing a group moves its programs onward to
whatever refuses next, which is why §3 re-measures rather than predicts.

| n | group (first refusal) | class |
|---:|---|---|
| **11** | `LG001 static has no G form` | **(i)** `Deklaration.Glob`/`gtyp`/`Expr.glob`/`Stmt.assignGlob` are in `Syntax.lean`; the exporter writes `Glob := Empty`. 7 of the 11 are scalar statics, 4 declare an ARRAY static, which has no single-`Wert` form — those stay (ii) |
| **11** | `LG002 type X is not an integer range`, `X` a RECORD (`type Zelle = { … }`) | **(i)** `Syntax.lean` §1/§9 says a record is a `Tab` with `count 1`; the exporter builds no such table. A big job (every `x.f` access changes shape), not this lane |
| **9** | `LG001 type X has no G form`, `X` **`opaque`** (`opaque type Pa = u64;`) | **(i)** the alias IS an integer range; `opaque` is a rule about a UNIT BOUNDARY, and `Deklaration` has no boundary — exactly the argument the ledger already makes for `pub` |
| **9** | `LG001 function f is not 'impl'` (`spec fn`, `extern fn`, `prim fn`, `divergent fn`) | **(ii)/(iii)** a foreign body is `D.Ax` and a `spec fn` is substituted; neither has a `Programm.rumpf` |
| **7** | `LG002 type X is not an integer range`, `X` an **exclusive** range (`u32 in 0 ..< N`) | **(i)** `int_ty` returns `None` for `b.exklusiv`; `0 ..< N` is `.int 0 (N-1)` |
| **7** | `LG001 type X has no G form`, `X` **`linear`** (`linear ghost type Marke;`) | **(i)** `D.Marke`/`stufen`/`Res.marke`/`Stmt.advances`/`retires` are all in the spec |
| **5** | `LG001 assume has no G form` | **(i)** `D.Annahme` exists, but is only consumed at `forever` and `retires` |
| **4** | `LG001 format has no G form` | **(i)** `Tab` with `count 1` plus `Block.pruefung` (`Syntax.lean` §9) |
| **4** | `LG001 device has no G form` | **(i)** `D.Reg`/`rklasse`/`Block.regLies`/`Stmt.regSchreib` |
| **4** | `LG005 const X is not a numeral` | **(i)** the constant is an array/aggregate literal, which the `Scope` cannot hold |
| **4** | `LG001 table X carries a form with no G counterpart` (`invariant`, `ops`, `tree`, `occupied`) | mixed: a table invariant is `D.Inv` **(i)**; `tree`/`occupied` are **(ii)** |
| **4** | `LG002 field f has no integer-range or bool form` (`option index into Self`, `wrapping`) | **(i)** for the option (`Ty.opt`, `Expr.some`/`istSome`); **(iii)** for `wrapping` |
| **4** | `LG001 type X has no G form`, `X` **`tagged`** | **(i)** `Ty.sum`, `Expr.fall`, `Stmt.onTag` |
| **3** | `LG001 lock X carries a form with no G counterpart` (`masks irqs`, shared hold) | **(i)** `D.maskiert` exists |
| **2** | `LG004 … runs a floored caller into a floorless callee (RufPasst.hb)` | **EXPORTER DEFECT** — see §5 |
| **2** | `LG001 arena X has no G form YET` (**O14**) | **(i)** by name: `ArenaZucker.lean` has the sugar, the exporter does not build the pair |
| **2** | `LG001 atomic has no G form` | **(i)** `D.atomar`, `Stmt.publish`, `Block.awaits`/`exchange` |
| **2** | `LG006 'traverse' domain is not a table` | **(ii)** a `traverse` over a computed domain has no `Stmt.traverse` form |
| 1 each | `requires profile`, a call in value position, `group`, `accumulates`, a lock protecting an unknown name, `when` on an item, a `let` past its annotation, a `deadline` clause, a float alias | mixed |

**The 10 that export today:** `104-referenz`, `108-disjoint-start-locks`,
`118-sperrinvariante-erhaltung`, `119-sperrinvariante-bloecke`, `130-derived-contract-pure`,
`15-own-traegt-beide-rechte`, `16-by-ops-am-feld`, `62-grenzwort-im-ausdruck`,
`69-integer-conversion`, `73-sugar-widths`.

### 1.1 The work order this table decides

Largest group of class **(i)** first, and the record group is named as (i) but deferred with a
reason:

1. **`static` (11)** — globals. The largest, and the prerequisite for O14.
2. **`opaque` (9) + exclusive range (7)** — two one-line causes, 16 first-refusals between them.
3. **the arena (2)** — `O14`, named in the assignment.
4. **`RufPasst.hb` (2)** — decide defect or rule, with the measurement.
4b. **the catch-all arm** — every remaining item kind refused BY NAME, with the form the
   specification would carry it as (§2.6).
5. **records (11)** — class (i), NOT done here: a record type changes the shape of every
   `x.f` access, the `Tab count 1` lowering, `count`, the footprint and the guard proofs. It is
   a lane of its own and is booked as such, not as an oversight.

*Steps 2 and 4 were in fact run before step 3, because the `hb` question was the only one whose
answer could move the number and the two one-line causes cost nothing. The order of the commits
is the order of the work; the order of this list is the order of the table.*

---

## 2. What was built, group by group

### 2.1 A scalar `static` is a `Glob` — the largest group (11)

`Syntax.lean` §1 says it in as many words: *"ein `const` ist ein Literal, ein `static` ein
`Glob`"*. The exporter wrote `Glob := Empty` throughout.

| surface | G form |
|---|---|
| `static mut X : <int range\|bool> = <lit>;` | `GGlob`/`gtyp`, and the **declared initialiser** as the `gSp0` entry |
| a read `X` | `Expr.glob` under `gdarf` |
| `old(X)` | `Expr.altGlob` |
| `X = e;` | `Stmt.assignGlob`, write right off `effects { writes X }` (`Signatur.gschreibt`) |
| a call | `RufPasst.hg` |
| `lock L protects { X }` | `L` in `gbraucht X`; `ggeteilt X` is true exactly where a lock guards it — the rule the tables already travel under, and the one that discharges `ggeteilt_bewacht` by `decide` |
| the member lists | `gCs` carries globals as `.inr`, `gS.orte` too, and the footprint mirror counts them |

**A slot starts at zero because no surface form names a slot initialiser. A `static` names
one, and zeroing it would have been a silent lie** — so the initialiser travels, checked
against the declared range in Rust.

Refused BY NAME, never by a catch-all:

* an **array static** (`[u8; K]`) — a `Glob` carries ONE `Wert`, not a row (LG002, naming the
  static and the reason); likewise a pointer, a record and a float static;
* a **`section` at a `static`** — a PLACEMENT, and a `Glob` has none (LG001). It used to hide
  behind the blanket `static` refusal: *the same class as `N320` at a function*;
* a write to a global the `effects` do not name (LG004), decided in Rust — a failing
  `by decide` is a Lean error and not a refusal.

**Repaired on the way:** the locks were read DURING the item walk, so a lock whose `protects`
named a carrier declared BELOW it saw an incomplete model. With tables that was a latent
ordering hazard; with globals it fires. Lock declarations are now collected and resolved once
every carrier is in.

**Measured: sieve (b) 10 → 10.** All 11 programs moved past the `static` and stopped at their
NEXT refusal — 4 at the array static (by name), the rest at a device, an `atomic`, a `backed`
table, a `return` under a lock, a top-level `let` of a call. *A group closed is not a program
gained.* Verified instead by a probe with a guarded `static`, a table and three functions:
exported and **compiled** under `lake env lean`, exit 0.

### 2.2 `opaque` and the exclusive range — two one-line causes (9 + 7)

* `opaque type Pa = u64;` was `LG001`. **`opaque` is a rule about a UNIT BOUNDARY** — outside
  the module the definition is not visible, so no arithmetic reaches the range — and
  `Deklaration` has no boundary at all. Word for word the argument the ledger already makes for
  `pub`. The alias IS its range; the drop of the attribute is NAMED in the printed ledger.
  `linear`, `ghost`, `tagged` and `order` still refuse, and a test holds them there.
* `type Idx = u32 in 0 ..< N;` was `LG002`. `int_ty` returned `None` for `b.exklusiv`.
  `lo ..< hi` is `lo .. hi-1` — the same numbers the checker computes with. An EMPTY exclusive
  range (`n ..< n`) still has no `Ty`: it names no value.

**Measured: sieve (b) 10 → 10.** All 16 moved past their first refusal to the next one (mostly
a `tagged` type or a record alias).

### 2.3 The lock floor — a defect, and the one group that moved the number (2)

`beispiele/124` and `beispiele/109` were refused with
`[LG004] … runs a floored caller into a floorless callee (RufPasst.hb)`. The assignment asked
which of the two it is; the measurement answers **both halves**:

**`hb` is a REAL rule.** `Λ` at a call site is the caller's TRACKED held set. The caller's own
untracked extras — locks of rank below its floor, held by ITS caller — are held while the
callee runs and are invisible to `hx`. `hb`
(`∀ c, V.boden = some c → ∃ c', S.boden = some c' ∧ c ≤ c'`) is what carries them across. It is
not weakened here.

**The defect is the exporter's.** `Signatur.boden` is not a measurement of a body; it is a
promise to callers, and its duty is `StufenOk`: `(P.rumpf f).ueberBoden c = true`. In
`Satz.lean` only the `.locks` arm constrains `ueberBoden`, so **a body that takes no lock
satisfies it for EVERY `c`** — its floor is free. The exporter wrote
`taken.map(rank).min()`, which is `none` for such a body: *the one value that promises callers
nothing.* In 124, `hauptA` takes `L` (floor 0) and calls the lock-free `setze`; nothing inside
`setze` can undercut anything, and `hb` refused anyway.

The floor is now the **minimum rank taken anywhere in the reachable call graph**, and `HOCH`
(one above every declared rank) where that set is empty:

* `StufenOk` — at most every rank the body takes directly;
* `hb` — `reach g ⊆ reach f` for every callee, so `floor f ≤ floor g`: never refused for a call
  inside the unit again;
* `hx` — an extra must rank below every rank the callee or its callees take, which is `H006`
  carried across the call boundary.

A unit with no locks keeps `none` throughout. Cycles and recursion are a SET question and are
walked with a worklist.

**Measured: sieve (b) 10 → 12** (`109-lockfree-entry-roots`, `124-two-threads-private`).

### 2.4 The bigger finding, and it came from measuring: four exports never typechecked

Nothing in this tree had ever run Lean over an export. Running `lake env lean` over all ten
generated files found **four failures**, all the same:

> `P130_derived_contract_pure_.lean:138:2: error: Insufficient number of fields for `⟨...⟩`
> constructor: Constructor `Speicher.mk` has 2 explicit field, but only 1 was provided`

`gSp0` printed `⟨fun t => nomatch t, (fun g => nomatch g)⟩` for a table-less unit, and that is
not two fields — **`nomatch` takes a COMMA-SEPARATED list of discriminants** and swallows the
second half. Every table-less export carried it since `gSp0` was introduced (lane 198). Both
halves now stand parenthesised, and a test pins the spelling.

*An export that does not typecheck is a refusal the exporter failed to make* — and the only
instrument that sees it is Lean. The check is a script in the lane's scratch
(`.claude/kratz-export/leanpruef.sh`); **making it a guardian is named in §4 as work this lane
did not do.**

### 2.5 O14 — the arena travels as its PAIR (2)

`ArenaZucker.lean` has carried `alloc`/`reset` as SUGAR since 2026-09-15; the exporter refused
the DECLARATION. It builds the pair now:

| surface | G form |
|---|---|
| `arena A capacity lo .. hi of T` | a table `A` of `count = hi` with one field `wert : T`, a global `A_used : int 0 hi` starting at zero, and `def gArena_A : ArenaForm gD` beside them |
| `reset A;` | `Stmt.arenaReset` |
| `let i = alloc A (v) else { … };` | `Block.arenaAlloc` |
| `A[i]` | the slot read of the one field |
| `effects { writes A }` | the write right on BOTH halves of the pair |

`hz` and `hpos` are decided in Rust and refused by name. **The reservation `lo` travels
nowhere**, as the `alloc` lane planned: it is the checker's static count (`N212`), whose
model-side consequence is already proved (`arenaAlloc_unter_schranke`).

**Two shapes stay refused, each BY NAME:**

1. **An `alloc` WITHOUT `else`.** `Block.arenaAlloc` always carries a full-arena branch; the
   emitted C carries none (`buf[used++] = v;`, no bound check); and what makes the branch dead
   is `N212`, which does **not** travel into the term. *Inventing a `return` the user did not
   write would put a guard into the exported term that neither the source nor the C has, and
   the chain would then compare two different programs.* That is a decision about the emitted
   C, not about the exporter, and it is written into O14 rather than papered over.
2. **An `alloc` at the TOP LEVEL of a body.** `Block.arenaAlloc` is a `Block` former (its first
   half is `Block.narrow`) and a body is an `Endblock` — the same wall `let x = f()` and
   `let … else` hit there.

**Measured: sieve (b) 12 → 12.** `beispiele/98` and `99` stop at shape (2), with the shape and
the reason in the message. Verified instead by a probe with all four forms (`alloc … else`
inside an `if`, `reset`, `A[i]`, the declaration): exported and **compiled** under
`lake env lean`. `Grammatik.ArenaZucker` had to be built first — *no export had ever imported
it.*

### 2.6 No item kind leaves through a catch-all

`collect`'s last arm was `other => "{} has no G form"`. It named the KIND and nothing else:
not the item, not what the specification would carry it as, not what is missing. **Twenty-two
of the 101 remaining refusals came out of it.**

Each kind now has its own arm, naming the item (where the kind has a name) and the
`Deklaration`/`Syntax.lean` form it would travel as — `device` → `D.Reg` +
`Block.regLies`/`Stmt.regSchreib`; `assume` → `D.Annahme`, consumed only at `forever` and
`retires`; `format` → a `Tab` with `count 1` and `where` as `Block.pruefung`; `atomic` → a
`Glob` with `atomar`/`nutzlast` plus publish/awaits/exchange; `group` → a `D.Inv` over more
than one carrier; `accumulates` → a `Glob` plus a generated assignment; `state` → `D.erlaubt`
+ `Stmt.uebergang`; `axiom`/`entrust`/`syscall` → `D.Ax` + `axiomCall`/`bindAxiom`; `check` →
a `Duty` mark consumed by `gates`; `rcu` → a `D.Lock` whose `observes` is `Stmt.locks`;
`walk` → one `Stmt.traverse` per level; `profile` → named assumptions, which `Deklaration`
carries only as `D.Annahme`; `use` → another UNIT, and `Deklaration` has no unit boundary.

Measured on `beispiele/112`:

> `[LG001] device Geraet has no G form: a device is `D.Reg` with
> `rtyp`/`rklasse`/`spiegel`/`rzusage`, and its accesses are
> `Block.regLies`/`Stmt.regSchreib`; this exporter builds no `Reg``

**Measured: sieve (b) 12 → 12** — *a message is not a form.*

---

## 3. What now stops the 101 refusals

Re-measured after every step, same method as §1:

| n | group (first refusal) | class |
|---:|---|---|
| **20** | `type X has no G form` — `linear` (7), `tagged` (4), `ghost`, `order` | (i) `D.Marke`/`stufen`/`Res.marke`/`advances`/`retires` and `Ty.sum`/`Expr.fall`/`Stmt.onTag` are all in the spec |
| **14** | `type X is not an integer range` — a RECORD (`type Zelle = { … }`) | (i) `Syntax.lean` §1/§9: a record is a `Tab` with `count 1`. A lane of its own: every `x.f` access changes shape |
| **11** | `function f is not 'impl'` (`spec`/`extern`/`prim`/`divergent`) | (ii)/(iii) a foreign body is `D.Ax`, a `spec fn` is substituted; neither has a `Programm.rumpf` |
| 6 | `assume` | (i) `D.Annahme` exists, consumed only at `forever`/`retires` |
| 6 | `device` | (i) `D.Reg`/`rklasse`/`Block.regLies`/`Stmt.regSchreib` |
| 6 | table clause (`invariant`, `ops`, `tree`, `occupied`, `owner`, `backed`) | mixed: `invariant` is `D.Inv` **(i)**; `tree`/`occupied` **(ii)** |
| 4 | `format` | (i) `Tab` with `count 1` + `Block.pruefung` |
| 4 | `const X is not a numeral` (array/aggregate constants) | (i) the `Scope` cannot hold them |
| 4 | **array/pointer `static`** | **(ii)** a `Glob` carries ONE `Wert` — new, and the honest answer for those four |
| 4 | field (`option index into Self`, `wrapping`) | (i) for the option (`Ty.opt`), (iii) for `wrapping` |
| 3 | lock clause (`masks irqs`, shared hold) | (i) `D.maskiert` exists |
| 3 | `atomic` | (i) `D.atomar`, `Stmt.publish`, `Block.awaits`/`exchange` |
| 3 | fn clause with no counterpart (`refines`, `maintains`, `deadline`, `by`) | mixed |
| 2 | `traverse` domain is not a table | (ii) |
| **2** | **`alloc` at the top level (O14)** | **(ii)** an `Endblock` form for the `Block` binders is a change to `Syntax.lean` |
| 1 each | `group`, `accumulates`, `use`, `when`, a call in value position, a `requires profile`, a `let` past its annotation, a top-level `let` of a call, a `return` under `locks` | mixed |

**The single biggest remaining class-(i) groups are the `linear`/`tagged` types (20) and the
record type (14).** Both are named here and in §4 as lanes of their own, not as oversights.

---

## 4. What this lane did NOT do, by name

* **`linear`/`tagged` types (20).** Class (i), and the largest group of all — `D.Marke` and
  `Ty.sum` are in the spec with their statements (`Stmt.advances`, `retires`, `onTag`,
  `Expr.fall`). A lane of its own.
* **Records (14).** Class (i): `Syntax.lean` says a record is a `Tab` with `count 1`, but every
  `x.f` access, the `count`, the footprint and the guard proofs change shape with it.
* **A guardian over the Lean-compilability of exports.** `.claude/kratz-export/leanpruef.sh`
  found four broken exports on its first run. It is a scratch script, not an instrument: it
  belongs beside `pruefe-emission.sh`, and until it is there **nothing in the tree notices when
  an export stops typechecking.**
* **An `alloc` without `else`** (O14 shape 1) — a decision about the emitted C, argued in §2.5.
* **The chain count.** Untouched, and it could not be touched from sieve (b).

---

## 5. Every measurement, and where it was taken

All on `ki-pc-fisch-101`, directory `gabbro-opus-exp` (`cp -a ~/gabbro-muse/stage/lake3` seed,
Lean through `~/gabbro-muse/bin/lean-slot`):

| measurement | result |
|---|---|
| `cargo test --no-fail-fast` | **60 suites, 0 failed**, after every step |
| `./instrumente/pruefe-emission.sh` | **ALL PASS — 37 durchgestochen, 264 of 264 translate, 2 reverse probes**, after every step; `MARKE_EMIT`/`_G`/`_M` untouched |
| `lake build` over the whole library | 252 jobs, exit 0 |
| `lake env lean` over every export | **12 of 12 LEAN-OK** (before: 8 of 10) |
| `zaehle-kette.py --lean --dateien …` | (a) 2, **(b) 12**, (c) 15, (d) 60, (e) 2 of 113; **CHAIN COUNT 2 of 113** |
| `sorry` / `admit` / `native_decide` / new `axiom` | **none** — this lane wrote no Lean at all |

The population is passed with `--dateien` because the rsynced tree has no `.git` and
`korpus.py` fails open there: it would count untracked files.

Scratch (`.gab` probes, sweep scripts, measurement files) lives in the worktree's gitignored
`.claude/kratz-export/`, never in `beispiele/` — *a scratch file inside the measured tree is a
corpus file*, and the `alloc` lane paid for learning that.

### 5.1 Guardian figures that moved, with their reason

Measured by running the same guardians over a `git archive 6479ea5b` tree and over this one.

| figure | before | after | reason |
|---|---|---|---|
| `pruefe-zahlen.py` / line continuations | 5353 | **5360** | seven `\` continuations in the new `lean_g.rs` comments |
| `pruefe-zahlen.py` / files the revocation guardian reads | 549 | **550** | this report |

**Both figures were already red at the baseline** (`KENNZAHLEN.md` books 3183 and 299, by 2170
and 250). This lane moved them by +7 and +1 and did **not** re-cut the ledger: writing 5360
there would book a jump whose history this lane did not measure. The `+7` and `+1` are booked
here instead — the same call the `alloc` lane made, for the same reason.

*`pruefe-kennungen.py` reads **409** refusal codes where `KENNZAHLEN.md` books 393. That drift
is NOT this lane's: no diagnostic code was added, `N360`–`N369` are returned unused, and the
baseline tree could not be held against it because `pruefe-kennungen.py` fails its own speech
test inside a `git archive` tree (its poison probe reads `UEBERSEHEN` there). Named, not
claimed.*

---

## 6. The seven commits

1. `MEASURE:` the 113-program sweep grouped by cause — the table of §1, no code.
2. `EXPORT:` a scalar `static` is a `Glob` (§2.1).
3. `EXPORT:` an `opaque` alias and an exclusive range travel (§2.2).
4. `EXPORT:` the lock floor is a CHOICE, and the exporter made the worst one — sieve (b)
   10 → 12, plus the four exports that never typechecked (§2.3, §2.4).
5. `EXPORT:` O14 — the arena travels as its PAIR (§2.5).
6. `REPORT:` this file, plus the re-measured sieve totals in
   `PLAN-UEBERSETZUNGSVALIDIERUNG.md` §6.5.
7. `EXPORT:` no item kind leaves through a catch-all (§2.6).

Nothing was merged and nothing was pushed.
