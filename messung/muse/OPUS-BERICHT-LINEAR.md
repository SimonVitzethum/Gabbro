# The exporter for `linear`/`tagged` types and records — and what the census actually says

**Opus lane `linear`. 2026-09-15.** Branch `worktree-agent-aa13adc03391e15d5`, base `efaa4db3`.
Every `cargo build`, `cargo test --no-fail-fast`, `pruefe-emission.sh`, `lake build`,
`lake env lean` and every `gabbro lean-g` run below was measured on `ki-pc-fisch-101`,
directory `gabbro-opus-lin`.

**Assignment:** close the two biggest class-(i) groups the exporter lane left — the
`linear`/`tagged` types (**20** programs) and the records (**14**) — *after verifying that
classification*. The classification did not survive the verification, and the assignment said
what to do then: *"that is the finding and the work changes shape."*

## Files touched

| file | why |
|---|---|
| `crates/gabbro-check/src/lean_g.rs` | every change below, and its module header (the ledger of deliberate drops) |
| `crates/gabbro-check/tests/lean_g.rs` | 13 new probes, both directions |
| `dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md` | §6.5: the re-measured sieve totals, and the rule for reading the census |
| `messung/muse/OPUS-BERICHT-LINEAR.md` | this report |

Nothing else. In particular **`Parser/`, `m1.rs`, `saetze.rs`, `instrumente/`, `beispiele/`
and `MARKE_EMIT` were NOT touched.** No new diagnostic code was needed: **`N360`–`N369` and
gift numbers `1020`–`1029` are returned unused** — every refusal below is an existing `LG00x`
whose message now names the form.

---

## 0. THE HEADLINE, in the numbers that must not be confused

| | before (`efaa4db3`) | after |
|---|---|---|
| **sieve (b)**, `gabbro lean-g` accepts | **12 of 113** | **15 of 113** |
| exports that ELABORATE under Lean | 12 of 12 | **15 of 15** |
| **CHAIN COUNT** | **2 of 113** | **2 of 113** |

Official run, `zaehle-kette.py --lean --dateien` on `ki-pc-fisch-101`, 113 tracked programs:

```
sieve totals: (a) 2  (b) 15  (c) 15  (d) 60  (e) 2 of 113
first stopping sieve of the programs without a closed chain: (a) elab: 91, (a) parse: 20
== CHAIN COUNT: 2 of 113 programs have a CLOSED chain ==
```

**The chain count did not move and could not.** Sieve (a) — the Lean parser and elaborator
(T3) — passes 2 of 113 and binds; this lane touched only sieve (b). *An export is not a
chain: a program that exports still has to pass the checker Bool, the user's duty and the
certificate, and 111 of 113 still stop at sieve (a), which two Muse lanes are widening.*
**A rising sieve-(b) number beside an unchanged chain count is the honest result.**

---

## 1. THE FINDING, and it is about the census and not about one group

> **A first-refusal count is not a count of programs a lane would gain.**

The exporter stops at its FIRST refusal, so its census counts *which sieve stops a program
first*. The two rows this lane was sent at were the two largest: `linear`/`tagged` (20) and
records (14). **After closing a row, its programs move on to whatever refuses next — and for
these two rows that is almost always a wall from a DIFFERENT group.**

That is measured, not predicted. A scratch probe (`GABBRO_PROBE_SKIP_LINEAR`,
`GABBRO_PROBE_SKIP_RECORD`; applied, measured, reverted) skipped **only the type
declaration** of a `linear`/`ghost` type and of a record alias and re-ran the whole
113-program sweep. The second wall of every program in both rows:

### 1.1 The `linear`/`ghost` row — TEN programs, and the group would gain ZERO

| program | the mark | **the SECOND wall** | its class |
|---|---|---|---|
| `07-eintritt-und-boot` | `linear ghost type BootPhase;` ×5 | `walk Seitentabelle` | (i), another group |
| `114-owner-with-producer` | `linear ghost type Marke;` | `table Plaetze` has an `owner` mark | (i), same family |
| `115-owner-read-with-producer` | `linear ghost type Marke;` | `table Plaetze` has an `owner` mark | (i), same family |
| `58-freiliste-zwei-formen` | `linear ghost type Griff;` | `table Halde` has a `backed` mark | **(ii)** |
| `halde` | `linear ghost type Griff;` | `table Arena` has a `backed` mark | **(ii)** |
| `02-geraet` | `linear ghost type QueuePhase order { setup, live };` | `device Vtd` | (i), another group |
| `22-bootstrecke` | `linear ghost type BootPhase order { … six stages };` | `function melde_roh is not 'impl'` | **(ii)/(iii)** |
| `66-transport-rueckgabe` | `linear ghost type Besitz order { fahrer, geraet };` | `function erzeuge_besitz is not 'impl'` | **(ii)/(iii)** |
| `04-schleifen` | `linear type Angemeldet;` | field `naechst` is `option index into Self` | (i), another group |
| `54-divergenz-leckt-nicht` | `linear type Marke;` | `assume zeitgeber_tickt` | (i), another group |

**Every one of the ten stops again.** Building the whole linear family — `D.Marke`,
`stufen`, `Res.marke` in `Λ`, `Signatur.konsumiert`/`produziert`, `D.eigner`,
`braucht … .inr (m, s)`, `Stmt.advances`, `Stmt.retires`, and the `Untermulti` and
`List.Perm` obligations at every call and every `return` — would move sieve (b) **by zero**.

*The census row said 20; that was the `linear` ten plus the `tagged` ten, and the `tagged`
ten were a different question (§2).*

### 1.2 The record row — FOURTEEN programs, and it is TWO groups with different classes

| program | shape | **the SECOND wall** | class of the record use |
|---|---|---|---|
| `05-nebenlaeufigkeit` | `ptr<normal,rw> Zelle` | `atomic FARBE_FERTIG` | **(i)** carrier |
| `13-zeuge-mit-staerke` | `ptr<normal,rw> Zaehlwerk` | `lock KAPPEN` carries a shared hold | **(i)** carrier |
| `14-paarung-ueber-zwischenfunktion` | `ptr<normal,rw> Bericht` | `atomic FERTIG` | **(i)** carrier |
| `132-raum-am-zeiger` | `ptr<mmio,r> Zelle` | address space in `lies_mmio` | **(i)** carrier |
| `32-zeichenkette` | `Text = { bytes : [u8; KAP], … }` | the ARRAY field itself | **(ii)** field |
| `56-auftragsring` | `Ring = { plaetze : [AuftragNr; N], … }` | the ARRAY field itself | **(ii)** field |
| `111-rufzulassung` | `Treiber = { senden : fn(u8) … }` | the FN-POINTER field itself | **(ii)** field |
| `126-vergleichssortierung` | `Vergleich = { cmp : fn(…) -> bool … }` | the FN-POINTER field itself | **(ii)** field |
| `127-treiberrueckruf` | `Rueckruf = { cb : fn(u32) … }` | the FN-POINTER field itself | **(ii)** field |
| `49-dispatch-tabelle` | `Treiber = { bereit, senden : fn … }` | the FN-POINTER field itself | **(ii)** field |
| `21-verbundwert` | `-> Completion`, `return Completion(id: …)` | **the result type** | **(ii) VALUE** |
| `25-entrust` | `entrust jitpuffer at Gastbild` | `assume gast_bleibt_in_seinem_raum` | — |
| `70-kernel-namen` | declared, not dereferenced | `function ueberschritten is not 'impl'` | — |
| `26-gleitkomma` | **not a record at all** — `type Anteil = f64 in 0.0 .. 1.0;` | `const TAU is not a numeral` | float alias |

**Two corrections to the census in one row.** The row was booked as fourteen records of class
(i); it is at most thirteen records, in two classes, plus a float alias that was never a
record:

1. **A record as a CARRIER is class (i).** `Syntax.lean` §1/§9 says it in as many words:
   *"ein `format` und ein Verbund sind Tabellen mit `count 1`"*. **Built** (§3).
2. **A record as a VALUE is class (ii), and no exporter work changes that.** `Typen.lean` §1
   lists every `Ty` there is — `int`, `bool`, `opt`, `sum`, `grund`, `never`, `fl`, `fnptr`,
   `ptr` — and **there is no product**. `impl fn fertig(k, n) -> Completion` with
   `return Completion(id: k, len: n);` and `let c = fertig(k, 7);` name no type the
   specification can carry. Closing it needs a new `Ty` constructor, reviewed as a diff of
   `Spec.lean` — not a lane of the exporter. **Refused by name** (§3.2).

---

## 2. What was built — `tagged`, the one group that moved the number

`tagged type N = { Leer, Kurz(u32 in 0 .. 100), Lang(u64) };` was
`LG001 type N has no G form`, and that stopped TEN programs at the declaration, before the
exporter had looked at a single statement. Everything it needs is in the specification:

| surface | G form |
|---|---|
| `tagged type N = { … }` | `Ty.sum cs`, where `cs : List (Option (Int × Int))` is the cases in DECLARATION order |
| `Kurz(x)` | `Expr.fall cs ⟨i, _⟩ (.zahl x)` — the payload fitted to exactly the case's range |
| `Leer` | `Expr.fall cs ⟨i, _⟩ .keine` |
| `match m { … }` | `Stmt.onTag` with an `Arms` list of ONE block per case, in that same order (`ArmCtx` pushes the payload of a case that has one) |
| `m : N` as a parameter, `-> N` as a result | `Signatur.params` / `erg` |
| `was : N` as a slot field | `D.typ t f = .sum cs` |
| `static ANFANG : N = Kurz(5);` | a `Glob` of `.sum cs`, and `gSp0` at the case the `static` NAMES |
| a `tagged` slot with no initialiser | case 0, payload zero — the same rule that starts every integer slot at zero, because no surface form names a slot initialiser |

**A case is its POSITION.** The case NAMES do not travel, so the source order of the `match`
arms does not travel either — only their assignment to cases. `D005` (exhaustive, no
catch-all) stays the checker's; what is checked here is what the TERM needs: exactly one arm
per case, because `Arms` has exactly that shape.

**Refused BY NAME, never by a catch-all:**

* a case payload that is not ONE integer range — `Nutzlast` is `Option (Int × Int)`, so a
  `bool`, a pointer, a record, a float or a nested tagged payload has none (LG002);
* a case name that two tagged types share — the exporter translates bottom-up and has no
  expected type to pick the `Ty.sum` with, and guessing would build a value of the wrong type
  (LG005);
* a `match` over an `option` or a reason — `Stmt.onOption` (with `Ty.opt`, `Expr.some`,
  `Expr.istSome`) and `Stmt.onGrund` are their forms, and neither is built here (LG004);
* a `tagged` type that is also `linear`/`ghost` — a `Ty.sum` is a VALUE and a `D.Marke` is a
  RESOURCE, and no `Deklaration` field carries both (LG001).

**Measured: sieve (b) 12 → 15** — `120-tagged-construction`, `121-tagged-static-init`,
`34-markierter-wert`. The other seven moved on: `01-tabelle` to a `wrapping` field,
`08-bereiche` to an array `static`, `09-ohne-zeiger` and `40-werte-und-griffe` to another
alias, `39-auftragsdienst` to a `linear` type, `41-handschlag` to a device, `42-zaehlwerk` to
a table clause.

### 2.1 A poison probe that exported cleanly, and why that was the right answer

The probe for the empty case list (`tagged type N = { };`) **exported with exit 0**. The
reason was upstream: the READER refuses `{ }` with `P035` — *"neither a record nor a sum
type"* — and the item never survives the parse. The exporter's own guard stays, as a SECOND
reader of that rule and as what makes `cases[0]` (the `sp0` value of a `tagged` slot) total;
the test now pins the reader, where the rule lives. *A poison probe that does not fire is a
measurement about the tree, and it has to be followed up rather than deleted.*

---

## 3. What was built — the record as a CARRIER, and the record as a VALUE by name

### 3.1 `Tab` with `count 1` (class (i))

The record NAME becomes the table name, each record field a slot field, and the one slot is
index `0`:

| surface | G form |
|---|---|
| `type Zelle = { wert : u32, fertig : bool };` | `Tab Zelle`, `count Zelle = 1`, `GZelleFeld` with one constructor per field |
| `p->f` | `Expr.durch p Zelle rfl f (.lit 0)` under the table's guards |
| `p->f = e;` | `Stmt.assignDurch` |
| `ptr<normal, rw> Zelle` | `Ty.ptr n true`, `D.tabNr n = some Zelle` |
| `effects { writes p }` (bare, at a record pointer) | `Signatur.schreibt Zelle` |

A **table** pointer still has to name `p.slots` — a table has more than one slot, and naming
the pointer would say less than the surface does. `p->f` through a pointer to a real table is
refused by name.

**Refused BY NAME:** a record field that is no `Ty` (an array, a nested record, a float, a
function pointer — `D.typ t f` is ONE `Ty`, and `Typen.lean` has no product and no row); a
record with no field (a `Feld` type needs a constructor); a record field carrying a `format`
clause (`@bitpos`, `offset_into`, `where`, `reserved`), whose forms are `Expr.leseBytes` and
`Block.pruefung`.

**Measured: sieve (b) 15 → 15**, exactly as §1.2 predicted before the work started. Verified
instead by a probe — a record read, written and re-written under an `if`, through both an `r`
and an `rw` pointer — which exports and **elaborates under `lake env lean`, exit 0**.

### 3.2 The record as a VALUE — class (ii), said out loud

The old message was `result of fertig has no integer-range or bool form`. That is true and
useless: it does not tell a user that a record is not a `Ty` **at all**. The refusal now
names the position (result / parameter / `let` annotation), the record, the reason
(`Typen.lean` §1 has no product) and **the carrier form that does work** (pass a
`ptr<normal, r> Completion`).

### 3.3 The type arm was the last catch-all of its kind

The exporter lane of 2026-09-15 gave every ITEM kind its own arm with the form the
specification would carry it as. The TYPE arm never got that treatment: five different shapes
came out as `type X is not an integer range`, and the whole linear family as `type X has no G
form`. Each now names its form: a float alias `Ty.fl` with fractional bounds, an array alias
a `Tab`, a function-pointer alias `Ty.fnptr n` with `D.sig`/`D.sigNr`, a pointer alias
`Ty.ptr t rw` with `D.tabNr`, `never` as `Ty.never`, a variant list without the `tagged` word
as the missing word — and the linear family as `D.Marke`/`stufen`/`Res.marke`/
`konsumiert`/`produziert`/`advances`/`retires`, **with the reason a mark is not a `Ty`: it is
a RESOURCE held in `Λ`, so the surface `fn f(m : Marke)` has no parameter to travel as, only
a `konsumiert` entry.** *A message is not a form — §1.1 is what says the form would buy
nothing today, and the message is what a user can act on meanwhile.*

---

## 4. A defect found BY LEAN, and by nothing else

The footprint mirror in Rust (`foot_block`, `foot_fn`) decided which places are carrier
accesses by counting suffixes: `T.slots[i].f` is three. A record access `p->f` is ONE, so the
mirror **saw no carrier at all**. `fuss_holds` therefore said the old footprint check passes,
and the export printed

```lean
example : fussOrtGB gP gFs = true := by decide
```

— which Lean **disproved**:

> `error: Tactic 'decide' proved that the proposition fussOrtGB gP gFs = true is false`

**A mirror that undercounts refuses nothing; it prints a false claim.** Both sites now read
one helper (`ist_traegerzugriff`), and a test pins both directions: a guarded record prints
the claim, a written lock-free one does not. *This is the same class the exporter lane found
when it compiled every export for the first time — an export that does not typecheck is a
refusal the exporter failed to make — and it is the second instance in two days.*

---

## 5. What now stops the 98 refusals

Re-measured after every step, same method as §1:

| n | group (first refusal) | class |
|---:|---|---|
| **12** | `type X has no Ty form` — the LINEAR family (`linear`, `ghost`, `order`) | (i) in the spec, **worth 0 programs** (§1.1) |
| **12** | `function f is not 'impl'` (`spec`/`extern`/`prim`/`divergent`) | (ii)/(iii) a foreign body is `D.Ax`, a `spec fn` is substituted; neither has a `Programm.rumpf` |
| 7 | `device` | (i) `D.Reg`/`rklasse`/`Block.regLies`/`Stmt.regSchreib` |
| 7 | `assume` | (i) `D.Annahme`, consumed only at `forever`/`retires` |
| **6** | **record field with no `Ty`** (array ×2, fn pointer ×4) | **(ii)** — named, and it is the honest answer for those six |
| 6 | table clause (`invariant`, `ops`, `tree`, `occupied`, `owner`) | mixed: `invariant` is `D.Inv` (i); `tree`/`occupied` (ii) |
| 5 | `atomic` | (i) `D.atomar`, `Stmt.publish`, `Block.awaits`/`exchange` |
| 5 | `static` without a `Glob` form (array/pointer ×4, a `section` ×1) | **(ii)** a `Glob` carries ONE `Wert`; a `section` is a PLACEMENT |
| 4 | `lock` clause (`masks irqs`, shared hold) | (i) `D.maskiert` exists |
| 4 | `format` | (i) `Tab` with `count 1` + `Block.pruefung` |
| 4 | `const X is not a numeral` (array/aggregate constants) | (i) the `Scope` cannot hold them |
| 3 | fn clause with no counterpart (`refines`, `maintains`, `deadline`, `by`) | mixed |
| 3 | field (`option index into Self` ×2, `wrapping` ×1 …) | (i) for the option (`Ty.opt`), (iii) for `wrapping` |
| 2 | `wrapping` field | (iii) |
| 2 | `traverse` domain is not a table | (ii) |
| 2 | `alloc` at the top level (O14) | (ii) an `Endblock` form for the `Block` binders changes `Syntax.lean` |
| **1** | **record as a VALUE** (`21-verbundwert`) | **(ii)** `Ty` has no product former |
| 1 each | `group`, `accumulates`, `use`, `when`, `backed`, `requires profile`, the `mmio` address space, a float alias, a call in value position, a `let` past its annotation, a top-level `let` of a call, a body that falls off with a result | mixed |

---

## 6. What this lane did NOT do, by name

* **The linear family.** Class (i) in the specification and **built nowhere**. §1.1 is the
  argument: ten programs, ten second walls, zero gained. It is written into the module header
  with every field it would travel in, so the next lane starts from the measurement and not
  from the census row.
* **A record as a VALUE, an array field, a function-pointer field.** Class (ii): each needs a
  `Ty` the specification does not have, and that is a `Spec.lean` review, not an exporter lane.
* **`Stmt.onOption` and `Stmt.onGrund`.** Both exist in `Syntax.lean`; a `match` over an
  `option` or a reason is refused naming them. `Ty.opt` at a field is the (i) group behind it.
* **A guardian over the Lean-compilability of exports.** Still a scratch script
  (`.claude/kratz-lin/leanpruef.sh`), and it found its second defect on this branch (§4). A
  parallel Opus agent holds `instrumente/` for exactly this; nothing here duplicates it.
* **The chain count.** Untouched, and it could not be touched from sieve (b).

---

## 7. Every measurement, and where it was taken

All on `ki-pc-fisch-101`, directory `gabbro-opus-lin` (`cp -a ~/gabbro-muse/stage/lake3` seed,
Lean through `~/gabbro-muse/bin/lean-slot`, cargo through `bin/cargo-slot`):

| measurement | result |
|---|---|
| `cargo test --no-fail-fast` | **60 suites, 0 failed**, after each group |
| `./instrumente/pruefe-emission.sh` | **ALL PASS — 37 durchgestochen, 264 of 264 translate, 2 reverse probes**, after each group; `MARKE_EMIT`/`_G`/`_M` untouched |
| `lake build` over the whole library | 254 jobs, exit 0 |
| `lake env lean` over every export | **15 of 15 LEAN-OK** (before: 12 of 12) |
| `lake env lean` over the two scratch probes | record carrier: exit 0 |
| `zaehle-kette.py --lean --dateien …` | (a) 2, **(b) 15**, (c) 15, (d) 60, (e) 2 of 113; **CHAIN COUNT 2 of 113** |
| `sorry` / `admit` / `native_decide` / new `axiom` | **none** — this lane wrote no Lean at all |

The population is passed with `--dateien` because the rsynced tree has no usable `.git` and
`korpus.py` fails open there: it would count untracked files. It is `git ls-files` restricted
to the top level of `beispiele/` — **113** files, the same population the counter uses.

Scratch (`.gab` probes, sweep scripts, the baseline tree, measurement files) lives in the
worktree's gitignored `.claude/kratz-lin/`, never in `beispiele/` — *a scratch file inside the
measured tree is a corpus file.*

### 7.1 Guardian figures that moved, with their reason

Measured by running the same guardians over a `git archive efaa4db3` tree and over this one.

| figure | before | after | reason |
|---|---|---|---|
| `pruefe-englisch.py` / line continuations | 5375 | **5426** | 51 `\` continuations in the new `lean_g.rs` comments and test snippets |
| `pruefe-englisch.py` / German comment lines in the checker (a RATCHET) | 7948 | **7958** | +10 — see below |
| `pruefe-widerruf.py` / files the guardian reads | 551 | **552** | this report |

**The first and third were already red at the baseline** (`KENNZAHLEN.md` books 3183 and 299).
This lane moved them by +51 and +1 and did **not** re-cut the ledger: writing 5426 there would
book a jump whose history this lane did not measure. The `+51` and `+1` are booked here
instead — the same call the two lanes before it made, for the same reason.

**The German ratchet is a real one, and it was measured against the base tree, not assumed.**
The first run of this lane put it at **7963** and the German-prose ratchet at **31 (from 30)**
— *the second ratchet is the one that matters, because a DIAGNOSTIC must be English*, and the
one new entry was a refusal message containing `Expr.durch`, which the guardian's word list
reads as German. The message was rewritten to name the surface spelling that works
(`T.slots[i].f`) instead of the constructor, and the prose ratchet is **back at 30, the
baseline**. The remaining **+10 comment lines** are English sentences containing Lean
constructor names (`.keine`, `.durch`, `.hier`) plus the ONE German sentence of `Syntax.lean`
this lane quotes — quoted once, in the module header, after the other three copies of it were
replaced by a reference. *Both numbers were found by running the guardian over a
`git archive efaa4db3` tree beside this one; neither was noticed by the build.*

*`pruefe-gruende.py` reads **9 verdächtig · 177 tragend · 162 unklar** on both trees:
unchanged. `pruefe-kennungen.py` reads 409 refusal codes on both: no diagnostic code was
added, and `N360`–`N369` are returned unused. `pruefe-englisch.py` exits `1` on both trees,
at the same stage, for the same pre-existing reason.*

---

## 8. The three commits

1. `EXPORT:` a `tagged type` travels as `Ty.sum` — sieve (b) 12 → 15 (§2).
2. `EXPORT:` a record is a `Tab` with `count 1`, and as a VALUE it is class (ii)
   (§1, §3, §4).
3. `REPORT:` this file, the re-measured sieve totals and the census rule in
   `PLAN-UEBERSETZUNGSVALIDIERUNG.md` §6.5, and the diagnostic reworded back under the
   German-prose ratchet (§7.1).

Nothing was merged and nothing was pushed.

---

## 9. The one sentence to carry forward

**Sieve (b) is itself multiplicative.** The chain census already says coverage is
multiplicative across the five sieves; this lane measured that it is multiplicative *inside*
sieve (b) too. A program refused by the exporter is usually refused by three or four groups
at once, and only the first is visible. **Closing the largest row therefore buys nothing on
its own** — which is an argument for finishing groups in the order that clears whole
PROGRAMS, not in the order of the row counts. The programs closest to exporting today are the
ones whose remaining walls are all class (i): that list is what the next exporter lane should
be given, and this report's §1.1 and §1.2 are the first two rows of it.
