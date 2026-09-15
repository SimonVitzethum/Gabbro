# The guardian booked 19 aggregate C values under scalar lemmas — repaired; and the C model extension was PRICED AND REFUSED: it unblocks ZERO programs

**Opus lane `aggregat`. 2026-09-15.** Branch `worktree-agent-a85ce4e034341505d`, base
`dc25e948`. Every `cargo build`, `cargo test --no-fail-fast`, `gabbro emit`,
`gabbro lean-g`, every guardian run and every sweep below was measured on
`ki-pc-fisch-101`, directory `gabbro-opus-agg`.

**Assignment, in two parts.** (1) Repair `instrumente/pruefe-cformen.py`, which classifies by
statement TEXT and therefore books an aggregate C value under a scalar correspondence lemma.
(2) Then decide with a measurement whether the C model should carry aggregates —
*"if it unblocks little, say so and stop after the guardian repair."*

> **Part 1 is done and it found MORE than the census said: 19 occurrences in 15 programs, at
> FOUR destinations, not two. Part 2's honest answer is ZERO, and this lane stopped.** No Lean
> was written, no Rust was changed, `grammatik/` and `crates/` are untouched, and
> `gabbro_ziel` is untouched by construction.

## Files touched

| file | why |
|---|---|
| `instrumente/pruefe-cformen.py` | the repair: the C TYPE decides the row, not the statement text. Four new rows, the aggregate scan, the return-type and aggregate-name tracking, four dated `KNOWN_UNCOVERED` entries |
| `instrumente/zaehle-kette.py` | passes the body context to the shared classifier (it imports `pruefe-cformen.py` as the single source of truth, and without the context it would be a SECOND, text-only classifier); speech test extended, **in both directions** |
| `dokumente/OFFEN.md` | the named absence **O16**, with the measured numbers and the refusal |
| `dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md` | §6.10: sieve (d) 60 → **55**, why it fell, and the obstacle-removed sweep |
| `dokumente/SATZKARTE.md` | §35's figure `(d) 60` struck through to 55, with the reason and the pointer |
| `messung/muse/OPUS-BERICHT-AGGREGAT.md` | this report |

**Nothing else.** `grammatik/`, `crates/`, `beispiele/` and `MARKE_EMIT` were NOT touched —
`git status` is clean on all of them. No diagnostic code was needed and none is reserved. Two
Muse lanes hold `Parser/` and the elaborator and another Opus agent holds
`RufLogik.lean`/`HandlerKongruenz.lean`/`Semantik.lean`; none of those was opened.

Scratch (the census scripts, the before/after comparator, the obstacle-removed probe, the
sweep transcripts) lives in the worktree's gitignored `.claude/kratz-agg/`, never in
`beispiele/` — *a scratch file inside the measured tree is a corpus file.*

---

## 1. THE REPAIR, AND WHAT IT FOUND

### 1.1 The defect, in one line of the model

`CSpeicher.lean` §1 is `CTy := int (sgn : Bool) (w : CWidth) | ptr` and §2 is
`CVal := int | ptr | undef`. **A C cell in this model holds a scalar.** Every place a C type
appears in the certificate's row language takes a `CTy`:

| `GRow` | the emitted C it would have to carry |
|---|---|
| `ret (cr : Option (CTy × CX))` | `return (Nachricht){ .marke = …, .last.Kurz = x };` |
| `bindLet (x) (tc : CTy) (ce)` | `Completion c = fertig(k, 7);` |
| `setVar (x) (tc : CTy) (ce)` / the memory | `p->slots[i].lage = s;` (a whole `Spanne`) |
| `call (fc) (cargs : List CX) (dst)` | `nimm(m);` (a whole `Marke` by value) |

The guardian built its row key from the statement TEXT, so `return c.len;` and
`return (Nachricht){ … };` were the same row `stmt:return-expr` — state (i), naming
`scorr_ret` and `ergCorr_run`. *A guardian that books a form under a lemma that does not
cover it is worse than one that reports it uncovered.*

### 1.2 The repair: the DESTINATION of a value decides

The classifier now knows three things it did not:

* the unit's **aggregate types** — `typedef struct { … } T;` and the union form, brace-counted
  because the emitter nests a union inside a tagged-union struct. **A `typedef enum` is NOT
  one**: an enum is an integer, which `CTy.int` carries — that is exactly why a tagged union's
  `marke` field is fine and its `last` field is not;
* every function's **C return type**, from the definition head and from the prototype;
* every body's **aggregate-typed names** — parameters passed by value, and locals.

A statement is aggregate-classified when it makes a C value of aggregate type FLOW:

| destination | row |
|---|---|
| the return slot | `stmt:return-aggregate` |
| a fresh local | `stmt:bind-aggregate` (`stmt:struct-init` keeps the compound literal, uncovered since 2026-09-13) |
| memory or a variable | `stmt:store-aggregate` |
| a parameter | `stmt:call-aggregate-arg` |

**Two things are deliberately NOT in the list, and the reason is the same principle.**
`(void)x;` on a struct has no destination — the certificate emits no row for it, and
`cCorr_block` (`BlockCorr.pre`) is about the block, not about the value. A POINTER to a
struct (`&v`, `p->f`) is a scalar `CVal.ptr` and stays where it was; `CX.addrL`'s own comment
already says *"a by-value struct local `x.f`"*.

### 1.3 What moved — measured by running BOTH guardians over the same emitted C

Not remembered and not read off the table: `git show HEAD:instrumente/pruefe-cformen.py` was
loaded as a second module beside the repaired one and both classified every statement of all
113 emitted programs (`.claude/kratz-agg/vergleich.py`).

| occ | programs | from | to |
|---|---|---|---|
| **16** | **14** | `stmt:return-expr` **[lemma]** | `stmt:return-aggregate` [uncovered] |
| 1 | 1 | `stmt:bind-call-unit` **[lemma]** | `stmt:bind-aggregate` [uncovered] |
| 1 | 1 | `stmt:store-slot-ptr` **[lemma]** | `stmt:store-aggregate` [uncovered] |
| 1 | 1 | `stmt:call-foreign` **[lemma]** | `stmt:call-aggregate-arg` [uncovered] |
| 2 | 1 | `stmt:bind-call-foreign` [uncovered] | `stmt:bind-aggregate` [uncovered] |

> **19 occurrences in 15 programs were in state (i) — "a correspondence lemma exists" — and
> the lemma was about scalars.**

The 14 programs with an aggregate return: `21-verbundwert`, `40-werte-und-griffe`,
`49-dispatch-tabelle`, `80-bibliothek-erklaert`, `94-uebersetzer-erklaert`,
`95-uebersetzer-vertrag`, `100-hardwareprofil`, `101-hardwareprofil-schluessel`,
`106-summe-uebersetzt`, `107-summe-zwei-rufe`, `111-rufzulassung`,
`120-tagged-construction`, `126-vergleichssortierung`, `127-treiberrueckruf`. The other
three, by name:

```c
21-verbundwert  / laenge_von: Completion c = fertig(k, 7);      -> bind-aggregate
40-werte-und-griffe / vergeben: p->slots[i].lage = s;           -> store-aggregate  (s : Spanne)
54-divergenz-leckt-nicht / abschluss: nimm(m);                  -> call-aggregate-arg (m : Marke)
```

**Two of these four destinations were not in the census this lane was sent with.** The store
of a whole struct into a table slot (`p->slots[i].lage = s;`, booked under
`scorr_assignSlotParam`, M2) and a struct passed by value to a foreign call (`nimm(m);`,
booked under `scorr_axiomCall`, H5) are the same class and were invisible to a text census
that looked for `return (T){` and `T x = f(`.

### 1.4 The three-state census, before and after

| | before | after the repair | after booking the four |
|---|---|---|---|
| forms seen | **77** (51 lemma, 4 assumption, **22** uncovered) | **81** (51, 4, **26**) | 81 (51, 4, 26) |
| occurrences | **1905** lemma, 187 assumption, **400** uncovered | **1886**, 187, **419** | 1886, 187, 419 |
| unclassified statements | 0 | 0 | 0 |
| verdict | **GREEN** | **RED: 4 new uncovered form(s)** | **GREEN** |

**The RED is the finding, and it is the correct outcome.** The four rows were then booked into
`KNOWN_UNCOVERED` dated `2026-09-15`, each with the model reason — *that is the guardian's own
mechanism for a named absence, the same one that carries `stmt:switch-tag` and
`stmt:struct-init` since 2026-09-13*, and it is the only way the red signal stays meaningful
for the next genuinely new emitter shape. The census above is unchanged by the booking: the
occurrences are still in state (iii), they are merely dated.

*The arithmetic closes exactly: lemma −19, uncovered +19, and 2 more moving inside state
(iii). That required one further correction — the two new call-shaped rows had to be added to
`classify_exprs`'s statement-level-call list, or the same call would have been counted a
second time as `expr:call` and the repair would have looked as if it had found expressions it
did not find.*

### 1.5 The speech test, in BOTH directions

`zaehle-kette.py`'s speech test (*"a sieve nobody has seen fail is a decoration"*) now plants a
whole little unit — a `typedef struct`, a `typedef enum`, a struct-returning function and a
scalar-returning one — and demands:

```
  the unit's aggregate types are exactly {P} (the enum is not one): yes
  return (P){ .id = k };            -> stmt:return-aggregate  / uncovered: yes
  P q = baue(1);                    -> stmt:bind-aggregate    / uncovered: yes
  nimm(q);                          -> stmt:call-aggregate-arg/ uncovered: yes
  return p.id;                      -> stmt:return-expr       / lemma:     yes
```

The last line is the counter-direction and it is the one that matters: **the scalar return of
the very same unit must stay where it was.** A guard that only shows the new rows can fire
shows nothing about the old ones.

*The test earned its keep within the hour:* the first obstacle-removed probe of §2 marked the
four rows as covered, and `zaehle-kette.py` **aborted** — `ABBRUCH: the speech test fell --
this run measures nothing`. The probe had to carry a matching copy of the test. A guardian
that refuses a tree in which an aggregate is silently "covered" is the guardian this lane was
sent to build.

### 1.6 A census beside it, so the next lane starts from numbers

| shape | occurrences | programs |
|---|---|---|
| programs emitting at least one `typedef struct`/`union` | — | **83** of 113 |
| function DEFINITIONS whose C return type is a struct | **15** | **14** |
| function NAMES with a struct return type (definitions + foreign prototypes) | **17** | **14** |
| emitted HEAD LINES with a struct return type (each definition also gets a forward prototype) | **32** | **14** |
| `return e;` inside a struct-returning function | **16** | **14** |
| function PARAMETERS of struct type (passed by value) | **20** | **18** |
| bodies with a struct-typed name in scope | **24** | **21** |
| locals of struct type | **6** | **3** |

*This corrects two figures of `OPUS-BERICHT-PRODUKT.md` §3.4, and the correction is this
lane's own point.* Its "8 aggregate returns in 6 programs" counted only the shape
`return (T){ … };`; by the C TYPE there are **16 in 14**, because `return region;` and
`return g;` return a struct too and look like any other return. Its "28 functions in 13
programs returning a struct by value" counted emitted HEAD LINES; by the C type there are
**15 definitions in 14 programs** (32 head lines, because every definition also gets a forward
prototype and two of the functions are foreign). *A count by text is a count of spellings.*

**The 20 struct PARAMETERS get no row of their own, and that is a decision.** A by-value
struct parameter is not a statement, and the guardian's table is statement and expression
forms; its READS already land in uncovered rows (`expr:field`, `expr:union-payload`,
`stmt:switch-tag`), and its flow INTO a call is `stmt:call-aggregate-arg`. What is genuinely
unbooked is the parameter itself at the function head — *named here so the next lane does not
have to find it again.*

---

## 2. THE MEASUREMENT THAT DECIDED THE MODEL QUESTION

> **An aggregate C value unblocks ZERO of 113 corpus programs.**

### 2.1 Method — the obstacle removed, then the SECOND wall

The rule this project learned the expensive way (`OPUS-BERICHT-LINEAR.md` §9,
`OPUS-BERICHT-PRODUKT.md` §1.1): **a census row says which wall a program hits first; it does
not say what removing that wall would gain.** Coverage is multiplicative across the sieves
and inside them.

So the four aggregate rows were given an existing lemma name — *the obstacle removed, the C
model carries an aggregate* — and **the whole 113-program chain sweep was re-run**
(`zaehle-kette.py --dateien …`, `.claude/kratz-agg/sonde-lauf.sh`). The tree was restored
afterwards and the restoration verified by SHA-256 on both instruments.

### 2.2 The result

| sweep | (b) export | (c) certificate | (d) C forms | (e) generic certificate |
|---|---|---|---|---|
| **honest** (repaired guardian) | 15 | 15 | **55** | 2 |
| **obstacle removed** (probe) | 15 | 15 | **60** | 2 |
| before the repair (mis-booking) | 15 | 15 | 60 | 2 |

Sieve (d) returns to exactly 60 and **nothing else moves** — which is also the proof that the
repair's only effect is the reclassification.

**Of the 15 programs that export, NOT ONE fails sieve (d) on aggregates alone.**

| exporting program failing (d) | what it fails on |
|---|---|
| `120-tagged-construction` | `expr:union-payload`, `stmt:decl-union-payload`, `stmt:switch-tag`, **and** `stmt:return-aggregate` |
| `121-tagged-static-init` | `expr:union-payload`, `stmt:decl-union-payload`, `stmt:switch-tag` — no aggregate at all |
| `34-markierter-wert` | the same three — no aggregate |
| `62-grenzwort-im-ausdruck` | `expr:neg` — no aggregate |

`120` is the program the assignment named, and it is the whole case: **its binding constraint
is the tagged-union READ side**, not the aggregate write side. `switch (m.marke)`,
`uint32_t k = m.last.Kurz;` and `m.last.F` have been uncovered since 2026-09-13 with their own
reason — *`gcorr_onTag` is proved but `ValCorr` has no case for a tagged union, so no related
state has a union variable.* An aggregate `CVal` closes none of those three.

### 2.3 The five it WOULD repair are stopped two sieves earlier

Over the whole corpus exactly five programs have the aggregate as their only (d) obstacle. Each
was then asked what stops it at sieve (b) — measured, by running the exporter:

| program | its sieve (b) wall |
|---|---|
| `100-hardwareprofil` | `LG001 assume plattform_takt_stabil has no G form` |
| `101-hardwareprofil-schluessel` | `LG001 requires profile has no G form` |
| `80-bibliothek-erklaert` | `LG001 function kernel is not `impl`` |
| `94-uebersetzer-erklaert` | `LG001 function einsetzen is not `impl`` |
| `95-uebersetzer-vertrag` | `LG001 function einsetzen is not `impl`` |

And the three programs whose *other* three destinations were found in §1.3:

| program | its sieve (b) wall |
|---|---|
| `21-verbundwert` | `LG002 the result of fertig is the record Completion, and a record has NO `Ty`` — **`O15`, priced and refused yesterday** |
| `40-werte-und-griffe` | `LG001 static GERAETEBASIS carries a `section`, which is a PLACEMENT` |
| `54-divergenz-leckt-nicht` | `LG001 type Marke has no `Ty` form, because a mark is a RESOURCE` |

*None of these eight walls is the aggregate, and none of them moves because the C model
learns one.*

### 2.4 And the chain count could not move either

The chain count is a conjunction over (a)…(e) plus a Lean-checked instance. Sieve (a) — the
Lean parser and elaborator (T3) — passes **2 of 113**: `104-referenz` and
`108-disjoint-start-locks`, the two with chain instances. **Neither carries an aggregate
anywhere** (neither appears in §1.3's list, and both keep column (d) = pass in the honest run
and in the obstacle-removed run). So the headline metric is unchanged by the repair and
unchanged by the extension — re-measured with `zaehle-kette.py --lean`, see §4.

### 2.5 DECISION: do not build it

**A model extension that pays for nothing is worse than a named absence** — the rule `O15`
was decided under yesterday, applied to the C side today. What the extension costs is not a
guess: `CTy` and `CVal` stop being flat; the memory of `CSpeicher.lean` has to store a
composite; a struct RETURN needs an **ABI decision the model does not have** (SysV: two
registers, or a hidden pointer); `korrOk` gains one arm per destination, each with a planted
defect; and `korrOk_fnCorr` has to be re-proved sound with its statement kept word for word.
Bought for zero programs.

**What pays first, measured on the same run:** the **tagged-union READ side**. It is what
actually holds `120`, `121` and `34` — the three exporting programs that fail (d) on anything
but `expr:neg` — and `gcorr_onTag` is already proved and merely uninhabitable. *The aggregate
side is necessary for `120` and it is not sufficient for any program.*

The absence is now named with its number (`OFFEN.md` `O16`), with the before-numbers written
down, so the next lane measures a movement instead of remembering one.

---

## 3. What this lane did NOT do, by name

* **The aggregate `CTy`/`CVal`.** Not built, and §2 is the argument rather than a preference.
* **The tagged-union read side.** It is what pays first; it is a `korrOk`/`ValCorr` change and
  `KorrespondenzAllg.lean` is another lane's.
* **`stmt:struct-init`, `stmt:decl-ptr`, `expr:field` and the other 22 uncovered rows.** They
  were uncovered before and are uncovered after; this lane moved no row out of state (iii).
* **`(void)x;` on a struct.** Left in state (i) on purpose, with the reason written into the
  guardian (§1.2). It is the one judgement call in the repair, and it is stated so it can be
  argued with.
* **The historical `(d) 60` bookings.** Five lane reports carry it. They are dated protocol
  and are NOT rewritten; the two live ledgers (`PLAN-UEBERSETZUNGSVALIDIERUNG.md` §6.10,
  `SATZKARTE.md` §35) say 55 with the reason.

## 4. Standards, and where each was measured

All on `ki-pc-fisch-101`, directory `gabbro-opus-agg` (Lean cache seeded from
`~/gabbro-muse/stage/lake3`, Lean runs queued through `~/gabbro-muse/bin/lean-slot`, cargo
with `PATH=$HOME/.cargo/bin:$PATH`; `cargo test` and the Lean runs strictly sequential in the
one tree, because they fight over the same `.olean`).

| standard | result |
|---|---|
| `cargo test --no-fail-fast` | **60 suites `ok`, 0 `FAILED`**, exit 0 |
| `instrumente/pruefe-exportlean.py --dateien beispiele/*.gab` | **EXPORTLEAN: GRUEN** — 15 accepted / 98 refused of 113 by each of the two generators, **30 of 30 exports elaborate, 0 Lean errors**, 1 pasted block byte-identical, 263 568 bytes elaborated |
| `instrumente/pruefe-genlean.py` | **GENLEAN: GRUEN** — 2 of 2 generated files byte-identical, 18 927 bytes compared |
| `instrumente/pruefe-cformen.py` | **GREEN** — 0 new uncovered forms, 0 unclassified statements, 0 missing lemmas, 0 missing assumptions (the four aggregate rows dated `2026-09-15` in `KNOWN_UNCOVERED`; the RED run they came from is §1.4) |
| `instrumente/zaehle-kette.py --lean` (113 programs) | **(a) 2, (b) 15, (c) 15, (d) 55, (e) 2; CHAIN COUNT 2 of 113 — UNCHANGED.** Speech test green in both directions |
| `sorry` / `admit` / `native_decide` / new `axiom` | **none — this lane wrote no Lean at all** |
| `#print axioms gabbro_ziel` | unchanged by construction: `grammatik/` untouched, `git status` clean there |
| `gabbro_ziel` | unchanged by construction, same reason |
| witnesses | none owed: no theorem was stated |

### 4.1 Guardian figures that moved, with their reason

The baseline was **measured, not remembered**: every file this lane changed was put back to its
`HEAD` version and this report moved out of the tree, the guardians re-run, and the tree
restored (`.claude/kratz-agg/grundlinie.sh`; `git status` checked afterwards).

| figure | before | after | reason |
|---|---|---|---|
| `pruefe-zahlen.py` / findings | 27 | **27** | unchanged — this lane's documents add none |
| `pruefe-zahlen.py` / unguarded bold cells outside the five guarded documents | 520 in 105 files | **527 in 106 files** | this report's cells. None of the four edited documents moves it |
| `pruefe-widerruf.py` / files the guardian reads | 557 | **558** | this report |
| `pruefe-todo.py` | 14 findings | **14** | unchanged; the stale README numbers (EBNF rules 170 vs 177, terminals 233 vs 240) were already red at the baseline and are not this lane's |
| `pruefe-grammatiktafel.py` | GRUEN, 0 of 240 terminals uncovered | **GRUEN, 0 of 240** | no EBNF production changed |
| `pruefe-kennungen.py` | ALL PASS, 832 files | **ALL PASS, 832 files** | no new diagnostic code |
| `pruefe-englisch.py` / German comment lines in the checker (a RATCHET) | 7958 (booked 7892) | **7958** | unchanged — **no checker source was touched.** It was already red at the baseline `dc25e948`, at exactly this number |

**The English ratchet was already red at the baseline**, and this lane did not move it and did
not re-cut the ledger. *Booking 7958 into `messung/KENNZAHLEN.md` would book a jump whose
history this lane did not measure* — the same call `OPUS-BERICHT-PRODUKT.md` §5.1 and
`OPUS-BERICHT-LINEAR.md` §7.1 made, for the same reason. `KENNZAHLEN.md` is untouched.

**`messung/KENNZAHLEN.md` does not book sieve (d)**, so the 60 → 55 move needed no entry
there; the two live ledgers that do carry it are updated (`PLAN-UEBERSETZUNGSVALIDIERUNG.md`
§6.10, `SATZKARTE.md` §35).

## 5. The one sentence to carry forward

**An instrument that cannot see a distinction books the claim it cannot check — and the number
it prints falls when you teach it to see, which is not a regression but the first honest
reading.** Sieve (d) was 60 four times in the live ledgers; it is 55, and the five it lost
were never passing anything.
