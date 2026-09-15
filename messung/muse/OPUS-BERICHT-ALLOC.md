# `alloc` and `reset`: the specification gets a form, the exporter gets a name

**Opus lane `alloc`. 2026-09-15.** Branch `worktree-agent-a4f53e372fd491f96`, base `21734817`.
Every Lean build, `cargo build`, `cargo test --no-fail-fast`, `pruefe-emission.sh` and every
`gabbro` run below was measured on `ki-pc-fisch-101`, directory `gabbro-opus-alloc`
(and `gabbro-opus-alloc-basis` for the baseline). The text guardians ran locally, against two
trees built from `git archive HEAD` — the split `CLAUDE.md` draws.

**Assignment:** `messung/muse/OPUS-BERICHT-GRAMMATIK-EMIT.md` §5.3 item 7 — *"The arena
statements have no constructor at all, so no program using `alloc`/`reset` can ever close a
chain — and nothing says so at the site."*

---

## 1. THE MEASUREMENT, first

### 1.1 Who uses the two statements

| file | what it does | `gabbro pruefe` |
|---|---|---|
| `beispiele/98-arena-erklaert.gab` | `arena Log capacity 2 .. 8 of u32`; three `alloc` (one with `else`), one `reset`, one more `alloc`, one read | **3 items, 0 errors, 0 hints** |
| `beispiele/99-arena-grenze.gab` | two arenas (`capacity 2 .. 2`, `capacity 0 .. 4`), five `alloc` (two with `else`), one `reset`, five reads | **4 items, 0 errors, 0 hints** |
| `beispiele/gift/885-arena-verkehrte-schranke.gab` | `capacity 8 .. 2` — declaration only | expects `N210` |
| `beispiele/gift/886-arena-alter-index.gab` | index read across a `reset` | expects `N211` |
| `beispiele/gift/887-arena-ohne-else.gab` | second `alloc` past the reservation, no `else` | expects `N212` |
| `beispiele/gift/888-arena-unbekannt.gab` | `reset Nirgendwo;` | expects `N213` |
| `beispiele/gift/889-arena-fremder-index.gab` | an index of `A` read on `B` | expects `N214` |

`programmlogik/gabbrov/V1.lean` matches on the word for other reasons and is not a user.

### 1.2 What the Rust checker demands

`crates/gabbro-check/src/arena.rs`, **756 lines**, four rules, each with its own poison probe:

| code | rule |
|---|---|
| `N210` | both bounds are constants with `0 ≤ lo ≤ hi`, and `hi` fits the emitted counter |
| `N211` | no use of an index outside its generation (a branch that resets on one side takes a fresh generation at the join) |
| `N212` | the `else` is owed exactly when the static count since the last `reset` may exceed the reservation |
| `N213` | `alloc` and `reset` name a declared arena |
| `N214` (in `m1.rs`) | an index belongs to the arena it is read on |

Effects: `writes A`. Costs: counted like `costs`. The per-function static count saturates at
`UNENDLICH` inside a loop; a reservation shared across functions is named as **not** covered.

### 1.3 What the emitter writes

| source | C | `cc -std=c11 -Wall -Wextra -Werror`, -O0 and -O2 |
|---|---|---|
| `let i = alloc A (v);` | `A_arena_speicher.buf[A_arena_speicher.used++] = (v);` | compiles |
| `reset A;` | `A_arena_speicher.used = 0;` | compiles |
| `arena A capacity lo .. hi of T` | a static array `buf[hi]` beside a `uint32_t used` | compiles |

`./instrumente/pruefe-emission.sh` on the whole corpus: **ALL PASS, 37 durchgestochen, 264 of 264
translate, 2 reverse probes** — unchanged by this lane.

### 1.4 What the model could already say

`grammatik/Grammatik/Arena.lean`, **262 lines, 12 theorems**, is a self-contained typed model:
`Arena k g` (used ≤ `hi` by construction), `ArenaIdx g n`, `Marke g` with a private constructor,
`alloc`, `reset`, `allocSeq`, `alloc_innerhalb_reserve`, `keine_fragmentierung`, `reset_used`,
`reset_verbraucht`. **It imports nothing from the grammar and nothing imports it**: it had no tie
to `Syntax.lean`, and its own CUTS section says `lookup` returns the slot POSITION, not a stored
value.

### 1.5 THE PART OF THE FINDING THAT DID NOT SURVIVE MEASUREMENT

*"Nothing says so at the site"* is **false for every chain-producing tool**, and this was probed
in four statement contexts (top level; inside an `if` branch; inside a `traverse` body;
`reset` alone, no `alloc`):

| tool | verdict on `beispiele/98` — before this lane |
|---|---|
| `gabbro lean-g` | `[LG001] arena has no G form` (at the DECLARATION, so the whole unit) |
| `gabbro obligations --g` | the same `LG001` |
| `gabbro certificate` | `function nutzen: REFUSED CS001: alloc has no printable CertStmt shape` |
| `gabbro corr-lean` | `GREFUSAL: statement 'alloc': no general row` + `KREFUSAL` |
| `instrumente/zaehle-kette.py` | `[.FFF0] 98-arena-erklaert.gab: no chain instance` |

**So the hole was loud at the gates and silent in the ledger.** What was actually missing was
(i) an entry in `dokumente/OFFEN.md`, the file whose stated purpose is *"so that an absence
cannot be mistaken for an oversight later"*, and (ii) a refusal a reader can act on: the arena
arm of `lean_g.rs` was the **catch-all** `other => "{} has no G form"`. *A catch-all that happens
to fire stops firing, without a word, the day an arm is added above it* — the same class as the
wildcard branches CLAUDE.md records.

### 1.6 The cost of the two routes the task named

**(a) two `Stmt` constructors, measured:**

| what moves | measured |
|---|---|
| `Stmt` constructors today | 26 |
| Lean files naming `assignSlot` | **79** |
| occurrences of the single leaf `retGrund` | **252**, across 30 files |
| `World` fields an arena would need | a slot store (the table half is there) **plus a new carrier kind** — every frame lemma in the tree is stated on `World.slots`/`World.globs` |

Two new constructors are two new arms in the semantics, the machine `G`, race freedom, deadlock,
`FortschrittG`, cost, the invariant families, non-interference and the goal proof; a new carrier
changes `World` and moves every frame lemma. **That is a programme of work, not a lane.**

**(b) refuse `alloc`/`reset` by name in the checker, measured:** **2 clean corpus programs fall**
(98, 99), **5 poison probes change code** (885–889), and it orphans a proved Lean model
(12 theorems), four checker rules, 756 lines of `arena.rs`, and the EBNF of `SYNTAX.md` §9.1
(`arena`, `allocstmt`, `resetstmt`, and the words `arena capacity alloc reset`). The task's own
test — *"if it is more than a handful, (a) is the honest route and (b) is a retreat"* — plus
§1.5's finding that the gap was already named at all four gates, settles it: **(b) would pay a
feature for a message that already exists.**

---

## 2. THE DECISION: (a), by the route the measurement points at — SUGAR

**`Stmt` does not grow. `Zucker.lean`'s idea does.**

An arena is, in the specification, a pair the language already has — *and it is literally the pair
the emitter writes*:

* a table `tab` with `count tab = hi` and one field `feld : T` — the slots, `buf[hi]`;
* a global `zaehl` of type `int 0 hi` — the `used` counter.

```
reset A;                        =  zaehl = 0;                        Stmt.assignGlob
let i = alloc A (v) else B;     =  narrow zaehl into 0 ..< hi, else B;   Block.narrow
                                   tab.slots[i].feld = v;            Stmt.assignSlot
                                   zaehl = i + 1;                    Stmt.assignGlob
```

`Block.narrow` IS the emitted guard: the value fits the range, or the `else` branch runs and does
not fall through — the same promise the surface `else` carries.

**Because it is sugar, an arena program is an ordinary `Block` term, so `theorem gabbro_ziel`
covers it with no new case and no re-proof.** That is the whole content of the decision.

### 2.1 What was built — `grammatik/Grammatik/ArenaZucker.lean` (new, 544 lines)

| name | what it is |
|---|---|
| `Wert.umTyp`, `Expr.umTyp` | the two transports of the counter's declared type; every use is confined here |
| `eval_umTyp`, `orte_umTyp`, `Wert.umTyp_hin_her`, `World.globs_lese` | the four lemmas that make them harmless — each by `subst`, which works because both sides are variables in the lemma's own statement |
| `ArenaForm D` | `tab`, `feld`, `zaehl`, `hz : D.gtyp zaehl = int 0 (D.count tab)`, `hpos : 0 < D.count tab` |
| `ArenaForm.stand A σ` | the used count read out of a world; `stand_le`, `stand_nonneg`, `stand_lese`, `stand_schreibSlot`, `stand_schreibGlob` |
| `Stmt.arenaReset` | `reset A;` |
| `Block.arenaAlloc`, `Block.arenaRumpf`, `Block.arenaBump` | `let i = alloc A (v) else B;` and its two halves |
| `arenaReset_stand` | after `reset` the counter is `0` |
| `arenaBump_stand` | the bump raises the counter by exactly one |
| **`arenaAlloc_unter_schranke`** | **below the hard bound the `else` is NOT taken**, and the index bound is the old counter |
| **`arenaAlloc_an_schranke`** | at the hard bound the `else` IS taken |
| `arenaAlloc_gdw_modell` | the syntax runs its body exactly while `Arena.alloc` returns `some` — the bridge to `Arena.lean` |
| `arenaAlloc_bump_modell` | a successful step bumps the same number by one on both sides |

**The reservation `lo` is deliberately NOT in the Lean form.** It is a STATIC count the checker
keeps (`N212`), and its only model-side consequence is `arenaAlloc_unter_schranke`: while the
counter stands under the hard bound, the `else` branch cannot run — *so the surface form that
omits the branch is sound for any choice of branch.* That is the syntactic half of
`Arena.alloc_innerhalb_reserve`.

### 2.2 The witness — non-degenerate, and both branches

`namespace ArenaZeuge`: `ZD` is a concrete `Deklaration` with **four** slots of a byte range and
a counter global over `0 .. 4`; `Log : ArenaForm ZD`; `welt c` is a world whose counter stands
at `c`.

| witness | what it runs |
|---|---|
| `zeuge_leer_unter` | counter `0 < 4` |
| `zeuge_voll_an` | counter `4 = 4` — **both halves of `arenaAlloc` are reachable in this fixture** |
| `zeuge_reset` | `reset` on the FULL arena leaves the counter at `0` |
| `zeuge_bump` | counter `1`, index `2` → counter `3` |
| `zeuge_alloc_leer` | on the empty arena the body runs and the index is `0` |
| `zeuge_alloc_voll` | on the full arena the `else` runs |
| `zeuge_modell` | the bridge instantiated at `kapLog = ⟨2, 4⟩` |

### 2.3 Rust: the refusal stops being a catch-all

`crates/gabbro-check/src/lean_g.rs`:

* a **by-name `ItemArt::Arena` arm** before the catch-all. Measured output on `beispiele/98`:

  > `[LG001] arena Log has no G form YET: the specification carries 'alloc'/'reset' as sugar over
  > a table plus a 'used' global (Grammatik/ArenaZucker.lean, 'Block.arenaAlloc'/'Stmt.arenaReset'),
  > and this exporter does not build that pair -- see OFFEN.md O14`

* the two `LG004` statement arms (unreachable while the declaration refuses first) now name the
  same form and the same ledger entry, *so the day the declaration is lowered the statement half
  is not a silent hole.*

**No new diagnostic code was needed.** `N360`–`N369` and gift numbers `1020`–`1029` were reserved
for this lane and are **returned unused** — they belong to route (b), which was not taken.

### 2.4 Ledger and plans

* `dokumente/OFFEN.md` **O14** — what is closed (the specification has the form), what is open
  (the exporter), what is *not* the gap (§1.5), what would close it, and why (b) was refused.
* `dokumente/SATZKARTE.md` **§33** — the theorem table above (renumbered at the merge: §32 went to the ticket lock).
* `dokumente/SYNTAX.md` — the two statement rows and the `arena` declaration row said *"no `Stmt`
  constructor"*; they now name `Block.arenaAlloc`/`Stmt.arenaReset` and the open half.
* `dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md` §6.5 — a bullet: the arena stops at the exporter,
  no longer at the specification.
* `TODO.md` §2 — the export task, with what to build and what does not travel.
* `AGENTS.md`, `TODO.md` — the stale "O1–O12" range corrected to O1–O14.

---

## 3. What was measured, before and after

### 3.1 Green

| measurement | result |
|---|---|
| `lake build` over the whole Lean library | **250 jobs, exit 0** |
| `#print axioms gabbro_ziel` | `propext, Classical.choice, Quot.sound` — **unchanged** |
| every theorem in `ArenaZucker.lean` | the standard three (or fewer) |
| `sorry` / `admit` / `native_decide` / new `axiom` | **none** |
| `cargo test --no-fail-fast` | **all suites green, 0 failed** |
| `./instrumente/pruefe-emission.sh` | ALL PASS, 37 durchgestochen, 264 of 264 translate |
| `instrumente/zaehle-kette.py` | 98 and 99 read `[.FFF0] no chain instance` before AND after; chain count unchanged |

### 3.2 Guardian figures that moved, each with its reason

Measured by running the same guardian set over two trees built with `git archive HEAD` (before)
and the same tree plus this lane's edits (after). **Exit codes identical for all fourteen
guardians.**

| figure | before | after | reason |
|---|---|---|---|
| `pruefe-englisch.py` line continuations | 5348 | **5351** | three `\` continuations in the new `lean_g.rs` refusal message. `1 von N Naehten kleben` unchanged |
| `pruefe-englisch.py` prose pieces beside the sinks | 3354 | **3355** | one new doc comment |
| `pruefe-englisch.py` checker comment lines | 37201 | **37214** | the new file's header. **German count unchanged at 7942** — the new text is English |
| `pruefe-englisch.py` instrument comment lines | 8230 | **8233** | the ratchet booking's three comment lines. German unchanged at 1086 |
| `pruefe-gestalt.py` files / theorems / definitions | 189 / 737 / 728 | **190 / 756 / 744** | the new file, booked in the ratchet `ERWARTET` as `"ArenaZucker.lean": (19, 0, 16)` with its reason beside it |
| `pruefe-zahlen.py`'s reading of the KENNZAHLEN line continuation figure | "steht als 3183, der Lauf sagt 5348" | "…sagt **5351**" | the same +3 |

**One thing this lane did NOT do, and says so:** `messung/KENNZAHLEN.md` carries **3183** for
*"Zeilenfortsetzungen — die Flaeche der Klebeprobe"* and **4677** for *"klebende Nahtstellen"*,
while the run says 5348 before this lane. *Both figures were already red at the baseline, by
2165 and 671.* This lane moved the measured value by **+3** and did not re-cut the ledger —
writing 5351 there would book a jump of 2168 whose history this lane did not measure. The +3 is
booked here instead.

`pruefe-gestalt.py`'s ratchet is stale in the other direction too (about 150 files, including
`Arena.lean` itself, stand as *"neu, nicht gebucht"* since it was frozen on 2026-09-11). This
lane booked **its own file only**; re-cutting the ratchet is a separate job with its own reasons.

### 3.3 A measuring-apparatus note, because it cost a run

The first `pruefe-emission.sh` on the server reported **`NEUE WURZEL EMITTIERT: 3 Dateien
ausserhalb der fuenf gebuchten Wurzeln`** and cut at stage 9. The three files were **this lane's
own scratch probes** (`kratz-alloc/k1-if.gab`, `k2-loop.gab`, `k3-reset-only.gab`), rsynced into
the server directory. The guardian was right and the finding was mine: *a scratch file inside the
measured tree is a corpus file.* Removed, re-run, ALL PASS. Scratch now lives in the worktree's
gitignored `.claude/`, never in the rsynced tree.

A second one: the baseline `zaehle-kette.py` run reused the `target/` directory copied from the
after-tree, so **the baseline chain measurement used the new binary.** It is reported anyway
because the column both runs produce for 98/99 is a refusal either way and the change cannot
make a refusal disappear — but the reader should know the two runs were not independent.

---

## 4. What is still open, by name

**O14: no arena program closes a chain, because `lean_g.rs` does not build the pair.** The
specification now has the form; the exporter refuses the declaration. Closing it means reading an
`ArenaDecl` into a `TableModel` of `count = hi` with one field plus a `GlobModel` of type
`int 0 hi`, lowering `StmtArt::Alloc`/`ResetArena` to `Block.arenaAlloc`/`Stmt.arenaReset`, and
re-measuring the chain count. The reservation does not travel.

Three cuts are written into the file itself and repeated here so they are not read as promises:

* **the generation is not in Lean.** `Arena.lean` carries it as a type index and a stale index
  does not typecheck there; in the syntax it is checker state and `N211` is the refusal. Nothing
  in `ArenaZucker.lean` forbids reading an older index.
* **the reservation `lo` is not in Lean**, on purpose (§2.1).
* **`Arena.lookup` returns the slot position, not a stored value**, so the bridge of §2.1 is
  about the counter and the index, not about content.

---

## 5. Where each thing was measured

* **`ki-pc-fisch-101`, `gabbro-opus-alloc`:** every `lake build` (queued through
  `~/gabbro-muse/bin/lean-slot`), `cargo build`, `cargo test --no-fail-fast`,
  `pruefe-emission.sh`, `zaehle-kette.py`, `pruefe-syntax.sh`, `pruefe-wortschatz.py`,
  `pruefe-grammatiktafel.py`, `pruefe-saetze.py`, `pruefe-todo.py`, `pruefe-kennungen.py`, and
  every `gabbro pruefe`/`lean-g`/`certificate`/`corr-lean`/`obligations --g` run.
* **`ki-pc-fisch-101`, `gabbro-opus-alloc-basis`:** the baseline `pruefe-todo.py`
  (13 BEFUNDE before and after, identical) and the baseline chain count.
* **Locally:** the fourteen text guardians over two `git archive` trees.

Nothing was merged and nothing was pushed.
