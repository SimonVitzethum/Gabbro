# Gabbro — what is finished

> **This file carries exclusively what is done.** What is open stands in [TODO.md](TODO.md),
> what is refuted in [dokumente/HISTORIE.md](dokumente/HISTORIE.md), what is measured in
> [dokumente/MESSUNGEN.md](dokumente/MESSUNGEN.md).
>
> **Every entry carries its evidence** — a file, a refusal code or a re-runnable command line.
> *A done report without evidence is the same number without a source list that W7 stands
> against* ([dokumente/WERKZEUGKASTEN.md](dokumente/WERKZEUGKASTEN.md)).

---

## The compiler — **ten** passes, none open

`cargo run --bin gabbro -- paesse` · **3 fully built, 7 partial, 0 open**

> **The tenth is NEW, and that is a change to the specification.** `SPRACHE.md`
> part III §6 fixes nine and says *"the specification is the pass list"* — a tenth therefore
> does not mean "one module more" but **the list has grown**. The reason is
> measured (SWEEP, V4), not designed: an invariant **between** carriers has no place in the
> nine passes.

| # | Pass | Codes | Evidence |
|---:|---|---|---|
| 1 | **Namen** | `N001`–`N003` | `crates/gabbro-check/src/namen.rs` |
| 2 | D1/D2 *(partial)* | `D001`, `D002` | `kbedingung.rs` — the K condition, `by ops` per **field** |
| 3 | **M1 + V1–V3** | `M101`–`M105` | `m1.rs`, `typen.rs` |
| 4 | M3 *(partial)* | `R001`–`R003` | `m3.rs` — spaces, rights, placement rule |
| 5 | M2 *(partial)* | `L101`–`L105` | `m2.rs` — real linearity |
| 6 | **M4/loops** | `S001`, `S002` | `schleifen.rs` |
| 7 | Pairing *(partial)* | `V001`–`V004` | `paarung.rs` |
| 8 | effects *(partial)* | `E001`–`E010` | `wirkungen.rs` — since 2026-08-16 **with the read half** (reading A) |
| 9 | costs *(partial)* | `K001`–`K004` | `kosten.rs` |
| **10** | **Group** *(new, partial)* | `U001`–`U007` | `gruppe.rs` — lock imprint, move **and connection statement** |

> **"Partial" for M2, M3 and pairing does not mean "half finished" but "finished, resting on a
> named item"** — ghost deletion, the barrier out of the space, the memory model. **Three
> of them are the same item: the axiom layer.**

**Plus the call graph** (`aufrufgraph.rs`, 268 lines) — it solved three blockers at once:
`H005`, the call effects in pass 8, and the separation at the class *Phase*.

## The plumbing classes — **8 of 11** carried

Newly collected 2026-08-15, **not reconstructed**, x86 only
([dokumente/MESSUNGEN.md](dokumente/MESSUNGEN.md), *Neuerhebung*):

| carried | by what |
|---|---|
| **Index** | `index into T` inherits `count N` · `M103` |
| **Overflow** | M1 range types · `M101`/`M104`; intended wraparound since «B32» at the slot **and** at the register |
| **Alias** | dissolved rather than closed — core state needs no pointer (A1); where it does, `own` makes it linear. Evidence: `beispiele/09-ohne-zeiger.gab`, `beispiele/15-own-traegt-beide-rechte.gab` |
| **Lock** | `rank`/`held`/`shared held` · `H001`–`H006` · `K002`/`K004`; the **lock order has been recomputed since 2026-08-16**, not merely declared |
| **Termination** | three loop forms · `bounded`/`on_exceeded`/`progress` · `S001`/`S002` in `schleifen.rs`, `beispiele/04-schleifen.gab` |
| **Leafness** | `descendants of` + `by consuming` with a witness ordering · domain bound in `kosten.rs`, `dokumente/FRAGMENTE.md` (`revoke`) |
| **Publication** | `publishstmt` at the store · pairing pass · `relaxed` carries no payload · `V001`–`V004` in `paarung.rs` |
| **Frame** *(booked in retrospect 2026-08-16)* | `effects` holds writes, `locks` **and reads** (`E010`, reading A) and the call effects (`E008` over the call graph). **The named limit:** `E010` speaks only about declared world state — in an excerpt it has zero bite, in a complete translation unit the name pass covers the rest |

## Constructs that are built and evidenced

| Construct | Reason | Evidence |
|---|---|---|
| **`locks shared`** | measured: 33 `read()` against 44 `write()` — the hottest path was not writable | `H001`–`H005`, `beispiele/10`, poison 38–42 |
| **`wrapping` at the register** («B32») | virtio's ring counter wraps by design; the intent stood nowhere | `beispiele/12-umlaufendes-register.gab`, `beispiele/gift/48-register-ohne-umlauf.gab` |
| **`heldpred`** | the strength of the witness, without weakening the expression | `dokumente/SYNTAX.md` (`atompred`), `beispiele/13-zeuge-mit-staerke.gab` |
| **`Some`/`None`** («B35») | `option` had **no constructor** — the existing code has always written it | `optionexpr` in `dokumente/SYNTAX.md`, `beispiele/01-tabelle.gab` |
| **`table … count N`** | `index into T` inherits the bound | `M103` in `m1.rs`, `beispiele/01-tabelle.gab` |
| **Placement rule** | an `ops` carrier lies in no `dma` space — a device writes past every grammar | `R001`, poison 58 |
| **`ancestors of`** («B41») | **the first measured need for a construct**: 4 bodies walk the device topology upwards, 226 of the 584 non-traversable lines lie there | `beispiele/18-vorfahren.gab`, `beispiele/gift/69-vorfahren-ohne-schranke.gab` |
| **`by ops` at the field** | the K condition turns from a **checking prescription into a grammar property**: `refcount -= 1` by hand is not writable | `D002` in `kbedingung.rs`, `beispiele/16`, poison 60 |
| **`shared held` (N3)** | `held` is computed for **exclusive** holders; the shared side has a computed quantity of its own | `K004` in `kosten.rs:497`, its own pot `geteilte_haltezeiten` |
| **Lock order checked** | `rank` was declared and was **never recomputed** — and two constructs appealed to it | `H006` in `geteilt.rs`, poison 67 (descent) + 68 (tie) |
| **`group … over { … }`** | an invariant **between** carriers has no room in any `table … invariant` — measured: V1–V4 in the existing code | `U001`–`U007` in `gruppe.rs`, `beispiele/17`, poison 63–66 |

## Measurements run, with gate and outcome

| Measurement | Outcome | Evidence |
|---|---|---|
| **Gate P2** — the corpus parses | **passed, 10 of 10** (and `dokumente/SYNTAX.md` 6 of 6) | `gabbro fragmente dokumente/FRAGMENTE.md` |
| **Mutation generator** | **passed** — `7 von 39` against `54 von 54` by hand | `erzeuge-mutationen.py`, `dokumente/MESSUNGEN.md` |
| **The 15 generator gaps** | **13 closed, 2 provably equivalent** | `./pruefe-luecken.py` |
| **`narrow` count** | **gate missed** — N = 2, and the protocol was contradictory | `./zaehle-bereichspflichten.py` |
| **Eleven plumbing classes** | **gate missed** — `N_neu = 5` (today 4) | `dokumente/MESSUNGEN.md`, *Neuerhebung* |
| **K/A/W over N_L** | **gate missed** — `W = 38 von 73` | `dokumente/MESSUNGEN.md`, *Buchung* |
| **Loader fragment, class *Phase*** | **the token carries: 7 against k = 5** | `dokumente/FRAGMENTE.md` F7 |
| **All four domain fragments** | **convergence metric: 0 new constructs** | `dokumente/FRAGMENTE.md` F7–F10 |
| **`Stale(T)`** | **refuted** — 2 of 5 transitions rest on `masks IRQ` | `dokumente/FRAGMENTE.md` F8, «B38» |
| **Base rate `format`** | **does not carry `format`** — 5 formats, 0 errors of the class | `dokumente/MESSUNGEN.md` |
| **`delete_leaf`** | **1,75 : 1** instead of the booked 3,6–6 : 1 | `dokumente/BEWEIS.md` |
| **`programs/`** | the reason for the breach no longer carries | `dokumente/MESSUNGEN.md` |
| **C emission, two units** | **the first yes-statements**: `.gab` → C → `cc -Werror` → executed → **result compared**. `beispiele/16` yields `42 1 8 0`; **`FRAGMENTE.md` F7 yields `123456`** — six boot steps, in order, each exactly once | `./pruefe-emission.sh`, `crates/gabbro-check/src/emit.rs` |
| **Ghost erasure** | **`linear ghost type` costs nothing at run time** — `BootPhase` carries F7's whole safety argument and leaves **no trace** in the C. Erased in the signature, at the call site and at the `let` binding; the counter-probe on the third produced `6` instead of `123456` | `crates/gabbro-check/src/emit.rs`, `./pruefe-emission.sh`, poison `geist-let-verschwindet-ganz` |
| **N1 (Caprock)** | **`MEM` is a leaf**, `system.rs:724` is wrong | `arbeitsprotokoll/03-N1.md` |
| **Closures by kind of use** | **gate VOID** — the population does not reproduce (89 → 64), and V-b is **empty** | `dokumente/MESSUNGEN.md`, *ERGEBNIS Verschlüsse* |
| **Four templates machine-checked** | `table.induktion` · `table.indexschranke` · `consuming.ordnung` · `consuming.leermenge` — **5 silent assumptions flushed out, 2 statements REFUTED**, register 17 → 19, unproved 16 → 15 | `beweise/*.thy` (Isabelle2025-2), `gabbro schablonen` |
| **B3 — non-traversable bodies** | **passed, `p = 0,96 %` against a mark of 5 %** — but **R1 missed** (rule written down after the run) | `./zaehle-b3.py ../caprock-messbasis`, `dokumente/MESSUNGEN.md` |
| **The 74 reassigned** | **238 obligations, each with `file:line`** — 173 K / 65 L; **gate MISSED at `H = 36`** hanging plumbing obligations. R1 kept this time (pre-registration in its own commit), R14 calibration **refuted the rule** and was repaired before the run | `dokumente/PFLICHTEN.md`, `./zaehle-pflichten.py` |
| **The escalation of 2026-08-14** | **6 of 7 items built**, 1 open («B19»), 1 unrecoverable — and the 36 sorted onto the eleven classes **refute two booked-as-carried classes by name** | `dokumente/MESSUNGEN.md`, *The escalation … settled* |

> **The B3 entry is the only one in this table that carries a protocol breach beside its
> outcome** — and it stands here rather than in a footnote, because a done table that carries
> only outcomes conceals the most expensive line: **the token rule was sharpened in four
> versions with visible numbers.** What saves the result is not care but **rule invariance**:
> all four versions (0,03 % · 4,36 % · 0,74 % · 0,95 %) pass the mark. *The number depends on
> the choice of rule, the verdict does not.*

> **And the reassignment turned the folder's headline metric against itself.** The same
> function, the same dividing line: the **Rust** original of `delete_leaf` gives **1,75 : 1**, the
> **Gabbro** fragment gives **0,62 : 1** — because Gabbro *writes down* nine plumbing obligations
> that Rust leaves unwritten. **The language does not create them, it makes them visible**, and
> `L : K` punishes it for exactly that (**R18**). *Hence the measurand is no longer the ratio but
> `H` — the plumbing that stays on the human: **36 of 173**, i.e. **79 % carried by
> construction**.*

## Grammar — the findings from P2

**G1–G11 closed** ([dokumente/SYNTAX.md](dokumente/SYNTAX.md), `beispiele/11`, poison 43–45):
`atomicdecl publishes` · `axiom -> typeexpr requires` · the `->` ambiguity **in the
grammar** · trailing comma · `u64::max` · `O`/`@version` as a named `Sonderform` ·
`clobbers { }` empty · `count N` · `cast` disappears · the `forever` example · eight domains.

**Label collision resolved** (2026-08-16): the counter-check findings in
`dokumente/MESSUNGEN.md` are now called `GP1`–`GP3`; `G1`–`G11` belong to the grammar.
*Two label systems with the same names are the same error class as two prose orderings that
nobody checks against each other.*

**Plus:** the payload form decided from the existing code (22 × `nothing`, 11 × parentheses,
2 × without — the grammar follows the 33), the `pub` laxity (`P034`), `pub const` in the
`table` body, and **`dokumente/SYNTAX.md` now holds its own grammar** (test
`die_beispiele_der_grammatik_gehen_selbst_durch`).

## The guardian chain — nine, each with a speech test in both directions

```
./pruefe-syntax.sh        forbidden forms, prose drift, closure, reachability,
                          terminal coverage — and ZERO build warnings
./pruefe-wortschatz.py    terminals against the table, Sonderform counter (3 of 5)
./pruefe-todo.py          holds the task list against itself, eight classes
./pruefe-kennungen.py     no refusal code in two files
./mutiere-pruefer.py      damages one rule at a time:   92 of 92
./erzeuge-mutationen.py   twists systematically:         7 of 39
./pruefe-luecken.py       the named gaps one by one:    13 of 15
./pruefe-emission.sh      .gab → C → cc -Werror → run → compare, TWO units
./commit.sh               R19 — commit messages only via file
```

> **The mutation density is a diagnostic in its own right, and on 2026-08-17 it found four
> things.** Measured per checker file, `1 310` of 6 823 lines carried **zero** mutations — *and a
> surface with zero mutations is not covered, it is undamageable.* **Today it is zero of 8 163.**
>
> 1. **The template ratchet's second tooth had been dead for a day.** It read *"all unproved AND
>    longer than 18"*, so **the first proved template made it false forever** — the register could
>    then grow without limit, and it grew 17 → 19 on that same day. *A ratchet with a single
>    detent is a stop, not a ratchet.* Repaired as the literal generalisation of the sentence
>    already standing beside it: **base mark plus one slot per proved template.**
> 2. **A pass could silently not run.** `SPRACHE.md` part III says *"the specification is the
>    pass list"*; 241 lines of `lib.rs` carried no mutation, so nothing enforced it.
> 3. **The call graph's collection side had never been looked at.** All seven probes called on
>    the top statement level only — a call in a `match` arm, under `locks` or in a loop body could
>    have gone missing, and **the corpus has exactly that shape** (`delete_leaf` calls three times
>    in `match` arms, `revoke` inside `traverse`).
> 4. **`gabbro annahmen` reported 15 assumptions where there are 14** — see below.

> **The axiom layer was the ratchet everything else was measured against, and it had no test.**
> `schablonen.rs` cites it as *the* example of a ratchet that already exists; `manifest.rs` had
> neither probe nor mutation. The first probe found that `beispiele/06` and `beispiele/07` both
> declare `axiom write_cr3` identically, and the command **concatenated instead of uniting** —
> *a promise "proved under A1…An" with a duplicated A claims a larger assumption set than it
> has.* **The dangerous case is the other one**, and the repair is built for it: two files
> declaring the same NAME with different content are a **contradiction**, not a duplicate, and
> the command now refuses by name instead of printing both lines silently.

**Plus three tests, each of which comes from a paid-for error:** no pass without registration ·
`dokumente/SYNTAX.md` against its own grammar · corpus test anchored at the content instead of at
the line number.

## The working rules — W1 to W12

Complete in [dokumente/WERKZEUGKASTEN.md](dokumente/WERKZEUGKASTEN.md). Each comes from a
**paid-for error in this folder**, each names the damage.

## Probes

**19 clean examples, 69 poison probes, 79 tests** —
`cargo test` · `cargo run --bin gabbro -- pruefe beispiele/*.gab`
