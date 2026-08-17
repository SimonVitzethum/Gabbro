# Gabbro — what is finished

> **This file carries exclusively what is done.** What is open stands in [TODO.md](TODO.md),
> what is refuted in [dokumente/HISTORIE.md](dokumente/HISTORIE.md), what is measured in
> [dokumente/MESSUNGEN.md](dokumente/MESSUNGEN.md).
>
> **Every entry carries its evidence** — a file, a refusal code or a re-runnable command line.
> *A done report without evidence is the same number without a source list that W7 stands
> against* ([dokumente/WERKZEUGKASTEN.md](dokumente/WERKZEUGKASTEN.md)).

---

## The compiler — **ten** passes, none open (plus two more: «B37» and the lock discipline)

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

## The plumbing classes — **9 of 11** carried

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
| **Phase** *(closed 2026-08-17 with «B37»)* | the linear ghost token carried the order as **linearity**, not as **order** — all 720 orderings of F7's six boot steps type-checked. `order { … }` on the token plus `advances a -> b` at each step; `O002` forces the step forward, `O003` refuses a step that meets the token on the wrong stage. Since K11.1 the branch is **decided**, not reported: all branches must reach the same stage (`O006`), a branch ending in `return` does not join, and a step inside a **loop** is refused — *a step happens once, a loop often.* **The named limit:** the softer reading — carrying a SET of stages and letting the next step accept all of them — is not built. *From the strict form one can loosen; the other way never* |

**The two that are NOT carried, and each for a different reason:**

| open | why | Evidence |
|---|---|---|
| **Race** *(carried in part since K11.2.1/.3)* | **`protects` now bites** (`H007`): every access to a protected place stands under its lock, and a lock nobody takes is reported (`H008`). **The ordering lowers** — `atomic_store_explicit`/`atomic_load_explicit` carry the ordering the source declared, not C's default, under **A10**. **The named limit, and it is the whole class:** Gabbro does not say **who runs concurrently**. `entry`/`boot` declare contexts, but all four `dispatch` targets in the corpus are `extern fn` — the hull over a context root is empty, so *„every place two contexts touch is locked or atomic"* cannot fire once. *And a differential test cannot show the absence of a race* | `geteilt.rs` (`H007`/`H008`), poison 74, `pruefe-emission.sh` unit 9, `gabbro annahmen` A10 |
| **Refinement** | *the lowering.* Eight translation units stand, measured by execution; seven of the ten fragments have no C at all. `gabbro zeugnis` says per file what its translation rests on — **but a certificate over THIS translation is no statement about ALL inputs** | `./pruefe-emission.sh` (8 units, each certificate against a booked finding), `crates/gabbro-check/src/zeugnis.rs` |

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
| **The record constructor** («B7») | a function could not **produce** a record. **And the braced literal is refused on purpose:** it would have been the first expression form continuing with `{`, and 76 corpus sites have a `{` right after an expression — *a wrongly set context flag misreads all 76 silently* | `P(a: …, b: …)`; `M106` = `deckt fs zs ⟷ map fst zs = fs` (`beweise/Verbund_Konstruktor.thy`), `M107`, `P036`, `P037`, `beispiele/21`, **six counter-probes** in `pruefe-notation.py` |

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
| **Three fail-open paths closed** | the emitter's whole design is *refuse by name*, and it had **three exceptions** — `option index into T` → `uint32_t` (**no bit pattern left for absent**), an unknown expression form → literal `0`, `None` → the call `None()`. All three compiled; two computed something else | `crates/gabbro-check/src/emit.rs`, poison `option-wird-vergroebert` |
| **`traverse` lowered, `forever` refused — and the pair is the point** | `traverse … over slots of` becomes a plain bounded `for`: **no runtime counter**, because the domain is finite by construction. `retry` becomes a `while` **with** one, because its condition depends on the world. *The C now shows side by side why the grammar demands `on_exceeded` there and not here.* And `forever` is **refused with the folder's own finding**: `per_pass … ops` is a compile-time claim, so `on_exceeded` has no runtime trigger — the clause could only be dropped silently. Measured `16 6 0 0` | `beispiele/19-traversierung.gab`, `./pruefe-emission.sh` |
| **F10 lowered — `retry` and `format`** | **`bounded N ops` is an operation BUDGET, not an iteration count** — divided by the per-pass cost the cost pass computes (body **plus** the `until` condition, which F4 shows can be the expensive half). And a **`format` is not a C struct**: padding and bit order are implementation-defined, so it becomes a byte pointer with accessors in the *declared* order plus **one** validity function from the `where` clauses. Measured `1 0 0 0 0 65`, and the 65 was predicted before the run | `./pruefe-emission.sh`, `crates/gabbro-check/src/emit.rs` |
| **F8 lowered — three decisions, not translations** | `option index into T` carries the **sentinel `N`** (free, because `count N` bounds the index to `0 ..< N`; and Caprock already does it by hand as `NIL`) · a `lock` emits **two prototypes and no body** (rank and hold time are compile-time, `H006`/`K002`) · **`locks X { … return … }` releases before EVERY return** — the C8 class, and the new exit path inherits the duty because the writer does not write it. Measured: `1 1 1 0 0 1 1 1` | `./pruefe-emission.sh`, template `option.sonderwert` |
| **Two more silent lowerings found by reading** | `x += 1` was emitted as `x = 1` — **the operator stood in the tree and the emitter never looked at it** — and `-> never` became plain `void`. Neither occurs in the three guardian units, *which is exactly why both survived* | `crates/gabbro-check/src/emit.rs`, poison `zuweisungsoperator-egal` |
| **Ghost erasure** | **`linear ghost type` costs nothing at run time** — `BootPhase` carries F7's whole safety argument and leaves **no trace** in the C. Erased in the signature, at the call site and at the `let` binding; the counter-probe on the third produced `6` instead of `123456` | `crates/gabbro-check/src/emit.rs`, `./pruefe-emission.sh`, poison `geist-let-verschwindet-ganz` |
| **N1 (Caprock)** | **`MEM` is a leaf**, `system.rs:724` is wrong | `arbeitsprotokoll/03-N1.md` |
| **Closures by kind of use** | **gate VOID** — the population does not reproduce (89 → 64), and V-b is **empty** | `dokumente/MESSUNGEN.md`, *ERGEBNIS Verschlüsse* |
| **K100.2 — five obligations rebooked into the axiom layer** | «B19» barriers · «B38» `masks IRQ` · «B39» the MMU writes `A`/`D` · `at dma` · `atomic release` — all five are statements about the **machine**, and the right home exists. **A rebooking is not a discharge**: it carries them **by name with a probe**, which is exactly the trust the brief grants. `gabbro annahmen` now reports **19** (was 14), and **two of the five have no probe** — the MMU one would have to stop the MMU. `H = 29 → 24` | `beispiele/06-annahmen.gab`, `gabbro annahmen` |
| **K100.1 — the yardstick sharpened, without a line of code** | Three hand-written `narrow` sites were counted as the same thing and are not: an **reachable** `else` branch is the programmer's statement *"this input is hostile"* (`FRAGMENTE.md`:1660, a hostile DTB) or a deliberate second net (`:268`); an **unreachable** one is a hole in M1 (`:1100`). *A yardstick that cannot tell a check from a ritual measures the wrong thing.* **The gate moved from "24 are allowed" to `N_ritus = 0` — one is too many** — and is almost met, because the old number summed two different things. `H = 31 → 29`, `L = 65 → 67` | `dokumente/PFLICHTEN.md`, `dokumente/MESSUNGEN.md` |
| **`verbund.konstruktor` machine-checked — and it was proved BEFORE the construct** | K100's second gate (`L ≤ 4`) says a template may not move from *designed* to *carried* without a proof first. Building «B7» would have done exactly that. **So the proof came first**: under `distinct fs`, `map fst zs = fs` makes *"each field set exactly once"* and *"none uninitialised"* **the same statement** — and the content lies one step further than the entry said: **the read-back is unique**. `ungedeckt 16 → 15`, `bewiesen 4 → 5`, `L` unchanged at 4 | `beweise/Verbund_Konstruktor.thy` |
| **`option.sonderwert` machine-checked — and it flushed out a premise nobody had written** | the encoding `None ↦ N`, `Some i ↦ i` is **injective**, which is what *lossless* means — **under `N < 2^w`.** At `N = 2^w` the sentinel falls onto slot 0 and `None` is `Some 0`. **The premise stood in none of the three places** (register, `SPRACHE.md`, emitter); the emitter emitted `#define T_NONE (N)` for `count 4294967296` without a word. *Satisfied in practice, unchecked in fact.* Now a check | `beweise/Option_Sonderwert.thy`, poison `sonderwert-ohne-wortgrenze` |
| **`atomic` payload-free, `check` as a function — and `descendants of` turned out to be a FINDING** | `publishes nothing relaxed` becomes `_Atomic`; **`release` is refused** — that a release store ESTABLISHES the visibility the pairing claims is a memory-model statement, and the class *Race* hangs on exactly that. A `check` becomes a `bool` function **carrying its claim and its counterprobe** — *a probe shipped without its claim is a number without a subject.* And `descendants of` **does not name the edge it walks**: `CapSpace` offers four candidates, and `chain(a, b) in` shows the grammar knows how. **An asymmetry in the grammar, not missing emitter code** | `crates/gabbro-check/src/emit.rs`, poison `release-wird-abgesenkt` |
| **Three more lowerings, and one of them names «B17»** | `x = None` resolves the **target** table's sentinel (not its own — a distinction that only shows with two tables) · `bank … at CAP.FRO * 16` becomes an indexed accessor whose base is **read from a field**, the address the stock computes by hand at `vtd.rs:442` · and **`transset` sets several bits in ONE write** — possible at a register word, *impossible at two slot fields, and that is «B17» one level up* | `beispiele/02-geraet.gab` now emits, poison `transset-nimmt-nur-den-ersten` |
| **TRAP 4 in the generated C, not in a comment** | `mirrors GCMD from GSTS;` — **one line per device** — becomes `write(GCMD, (read(GSTS) & ~changed) \| new)`. GCMD is `class w`, i.e. unreadable, so a read-modify-write is impossible; the state bits to carry sit in the register **next to it**. *In the measured code this is a mask plus a wall of comment (`vtd.rs:42-52`).* Measured `1 1 1 1` — **the second and fourth numbers ARE the trap**: without `mirrors` they are 0 and the unit switches translation off mid-operation. And the `requires` becomes **no runtime check** — the same kind of clause as `requires Held(…)`, i.e. a caller obligation; asserting here and not there would be the silent exception | `beispiele/20-falle-vier.gab`, `./pruefe-emission.sh` |
| **The assumption set now travels WITH the code** | `SYNTAX.md` §12 demands *"the assumption set is emitted into the artefact ('proved under A1…An'), as a set of NAMES WITH CLASS"* — and until 2026-08-17 nothing did it: `gabbro annahmen` printed to the console and the artefact knew nothing. *A promise that lives only in a tool invocation does not travel with the code.* It now stands in the generated header, beside the licence notice and for the same reason | `crates/gabbro-check/src/emit.rs`, poison `annahmen-fahren-nicht-mit` |
| **Device bit fields — read yes, write no** | `v.GSTS.TES` becomes `((word >> 31) & 1u)`. **Writing one is refused**: a write to a single bit is a read-modify-write on the WHOLE register, impossible for `class w` — *and that is exactly trap 4*, for which `mirrors` exists and is not lowered. A bit position beyond the declared register width is an **error**, not an open point («B24» is about a `format` spanning two words, where the width is unsaid) | `crates/gabbro-check/src/emit.rs`, poison `bitlage-darf-herausragen` |
| **`device … at mmio` lowered** | a register is **not a field**: `r.AVAIL_IDX += 1` becomes `(*(volatile uint16_t *)(r->basis + 258)) += 1`. *`volatile` is the one place where the lowering must FORBID the C compiler something.* **`at dma` is refused** — which barrier a `dma` access needs is a memory-model statement, and M3 does not build it either. Measured `8 0 64 8`, the second number being «B32»'s intended wraparound | `beispiele/12-umlaufendes-register.gab`, `./pruefe-emission.sh` |
| **Four templates machine-checked** | `table.induktion` · `table.indexschranke` · `consuming.ordnung` · `consuming.leermenge` — **5 silent assumptions flushed out, 2 statements REFUTED**, register 17 → 19, unproved 16 → 15; **20/16 since `option.sonderwert`** (2026-08-17) | `beweise/*.thy` (Isabelle2025-2), `gabbro schablonen` |
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
./mutiere-pruefer.py      damages one rule at a time:  132 of 132
./erzeuge-mutationen.py   twists systematically:         7 of 39
./pruefe-luecken.py       the named gaps one by one:    13 of 15
./pruefe-emission.sh      .gab → C → cc -Werror → run → compare, SEVEN units
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

**23 clean examples, 75 poison probes, 119 tests · 9 translation units** —
`cargo test` · `cargo run --bin gabbro -- pruefe beispiele/*.gab`
