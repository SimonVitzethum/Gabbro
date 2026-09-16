# OPUS-BERICHT-ATOMFELD — the atomic array

*Opus agent, 2026-09-16, branch `agent-a0284a88a82c3d818` off `ba081089`. Server directory
`gabbro-opus-atf`. The lane's question: a firewall written outside this tree
(`/home/ubuntu/brandmauer`) needed one counter per rule, 256 of them, and could not write
`atomic REGEL : [u32; 256]`. It wrote 5136 lines instead of about 60.*

---

## 0. What this lane concluded

**The wall was real, the lowering is honest, and it is built.** The checker accepted an
indexed atomic update, the emitter refused the declaration by name (`C001`), and the two
were both right about different things — but the checker's acceptance was worse than the
firewall lane knew: it accepted an **unbounded** one. That hole is closed here, in the
checker, with the same rule an ordinary table index gets (`M103`) plus one new refusal
(`N380`) for the case where no bound can be shown at all.

**The race exemption of the goal theorem is not widened**, and §4 is the argument with the
Lean text beside it. Nothing in `grammatik/` was touched; `#print axioms gabbro_ziel` is
the three standard axioms, measured after the change.

**The payoff, measured on the real program:** 5136 lines → **287**, 1797 ops per counter
increment → **11**, 9824 lines of emitted C → **385**. §6.

---

## 1. The wall, measured in this tree

Smallest program that shows it (`.claude/muse-arbeit/kratz/atf/w1.gab`): one atomic array,
one indexed increment, nothing else.

```gabbro
pub atomic REGEL : [u32; 256] relaxed;
...
    let alt : u32 = REGEL[r] exchange update(t)
        bounded 64 ops on_exceeded streit
    { return folge(t); } publishes nothing;
```

**`gabbro pruefe` — accepted** (`5 items, 0 errors, 1 hints`, the hint is `E247`, which for
an atomic is correctly ignored). **`gabbro emit` — refused, twice:**

```text
error: [C001] w1.gab:4:5: no lowering: `atomic` of an unresolvable type
    4 | pub atomic REGEL : [u32; 256] relaxed;
      = the emitter refuses by name instead of emitting something plausible -- a generator
        that guesses undoes every pass in front of it
error: [C001] w1.gab:14:5: no lowering: `exchange` on something that is not a declared
        `atomic` -- without a declaration there is no memory ordering, and choosing one
        would mean inventing it
```

### Which arm refuses, and why it was written that way

**The first refusal is `emit.rs`, the `ItemArt::Atomic` arm** (before this lane, line 2431).
Both of its branches — the payload-free one and the ordered one — read

```rust
match ctyp(&a.typ, &namen) {
    Some(c) => aus.push_str(&format!("\n_Atomic {c} {};\n", a.name.text)),
    None => weigere(absagen, a.span, "`atomic` of an unresolvable type"),
}
```

`ctyp` answers a C **type word**, and it has no arm for `TypExpr::Feld`. **That is not an
oversight, it is the shape of C:** an array declarator is `T name[N]`, with the size after
the NAME, so there is no type word to substitute into `_Atomic {c} {name};`. `ctyp`'s own
header says its callers turn a `None` into `C001` by name rather than guess — and a guessed
array declaration is the worst kind of guess, because `_Atomic uint32_t REGEL;` would have
compiled and been one counter where the program wanted 256.

**The second refusal is the `StmtArt::Exchange` arm**, and it is a consequence of the first:

```rust
let ziel = x.ort.text();
let Some((typ, speichern, laden)) = u.atomics.get(&ziel).cloned() else { … C001 … };
```

`u.atomics` is keyed by the atomic's NAME. `x.ort.text()` of `REGEL[r]` is the string
`"REGEL[r]"`, which is not a key of that map and never will be. The same accident sat in
three more arms (`Publish`, `AwaitLoad`, and the bare read in `ort()`), each asking the map
for itself. **The refusal text is right about the general case** — an `exchange` on a place
that is not a declared atomic has no memory ordering, and inventing one is exactly what
`C001` stands against. It was simply never true of `REGEL[r]`: the declaration is right
there.

**So: there was a reason, and it is answered rather than removed.** The declaration arm
now builds a DECLARATOR instead of a type word (`atom_declarator`), and the four access
arms ask one reader (`atom_target`) that resolves a place to the C designator of the atomic
OBJECT — `GESAMT` for a scalar, `REGEL[r]` for an element. Every refusal that was right
stays: an unresolvable element word, an unfoldable length, a place with any other suffix
shape.

## 2. What the checker was really doing — the finding that outranks the wall

The firewall's `BEFUNDE-bm4.md` F2 notes an asymmetry: the indexed *read* is refused
(`N271`), the indexed *exchange* checks clean. **Measured here, the acceptance is not a
model of indexed atomics; it is the absence of one.**

| probe | shape | UNCHANGED checker |
|---|---|---|
| `w4.gab` | `REGEL[r] = v publishes nothing;`, `r : u32 in 0 .. 300`, `[u32; 256]` | `M103`, correct |
| `w2.gab` | the same index at an `exchange` | **`0 errors`** |
| `1043` shape | the same index at an `awaits` | **`0 errors`** |
| `p4.gab` | `REGEL[b] = v`, `b : bool` | **`0 errors, 0 hints`** |
| `p5.gab` | length is a `static`, index reaches 300 | **`0 errors, 0 hints`** |

Two independent holes:

1. **`M1::index_pruefen` was called at an assignment and at a `publishes` and nowhere
   else.** The `N271` note beside it says why nobody noticed: *"the legal indexed atomics
   never reach this arm: all three read their source through `typ_von_ort` directly."* They
   read the **type** directly — and `M103` does not live in `typ_von_ort`. U9's own sentence
   (*M4 holds on BOTH sides, and a write is the more dangerous direction*) was written and
   not applied to the one statement that both writes and is exempt from race freedom.
2. **`M103` steps aside when it cannot compare** — a length that did not fold to a constant
   (`Typ::Feld { laenge: None }` does not even match its arm) and an index type with no
   range (`bereich()` is `None`).

Hole 2 is shared with ordinary tables and **is not closed here**; see §7.

## 3. What was built

### Checker (`crates/gabbro-check/src/m1.rs`)

| change | effect |
|---|---|
| `fn atom_array(name, lage) -> Option<Option<u128>>` | "is this an atomic whose declared type is an array, and did its length fold?" — the outer `Some` decides whether an indexed access is a form, the inner one whether its bound can be shown |
| `N271` gains **one** exception | exactly one `Index` suffix over an atomic ARRAY. Every other suffix shape keeps every word of the refusal, and the message now names which carrier it is talking about (`a scalar` / `an array of scalars`) |
| `index_pruefen` gains **`N380`** | an indexed access to an atomic array whose bound is not SHOWN — unfoldable length, or an index with no range |
| `StmtArt::Exchange` and `StmtArt::AwaitLoad` call `index_pruefen` | `M103` now reaches the RMW and the acquire load |

### Emitter (`crates/gabbro-check/src/emit.rs`)

| change | effect |
|---|---|
| `Namen::atom_arrays: HashMap<String, u128>` | the atomics whose declared type is an array, with their length. `atomics` carries the **element** type for them — that is what every access yields |
| `fn atom_declarator` | `uint32_t GESAMT` / `uint32_t REGEL[256]`; the caller writes the `_Atomic`. `_Atomic` on the ELEMENT type, because C11 6.7.2.4p3 makes `_Atomic (uint32_t[256])` a constraint violation while `_Atomic uint32_t REGEL[256]` is an array of atomic objects — and `&REGEL[i]` is then the `_Atomic uint32_t *` every `atomic_*_explicit` generic wants |
| `fn atom_refusal` | two reasons instead of one: an unresolvable element word, and an unfoldable length (`[]` at file scope is an incomplete type, a guessed size is a buffer nobody asked for) |
| `fn atom_target` | the ONE reader the four access arms share. Byte-identical for a scalar (`Ort::text()` of a suffix-free place IS the name) |
| `Publish`, `AwaitLoad`, `Exchange`, `ort()` bare read | all four go through `atom_target` |
| the `Exchange` arm **hoists its index** | `uint64_t _axN = (uint64_t)(<index>);` before the loop. The designator stands three times in the lowering, once INSIDE the retry loop; written straight in, an impure index would select a different element on every lost race. One `const` binding settles it for every index at once |
| `benutzte_namen` reads the INDICES of an atomic place | the three arms walked only the value. Measured at the first emitted atomic array: `void setz(uint32_t r, …) { (void)r; … &REGEL[r] …}` — `cc` accepts it (a `(void)` before a use is legal), which is the bad half: **the line is a statement that the parameter is unread, and it was false** |

### Corpus

| file | what it pins |
|---|---|
| `beispiele/140-atomic-array-counter.gab` | the payload-free array: indexed `exchange`, indexed bare read, indexed `publishes` |
| `beispiele/141-atomic-array-pairing.gab` | the ORDERED array with a live `publishes`/`awaits` pairing through the element |
| `beispiele/gift/1040-atomic-array-length-not-constant.gab` | `N380`, unfoldable length |
| `beispiele/gift/1041-atomic-array-index-without-range.gab` | `N380`, `bool` index |
| `beispiele/gift/1042-atomic-array-exchange-out-of-range.gab` | `M103` at an `exchange` — the hole |
| `beispiele/gift/1043-atomic-array-awaits-out-of-range.gab` | `M103` at an `awaits` — the other hole |
| `beispiele/gift/1044-atomic-array-field-behind-index.gab` | `N271` still holds at `REGEL[0].x` — **the boundary of the widening, measured** |

`saetze.rs`: `m1.bare_atomic_place` extended with the exception and its boundary;
`m1.atomic_array_bound` added for `N380`.

### The emitted C, verbatim (from `beispiele/140`)

```c
_Atomic uint32_t REGEL[256];

void zaehle_regel(uint32_t r) {
    /* the index, evaluated ONCE -- the loop below re-reads the value, never the expression */
    uint64_t _ax1 = (uint64_t)(r);
    /* REGEL[_ax1] exchange update(t) -- a bounded CAS loop, and bounded is the point: … */
    uint32_t alt;
    {
        uint32_t _ci1 = 0;
        uint32_t _cx1 = atomic_load_explicit(&REGEL[_ax1], memory_order_relaxed);
        for (;;) {
            uint32_t _cn1;
            { const uint32_t t = _cx1; _cn1 = folge(t); goto _cn1_fertig; _cn1_fertig: ; }
            if (atomic_compare_exchange_weak_explicit(
                    &REGEL[_ax1], &_cx1, _cn1, memory_order_relaxed, memory_order_relaxed)) break;
            if (_ci1 >= (uint32_t)(64)) { regel_streit(); }
            _ci1++;
        }
        alt = _cx1;
    }
    (void)alt;
}

uint32_t lies_regel(uint32_t r) {
    uint32_t n = atomic_load_explicit(&REGEL[r], memory_order_relaxed);
    return n;
}

void loesche_regel(uint32_t r) {
    /* publishes { nothing } -- paired at compile time (V001-V004) */
    atomic_store_explicit(&REGEL[r], 0, memory_order_relaxed);
}
```

And from `beispiele/141`, the ordered twin — the order stands once, at the CARRIER:

```c
_Atomic bool BEREIT[4];
#define BEREIT_ORDER memory_order_acquire
…
    atomic_store_explicit(&BEREIT[i], true, memory_order_release);
…
    bool fertig = atomic_load_explicit(&BEREIT[i], memory_order_acquire);
```

Both compile at `-O0` and `-O2` under `cc -std=c11 -Wall -Wextra -Werror`.

## 4. The race rules — the part that was worth stopping for

**The question: does an atomic array widen the exemption the goal theorem carries?**

`Zielsatz/Spec.lean` proves `RennfreiBis` for every carrier that is not exempt:

```lean
      ¬ AtomarAusgenommen c → ∃ L, Bewacht c L ∧ GeordnetG ms fs L i j
```

and `Zielsatz/Akzeptiert.lean` decides the exemption:

```lean
def atomarB : D.Tab ⊕ D.Glob → Bool
  | .inl _ => false          -- a TABLE is never exempt
  | .inr g => D.atomar g     -- one Bool per GLOBAL carrier

def ausgenommenB (c : D.Tab ⊕ D.Glob) : Bool :=
  !(waechterVon c).isEmpty || atomarB c
```

**Three things follow, and each was checked rather than assumed.**

**(a) The exemption is per CARRIER, not per access, and it is one Bool.** An atomic array
is one `D.Glob`. It cannot become a `.inl` by growing a length: the danger the task names —
"smuggle a table past the footprint rules" — would require lowering the array as a `table`,
and nothing here does. Measured on the Rust side, which is where the change lives:

| pass | probe | result |
|---|---|---|
| effects | `e1.gab`: `writes REGEL` omitted at an indexed exchange | **`E005`** — the pass SEES the indexed write |
| export | `e2.gab`: `pub fn` naming a non-`pub` atomic array | **`N038`** — it is a carrier, named once |
| footprint | `beispiele/140` | `E247` names `REGEL` — ONE name per function, not 256 |
| shared | `geteilt.rs:675`, `ItemArt::Atomic(a) => geschuetzt.push(a.name…)` | the whole array enters as ONE name — the Rust analogue of `atomarB`, unchanged |

**(b) The exemption is only honest if EVERY access is an atomic operation.** For a scalar
that is why `N270` refuses a bare store and why the bare read lowers to
`atomic_load_explicit`. For an array the same duty falls on four forms, and all four are
now explicit calls on `&REGEL[i]`. The one that mattered: the bare indexed READ. Letting it
through `N271` without lowering it to `atomic_load_explicit` would have put a plain access
to an `_Atomic` object beside a CAS loop — undefined in C11, stuck in the C model
(`C-SPEICHERMODELL.md` §1c), **and covered by nothing**, because race freedom does not
speak about this carrier. A bare indexed STORE is refused unchanged: `N270` reads
`z.ziel.basis.text`, so `REGEL[i] = v;` falls exactly as `AT = v;` does.

**(c) The bound is part of the same argument, not a separate nicety.** An out-of-range
atomic RMW is an unchecked write to an arbitrary address. At a table, `M103` and the
footprint and the guard all speak; at an atomic array, `M103` is the only one that does.
That is the whole reason `N380` exists and the whole reason it is strict here and not
elsewhere.

**And the Lean side is untouched, which is a statement and not an omission:**

- `Ty` (`Typen.lean`) has **no array constructor**. Arrays live only in `Tab`. So a
  `D.Glob` cannot carry an array type, and there is no atomic array in the model at all.
- `gabbro lean-g` **already refuses every `atomic`** (`LG001`: *"an `atomic` is a `Glob`
  with `atomar = true` … this exporter writes `atomar := fun _ => false` and exports none
  of the three"*). No program with an atomic — array or scalar — reaches the model through
  the exporter today.

**Consequence, stated plainly: this arm stands AHEAD of the model.** It is a Rust-side
lowering whose Lean counterpart does not exist yet, exactly as the scalar `atomic` was
before it and still is. `#print axioms gabbro_ziel` after the change:

```text
'Gabbro.Grammatik.Zielsatz.gabbro_ziel' depends on axioms: [propext, Classical.choice, Quot.sound]
```

unchanged, as are `gabbro_ziel_zeuge`, `probeA_widerlegt_gilt`, `probeD_widerlegt_gilt`
and `w1_abgelehnt`. The lane did not stop, because nothing widened; §7 books what stays
open.

## 5. Guardians, measured before and after from a clean tree

Base = this worktree with the change stashed (`git stash -u`), same machine, same run.

| guardian | base | after | booked |
|---|---|---|---|
| `cargo test --no-fail-fast` (fisch) | — | **exit 0**, 61 `test result: ok`, 0 failed | — |
| `pruefe-emission.sh` | — | **ALL PASS** — 37 durchgestochen, 277 of 277 translate, 2 reverse probes; `283 of 283` emitting files compile, clang agrees on every one | with `MARKE_EMIT=116`; see below |
| `#print axioms gabbro_ziel` | 3 standard | **3 standard** | — |
| `pruefe-kennungen.py` | — | **ALL PASS** (412 codes, each to exactly one file) | 411 → **412** (`N380`) |
| `mutiere-pruefer.py --anker` | 394 of 422 | **394 of 422** | re-anchored, see below |
| `pruefe-englisch.py` ratchets | 30 feeders / 7958 German comment lines / 676 German identifiers | **30 / 7958 / 676** | unmoved |
| `pruefe-todo.py` | 14 findings | 14 findings | unmoved |

### The numbers that move, each with its reason

- **`MARKE_EMIT` 114 → 116.** The two new examples emit. The counter is the merger's, so
  the tree is left at 114 and the guardian says so in its own words: *"FUND: 116 statt 114
  emittierende Dateien in beispiele/ -- die Marke gehoert nachgezogen (der gute Fall, und
  trotzdem ein Befund)."* Measured with 116 substituted on the server: **`EMISSION: ALL
  PASS`**, exit 0, stage 10 reached. `MARKE_EMIT_G` is untouched at 18 — the five poison
  files do not emit.
- **Diagnostic codes 411 → 412** (`N380`). `pruefe-kennungen.py` ALL PASS.
- **`mutiere-pruefer.py`: one anchor re-anchored.** `laden-nimmt-die-speicherordnung`
  pinned the literal line `let Some((typ, _, ordnung)) = u.atomics.get(&quelle) else {`,
  which moved when the `awaits` arm started asking `atom_target`. `--anker` reported it the
  same day (394 → 393, `!! FEHLT`), and it is back at 394 with the mutation unchanged in
  meaning: it still swaps the store order into the load position, at the same arm. **And
  the re-anchored mutation was RUN, not assumed:** applied to the server tree, built,
  `cargo test --no-fail-fast` → `FAILED. 161 passed; 1 failed`, source restored and
  md5-compared byte for byte. *An anchor that no longer grips measures nothing and reads
  exactly like one that does — and an anchor that grips but no longer bites is the same
  thing one step later.*
- **`pruefe-zahlen.py`**: the booked numbers in `messung/KENNZAHLEN.md` are stale on master
  already (every one of the lines below was red before this change). The measured sides
  that move: `Absagekennungen` 411 → 412, `fremde Ruempfe im Korpus` 145 → 146,
  `Absagen ohne erkennbaren Grund` 163 → 164, `Zeremoniestellen insgesamt` 1773 → 1794.
  **`Mutationsanker, die im Pruefer wirklich sitzen` 394 → 393 → 394** — that one was a
  real regression for the length of an afternoon, and it is the entry above.
- **`pruefe-englisch.py`: nothing moves, and it took a rename to get there.** The first
  version of the corpus files carried German names (`1040-atomfeld-ohne-konstante-laenge`),
  and the German-word detector counted the filename quoted in `saetze.rs` — feeders 30 →
  31. All seven corpus files and the four new Rust identifiers were renamed to English.
  *A guardian that counts the language of a filename is right to.*

**Number ranges used** (AGENTS.md §7): diagnostic code `N380` (reserved `N380`–`N389`, one
used, nine free); poison files `1040`–`1044` (reserved `1040`–`1049`, five used); examples
`140`, `141` (reserved `140`–`145`, two used). The sequential counters in AGENTS.md §7 are
untouched: next free code is still `N320`, next free example still `132`.

## 6. The payoff on the real program

`/home/ubuntu/brandmauer/gab/zaehler.gab` was rewritten in this agent's scratch directory
(`.claude/muse-arbeit/kratz/atf/zaehler-feld.gab`); **the firewall project was not edited.**
The rewrite is mechanical and deliberately minimal: the header, the seven scalar counters,
their seven increment helpers, `folge`, `zaehle_urteil`, `zaehle_fehl`, `zaehle_voll` and
`lies_zaehler` are taken over **verbatim**. The one change is that `REGEL000 .. REGEL255`
and the two flat 256-way if-dispatches become one `atomic REGEL : [u32; 256]`.

| | today (256 scalars) | with the array | factor |
|---|---|---|---|
| lines of Gabbro | **5136** | **287** | 17.9× |
| items | 535 | 25 | 21.4× |
| `zaehle_regel` ops (`gabbro kosten`) | **1797** | **11** | 163× |
| `lies_regel_treffer` ops | 1538 | **4** | 384× |
| lines of emitted C | 9824 | **385** | 25.5× |
| CAS loops in the C | 263 | 8 | 33× |
| `effects` entries at `zaehle_regel` | 514 | 4 | — |

`gabbro pruefe`: `25 items, 0 errors, 16 hints` (all 16 are `E247`, the same hint the
original carries 526 times and ignores for the same reason). `gabbro kosten`: 15 bodies,
0 open, 0 derived, slack 0 or 1 everywhere. The emitted C compiles at `-O0` and `-O2` under
`cc -std=c11 -Wall -Wextra -Werror`.

### It is as correct as the 256 scalars, and that is a run

`.claude/muse-arbeit/kratz/atf/test-zf.c` mirrors the firewall lane's own harness —
single-threaded accounting, then 4 pthreads × 200 000 `zaehle_urteil(1)` +
`zaehle_regel(7)` on the SAME counters — **plus a check the 256-scalar version could not
express**: that all 254 other elements stay zero.

```text
ALL OK            (-O0, bound 64)
ALL OK            (-O2, bound 1 000 000)
```

800 000 / 800 000 on four counters, zero lost increments, no neighbouring element touched.

### One finding from the harness, and it is NOT the array's

At `-O2` with the module's declared `bounded 64 ops`, the run aborts: `zaehler_streit`
fires. **The control run says this is the machine and not the lowering.** The ORIGINAL
256-scalar module, emitted by the same binary and hammered by the same harness, aborts
identically at `-O2` and passes at `-O0`; both are lossless when the bound is raised.

| | `-O0`, bound 64 | `-O2`, bound 64 | `-O2`, bound 10⁶ |
|---|---|---|---|
| 256 scalars | 800 000/800 000 | **STREIT** | 800 000/800 000 |
| atomic array | 800 000/800 000 | **STREIT** | 800 000/800 000 |

`BERICHT-bm4.md` §6 books the contention abort as *"reasoned about, not triggered"* — on
16 cores with a `-O2` loop it triggers, and 64 consecutive lost races is not the rare event
the module header assumes. That is a finding for the firewall's own module header, not for
this tree.

## 7. What is NOT closed, named rather than papered over

1. **The same two silences are open at an ordinary table.** `T.slots[b].z` with `b : bool`
   checks clean, and so does an index into an array whose length did not fold. `N380` holds
   the atomic array only. The reason is scope, and it is honest: closing the table half
   moves corpus numbers across the whole tree and needs its own measurement; a NEW arm owes
   no corpus a migration and takes the strict rule for free. **Measured, so that the next
   lane starts from a number and not a suspicion:** `p4.gab` in this agent's scratch
   directory carries both shapes side by side, and the table half is silent today.
2. **No model form.** `Ty` has no array, `gabbro lean-g` refuses every atomic (`LG001`).
   The atomic array is in the same position the scalar atomic has always been: lowered by
   the emitter, absent from the model, and therefore outside the chain
   source → model → C. Belongs in `dokumente/OFFEN.md` beside the scalar entry; this lane
   did not edit that file, to keep the diff to one topic.
3. **Weak memory.** Every C shape here was verified on x86_64 only, like the rest of the
   tree (`SYNTAX.md` §11 bounds its own table the same way).
4. **Nested atomic arrays** are not a form and are refused (`N271`, gift 1044). No
   `atomic` declaration can write one today, so the refusal costs nothing; if the grammar
   ever grows one, the refusal is where it is found.

## 8. Files

```
crates/gabbro-check/src/emit.rs     +266/-  (atom_arrays, atom_declarator, atom_refusal,
                                             atom_target, the four arms, the index hoist,
                                             benutzte_namen)
crates/gabbro-check/src/m1.rs       +160/-  (atom_array, N380, the N271 exception,
                                             index_pruefen at Exchange and AwaitLoad)
crates/gabbro-check/src/saetze.rs   + 66/-  (m1.atomic_array_bound; m1.bare_atomic_place
                                             extended)
instrumente/mutiere-pruefer.py      + 11/-  (laden-nimmt-die-speicherordnung re-anchored)
beispiele/140-atomic-array-counter.gab            new
beispiele/141-atomic-array-pairing.gab            new
beispiele/gift/1040..1044-atomic-array-*.gab      new
```

Scratch, not committed: `.claude/muse-arbeit/kratz/atf/` — the wall probes (`w1`–`w5`,
`p1`–`p5`), the effects falsifications (`e1`, `e2`), the rewritten counter module
(`zaehler-feld.gab`) and the two harnesses (`test-zf.c`, `test-orig.c`).

*Not merged, not pushed.*
