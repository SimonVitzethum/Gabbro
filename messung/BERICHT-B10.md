# «B10» through the cost gate — the demand first

Lane B10, started 2026-09-03 at `1cb66b0`. Running report; every finding lands here as it
is measured, with the command beside it.

---

## 0. Two gaps wear one booking, and only one of them was named

`F03` refuses at the emitter with

    `queue` -- «B10»: `traverse` yields no value and knows no `break`, so `by consuming`
    drains the WHOLE queue; that is a different program

The owner's decision names something else:

> `traverse … over mappings of` needs a named resolver from frame to readable node; the
> generated C takes it as a parameter, and Gabbro has no clause to write it.

**These are two different gaps.** `messung/BERICHT-H0.md`:129 calls the second one
*«B10»-shaped* — a family resemblance, not the same entry. The tree keeps them apart in the
emitter itself: `emit.rs`:8487 carries the `queue` refusal, `emit.rs`:8512 the `mappings of`
one, and their texts say different things.

    grep -rn '«B10»' --include='*.gab' --include='*.md' --include='*.rs' .

So the demand has to be measured **twice**, once per gap. It comes out very differently.

---

## 1. The demand for `traverse … over mappings of` — ZERO live sites of 57

Every `traverse` statement in the tree, grouped by domain:

    grep -rn --include='*.gab' -E '^\s*traverse ' . | grep -v '^\./\.claude'   # 57 lines

| domain | statements |
|---|---|
| `slots of` | 29 |
| `descendants of` | 10 |
| `ancestors of` | 8 |
| `elems of` | 3 |
| `queue` | 3 |
| `threads` | 2 |
| `chain(a, b) in` | 1 |
| **`mappings of`** | **1** |

**And that one site is a poison probe.** It is
`beispiele/gift/571-walk-ebenen-laufen-um.gab`:52, whose first line reads `-- erwartet: K003`:
a file built to prove the cost pass refuses a wrapped `levels`. It must **not** lower. A
lowering would take its expected verdict away.

The site that once wanted the construct was `messung/fragmente/F09.gab`. The `H = 0` lane
removed it, and the reason was not convenience: `SPRACHE.md` §5.4 already said a run-time
traversal over `mappings of` can hold no cost promise. The statement about the SET became a
`walk` invariant, the statement about ONE entry became an ordinary routine. **The demand did
not move to another file; it dissolved.**

    grep -rn 'traverse[^;]*mappings of' --include='*.gab' .
    # F09.gab:42,47  -- comment lines documenting the REMOVED statement
    # gift/571:52    -- the poison probe

**Live demand: 0 of 57.**

---

## 2. The demand for the named resolver — ONE site, a test driver

`walk W` emits `W_absteigen`, and it takes the resolver as a C function pointer:

    crates/gabbro-check/src/emit.rs:10342
        static inline __attribute__((unused)) bool {n}_absteigen(…,
                bool (*knoten_zu)(uint64_t, const {n}_knoten **), const {elem} **blatt)

Callers in the whole tree:

    grep -rn 'absteigen' --include='*.rs' --include='*.sh' --include='*.gab' --include='*.md' .

**One** — `instrumente/pruefe-emission.sh`, the `fragment9` driver, four calls in one C
`main`. No Gabbro program calls it, and none can. Eleven `walk` declarations stand in the
corpus; every one of them emits a descent function that carries
`__attribute__((unused))` because nobody uses it.

    grep -rn '^\s*walk [A-Za-z_]* levels' --include='*.gab' .   # 11

The resolver in that driver is nine lines of C and its whole content is one comparison
against one constant frame. It exists to make the `fragment9` Durchstich measure the
descent — **it is measuring apparatus, not a program.**

Caprock was checked as the third source of demand. Its one real page-table descent is
`crates/caprock-hal/src/x86_64/vtd.rs`:1408, `slpt_free`, and it needs **no** resolver: it
reads `(tbl + i * 8) as *const u64` directly, so the frame IS the readable node. It also
walks NODES rather than mappings, so it is not this domain at all.

**Live demand: 1 site, and that site is a test harness.**

---

## 3. Rule A settles it, and the tree booked it that way three times already

Rule A: *no construct without measured demand.* A construct for one caller — and a caller
that is measuring apparatus — is what the rule exists to prevent.

The booking is not new. `dokumente/PFLICHTEN.md`:398 carries the decision of 2026-08-20:
`mappings of` is the **leaf set**, because W^X is a statement about the set. What follows
from that decision was written down at the same time and has stood since:

> *a run-time traversal over the leaf set will carry no cost promise afterwards — that is
> the consequence of the decision, and it is borne, not defined away.*
> — `crates/gabbro-check/src/emit.rs`, above the refusal

A construct with zero live callers, whose first act would be to lose the cost promise the
whole domain was built to carry, does not need a gate to stop it. **It fails at the demand.**


---

## 4. The gate anyway, criterion by criterion

The demand already settles it, but the owner asked for the gate, and a criterion measured
is worth more than a criterion assumed. Baseline first, so that any later figure has
something to be a change against.

    ssh ki-pc-fisch-101 'cd gabbro-b10 && cargo test --offline --no-fail-fast'
    # 402 passed, 0 failed  (31 result lines, summed -- a single `tail` truncates the log
    #                        and reported 36; a measurement that cuts its own population
    #                        measures the wrong question)

### Criterion 1 — no new source word: **HOLDS, and there is a precedent word**

    python3 instrumente/zaehle-wortschatz.py     # 221 words / 208 without a reason / 333 positions

`via` is **already in `kw.rs`** (line 321) and already stands in two positions, both of
them the shape *"name a mechanism by an identifier"*:

    dokumente/SYNTAX.md:250   entrydecl = "entry" ident [ "vector" constexpr ] [ "via" ident ] …
    dokumente/SYNTAX.md:717   reach     = place "reaches" place "via" ident ;

A resolver clause in the `walk` declaration — `via <ident>`, naming a declared `fn` — would
be a **new position of an existing word**. That is precisely the «B13» shape (`count`
reserved without a production, `anzahl(o)` parsing at the same place), and the word count
would stay at 221 while positions went 333 → 334.

**So criterion 1 is not what stops this.** Worth writing down, because the cheap assumption
is the opposite one.

> The tool says so about itself: *"a new position of an existing word — the figure above
> counts it, the ratchet does not catch it, and it is the form in which the vocabulary has
> demonstrably grown since 2026-08-28."*

### Criterion 2 — one pass slot: **HOLDS for the clause, FALLS for the construct**

Twelve passes, `messung/PASSREGISTER.md`. A `via <ident>` clause needs name resolution
(`D017`-shaped), a signature check, an effects join (the resolver READS), and an emission
change — all in passes that exist. No new pass.

**The construct on top of it does not fit, and the pass that refuses it is the cost pass.**
Measured, not argued, on a `walk T levels 4` with `node : [Pte; 512]`:

    ssh ki-pc-fisch-101 'cd gabbro-b10 && ./target/debug/gabbro pruefe /tmp/b10probe.gab'
    error: [K001] …:21:16: `zaehle` promises <= 4096 ops, the body costs 68719476736

`512^4`. The only promise the pass accepts is the whole figure:

    ./target/debug/gabbro pruefe  /tmp/b10probe2.gab   # costs <= 68719476736 ops -> 0 errors
    ./target/debug/gabbro emit    /tmp/b10probe2.gab
    error: [C001] …:23:5: no lowering: `mappings of` -- … What is missing is the lowering:
                          it needs a generated recursive descent along `down` and `leaf`

**That is the whole shape of the thing.** Build the lowering, and every program that uses it
must write `costs <= 68719476736 ops` on its own head — or be refused by `K001`. The
construct would ship a loop about which no routine can make a usable promise. `SPRACHE.md`
§5.4 said it before the pass did, and `emit.rs` carries it above the refusal:

> *a run-time traversal over the leaf set will carry no cost promise afterwards — that is
> the consequence of the decision, and it is borne, not defined away.*

### Criterion 3 — the Isabelle counterpart builds: **baseline GREEN, nothing proposed**

    rsync -rlpgoD --delete --exclude 'target/' … ./ ki-pc-fisch-101:gabbro-b10/
    rsync -a                                  beweise/ ki-pc-fisch-101:gabbro-b10/beweise/
    ssh ki-pc-fisch-101 'cd gabbro-b10/beweise && ~/Isabelle2025-2/bin/isabelle build -D . -o threads=12'
    # Finished Gabbro (0:00:06 elapsed, 0:00:25 cpu, factor 4.29)   EXIT=0

Both transfers into the one directory, in that order. The criterion is **not decidable**
beyond this baseline, because nothing is proposed to prove: a counterpart for a construct
with no caller would be a theorem about an empty set of programs.

### Criterion 4 — `exec` untouched: **HOLDS**

    grep -n 'exec' dokumente/AUFTRAG-GABBROV.md   # §9 hold list: "`exec`s Grossschrittigkeit"

Nothing here reaches `exec`. The resolver clause is a declaration-level name binding and the
descent is already emitted; the big-step semantics does not see either.

---

## 5. Recommendation

**Do not build it. The demand is zero live sites, and the gate is not what stops it.**

Three findings, in the order they were measured:

1. **`traverse … over mappings of` has no live caller** — 1 of 57 traversals, and that one
   is a poison probe expecting `K003`. The site that wanted it dissolved rather than moved.
2. **The named resolver has one caller, and it is measuring apparatus** — the `fragment9`
   driver. Eleven `walk` declarations emit a descent function carrying
   `__attribute__((unused))`.
3. **The cost pass refuses the result anyway.** `68719476736` for `levels 4`, measured.
   Building the lowering hands every user a promise nobody keeps — the exact fault
   `K001` exists to catch, and the one the folder has already paid for twice (`revoke`,
   `A4`).

Rule A: *no construct without measured demand.* This is the case the rule was written for.

**The design, for the record, if the demand ever arrives.** The resolver clause is
`via <ident>` in the `walk` declaration, naming a declared `fn(u64) -> option index into T`
or its pointer-returning equivalent; it costs no new word, needs no new pass, and would make
`W_absteigen` callable from Gabbro. **It is worth having on its own, separately from
`traverse … over mappings of`** — it turns eleven dead descent functions into live ones and
does not touch the cost promise, because a descent along ONE path is `levels` steps and not
`node_length ^ levels`. *That is a different item, and it should be booked under its own
name rather than under «B10».*

**And the thing «B10» actually is** — the value-yielding, exitable search loop — has real
measured demand: `F03`:174, `F01`:423, five search loops in `messung/SCHLEIFENZUSAGEN.md`,
two probe sites. The template is already designed and named: `ops.suche` /
`ops finde …`, `crates/gabbro-check/src/schablonen.rs`:711, `Stand::Entworfen`, with its
obligation written out. *If a construct is to be decided today, that is the one with the
denominator — and it is not the one the decision named.*

---

## 6. The corpus-wide sweep, and a stale register line it turned up

The grep in §1 counts source text. This counts **verdicts**, over every `.gab` in the tree:

    for f in $(find beispiele messung sonden netz passlogik programmlogik -name '*.gab' | sort); do
        ./target/debug/gabbro emit "$f" 2>&1 | grep -q 'no lowering: `mappings of`' && echo "$f"
    done
    # beispiele/gift/571-walk-ebenen-laufen-um.gab      <- and nothing else

**One file in the whole tree reaches the refusal, and it is the poison probe.** That is the
demand figure taken from the checker rather than from the text, and it agrees.

While measuring it, two lines in `messung/ABSAGEFORMEN.md` turned out to be **stale**, and
they are stale in the direction that hides the finding:

| line | says | measured today |
|---|---|---|
| 231 | `mappings of` … `messung/fragmente/F09.gab` `K001` — **ungeklärt** | `gabbro pruefe messung/fragmente/F09.gab` → **9 items, 0 errors**; `gabbro emit` → 0 errors |
| 401 | refusal `6532` … `mit Fehler` … `messung/fragmente/F09.gab` `K001` | the covering site is now `beispiele/gift/571`, not F09 |

The `H = 0` lane removed F09's `traverse`; the register was not re-read. **A register that
names a site which no longer exercises it reports coverage it does not have** — the same
class as a guard that measures a mixture. Left for the owner to place rather than edited
here: `ABSAGEFORMEN.md` belongs to another lane, and two lanes moving one line is the merge
fault this week already produced six times.

    ssh ki-pc-fisch-101 'cd gabbro-b10 && ./target/debug/gabbro pruefe messung/fragmente/F09.gab'
    ssh ki-pc-fisch-101 'cd gabbro-b10 && ./target/debug/gabbro emit  beispiele/gift/571-walk-ebenen-laufen-um.gab'
