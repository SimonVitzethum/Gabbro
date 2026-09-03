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

