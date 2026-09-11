# H020: a write a `locks` line covers but no guard holds

Worktree lane-104, base 58d6b83. G3 remainder of `SYNTAX-INTERFERENZ-ENTWURF.md` §4
(`NEBENLAEUFIGKEIT-ENTWURF.md` §6 Q1, checker-lane half): the checker had no held-set
analysis, so `disziplin` -- every writer holds the carrier's guards -- was assumed, not
checked. This lane supplies held lock sets per write site for the intraprocedural
direction and pins one rule on them.

## 1. The rule

A direct write (`=`, `publish`, `exchange` target) to a place covered by a declared
lock's `protects` list falls with `H020` when its ONLY cover is a declared
`effects { locks L }` line: no enclosing `locks L` block, no `requires Held(L)`.

```gabbro
lock L protects { T } rank 0 held <= 100 ops;
impl fn m(j : index into T, m : index into T)
    effects { writes T.slots, locks L } costs <= 16 ops
{
    locks L { T.slots[j].v = 0; }   // redeems the line (`H011`), guards THIS write
    T.slots[m].v = 1;               // -> H020: the line covers the function, and no
}                                   // guard covers this site
```

## 2. Why the gap is real: the `H007`/`H011` handshake

`H007` (`schutz` in `geteilt.rs`) counts the line as HELD at every site; `H011`
redeems the line at FUNCTION granularity (own block, callee hull, or `requires`).
A body that takes `L` around one statement satisfies both and still executes its
other write unguarded. Before this rule that program passed with zero errors --
function-granularity cover is not site cover.

`H020` fires if and only if `H007` stays silent because of the line, so one site
never draws two refusals for one missing guard. Disjoint by construction:
no line at all is `H007`'s; line plus site cover is clean.

## 3. Where per-body held sets are computed (read-only map)

Investigated first, changed nowhere. Five sites, one new:

| site | what it supplies | owner |
|---|---|---|
| `aufrufgraph.rs` `Graph::huelle` / `huelle_der_gerufenen` | transitive effect hull per function (`Huelle.wirkungen`, `locks`/`locks shared` lines among them) | shared infra, untouched |
| `geteilt.rs` `Rufwissen::nimmt` + `forderungen` | caller-side lock knowledge over the hull (`H006`/`H012`/`H005`) | untouched |
| `geteilt.rs` `schutz` (`H007`) | per-site walk with the MIXED set `da` (blocks + lines + requires) | untouched |
| `geteilt.rs` `fenster_sammeln` (`H018`) | per-write-site held sets, dma/mmio scoped | untouched |
| `geteilt.rs` `h020`/`h020_block` (NEW) | per-write-site held sets, general: enclosing `locks` stack only, lines and requires carried beside it so the rule can tell cover kinds apart | this lane |
| `m1.rs` `frische_*`, `veraltet`, `traeger_im_ausdruck` | freshness internals | lane-103's territory -- NOT read for this rule, NOT touched |

## 4. Probes (numbers 737/738/739, verified free: max gift is 733, no `H019`/`H020` anywhere)

| probe | kind | shape |
|---|---|---|
| `beispiele/gift/737-line-covers-write-without-guard.gab` | must fall (`-- erwartet: H020`) | block around one write redeems the line, second write naked; guarded twin in-file |
| `beispiele.rs` `h020_silence_and_single_fire_738` | must pass + purity pin | block-guarded and `requires Held(L)` shapes stay error-free; 737/739 fall with EXACTLY `["H020"]` (the file-level gift run only asserts firing, so single-fire purity is held here) |
| `beispiele/gift/739-hull-redeems-line-write-stays-naked.gab` | boundary (`-- erwartet: H020`) | line redeemed through a callee hull (`H011` silent), own write naked; full-delegation twin in-file |

## 5. Exemptions and booked cuts

Exempt, each with its owner: `spec fn` (`H007`/`H018` share it); no line (then `H007`
fired); `requires Held(L)` (caller's duty -- the `beispiele/01` `aushaengen` idiom
writes naked under `requires Held(KAPPEN)` and must stay clean); RCU-touched places
(`H010` owns RCU writes, even line-covered ones); reads (G3 `disziplin` constrains
writers); calls (transitive writes through the call edge need the `verlangt` + hull
join -- open, not this rule).

Corpus audit (read-only, 2026-09-11): no `dokumente/` fragment matches the trigger.
`FRAGMENTE.md` B1 (`unlink`, `release_slot`, `delete_leaf`) writes naked under
`requires Held(CAPS)`/`Held(MEM)` -- exempt; `CAPS` protects `{ plaetze, cdt }`,
which the `c.slots` writes never touch. `call` (fence 567-719) names `locks SCHEDS`
with no in-unit declaration. `toeten` and `holen` write under their blocks.
`SYNTAX.md` `locks CAPS` is undeclared (`H016`'s); the `forever` sketch body does not
parse to writes. `SPRACHE.md`, `README.md`, `MEMO-GLEITKOMMA.md` name no lock lines.

## 6. Booked follow-up (not this lane)

* No `Satz` entry: `saetze.rs` is frozen for this lane (central). `H020` ships
  sentenced only here; the registry row is owed.
* `BENANNT` (`korpus.rs`) untouched per scope: by the audit in §5 `H020` fires
  nowhere outside its probes, so no entry is owed today. If a later widening makes
  it fire on the corpus, the entry belongs to that lane.
* Call-edge direction: held set AT a call site against the callee hull's writes
  (`NEBENLAEUFIGKEIT-ENTWURF.md` §6 Q1, full answer).
* `m1.rs` freshness internals untouched throughout (lower-numbered lane owns ties).

## 7. Verification

Only `CARGO_BUILD_JOBS=4 cargo test -p gabbro-check --test beispiele` (lane scope;
no other targets, no builds elsewhere). The run covers the clean `beispiele/*.gab`
corpus (no new silence broken), all 500 gift files including 737/739, and the 738
pin test. Tail in the lane report.
