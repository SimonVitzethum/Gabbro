# V4 freshness: the teardown-idiom false positive (lane-43 price, booked)

Status: measured 2026-09-10 on the merge of lanes 42-51. Lane-43 closed a
real hole (V4 taints survived unknown callees: `frische_alle_toeten` on the
empty-`pfade` path, `m1.rs`, pinned by gift 715-717) and paid a real price:
fragment F1 (Caprock `delete_leaf`, frozen excerpt) now falls at `M147` on
the index `obj`, its piercing fails, and `H` rises 1 to 2 with the fragment,
ceremony and Zeremonie counts beside it. All of those cells are carried in
the same commit; nothing below reverts the fix.

## Why the firing is wrong here (and right in general)

```
let obj = c.slots[s].object;   // obj read from carrier c.slots
unlink(c, s);                  // writes c.slots
release_slot(c, s);            // writes c.slots
narrow o.slots[obj].refcount ...  // M147: obj may be stale
o.slots[obj].refcount -= 1;       // M147 again
```

Strictly, `obj` no longer equals `c.slots[s].object` after the two writes.
But `obj` is never re-compared against `c.slots`: it indexes `o.slots`, a
different, unwritten table. The value is still the right object id for that
purpose. The discipline is carrier-granular (any write to `c.slots` kills
every fact read from it) where the idiom needs use-granularity: an index
into a disjoint carrier survives writes to the read carrier.

Worse, the prescribed remedy does not apply: re-reading `c.slots[s].object`
after `release_slot` reads a FREED slot. Forcing the re-read would change
semantics, not restore safety. A refusal whose remedy is wrong is worse
than silence -- on a frozen excerpt it can only hang honestly, which is
what `H = 2` now books.

## The trade, both sides measured

Close (synthetic, constructed): unknown-callee staleness passed silently
(715 fell with `[]` pre-fix); the fix expires more and never less
(fail-closed, same direction as the V1-V3 coarse rule); clean corpus
`beispiele/` shows no over-firing (24/24 gift suite green).

Cost (real, one fragment): F1's teardown loop is exactly the
read-index-then-mutate idiom; `H` 1 to 2, one clean fragment fewer (9 to
8), 49 ceremony sites out of the count (1376 to 1327). The F05 precedent
(17 files, no measured Mangel, reverted) does NOT transfer: here the
Mangel is measured and the cost is one fragment, and `H` exists precisely
to book hanging obligations instead of hiding them.

## What precision would fix (next lane, not this one)

Index-vs-content awareness (an index into a disjoint carrier survives), or
carrier-disjointness awareness (different declared tables are disjoint in
the model; the C side is A2/A3 territory). Until then the rule over-fires
exactly on teardown loops through allocator callbacks, and F1 hangs by
name. `saetze.rs` PAARUNG `vorbehalt` staleness from lane-45 is booked
separately and left standing for the same reason (comment blast radius
against `--anker`).
