# Await revalidation (V011)

## Claim

A clean `awaits` load expires on a `Publish` to the same carrier. Reading the old
binding after the publish without revalidation falls as `V011`. Revalidation is a
fresh `awaits` load after the publish.

## Shapes

Stale (falls):

```gabbro
let f = F awaits { n };
n = 1;
F = true publishes { n };
if f { return n; }   -- V011
```

Fresh twin (silent): same prefix, then `let g = F awaits { n };` and decide on `g`.

Boundary (silent each):

- publish BEFORE the load, then use: the load is younger than the store;
- awaits `F`, publish `G`, use the `F` binding: a different carrier does not expire.

## Rule (paarung.rs)

- Intra-body, linear, branch-local: a publish inside one `if` arm expires uses
  inside that arm only, never uses after the `if` or in a sibling arm. Fewer ends
  recognised means fewer refusals; `beispiele/42` awaits in one match arm and
  publishes in another, and that common path stays green.
- Clean carriers only (`acquire`, `release`, `seq`): `relaxed` or missing ordering
  already falls at `V004`/`V005`.
- Read positions are the `V007` positions (`eigene_ausdruecke` plus the `narrow`
  subject); call arguments stay out for the same reason they stay out there.
- `exchange` to the same carrier does NOT expire; this rule tracks `Publish` only.

## Evidence

- `beispiele/gift/755-stale-awaits-used-after-publish.gab`: stale use, must fall V011.
- `beispiele/gift/756-fresh-awaits-after-publish-silent.gab`: stale arm falls, fresh
  arm stays silent.
- `beispiele/gift/757-awaits-expiry-boundary.gab`: stale arm falls, order-first and
  other-carrier arms stay silent.
- Unit twins in `paarung.rs` (`v011_tests`): stale falls once, revalidation silent,
  other-carrier plus publish-before-load silent.
- Targeted run: `CARGO_BUILD_JOBS=4 cargo test -p gabbro-check --test beispiele`
  (tail recorded at commit time).

## Non-goals

Store-without-decision (`ZUSTAND = alt` style) is not pinned here: any read of the
stale name, including a store value, counts as a use. The 717-style store-silence
belongs to the V4 freshness family, not to this rule.
