# CROSSBODY-REGEL: cross-body freshness expiry already has a transport -- so `H023` is NOT built here

Worktree lane-135, base 6f26e76. Scope: expire V4 taints across call edges
using callee write-hulls, with `nebeneinander.rs` as the candidate home;
gift probes 752/753/754; this note. Verdict, stated first: **no new checker
code in this lane.** The transport exists -- in `m1.rs`, not in
`nebeneinander.rs` -- and a second one would duplicate it. What this lane
ships is three pinning probes plus this report. `H023` stays assigned-free
and unbuilt, deliberately.

## 1. The transport that already runs (evidence, not belief)

`FRISCHE-V4-ENTWURF.md` §2d orders: a call kills taints of carriers in the
callee's writes-hull. That sentence is implemented, today, in
`crates/gabbro-check/src/m1.rs`:

* `rufe_toeten_fakten` (`m1.rs:3214`): after the V1--V3 kill, the V4 kill runs
  at the same edge (`m1.rs:3246-3260`). A readable hull expires per carrier
  (`frische_toeten_traeger`); an unreadable one expires everything
  (`frische_alle_toeten` -- the coarse rule, same direction as V1--V3).
* `geschriebene_orte` (`m1.rs:3265-3311`): reads the callee's DECLARED
  `effects` (`writes`/`allocs`/`consumes`/`publishes`/`masks`), module-aware
  (`u.funktion(&self.modul, pf)`), world names only (`ist_weltname`), with
  fallback to the coarse rule on empty lists, unknown effect kinds, and
  parameter-named bases. `E008` reconciles each body hull against its declared
  list, so the declared list covers transitive writes -- the "hull" in §2d is
  read through the declaration, not re-walked.
* Both call shapes funnel through it: statement calls (`m1.rs:1427-1430`),
  `let`/`let-else` returns (`m1.rs:738`, `m1.rs:834-835`), and calls inside
  arbitrary expressions (`rufe_im_ausdruck`, `m1.rs:3180-3190`). The refusal
  itself is `M147` (`m1.rs:3676-3690`), at decision positions only
  (`frische_gebrauch`, `m1.rs:3529-3594`).

The indirect-call half is already pinned: gift/715 (statement call expires
all), gift/716 (`let`-RHS call expires all, return stays clean), gift/717
(refresh and store silent, `narrow` subject falls). What had NO probe is the
direct-call half -- fine-grained expiry per hull carrier. That is the gap
this lane pins.

## 2. Why `nebeneinander.rs` is the wrong home (three independent reasons)

1. **No taint map to expire.** The V4 map (`frisch`/`veraltet`, `m1.rs:303-320)
   is per-body state threaded through `m1`'s statement walk. `nebeneinander`
   runs AFTER `m1` (`lib.rs:407-417`) and receives only `(baum, absagen)`.
   Expiring "across call edges" there means either re-deriving the map --
   duplicating ~500 lines of `m1` internals (growth rule, decision-vs-store
   positions, index-vs-content precision, loop/call kills) -- or having `m1`
   expose it, which touches `m1.rs`. Both are owned elsewhere this turn
   (`m1.rs`/`paarung.rs`/`geteilt.rs` are sibling territory); per scope the
   lane then pins instead of touching.
2. **No retroactive expiry.** `m1` has already emitted its `M147` refusals by
   the time `nebeneinander::pass` runs. A second expiry there cannot un-fire
   or re-fire them; it can only add a SECOND refusal (`H023`) on the same
   stale shape -- two codes for one defect, and every exact-fire probe of the
   `M147` family would need re-cutting in central files this lane must not
   touch.
3. **Code-to-pass mapping.** Only `W`-codes live in `nebeneinander.rs`
   (`W001`/`W002`/`W003`); the `H`-family lives in `geteilt.rs`. An `H023`
   emitted from `nebeneinander.rs` breaks the one-file-one-family invariant
   the `pruefe-kennungen.py` guardian assumes, while `saetze.rs`, the
   `mutiere-pruefer.py` register, the `BENANNT` corpus class, and
   `tests/beispiele.rs` are all frozen central -- an unsentenced,
   unregistered, uncounted code would ship. `H020` already booked its registry
   row as owed follow-up; a second one in a stranger pass is not owed, it is
   refused.

## 3. Probes (numbers 752/753/754, verified free: gifts reach 739, no `H023` anywhere)

All three expect `M147` -- the existing transport's code, not a new one. Each
file carries its verdict (the gift harness asserts presence); the silent arms
are pinned by the "exactly one" claims below, read off the implementation in
§1 (same standing as gift/703 and gift/717, whose purity the file-level run
likewise does not assert).

| probe | kind | shape |
|---|---|---|
| `beispiele/gift/752-direct-call-expires-stale-read.gab` | must fall (`-- erwartet: M147`) | `alt` read from `ZUSTAND`, direct call to `schreiber` (`writes ZUSTAND`), decision on `alt` falls |
| `beispiele/gift/753-direct-call-disjoint-hull-stays-fresh.gab` | boundary (`-- erwartet: M147`) | `intakt`: same read, call to `fremd` (`writes ANDERE`) -- decision stays silent; `faellig`: overlapping-hull control falls |
| `beispiele/gift/754-direct-call-refresh-and-store-silent.gab` | boundary (`-- erwartet: M147`) | direct-call mirror of gift/717: re-read arm silent, store arm silent, stale-decision control falls |

## 4. Pinned hole (not this lane)

* Transitive-hull reading: `geschriebene_orte` reads the callee's DECLARED
  list, not `Graph::huelle`. Soundness rests on `E008`'s reconciliation; a
  caller-side check against the transitive hull (`aufrufgraph.rs`) would be a
  second transport of the same fact -- same duplication verdict as §2.
* `H023` (or any cross-body freshness code in `nebeneinander.rs`): needs the
  taint map across the pass boundary. Owner if ever built: whoever owns the
  `m1` freshness internals, not a pairwise-interference pass.
* No `Satz` entry, no `BENANNT` entry, no count re-anchoring: central, frozen
  for this lane. Gift population moves 500 -> 503 files; the re-anchor
  belongs to integration.

## 5. Registers touched and verification

Touched: three gift files plus this note. Untouched by choice with reason in
§2: `nebeneinander.rs` (sole-owned this turn, zero lines changed);
untouched by scope: `m1.rs`, `paarung.rs`, `geteilt.rs` (siblings),
`lib.rs`/`saetze.rs`/`mutiere-pruefer.py`/corpus classes/`tests/beispiele.rs`
(central).

Only `CARGO_BUILD_JOBS=4 cargo test -p gabbro-check --test beispiele` (lane
scope; no other targets, no builds elsewhere). It covers the clean
`beispiele/*.gab` corpus plus all 503 gift files including 752/753/754. Tail
in the lane report.

## 6. Transitive (two-hop) expiry: the same transport, one hop further out (probes 769/770/771, verified free)

Numbers 769/770/771 were verified free at this base (gifts reach 763; 764-771
all absent). All three expect `M147` -- the existing transport's code, not a
new one. Each file carries its verdict; the silent arms are pinned by the
"exactly one" claims below, read off the implementation in §1 (same standing
as gift/703, gift/717, and gift/753/754, whose purity the file-level run
likewise does not assert).

| probe | kind | shape |
|---|---|---|
| `beispiele/gift/769-transitive-call-expires-stale-read.gab` | must fall (`-- erwartet: M147`) | `alt` read from `ZUSTAND`, call to `mitte` (which calls `schreiber`, `writes ZUSTAND`, covered by `mitte`'s own declared `writes ZUSTAND`), decision on `alt` falls |
| `beispiele/gift/770-transitive-call-disjoint-hull-stays-fresh.gab` | boundary (`-- erwartet: M147`) | `intakt`: same read, chain through `mitte_fremd` (`writes ANDERE`) -- decision stays silent; `faellig`: overlapping-chain control falls |
| `beispiele/gift/771-transitive-call-refresh-and-store-silent.gab` | boundary (`-- erwartet: M147`) | transitive mirror of gift/754: re-read arm silent, store arm silent, stale-decision control falls |

Measured per-file runs over the built binary: 769 reports exactly one `M147`
(at `entscheide`); 770 reports exactly one `M147` (at `faellig`, `intakt`
silent); 771 reports exactly one `M147` (at `faellig` arm 3, refresh and store
arms silent).

Why this is the same transport and not a second one: `geschriebene_orte`
reads the DIRECT callee's declared list, and the mid's declared list covers
its own callee's write because `E008` reconciles each body hull against its
declaration. Transitivity therefore arrives through the declaration, not
through a re-walk of `Graph::huelle` -- the pinned hole of §4 stands, and
these probes pin that the declared-list reading carries the two-hop shape
with it.

## 7. Booked remainder beside these probes: awaited loads do NOT expire across a call

`V011` (`paarung.rs` `stale_gebrauch` / `stale_block`) is per-body state
threaded through one block walk, branch-local on purpose, `Publish`-only --
and it never looks at a call edge. `M147` does expire across the same edge,
but it tracks plain `let x = CARRIER` reads, never `AwaitLoad` bindings. So
an awaited load in the caller, a direct call to a function whose hull
publishes the same carrier, and a use of the old binding afterwards is
silent on both maps.

Measured, not believed: a caller that awaits `F`, calls a mid that publishes
`F`, then decides on the old binding reports `0 errors, 0 hints` -- the hole
is real and stands open. Owner if ever built: whoever owns the `m1`
freshness internals or the `paarung.rs` awaited map, with the taint map
carried across the call edge the way §2 refuses to duplicate here. `H023`
stays assigned-free and unbuilt; `ableitung.rs` is untouched (its cross-body
functions -- `leite_ab`, `fehlende_kanten`, `erhebe_kantenbuch`,
`Ableitung::pfad`, `pass`, `verbreitere` / `verbreitere_fuer_probe` -- derive
or refuse edges, they expire nothing, and this lane changes none of them).

## 8. Registers touched and verification (this lane)

Touched: three gift files (769/770/771) plus this note (§§6-8). Untouched by
choice with reason in §2 (still standing): `nebeneinander.rs`,
`ableitung.rs`, `m1.rs`, `paarung.rs`, `geteilt.rs`; untouched by scope:
`lib.rs`/`saetze.rs`/`mutiere-pruefer.py`/corpus classes/`tests/beispiele.rs`
(central). No `Satz` entry, no `BENANNT` entry, no count re-anchoring:
central, frozen for this lane. Gift population moves 503 -> 506 files; the
re-anchor belongs to integration.

Only `cargo test -p gabbro-check --test beispiele` (lane scope; no other
targets, no builds elsewhere). It covers the clean `beispiele/*.gab` corpus
plus all 506 gift files including 769/770/771. Tail in the lane report.
