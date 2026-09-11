# Bau from bodies: `Geteilt.Bau` beside `H013` (lane 132)

Worktree lane-132, base 6f26e76. The proof (`grammatik/Grammatik/Geteilt.lean`)
speaks about one closed-world declaration per unit -- `Bau` -- and feeds it into
the W5 premise (`ungeteilt_aus_baulauf`: an unshared carrier belongs to one
thread). The checker never built it: `H013` answers the shared question by hand.
This lane builds the Bau from real bodies in Rust and evaluates the W5 premise
over it BESIDE `H013` -- computed, pinned silent, verdict unchanged.

## 1. What is built, from what source each

`crates/gabbro-check/src/bau.rs` (new; wired as `geteilt::bau`, no `lib.rs`
registration -- the Bau answers this pass's question, it is not a thirteenth
pass). Read-only reference: `grammatik/Grammatik/Extraktion.lean`, unchanged.

| `Bau` field | Lean shape | Rust source |
|---|---|---|
| `eintritt` | `bauAus` entry codes (§6) | `entry` roots via `kontexte::erhebe`, resolved with `Graph::aufloesen` in context order; unresolvable roots skipped, as at `H013` |
| `ruft` | `ruftDirekt` (W-EXT, §1) over `ruftNorm` (§2) | the graph's resolved direct calls per body (`Knoten::rufe`, which the graph collected by traversing the bodies -- contracts, index-position calls, predicates included), filtered to the declared-function domain; transitions, `ops` heads and conversions are nodes but not functions, so they are no edge |
| `schreibt_fn` | `fussAus` (§3) | the DECLARED `writes` effects per function, reduced to carrier roots, filtered to the world domain (a parameter-rooted place falls out, as out-of-domain effects fall out of `fussAus`) |
| `geteilt` / `traeger` | `geteiltAus` / `traegerAus` (§4) | handed in from the `H013` section (`welt`, `geschuetzt` -- no second computation, no second register); unknown carriers read shared (cut S5, fail-closed to the loud side) |
| `neben` | `nebenAus` (§5) | the `concurrent` sets, both ends resolved, unordered and deduplicated; an unresolvable member drops out (the refusal belongs to `W003`) |

Reachability is fuel-bounded (`schritt_bis` / `traeger_bis`, mirroring
`schrittBis` / `traegerBis`); the fuel saturates a finite call graph
(`sattigung` = function count). `pruefe_ungeteilt` mirrors
`pruefeUngeteilt`/`ungeteiltOk`: unshared carriers reached by more than one
thread.

## 2. The W5-consumption hunk (in `geteilt.rs` ONLY)

Inside the `H013` section, after the verdict loop: build the Bau, evaluate the
premise, bind it to `_w5_traeger`. It emits NOTHING -- a divergence between the
two answers is a finding about the derivation, never a refusal, and stays out
of `absagen` for exactly that reason. Zero-delta by construction: the only new
code on the verdict path is a pure computation whose result is discarded.

## 3. Probes (numbers 743/744/745, verified free: max gift nearby is 739)

Each file falls with `-- erwartet: H013` (the harness asserts containment) and
carries a verified-silent twin (`ruhig`: lock-guarded table writes under the
guard, standing in no entry -- the shape `h020_silence_and_single_fire_738`
pins).

| probe | Bau field exercised | shape |
|---|---|---|
| `beispiele/gift/743-transitive-call-reaches-unshared-write.gab` | call edges from bodies | entry dispatches to `mitte`, `mitte` calls `tief`, `tief` writes `z` -- the write reaches only through the body edge; second entry writes `z` directly |
| `beispiele/gift/744-common-lock-hull-keeps-h013.gab` | footprints from effects | both entries write `z` directly (no hop -- the declared `writes` line is the whole footprint) under a COMMON `locks L` hull, so the pair level stays silent by reading; `H013` and the Bau do not read locks and refuse the same carrier |
| `beispiele/gift/745-declared-pair-over-disjoint-carriers.gab` | pair list from concurrent sets | `concurrent { h_a, h_b };` over entries writing DISJOINT carriers `za`/`zb` -- the pair level stays silent on its own, `H013` falls once per carrier, the Bau carries the pair in `neben` (second half of `BauLauf`, not of the premise) |

Co-firing, read off the passes (not asserted by the harness, which pins
containment of `H013` only): 743/744 name two entries with overlapping write
hulls and no shared set, so `nebeneinander.rs` answers `W002` beside `H013`;
744's common lock is hull-level (open question 1), not site cover, which is why
`H020` stays silent there. 745's disjoint declared pair keeps both pair rules
silent.

## 4. Booked cuts

S2 (indirect call: no edge -- `E009` owns the refusal), S3 (writes only --
reaching means touching for writing), S4 (unresolvable pair member drops out --
`W003` owns the refusal), S5 (unknown carrier reads shared). What stays a
premise is the dynamic coverage (`BauLauf`): every access covered by static
reachability -- stated, not shown. Unit tests for the pure half
(`schritt_bis`, `pruefe_ungeteilt`, S5, root cut) live in `bau.rs`.

## 5. Behavior deltas (must be zero on clean corpus)

`cargo test -p gabbro-check --test beispiele` with `CARGO_BUILD_JOBS=4`:
`jedes_beispiel_geht_sauber_durch` green (no new refusal on any clean unit --
the hunk emits nothing) and `jedes_gift_faellt_mit_seinem_code` green over all
gift files including 743/744/745 (`H013` preserved on each). See the test tail
in the commit trailer / lane report.
