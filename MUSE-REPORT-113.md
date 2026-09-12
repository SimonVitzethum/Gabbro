# MUSE-REPORT-113 (lane E7: error mapping into the region)

## What was built

A diagnostic about a library call's region now points at the line and column
INSIDE the region the user wrote, not at the call.

1. **Span map type** -- `crates/gabbro-check/src/regionkarte.rs`, `pub struct
   RegionKarte<'a>` over `&'a [RawToken]`, registered as `pub mod regionkarte`
   in `crates/gabbro-check/src/lib.rs`:
   - `RegionKarte::neu(region)` / `RegionKarte::vom_ruf(ruf)` -- the map carried
     with the library call through the checker;
   - `erste()` -- first region token span (where a region-as-a-whole diagnostic points);
   - `fuer(i)` -- payload/expansion element `i` back to token `i`, clamped to the
     last token past the end, `None` for an empty region (no user line to point at);
   - `ruf_span(ruf)` -- first region token, falling back to the whole-call span
     only when the region is empty.
2. **One real diagnostic routed through it** -- the E2 "translation not run"
   refusal `N069` in `crates/gabbro-check/src/namen.rs` (`melde_bibliothek_ruf`)
   now reports at `RegionKarte::vom_ruf(r).ruf_span(r)` instead of `r.span`, and
   names the first region token in a note. Unresolved calls (`N057`) stay at the
   call span: they are about names, not region content.
3. **Tests**:
   - `crates/gabbro-check/tests/paesse.rs`:
     `library_n069_points_at_first_region_token_across_lines` (statement position,
     region over three lines; asserts reported line AND column equal the `dispatch`
     token's site via `Zeilenindex`, and that the token line is below the call line)
     and `library_n069_points_into_binding_position_region_too`;
   - unit tests `regionkarte::tests::{payload_index_maps_to_its_token_in_order,
     payload_index_past_the_end_clamps_to_the_last_token, empty_region_maps_nothing}`;
   - gift probes `beispiele/gift/875-library-region-span-statement.gab` and
     `876-library-region-span-binding.gab` (`-- erwartet: N069`, multi-line regions).
4. **Register updates**: sentence `namen.bibliothek_ruf` in `saetze.rs` records the
   span routing and probes 875/876; `README.md` and `DONE.md` poison counts
   585 -> 587 (own convention: old value struck through).

## Deliberately NOT used

- New codes 205-209: no new refusal was needed -- the routed diagnostic is the
  existing `N069`, which already has a sentence and a `BENANNT` entry, so no
  sentence ratchet, code-ownership or corpus-name guardian moves. The unused
  ranges stay free for later lanes.
- Gift probes 877-879: two probes pin both call positions; the rest stay free.

## Verification

- `./cargo-pruef` ends `== exit 0; failing tests: 0` (all suites green).
- New tests run and pass individually: 2/2 in `paesse`, 3/3 in `regionkarte`.
- Rendered check: `target/debug/gabbro pruefe beispiele/gift/875-…` reports
  `error: [N069] …875…:24:9` with the caret under `dispatch` inside the braces.
- `./lean-bau`: `Build completed successfully (61 jobs)` -- `grammatik/` untouched.
- Guardians: `pruefe-saetze.py` (55 ohne Satz = mark, green), `pruefe-kennungen.py`
  (ALL PASS), `pruefe-todo.py` shows only the 3 findings that already exist on the
  clean tree (verified via `git stash` baseline); `pruefe-englisch.py` exits 1 on
  baseline too (pre-existing); `pruefe-vergabe.py` ratchets unchanged (24/80,
  pre-existing). README Kennzahlentafel check passes (blind-spot numbers unmoved).
- `./emission-pruef` NOT run: the emitter is untouched (only a diagnostic span and
  notes changed) and neither new probe expects emitter codes, so no emission unit
  can see a difference.

## Open / for later lanes

- `fuer(i)` has no caller yet: it is the hook the translator (lanes E3/E5) will use
  when payload elements exist. Until then it is covered by unit tests only.
- Empty region (`@lib#f(a) { }`): parses, `N069` falls back to the call span. If a
  later lane wants an explicit "empty region" refusal, code `N205` is free.
