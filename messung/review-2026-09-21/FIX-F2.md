# Fix lane F2 — dynamic arenas (review G08 F1–F4, F6)

*2026-09-21, branch `review-0921-integration`, base `fa5c6846` (fix lane F1). Built and
measured LOCALLY (fisch unreachable), `free -g` beside every heavy run: 31 GB total, 20 GB
available each time.*

## What was fixed

### 1. `N426` against the UPPER commit bound (G08 F1, HIGH) + `grow`'s `else` order

`crates/gabbro-check/src/arena.rs`. The runtime never decommits, so the ceiling is a
whole-run question. The pass now carries, beside the old LOWER bound (`verpflichtet`, `min`
at joins — kept for a future `R-commit`), an UPPER bound per arena (`Stand::hoch`):

- joins take the maximum; `reset` leaves it alone;
- loops: the body's per-pass commit `d` is measured on the first walk; the second walk (the
  later passes) starts at entry + `d`·(N−1) for `retry … bounded N`, at `UNENDLICH` for
  `forever`, `traverse` and a non-constant `retry`; after the loop entry + `d`·N resp.
  `UNENDLICH`;
- calls and `start`s add the callee's per-invocation bound. The bounds come from silent walks
  of every body, iterated to a fixpoint over the call graph (a cycle that commits saturates;
  a call through a place is `UNENDLICH` into every grown arena);
- the whole-program total sums call-graph roots (routines no other routine calls or starts,
  plus cycle members) once per load, a `concurrent` body once per naming, an `entry …
  dispatch` target without bound; each body starts at floor + total − its own share;
- `N426` refuses every `grow` whose upper bound + amount may pass `M` (message names the
  bound, or says "no bound").

Soundness argument (in the module head's terms): if no `grow` is refused then floor + total ≤
`M`, because the walk that computes a root's bound reaches floor + total on its maximal path,
and the first point past `M` is either a `grow` (refused) or a call whose callee, entered at
floor + total − its share, crosses inside (induction down the call chain).

The `else` of `grow` now walks from the state BEFORE the request (PLAN §4); before, it walked
from the bumped state (a `grow` inside the `else` fell spuriously).

**Decision: `N426` reused, not a new code.** The rule is the same ("a commit the checker
cannot hold below the ceiling is refused"); only its measure was wrong. Sentence
`arena.wachsen_commit` rewritten (aussage, vorbehalt with the run model and the overcommit
note, gemessen_an).

Poison probes (all accepted by the pre-fix binary, measured): gifts **1132** (`grow` in
`forever`), **1133** (after an `if` that grew), **1134** (two functions), **1135** (callee
called twice). `paesse.rs`: `arena_grow_obere_schranke_n426` (branch, two roots, callee
twice, `retry bounded 2` × 5 — each with a positive twin provably below the ceiling),
`arena_grow_ohne_schranke_n426` (forever, recursion, `entry` dispatch target),
`arena_grow_else_vom_alten_stand` (positive; red before the fix). Unit tests:
`verbindung_max_obere_schranke`, `generation_ohne_zaehlung_bewegt_sich_an_der_verbindung`.

### 2. `N211` across calls, parameters and untracked carriers (G08 F2, MEDIUM) — full version

- per routine a may-reset set (own `reset`s ∪ callees' ∪ started roots', fixpoint; a call
  through a place = every arena the program resets); a call/`start` applies it as a fresh
  generation;
- a parameter typed `index into A` is live in the entry generation (until the first `reset`
  of `A` on the path, here or in a callee); an argument at such a parameter is checked like a
  read at the call;
- `let j = a;` copies tracking (before: `j` became untracked and silent);
- an index reaching `A[…]` through a global, a field, a slot, a call result or an untracked
  local: refused wherever the program resets `A` at all;
- calls inside one expression are applied before its reads (C operand order is unspecified);
- the join now also moves a generation that changed on one side without a count (was a
  latent hole once calls reset).

Gifts **1136** (the review's `alloc; leere(); alloc; A[a]`), **1137** (parameter after
`reset`), **1138** (call result, program resets `A`). `paesse.rs`:
`arena_reset_im_gerufenen_n211` (two levels deep, one branch; twin reads first),
`arena_index_ueber_den_aufrufrand_n211` (stale copy handed to a parameter; twin clean),
`arena_index_ohne_generation` (twin clean where nothing resets). Sentence
`arena.erklaerung` updated. Claims corrected to exactly this in `ArenaReset.lean` (header +
CUTS), `beispiele/154` header (comment only), PLAN-DYNAMISCH §6, SYNTAX §9.1, module head.

**Remaining gap (stated everywhere above, `OFFEN.md` O20):** a `reset` in a routine running
CONCURRENTLY with the index holder (another `concurrent` root, a `child` path, an interrupt
handler) is not applied — generations are tracked along one thread of control.

### 3. `ArenaDyn.lean` (G08 F4)

Removed (not renamed) the decorative `region_verpflichtet`/`_zeuge` (witness discharged
`hlink` without the run — lane-147 pattern) and `dynVerfein` (restated a structure field),
with `Aw0/Aw1/grow_gelingt`. Added a real statement about the one runtime fact the record
models, the past-ceiling stop over a run's commit sequence: `dynGrowListe`,
`dynGrowListe_gelingt` (total ≤ room ⇒ never stops, ends at prefix + total),
`dynGrowListe_scheitert` (total > room ⇒ stops, any order), witnesses
`dynGrowListe_gelingt_zeuge` (`8,8` under `max 24`), `dynGrowListe_scheitert_zeuge` (under
`max 16` each commit fits alone, the run stops — why the lower bound was wrong),
`dynGrowListe_zwilling` (`rfl`). Subject line and CUTS say "no refinement is claimed"; link to
Rust/C is by name only. SATZKARTE §41 added.

### 4. OOM `else` under overcommit (G08 F3)

`laufzeit/arena_dyn.c`: the `memset` is removed — commit is lazy and touch-free (the new
bytes were `PROT_NONE` until this call and commit is monotone, so a private anonymous mapping
reads zero). Comments in `.c`/`.h`, PLAN §4 (R-grow-else) and the sentence state honestly:
the `else` runs only when the platform refuses the commit (Linux: strict accounting,
`vm.overcommit_memory=2`); under the default heuristic OOM is the OOM killer at first touch.
No fail-stop is claimed; the refusal branch is untested. Measured: a local harness (scratch,
not committed) reserves 100 000 slots, grows 3000 then 96 992, checks all new slots read 0
and old data survives — `cc -std=c11 -Wall -Wextra -Werror`, exit 0.

### 5. `pruefe-osfrei.py` in the guardian run (G08 F6)

`abnahme.py` already globs every `instrumente/pruefe-*` — the script was in the population but
`NICHT FAHRBAR` (mode 644: "Permission denied"). Fixed by the executable bit (git mode
100755). Measured through `abnahme.fahre_einen`: `gruen`, exit 0; `--selbsttest` 3 of 3;
the scan: 1312 files, no OS token outside `laufzeit/`.

## Measured

| check | result |
|---|---|
| `cargo test --no-fail-fast` | 68 collections, **1252 passed, 0 failed, 1 ignored** (baseline 1244/0/1; +6 `paesse` tests, +2 unit tests); run twice, the second after the last doc edit |
| `lake build` (grammatik) | 281 jobs, green; `gabbro_ziel`: `propext, Classical.choice, Quot.sound` |
| `pruefe-emission.sh` | ALL PASS — 37 differential, 288 of 288 compile, 2 reverse probes (ASan stage 6b not run locally; a first run overlapped a `git stash` of mine and was discarded and re-run) |
| `pruefe-saetze.py` | exit 0 (433 codes, 180 sentences, 0 invented) |
| `pruefe-kennungen.py` | ALL PASS |
| `pruefe-osfrei.py` | pass (1312 files) |
| `pruefe-todo.py` | 16 findings, unchanged from base |
| `pruefe-englisch.py` | red as on base; German counts unchanged (37 German prose pieces, 7965 German comment lines, both before and after) |

**Corpus diff** (every `beispiele/*.gab` and `beispiele/gift/*.gab`, 876 files, codes with
positions, pre-fix binary vs post-fix): **0 files differ** apart from the seven new gifts. No
example uses `grow`, and no existing program carries an index across a resetting call, a
parameter, or an untracked carrier into a reset arena.

## What stays open

- **O20** (new): generations along one thread only; the commit total assumes roots entered
  once per load (a separately linked re-entry can still reach the runtime `abort`).
- Conservative edges, stated in the sentence: a recursion with `decreases` still counts as
  unbounded; a call through a place in a program with a `grow` into a writable arena is
  refused; a read beside a resetting call in the same expression falls.
- Not in this lane: `R-commit`/`R-max` unwired; PLAN §9 Lean work and the two `Spec.lean` (d)
  texts unassigned (G08 F5, TODO wave-D note); `grow A by 0` still accepted (G08 F7, PLAN says
  `n >= 1`); `beispiele/153` stale header (F7); the allocation COUNT stays per function.
- `check` item blocks are not walked by the arena pass (pre-existing; they are obligations,
  not run code).
