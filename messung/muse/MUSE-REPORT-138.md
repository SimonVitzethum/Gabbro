# MUSE-REPORT-138 (lane 138: transfer the footprint rule `fussOrtGB` + `kandB`)

Rust lane. The checker now enforces the exact condition of the goal theorem's
decidable footprint premise -- five new codes E245-E249, all at hint level, with
the severity itself as the measured finding.

## What was done

`crates/gabbro-check/src/wirkungen.rs` (only checker file touched, +452 lines):

- `footprint_against_guards` (wired at the end of `pass()`): per function, the
  footprint = own `requires`/`ensures` carriers + body-read carriers + direct
  callees' contract carriers (roots = whole tables/globals, the granularity of
  `D.Tab + D.Glob`). Every root some function writes must be guarded by a
  signature-held lock (`requires Held(L)` over a `lock L protects` line), else
  the leg flags: E245 (`requires`), E246 (`ensures`), E247 (body), E248 (direct
  callee, at the call site, naming the callee). E249 admits an indirect call
  only if every function behind the pointer keeps its contract carriers inside
  the caller footprint (`kandB`/`KandOk`); candidates are the address-taken
  (`&f`) functions, else every function of the unit. One flag per
  (function, carrier, leg).
- Helpers: `carrier_root`, `clause_roots` (same read detection as E220, plus
  the device-root exception), `body_roots` (same walk/filter as E010),
  `calls_with_spans`, `address_taken`, `held_guards`.
- Deliberate boundary, faithful to the model: device-rooted reads carry NO
  footprint (`regLies` contributes no `Orte`, `ZielOrt.lean:180`; device
  carriers enter only via `D.rtraeger`, which the surface cannot declare --
  default none). `syscall`/`axiom` contracts, `maintains`, `= pred ;` bodies
  unread (the E220 line). Lock identity by short name; shared holding counts
  (whether it suffices for a writer is H001's question).

`crates/gabbro-check/src/saetze.rs`: new sentence `wirkungen.fusswache`
(E245-E249, state measured).

Probes: `beispiele/gift/915-919` (one leg each; 917 carries H007, 918 E245 as
documented companions; guarded twins in-file, silent). `beispiele/110-111`
(fully silent guarded/admitted shapes; both emit and compile under
`cc -std=c11 -Wall -Wextra -Werror`).

Tests: `crates/gabbro-check/tests/fusswache.rs` (9 tests: five legs fire with
cover-but-no-guard, guarded twins silent, read-only carrier silent, E248/E249
exactly once with the admitted twin quiet).

Docs: README (91/91 examples, 623 gifts, 363 diagnostics, 709 tests),
DONE.md (same), TODO.md (`3733` -> `4634` continuation lines, of which 29 are
this lane's), `pruefe-emission.sh` marks (91 emitting examples, 12 emitting
gifts -- the four hint-level poisons emit by design).

## Corpus measurement (the task's "measure first")

- `beispiele/*.gab`: 15 of 89 fire, all hints -- E247 in 13 files
  (05, 14, 27, 28, 31, 35, 39, 41, 42, 49, 58, 64, 96), E246 in 22/96, E248 in
  22/57; E245/E249 silent. Includes single-threaded drivers (49: `hart_bereit`
  reads `ZUSTAND` written by `hart_senden`, no lock in the unit), lock-free
  sharing (41), RCU (31), boot (22). The model premise excludes every one of
  them -- for programs with no concurrency at all this is not strictness, it
  is a false positive class. Hence hint level: the condition is exact, only
  the severity is not. This is the finding the task anticipated, and it is
  load-bearing for the transfer: `fussOrtGB` as stated cannot be promoted to
  a refusal without refusing the corpus.
- Doc corpus (`FRAGMENTE`/`SYNTAX`/`SPRACHE`/`README`/`MEMO-GLEITKOMMA`):
  zero firings -- excerpts rarely declare the writer side, so carriers read
  as read-only. No BENANNT change.
- `gabbro blindstellen`: unchanged (78/170/24/12 of 285) -- the new hints
  ride existing constructs.

## Last results

- `./cargo-pruef`: `== exit 0; failing tests: 0`.
- `./emission-pruef`: `ALL PASS -- 35 durchgestochen, 236 von 236 uebersetzen`
  (after staging, so the new files are in stage 9; the gift lid
  `MARKE_EMIT_G` moves 8 -> 12 with reason -- hint poison emits by design).
- `./lean-bau`: `Build completed successfully (89 jobs).` (no `grammatik/`
  changes).
- `pruefe-kennungen.py`: ALL PASS, 363 codes. `pruefe-saetze.py`: 363 codes,
  145 sentences, 55 without, 0 invented.
- `pruefe-todo.py`: 9 findings, all pre-existing/speech-probe (mine fixed).
- `pruefe-englisch.py`: exit 1 as at baseline (1 booked German message in
  `schablonen.rs`, pre-existing glued seam `saetze.rs:2014`); nothing in new
  code, messages, or comments.
- `pruefe-zahlen.py`: red at baseline (wave drift in PASSREGISTER/README/
  PLAN patterns); the one line of mine (`3733` -> `4634`) booked.

## What remains open

- The device leg of (1) is vacuous by construction (no `rtraeger` surface).
  If the surface ever declares register carriers, the `geraete` filter is
  where they slot in -- currently a cut, stated in code and sentence.
- E249 candidate resolution is by short name; a `&m::f` from another unit
  resolves only within the file (the checker is per-file, same as E220).
- Severity: if the corpus ever carries guards, E245-E249 can move to error
  level without changing the condition. Until then the hints pin the exact
  shape the theorem needs.

## What I believe is wrong (in the task)

- Nothing structural. Two notational notes: the "codes 245-249" carry the
  E letter (effects pass; the kennungen guardian binds one code to one file,
  and the rule lives in `wirkungen.rs`); gifts are `-- erwartet: Hinweis
  E24x`, the pinned-hint form the gift runner supports since S007.
- "Every newly refused example is a finding" + "`./cargo-pruef` green" +
  the strict `beispiele.rs` gate jointly force hint level -- there is no
  error-level reading of this task that ships. The report above states the
  finding instead of weakening the condition.
