# MUSE-REPORT-144: `.gab` -> G program term (`gabbro lean-g`)

Lane 144 (item 5 of `messung/URTEIL-OPUS-2026-09-13.md` §6). The mechanical
path from a checked unit to `Programm D` exists now: a Rust exporter, a CLI
subcommand, generated files that check, and correspondence files in the
build. All green runs below were re-measured at the end, on this branch.

## What was built

**Rust exporter** (`crates/gabbro-check/src/lean_g.rs`, new, `pub mod lean_g`
in `lib.rs`): `export(source_name, tree) -> Result<String, Refusal>` prints
a Lean file defining the carrier inductives (`GTab`, `GLock`, one field
inductive per table, `GFn`), one `Signatur` per function, the declaration
`gD` (as a reducible `abbrev`, which the proofs need), context/hold
abbrevs, one `darf` theorem per held (function, table) pair, one `RufPasst`
theorem per call site, contracts, bodies, the program `gP`, the member list
`gFs`, and the two checks as `example ... = true := by decide` (plain
`decide` throughout; no `native_decide`, no `sorry`).

**CLI** (`crates/gabbro-cli/src/main.rs`): `gabbro lean-g <file.gab>`,
next to the `lean` arm with the same shape (checker runs first, errors
refuse the export, refusals name the file and the `LG` code). Help text and
`COMMAND_NAMES` extended; `crates/gabbro-cli/tests/fahnen.rs` register
extended by one line.

**Measured counterpart table** (module docs of `lean_g.rs`, printed header
of every export): tables/locks/`impl fn` with pointer/index/range
parameters, `requires Held`, comparison `ensures` over slot reads / `old` /
`result` / literals, straight-line bodies of slot writes, direct calls and
trailing `return`. **Refused by name, never truncated:** `LG001` item
without a form (globals, devices, axioms, non-`impl` fns, `locks`-without-
`Held`, empty unit), `LG002` type without a `Ty` form, `LG003` contract or
index expression without an `Expr` form, `LG004` body form without a
`Stmt`/`Endblock` form (incl. calls across different held sets,
`RufPasst.hh`), `LG005` unresolvable name/count/rank/range.

**Targets:**
1. `gabbro lean-g beispiele/104-referenz.gab` checks with `./lean-probe`:
   **0 errors**. Same for `beispiele/108-disjoint-start-locks.gab`:
   **0 errors**.
2. `grammatik/Grammatik/Export104.lean` (new, in the build): pasted
   generated definitions (namespace `G104_referenz`) plus
   `export104_fragment`, `export104_fuss`, `export104_checks` (joint with
   `r4P_fragmentG`/`r4P_fussG`), `export104_data` (14 conjuncts of
   declaration-data agreement with `r4D`). Full `=` with `r4P` is not
   statable (different declaration inductives; see finding 1) -- the
   correspondence above is the honest maximum, and the CUTS block lists
   every remaining difference precisely.
3. `grammatik/Grammatik/Export108.lean` (new, in the build): pasted
   definitions plus `export108_fragment`, `export108_fuss`,
   `export108_data` (counts, ranks, guards, disjoint held sets).
4. `crates/gabbro-check/tests/lean_g.rs` (new, 18 tests): both file
   positives, namespace derivation, and one test per refusal code/shape
   (LG001 x4, LG002, LG003 x2, LG004 x5, LG005 x3).

## Verification (all re-measured at the end)

- `./cargo-pruef`: exit 0, zero failing tests (incl. 18 new `lean_g`
  tests and the extended `fahnen` register).
- `./lean-probe` on both generated files: 0 errors each.
- `./lean-bau`: exit 0, 0 error lines; all new theorems depend only on
  `[propext, Classical.choice, Quot.sound]` (`#print axioms` in both files).
- `pruefe-kennungen.py`: exit 0.
- `pruefe-englisch.py`: completes all measurements. Three marks re-booked
  with dated per-file measurement notes (its own documented process):
  comments 7905 -> 7949 (all merged-lane drift: kosten.rs +44, emit.rs +1,
  beispiele.rs -1; lane 144 contributes 0, verified per file against the
  booking commit), feeders 23 -> 26 and sinks 1 -> 2 (mine: three emitted-
  Lean template lines and the `gDarf` template -- Lean constructor names,
  not prose). Exit stays 1, exactly as at baseline: any German sink hit,
  booked or not, returns 1 (the pre-existing `main.rs:713` message alone
  guarantees it).
- `pruefe-todo.py` crashes with a Traceback at baseline too (broken
  guardian, another lane's scope); `pruefe-syntax.py` does not exist.
- Emitter untouched, so no `./emission-pruef` owed.

## Findings (measured, in work order)

1. **Up-to-naming equality is not a Lean proposition.** The export uses
   fresh inductives (`GTab`, `GLock`, `GFn`); `r4P` uses `Unit`/`R4Fn`.
   `=` needs one type, so target (2)'s "EQUALS ... up to naming" cannot be
   stated, let alone proved. Proved instead: both decidable checks on both
   programs jointly, plus construct-by-construct data agreement. The
   alternative -- generating into `r4D`'s exact types -- would couple the
   exporter to one hand translation and is refused as design.
2. **`RufPasst.hh` is a real wall, now mechanically confirmed** (verdict
   note T): a helper called with and without a lock has no `RufPasst`
   term, so the exporter refuses it (`LG004`, pinned by
   `refuses_held_mismatch`). The checker accepts what the model cannot
   type; the refusal names the held sets.
3. **`haelt` comes from `requires Held`, not from `effects locks`.**
   108's readers hold by signature with no `locks` effect; union would
   invent witnesses, equality would refuse a good program. Effects-locks
   beyond `Held` still refuse (they would need the `locks` statement).
4. **A bare word travels as its full range** (`u32` -> `.int 0
   4294967295`), via the checker's own `breite_von`/`grenzen`. The range
   is denoted by the spelled word, not invented.
5. **Elaboration order decides whether generated proofs live.** Four
   hard-won rules, each probed in isolation under `$TMPDIR/micro*.lean`:
   carrier references must be named inductives (never `Fin` literals);
   `gD` must be a reducible `abbrev` (instance search sees through
   projections only then); `darf` facts must be top-level theorems with
   concrete types (`decide` never unfolds a plain def during synthesis);
   `D` must be pinned explicitly at `.slot`/`.durch`/`.altSlot`
   (`(D := gD)`), and literal indices need full `Expr`-type ascriptions.
   `fin_cases` is unavailable (no mathlib); `cases + decide` covers it.

## Open (not this lane)

- No driver/idle-function synthesis (`treiber`/`ruhe` stay hand-written);
  no `let`/control-flow/loop/sum forms; no costs/hold-budget/`reads`
  forms. Each refuses cleanly.
- User obligations (`KoerperGutR`) and runs stay proved about `r4P`;
  `gabbro prove` still targets `Body.lean`, not the G obligation
  (verdict items 4-5 downstream work).
- Task text notes: the G syntax lives in `Syntax.lean` (run, not defined,
  by `RufMaschineG.lean`); target (2)'s equality as discussed in finding 1.
  Nothing else in the task turned out wrong.

## New names

Rust: `lean_g::{export, Refusal}` + `collect/check_fn/emit` internals;
CLI `lean-g`. Lean: `G104_referenz::{gD,gP,gFs,...}`,
`export104_fragment/fuss/checks/data`;
`G108_disjoint_start_locks::{gD,gP,gFs,...}`,
`export108_fragment/fuss/data`. Last `./lean-bau` result line:
`== lake exit code: 0` / `== 0 error line(s) in the COMPLETE output`.
