# MUSE-REPORT-145: null dereference in beispiele/38

Lane 145, 2026-09-13. Verdict: **the CHECKER must refuse the program.**
The emitter lowers `= 0` faithfully and has no move: there is no non-null
spelling of address 0 in C.

## What was measured

- `beispiele/38-unveraenderlicher-zeiger.gab` emitted
  `static Platz * const tz = (Platz *) (uintptr_t)0;` with
  `tz->slots[i].a = 5;` in the body (surface construct:
  `static tz : ptr<normal, rw> Platz = 0;`, checker said `0 errors`).
- The prior lane's cure (route through `(uintptr_t)`, 2026-09-02) is
  spelling, not cure: `(uintptr_t)0` is still an integer constant expression
  with the value 0, hence still a null pointer constant (C11 6.3.2.3p3).
  Measured: the unchanged emission under `-fsanitize=undefined` aborts with
  `member access within null pointer` at the store (exit 1).
  `clang --analyze` stays silent on the same file -- the 2026-09-02 silence
  was the tool's, not the program's.
- Corpus sweep (emit every file, grep emitted C for `(uintptr_t)0`):
  **before: 239 emitting units, 1 hit** (`beispiele/38`, confirmed in the
  saved pre-change emission); **after: 239 emitting units, 0 hits**
  (95 `beispiele/`, 12 `beispiele/gift/`, 74 + 58 `messung/`, 0 `messungen/`).
  The only other surface `ptr = 0` sites (`messung/k3-fragmente/K01`, `K07`,
  both `static mut`) never emitted -- both are refused on other grounds
  (`M119`, `E010`) before and after.

## What was built

- **Rule `N260`** (`crates/gabbro-check/src/namen.rs::immutable_null_pointer`,
  wired into `namen::pass`; helpers `declares_pointer`,
  `refuse_null_pointer`, `walk_block_for_null_lets`): an immutable pointer
  (`static` without `mut`, `let` without `mut`, `const`) whose initializer
  folds to `0` (`Umgebung::konst_wert`, so value-based -- a `const` name for
  zero, `(0)`, `1 - 1` are the same refusal) is refused. `static mut ... = 0`
  stays silent (kernel NULL-init idiom, flow decides); nonzero numbers stay
  `M140`'s; decay stays silent. The body walk reuses the exhaustive
  `crate::unterbloecke`, so a new statement form breaks the build instead of
  silently leaving the walk.
- **Sentence** `namen.immutable_null_pointer` in `saetze.rs`
  (with-code, so the sentence-less ratchet stays at 55).
- **Poison probe** `beispiele/gift/931-null-pointer-through-an-immutable-static.gab`
  (`-- erwartet: N260`, refused with N260 ALONE).
- **Tests**: new `crates/gabbro-check/tests/null_pointer.rs` (10 tests:
  static/let/const fall alone, mut twins silent, const-indirection falls,
  nonzero is `M140`, decay silent, rehang still draws `M118` beside `N260`);
  `korpus.rs` BENANNT entry; `gestalt.rs` null row now pins the
  `M140`-to-`N260` handoff; `komplement.rs::no_null_spelling_in_example_38_emission`
  pins the repaired emission (store present, no `(uintptr_t)0`);
  `rechenwerk.rs` M118 assertions moved from rendered-text search to code
  lists (the `N260` note names `M118` in its text).
- **Repaired `beispiele/38`** (still clean, still emitting): the store is a
  `static mut SPEICHER : [Platz; 4]`, the function binds it with
  `let tz : ptr<normal, rw> Platz = SPEICHER`. Emission holds no null
  spelling, runs clean under UBSan and ASan (`a=5`), agrees `-O0`/`-O2`.
  The M118-static/`T * const` lesson is gone with the old declaration --
  the file says so in its header. An immutable `static` pointer has no valid
  spelling left (number: `N260`/`M140`; array name: checks but `C001`s) --
  booked in the file as the open remainder.
- **Docs**: `BEWEIS.md` row 9 + a dated second-cut section;
  `C-SPEICHERMODELL.md` finding 1 marked fixed-at-checker.
- **Ledgers I moved** (all verified against today's tool output):
  codes 368/369, gifts 639/640, examples 95, sentences 148/149,
  blind 78->77 / poison-only 24->25 (the repair covered a cell, the probe
  added one), gruende tragend +1 with dated entry. `pruefe-todo.py`
  18 -> 12 Befunde (all remaining pre-existing). `pruefe-zahlen.py` was
  first run after the change (23 Befunde) and stands at 22 after the
  poison-only ledger fix -- no zahlen baseline exists, so attribution is
  per-Befund: none of the 22 names this lane's objects.

## Gate results

- `./cargo-pruef`: **exit 0, 0 failing tests** (full suite).
- `./emission-pruef`: **ALL PASS -- 35 durchgestochen, 240 von 240
  uebersetzen** (incl. ASan stage, no finding).
- `./lean-bau`: **Build completed successfully (103 jobs)** (no Lean
  changes in this lane).
- Guardians: kennungen ALL PASS (369, N: 93); saetze 369/149/55-holds;
  vergabe candidates still 29, N260 not among them; englisch adds zero
  German messages/Zubringer/comments (comment ratchet still red at
  baseline 7949, unchanged); gifttreffer +1 seen/+1 clean/+0 masked
  (verdeckt still baseline-red at 25, syscall 850-854 still failing --
  both pre-existing, other lanes').

## Open remainders

1. `static mut p : ptr<T> = 0` still lowers to a null spelling; dereference
   without prior assignment is UB the checker does not see (flow, K01/K07
   shape). Needs flow-sensitive nullness or an `option`-like nullable
   pointer -- a new feature, not a rule.
2. Immutable `static` pointers are uninhabitable: the checker accepts
   array decay in static-init position but the emitter refuses it
   (`C001`). A future emitter lane can lower `static T * const p = ARR;`
   (a valid C address constant) and re-inhabit them.
3. New rule has no `mutiere-pruefer.py` anchors yet (mutation coverage for
   `N260` unmeasured).
4. Pre-existing redness left untouched: EBNF/Kennzahlen ledgers,
   englisch comment ratchet (7949 vs 7905), gifttreffer syscall probes +
   verdeckt 25, zahlen drift (PASSREGISTER/Zeremonie/Mutation/Umgebung).

## Where the task is wrong

- The task's emitter branch ("fix emit.rs so no null pointer is
  dereferenced") is unimplementable for this program: keeping the value 0
  and dropping the UB cannot both hold in C. The `(uintptr_t)` spelling the
  task implicitly blesses as fixed is still null. The decision for the
  checker is therefore forced, not a judgment call.
- "Diagnostic code from the free range 260-264": `N259` is reserved
  (writer side, `H007`), so the usable free code was `N260` -- taken as
  stated.
- The task says nothing about `beispiele/38` staying a clean example, but
  `jedes_beispiel_geht_sauber_durch` requires it; the repair (not deletion)
  is owed to that test, and the M118 example-level witness could not be
  preserved -- only the rule, its inline tests, and the refusal are.
