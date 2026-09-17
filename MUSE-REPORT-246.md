# MUSE-REPORT-246 -- Generated per-unit driver: start.c ROOTS from the `concurrent` decl

Lane 246. Task: `gabbro build` (or an explicit step beside it) generates the driver from
the unit's `concurrent` declaration -- one wrapper per root, thread per root, join all,
idle-root shape present, lock primitives defined (mutex on hosted) -- pinned per unit so
adding/dropping a root without regenerating fails LOUDLY; plus the P017 findings list for
the syntax lane. `parse.rs`, checker passes, `emit.rs`, Lean and `MARKE_EMIT*` untouched.

## 1. What was delivered (3 files, build side only)

- `crates/gabbro-cli/src/treiber.rs` (new): the generator and the probe readers.
  `treiber::erzeuge` renders `<unit>.treiber.c` in the exact shape of
  `laufzeit/start.c` (wrapper per root, `pthread_create` per root, join loop sized by
  `N_WURZELN`, `ruhe()` idle root present but never spawned on hosted, mutex
  primitives for every lock incl. the `_nimm_geteilt`/`_gib_geteilt` pair where a
  shared lock asks for it, `NACHLAUF` marker for the test half);
  `treiber::pin_pruefe` asserts source set == driver set and `N_WURZELN` counting
  them, naming both sets on failure; `treiber::pthread_create_menge`,
  `treiber::n_wurzeln`, `treiber::gueltiger_c_name` (ASCII `[A-Za-z_][A-Za-z0-9_]*`
  only -- anything else is refused before generation, never truncated into a C
  name); `treiber::GENERATOR_KENNUNG` (`"treiber-gen-1"`, mixed into the unit
  fingerprint so a template change with unchanged sources rebuilds every
  driver-owning unit once).
- `crates/gabbro-cli/src/bau.rs` (extended): one walk (`TreiberFund`,
  `TreiberSperre`, `FunktionsForm` out of the same `modulkarte`/`sammle` parse as
  the entry rule -- no second reading of one text); `treiberregel` resolving
  every member to exactly one nullary body (unresolvable member, parameterised
  member and C-name collision refuse in sentences; duplicate namings unite);
  `TreiberPlan`; the driver step beside the entry rule (dry run prints the plan,
  the real run writes `<unit>.treiber.c` after the checker accepts, reports
  `built <unit> (+ <unit>.treiber.c)`, checks driver presence in the `Aktuell`
  fast path).
- `crates/gabbro-cli/tests/treiber.rs` (new): 4 integration tests (hand pin for
  `laufzeit/start.c`, generated pin incl. dry-run plan line, stale driver fails
  loudly both directions, 124 through the GENERATED driver with the identical
  observable behaviour as through the hand file).
- Unit tests: 6 in `treiber.rs` (`erzeugter_treiber_haelt_pin`,
  `geteilte_sperre_bekommt_geteiltes_paar`, `abgestandener_treiber_faellt_laut`,
  `vergessener_zaehler_faellt`, `c_namen_sind_ascii_woerter`,
  `zweimal_erzeugt_ist_bytegleich`) + 4 `bau::treiberregel_tests`
  (`wurzeln_sind_vereinigung_ueber_bloecke`,
  `wurzel_mit_parametern_wird_abgewiesen`, `doppelte_sperre_vereinigt_geteilt`,
  `ohne_wurzeln_kein_treiber`).

## 2. Verification (last lines, measured)

- `./cargo-pruef`: `== exit 0; failing tests: 0` (run 4, current sources; runs 1-2
  were red on `replacen`/`GENERATOR_KENNUNG` placement, both fixed).
- New tests executed directly, not just absent from the failure list:
  `treiber-*`: 4 passed; `gabbro-* treiberregel`: 4 passed; `treiber.rs`
  standalone unit binary: 6 passed.
- 124 end-to-end (`lauf_124_durch_erzeugten_treiber`): generated driver + 124
  observation at `NACHLAUF` (build artefact and test artefact differ by exactly
  that block, asserted by round-trip replace) compiles under
  `-std=c11 -O0 -Wall -Wextra -Werror -pthread`, 5/5 runs exit 0 with invariant
  `konto[0]==konto[1]` and privates `7,7` / `5`; hand `start.c` over the SAME
  emitted C answers the same shape. "Identical output" reads as line shape +
  predicate, NOT byte-identical stdout: the shared value is schedule-dependent
  (30 or 70, lane 202 over 200 runs), so a byte comparison would be the wrong
  artefact -- this is the stated F7.1 confirmation.
- `./lean-bau`: `== lake exit code: 0` / `Build completed successfully (274 jobs)`
  (no `.lean` file touched -- `git status` shows only the 3 files above; Lean
  green is structural, re-verified by file list, not re-run after the last
  Rust-only edit).
- `MARKE_EMIT*` untouched; `instrumente/pruefe-emission.sh` untouched.

## 3. Corpus verdict diff (F5): zero moves

`git diff --name-only` names exactly `crates/gabbro-cli/src/bau.rs` (plus the two
new cli files untracked); `crates/gabbro-check` and `crates/gabbro-syntax` are
untouched, so no check verdict can move structurally -- the build scans raw
sources beside the checker and feeds nothing into it. Mechanical pin:
`der_korpus_bringt_nur_benannte_absagen` (korpus.rs, verdict codes over the
corpus) passes: `test ... ok, 1 passed, 0 failed`. Check verdicts moved: 0.

## 4. Reserved codes N441-445 and gifts 1102-1106 (F6): left free, with evidence

One paragraph with command output, as required. The driver rule refuses in
sentences, like the entry rule and the four manifest refusals before it
(`eintrittsregel` documents why: `pruefe-kennungen.py` counts identifiers per
FILE as a ratchet, `pruefe-saetze.py` demands a `Satz` per identifier, and a
manifest-level refusal has no `Satz` to give -- registering one would need a
thirteenth pass against twelve). Evidence: `python3
instrumente/pruefe-kennungen.py` ends `== KENNUNGEN: ALL PASS -- jede Kennung
gehoert genau einer Datei ==` (416 codes, N-class 132); `grep -rEn '"N44[0-9]"'
crates/ dokumente/ instrumente/` is empty, so N441-N445 stay free for a lane
whose refusal CAN carry a `Satz`; no gift file was added, so 1102-1106 stay
free with them. The task's "(build-side refusals only, e.g. root unresolvable
at build time -- measured only)" is satisfied as sentences: the unresolvable
root IS refused at build time (and earlier by the checker's `W003`
fail-closed); what it is not is a numbered code.

## 5. P017 findings list for the syntax lane (deliverable 2)

Line drawn: this lane GENERATES the driver from the declared set and invents
no statement syntax; `parse.rs` untouched (lane 222's). Shapes that exist
nowhere (measured in `messung/schreibprobe/S01-faden-start.gab` and
`OPUS-BERICHT-SCHREIBBAR.md` row 1 -- all still true on this tree, `P017` =
"assignment or call expected"):

1. `concurrent { hauptA, hauptB };` in a BODY: `P017` + `P033` -- `concurrent`
   is an ITEM, it declares; it does not start.
2. `spawn f;` / `start f;` / `concurrent f;` as statements: `P017` each.
3. `threads { ... };`: `P017` + `P033`.
4. `let t = spawn(f);`: `M119` (`spawn` declared nowhere) + `H021` -- there is
   no handle, no thread identity, nothing to bind.
5. `hauptA();`: parses -- and is a SEQUENTIAL call, not a thread; the one
   shape that looks like a start and is not.

Fuel for the lane after 222 (not built here): any future start statement must
(a) name an already-declared root (never a fresh path -- resolution is the
`W003` fail-closed question), (b) pass no arguments (declared starts take
none; their `Env` travels in `E.starts`), (c) return no handle (no join handle
exists in the model -- `main` joins a fixed array), and (d) stay out of the
emitted unit's meaning: starting is assumption (d) `Laufzeit`, the runtime's
half, which is exactly why the generator lives in `bau.rs` beside the entry
rule and not in the language.

## 6. Resubmit double-checks (F7), each confirmed

1. Identical output = line shape + predicate, not bytes (see section 2).
2. `Aktuell` hole closed: `GENERATOR_KENNUNG` is mixed into the fingerprint of
   every driver-owning unit (a unit without roots carries no version); bump the
   constant on every template change. Existence alone no longer suffices, by
   construction.
3. Roots unite across blocks: a body named twice (one block -- the checker's
   `N304` at CHECK time -- or two) is one root, one thread; the union starts
   exactly the declared set, contradicting no verdict. Matches checker
   semantics: `nebeneinander.rs` reads pairs per block, and a shared member
   simply stands in more pairs.
4. Locks dedup by name with `geteilt` ORed: duplicate declarations are legal
   input to the build (the build refuses nothing the checker accepts); one
   primitive set per name serves all declarations of it, and either declaration
   earns the shared pair. `pub` duplicates collide earlier at the checker's
   `N039` ("one C name, one binding"); contradictory `protects` sets stay the
   checker's question -- the driver defines symbols, it decides no protection.
5. `cc` is `/usr/bin/cc` (Ubuntu 13.3.0) on this machine, where `./cargo-pruef`
   runs; the 124 end-to-end test passed here. Off this machine without `cc` the
   test fails at `Command::new("cc")` -- loud, not silent -- the same bar the
   emission guardian sets (no `cc` = red, W1).

## 7. What remains open / what I believe is wrong

- Open: the emission guardian has no concurrent executed stage (lane 202 §7:
  `lauf` compares one exact string; a concurrent run needs the predicate
  comparison this lane's `BEOBACHTUNG_124` asserts). Natural next step: a
  `lauf`-beside stage running `<unit>.treiber.c` + observation, booked as
  executed-set 38 with predicate comparison. Not built here (guardian is out
  of scope).
- The `ruhe()` idle root is present in every generated driver and never
  executed on hosted -- same standing as lane 202's hand file (by inspection,
  names no carrier).
- No starvation/fairness claim beyond lane 202's 200 runs; no TSan leg in the
  test (lane 202 ran TSan by hand; the committed test asserts the predicate,
  not the race report).
- Nothing in the task believed wrong. The reserved-code decision (sentences,
  not N441+) is a judgement call documented in section 4, reversible by
  consuming the codes later without touching the generator.
