# MUSE-REPORT-137 (lane 137: TRANSFER `StartExklusiv` as checker rule N240)

Rust lane. The goal theorem over machine G (`ziel_ort_geraet`,
`ZielOrtGeraet.lean:1105`) takes `hex : StartExklusiv init` -- no two
threads start in functions holding a common lock by signature
(`RufMaschineG.lean:2011`; consumed by `exklusivG`, `ZielOrt.lean:424`).
The audit (`AuditZiel.lean`, probe B) gives the practical shape: for the
usual constant thread assignment it collapses to "a thread ENTRY function
holds no lock by signature", and the same lock-holding routine on two
threads never satisfies it (`audit_same_lock_start_excluded`).

## What was done

New checker pass `crates/gabbro-check/src/startexklusiv.rs` (code N240,
the only code of the 240-244 range this lane uses), wired beside
`nebeneinander::pass` in `lib.rs` (both run variants, no pass number of
its own -- a rule of the same column, like `kontexte::pass`):

- Thread starts known to the checker: `concurrent { … }` members plus
  `entry`/`boot` dispatch roots (one pool -- one boot assignment starts
  them all; there is no `spawn` syntax, threads are table rows, entries
  dispatch into ordinary `fn`s -- lane 120). Resolved through the call
  graph; unresolvable starts are skipped (W003 owns the member, N018 the
  dangling dispatch); `entrust` roots are skipped (guest unknown).
- Signature-held locks per start function: `requires Held(L)` flat over
  the predicate tree (`aufrufgraph::held_aus_pred`), short-name identity
  like the pair check beside it.
- Refusal: any lock required by two distinct starts, at ANY strength --
  once per (function pair, lock), span at the second start, naming both
  starts, both functions and the lock, with the model premise
  (`StartExklusiv`, `exklusivG`, `ziel_ort_geraet`) and the remedy
  (lock-free entry + `locks` inside, or disjoint locks) in the notes.
  REVIEW (accepted): the first version exempted shared-shared
  co-holding; the reviewer refused it -- `StartExklusiv` bans ANY common
  signature lock between distinct starts and the model has no notion
  under which two `Held(L, shared)` starts are compatible, so a checker
  that accepts such a program defeats the transfer. Strength is now read
  and dropped. The pass docs note where a future per-holder shared-lock
  model could land a relaxation.

## Corpus measurement (before the rule could bite)

Static, then confirmed by the run: 0 of 89 clean examples and 0 existing
gifts pair two lock-requiring starts. The only multi-entry file with Held
contracts (`beispiele/59`) dispatches lock-free and takes the lock inside
-- the audit's usual shape. No refusal on arrival: no finding to book,
and `jedes_beispiel_geht_sauber_durch` never went red for this rule.

## Probes (both directions)

- `beispiele/gift/910` two entries, one lock; `911` declared pair;
  `912` same routine on two entries (the audit's excluded shape);
  `913` shared-shared fall (strict transfer -- first version pinned it
  silent, review reversed it); `914` exclusive-vs-shared fall (twin set
  rebuilt with bodies of its own after the strict rule made the reused
  `read_b` a self-pair refusal); `915` boot root plus entry (the boot
  leg of the start pool, previously built but unprobed). Each falls with
  exactly `[N240]` (measured per file with the built binary).
- `beispiele/108` declared pair over disjoint locks, `109` two entries
  over lock-free dispatch roots: fully clean (0 errors), emit C, `cc
  -Werror` accepts both.
- `crates/gabbro-check/tests/startexklusiv.rs`: 5 snippet tests --
  shared-lock pair falls, disjoint stays silent, shared-shared falls
  (strict transfer), same-function entries fall, lock-free entries silent.
- Sentence `nebeneinander.startexklusiv` (N240) in the register, with the
  Lean counterpart (`RufMaschineG.lean`, `AuditZiel.lean` probe B) as
  `fundstelle`.

## A finding this lane owns (not the transfer)

`concurrent` had no certificate row: the first clean example carrying the
declaration (`beispiele/108`) emitted fine but fell out as UNZUGEORDNET
in `zeugnis.rs` -- a trust surface only the emitter knew (it silently
drops the item). Fixed with one EINORDNUNG row (`Geloescht`: the set
generates nothing, like `group`) plus the reader arm. `emit.rs` needed
no change (it already skips the item).

## Incidents during the build (all repaired, none hidden)

- Snippet helper named a function `free` and gift twins used `free`:
  N041 (a name C has taken) fired beside N240. Renamed to `idle`.
- `disjoint_locks_stay_silent` first protected one table by two locks:
  H007 fired. Each lock got its own table (the shape the gifts use).
- First `cargo-pruef`: 3 red -- the two above plus
  `jeder_erstname_tut_dasselbe_wie_sein_zweitname`, which passes in
  isolation (7.5 s) and in the re-run: environmental (loaded build
  server), not this lane -- the test compares two spellings of one code
  path, which this lane cannot split.
- First `emission-pruef` after the work commit: 232/232 compile, but the
  booked `beispiele/` mark stood at 89. Moved to 91 with the dated
  comment the script's convention asks for (`MARKE_EMIT`).

## Last results

- `./cargo-pruef`: `== exit 0; failing tests: 0` (initial run, and
  again after the review change -- strict rule, repurposed 913/914, new
  915, flipped snippet test).
- `./emission-pruef`: `== exit 0`, `EMISSION: ALL PASS -- 232 von 232`.
- `./lean-bau`: `Build completed successfully (89 jobs).` (no Lean file
  touched; rule 13 is vacuous -- no new Lean theorems).
- `pruefe-kennungen.py`: 359 codes, ALL PASS (N 87 -> 88).
- `pruefe-saetze.py`: 359 codes, 145 sentences, 55 without sentence
  (mark holds), 0 invented.
- `pruefe-todo.py`: my numbers match (README 359/91/623, DONE 91/623);
  remaining findings are pre-existing drifts this lane never touched
  (EBNF 170->176 / terminals 233->239, Kennzahlen mit Befehl 89->82,
  unbewachte Zahlen 179->180, one undated strikethrough).
- `pruefe-englisch.py`: exit 1 as before this lane -- the single booked
  German message is the CLI policy debt (`main.rs:713`); comment count
  unchanged at 7905, no hit in any file of this lane.

## Numbers moved (guardian-checked ones first)

README: 359 diagnostics, 91 clean examples (91 emit C), 624 poison
files, 693 tests, 95 sentences claiming 228 codes, 232/232 emission.
DONE: 91 clean examples, 624 poison probes, 693 tests.

## What remains open / what I believe is wrong

- The strictness is now the reviewer's call, and it stands as built:
  shared-shared starts fall. The earlier exemption paragraph is kept in
  history above (gifts 913/914 first versions) but no longer in the rule.
- Same-function starts in a lock-FREE routine are silent (correct: the
  collapsed check holds vacuously). Same-function starts only refuse via
  a non-empty held set -- matching the counter-lemma exactly.
- No Lean work: the task names no Lean file, TARGET, or ZEUGE line.
  The transfer is one-directional (checker enforces a model premise);
  no soundness theorem connects N240 acceptance to `StartExklusiv`
  satisfaction -- that wiring (checker-to-model adequacy for the start
  assignment) belongs to a Lean lane, not this one.
- `boot` roots join the start pool but no probe pins a boot pair (the
  corpus has one boot root, `beispiele/07`, dispatching out of unit):
  the boot leg of the rule is built, read, and untested.
