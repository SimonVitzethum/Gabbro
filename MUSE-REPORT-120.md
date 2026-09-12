# MUSE-REPORT-120 (lane 120: checker rules for two Lean facts Rust did not enforce)

## What was done

Rust lane. Two new checker rules, both closing gaps lanes 100/101 measured:

1. **Contract footprint (E220/E221, `crates/gabbro-check/src/wirkungen.rs`).**
   A function's `requires` (E220) / `ensures` (E221) may read only carriers its
   effects declare (`reads` or `writes`), or carriers no function of the program
   writes (read-only). Refusal names the carrier and the missing effect.
   This is the repaired form of lane 101's finding: write-signature
   containment alone rejects ordinary read contracts, so the rule asks for
   `reads` OR `writes` cover plus the read-only exception.
2. **Unshared-carrier fact per thread (H222, `geteilt.rs` + `bau.rs`).**
   Threads are `entry` dispatch roots (no `spawn` syntax exists; threads are
   table rows, entries dispatch into ordinary `fn`s). A carrier NOT declared
   shared that is written by the code of two threads is refused once per
   carrier, naming the carrier and both entry roots. Built by EXTENDING
   `pruefe_ungeteilt` (new `ungeteilt_mit_faeden` returns the same carriers
   with thread witnesses; `pruefe_ungeteilt` is now its projection), not by a
   second reachability -- one computation, two readers. The previously silent
   W5 block beside H013 now decides.

## Exact names

- `wirkungen.rs`: `vertrag_liest`, `vertrag_orte`, `schreiber_des_programms`,
  `merke_schreiber`, `vertrag_gegen_wirkungen`; codes `E220`, `E221`.
- `bau.rs`: `ungeteilt_mit_faeden` (new), `pruefe_ungeteilt` (kept, now a
  projection); unit test `w5_nennt_die_beiden_eintrittswurzeln`.
- `geteilt.rs`: `span_des_eintritts` (helper); code `H222` (no other file
  mentions it, quoted or otherwise, except tests which the guardian skips).
- `saetze.rs`: new `wirkungen.vertragsfuss` (E220/E221) and
  `sperren.ungeteilt` (H222) -- both codes arrived WITH sentences, so
  `pruefe-saetze.py` holds at MARKE 55 (333 codes, 55 without sentence,
  0 invented).
- Tests: new `crates/gabbro-check/tests/vertragsfuss.rs` (6 tests, poison +
  positive twins over snippets); `tests/bau.rs` gains
  `h222_refuses_the_pair_and_names_it` and `h222_silent_over_guarded_single_thread`.
- Probes: `beispiele/gift/895` (E220, requires), `896` (E221, ensures),
  `897` (H222 direct pair), `898` (E220 index path + read-only twin),
  `899` (H222 transitive leg + guarded twin). Each gift carries its positive
  twin in the same file. Measured refusal sets: 895 `[E220]`, 896 `[E221]`,
  898 `[E220]` exactly; 897 `[H013]x2 + [H222] + [W001]`;
  899 `[H013] + [H222] + [W001]` (companions documented in the file headers).
- Docs: README `330 -> 333` diagnostics, README + DONE `585 -> 590` poison
  files (strikethrough convention). `korpus.rs` BENANNT untouched -- none of
  the three codes fires on the doc corpus.

## Corpus measurement (the task's "measure first")

- `beispiele/*.gab`: ZERO E220/E221/H222 (all 76 stay clean). No finding to
  report there -- corpus authors already declare `reads` broadly, and
  contracts mostly read parameters.
- Doc corpus (FRAGMENTE/SYNTAX/SPRACHE/README/MEMO): zero firings (korpus test
  green without BENANNT additions).
- Whole tracked tree scan: E220/E221 fire NOWHERE outside the new gifts;
  H222 fires additionally on three EXISTING H013 gifts
  (`146`, `743`, `744`) as the designed companion (pair where H013 sees the
  entry). Their `-- erwartet: H013` still holds (contains-check).
- `gabbro emit` runs the checker first, so all five new gifts emit nothing;
  stage 9's population (`git ls-files`) is unaffected by this lane. The
  stage-9 mark drifts in the emission log (76/75, 132/73, 8/2 gifts,
  UMGEKEHRT 2/4, new roots) come from other merged lanes' tracked files --
  the 8 emitting gifts are 286/414/689/718/719/727/758/777, none mine.

## Last results

- `./cargo-pruef`: `== exit 0; failing tests: 0` (build + `test --no-fail-fast`).
- `./lean-bau`: `Build completed successfully (61 jobs).` (no Lean files touched).
- `./emission-pruef`: aborts at stage 9 on PRE-EXISTING mark drifts (above);
  no new stage failure from this lane (nothing new emits, emitter untouched).
- `pruefe-kennungen.py`: ALL PASS. `pruefe-saetze.py`: 55 without sentence,
  0 invented. `pruefe-todo.py`: README/DONE sections clean after the number
  updates; 3 remaining findings (`Kennzahlen mit Befehl` 89/88 x2,
  `unbewachte fettgedruckte Zahlen` 179/180) are pre-existing drifts in
  TODO.md counters over docs/tools this lane never touched.
  `pruefe-englisch.py` red on the pre-existing German-comment ratchet
  (7905, unchanged -- all new comments English).

## Deliberate boundaries (cuts, not oversights)

- Functions only: `syscall`/`axiom` contracts (same shape), `maintains`, and
  the `= pred ;` body of a `spec fn` are not read. Calls into spec functions
  count only their arguments. Bodyless (`extern`) functions ARE checked.
- Cover is `reads`/`writes` only (task-literal); `consumes`/`publishes` do not
  cover, and `locks`/`masks`/`allocs`/`diverges`/`pure` carry no place.
- Predicate words pruned: `Has(X)`/`Held(L)` name a capability/lock, not a read.
- Quantifier binders treated as local (scoped, popped after the body);
  quantifier domains and `Erreicht` places count as reads.
- Device registers read bare are outside known world state (the E010 line) --
  same boundary, no new noise class. Transition `writes` count as writers.
- H222 applies no `ein_kern`/`masks` exemption (masking orders one core
  against preemption; cross-entry state persists regardless) and reads the
  same `welt`/`geschuetzt` domain as H013 (unknown reads shared, S5).
- No Lean work: the task names no Lean file, TARGET, or ZEUGE line, and adds
  no Lean theorems -- rule 13 is vacuous for this lane. The Lean facts these
  rules enforce are `vertragFussB`/`hReqTAll_aus_B` (+ siblings, lane 101)
  and `nurGB`/`unsharedSepB` (lane 100).

## What I believe is wrong (minor)

- The task's code range `220-224` carries no letter; I used E220/E221
  (effects pass) and H222 (sharing pass) since the kennungen guardian binds a
  code to exactly one file and the two rules live in different passes.
- `pruefe-englisch.py` and the `pruefe-todo.py` TODO drifts were red before
  this lane; the emission stage-9 marks likewise. A lane that only runs the
  full guardians AFTER its change cannot tell pre-existing red from its own
  without a baseline run -- cheap for text guardians, expensive for emission.
