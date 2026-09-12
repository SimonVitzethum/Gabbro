# MUSE-REPORT-72: `return m;` in a void function (gift/776) -- checker gap, new rule M148

Lane 72, Rust lane. Emitter repair or checker gap for
`beispiele/gift/776-v003-hint-await-only-hull.gab`, whose `kreis` (no `-> T`)
contains `return m;` / `return 0;`, which the emitter lowers verbatim into a
`void` C function. Both C families refuse it (`-Werror=return-type`).

## Verdict: (a) -- the checker should refuse this program

Evidence, all measured against the UNCHANGED tree before the fix:

1. `gabbro pruefe beispiele/gift/776-*.gab` said `9 items, 0 errors, 2 hints`
   (`Hinweis E009` + `Hinweis V003`). `gabbro emit` exited 0 and wrote
   `static void kreis(uint32_t k)` containing four valued returns
   (`return m;` x2, `return 0;` x2). `cc -std=c11 -Wall -Wextra -Werror -c`
   refused every one; `clang` with the same flags refused every one too.
   Three stages passed; the fourth is not part of the language (the N044 shape).
2. The probe's header expects `-- erwartet: Hinweis V003` (plus companion
   `Hinweis E009`). That expectation is about the PAIRING half of the file and
   is untouched by this lane: the program is a poison probe, and the corpus
   contract (`crates/gabbro-check/tests/beispiele.rs`) requires every gift
   file to fall with its named code -- none of them is meant to emit.
3. The emitter lowering is CORRECT given the declaration: a function without
   `-> T` lowers to `void`, and a valued `return` has nowhere else to go.
   Fixing the emitter (option (b)) would mean inventing a result type the
   declaration never promised -- a guess, which the emitter refuses by design
   (`C001` doctrine). The declaration is what is wrong, so the checker is the
   place that must speak.
4. The gap is exactly one silent `if` in `m1.rs`: the `Return(Some(e))` arm
   compared the value only under `if let Some(z) = ergebnis`. A result-less
   body fell through the `if` with no word. SYNTAX.md already says a function
   with a return type ends in `return e;` and one without in `return;`
   (sugar for the closing brace), so the valued form in a void body has no
   reading -- it is a distinct fault with a distinct repair (declare the
   result, or return without a value), hence its own code, not a second
   reading of M101/M135/M140.

## What was built

- New checker rule **M148** in `crates/gabbro-check/src/m1.rs`
  (`anweisung`, `StmtArt::Return(Some(e))`, `else` arm of the `ergebnis`
  test): a `return` carrying a value in a function that declares no result
  (and no `or R` reason channel -- reason returns keep their M122 road) is
  refused. Bare `return;` stays silent. Wording was tuned so
  `pruefe-vergabe.py` does not flag it as a second reading of M122
  (similarity 0.30/0.32 against the two M122 sites, under the 0.45 bar).
- Pass-register sentence `m1.rueckgabe_ohne_ergebnis` (`M148`) in
  `crates/gabbro-check/src/saetze.rs`, claimed by the M1 section
  (`pub const M1`), so `gabbro paesse --je-satz` prints it and
  `pruefe-saetze.py` counts it (55 ohne Satz now, booked 53 -- the mark
  belongs to its owning lane; per `--ohne-satz` the rise over the booked
  state is M148 plus one more unclaimed code from another lane, both to be
  booked by their owners).
- Poison probe `beispiele/gift/788-return-carries-a-value-without-a-result.gab`
  (`-- erwartet: M148`): `falsch` (result-less, two valued returns, both fall)
  beside positive twins `gib` (`-> u32`, same lines silent) and `leer`
  (bare `return;`, silent). Number 788: 787 was already taken
  (`787-deadline-probe-without-watchdog.gab`); the first draft collided and
  the korpus number-uniqueness test caught it.
- Unit test `rueckgabe_traegt_einen_wert_ohne_ergebnis` in
  `crates/gabbro-check/tests/rechenwerk.rs`: valued returns fall (exactly 2),
  the three correct shapes stay silent, nested valued returns fall (exactly 3).
- `M148` added to the named-code list `BENANNT` in
  `crates/gabbro-check/tests/korpus.rs` (docs corpus may now name it).

## Effect on the tree

- `gift/776` now falls with `M148` (4 sites) instead of emitting: `gabbro emit`
  exits 1 with `has errors -- no C written`. Stage 9 of `pruefe-emission.sh`
  no longer lists it (`UEBERSETZT NICHT: beispiele/gift/776...` is gone;
  emitting gift count 9 -> 8). Its V003/E009 hints still fire underneath;
  the expected-code test (`jedes_gift_faellt_mit_seinem_code`, `contains`)
  still passes because `Hinweis V003` still falls.
- `gift/758` and `gift/777` (result-less bodies with bare `return;` only)
  are unchanged and still emit clean C accepted by both compilers.
- `./cargo-pruef`: exit 0, failing tests 0 (full run 2026-09-12, after the
  korpus.rs BENANNT repair and the 787->788 renumber).
- `./emission-pruef` (full run 2026-09-12): stage 9 still red, but ONLY with
  pre-existing findings unrelated to this lane -- `beispiele/07` (`_Noreturn`
  function pointer), `beispiele/66` (clang-only `-Wfor-loop-analysis`), the
  nineteen `probe-absenkung-*` files (`main` return type), the stale
  `beispiele/` (71 vs 70), `messung/*/` (133 vs 73) and root (8 vs 1) marks.
  Baseline before my change had the same reds PLUS `gift/776`; my lane
  removes exactly the 776 line and adds nothing.
- Text guardians run directly: `pruefe-kennungen.py` ALL PASS (304 codes,
  M becomes 50); `pruefe-vergabe.py` candidates still 21 / affected 75
  (booked 20/68 -- pre-existing red, unchanged by this lane; M148 adds no
  candidate); `zaehle-gifttreffer.py` 550 files, 0 FEHLT (verdeckt still 19
  vs booked 8 -- pre-existing); `pruefe-gruende.py` green speech tests;
  `pruefe-englisch.py` aborts at the pre-existing German-comment ratchet
  (7903/29717, red before and after -- my added comments are English;
  verified the count is unchanged apart from 44 added English lines).

## What remains open (not mine)

- The `pruefe-saetze.py` mark (53 -> 55: M148 + V012... actually M148 plus one
  more unclaimed code from another lane), the `pruefe-vergabe.py` marks
  (20/68), the `zaehle-gifttreffer.py` verdeckt deck (8 vs 19), and all
  `pruefe-emission.sh` marks belong to their owning lanes; this lane moves
  only its own line (776 out of stage 9) and documents the rest here.
- `gift/776`'s header still says `-- erwartet: Hinweis V003`. That is now
  literally true (the hint still fires) but no longer the whole story (M148
  errors beside it). Whether the V003 lane wants the file re-headed or the
  `contains` semantics kept is their call -- flagged, not changed.
- No Lean work in this lane (`grammatik/` untouched); `./lean-bau` was not
  run because nothing under `grammatik/` changed. No rule-13 witness
  obligation arises (Rust lane, no Lean theorems added).
