# MUSE-REPORT-151: the `owner` producer (D026)

Lane 151 (D026 / owner producer). The `owner m` clause is refused as `D026`
"until the producer stands: who mints the FIRST mark is unwritten"
(`dokumente/SYNTAX.md` §9, `crates/gabbro-check/src/kbedingung.rs::eigner`,
poison `gift/694`, `messung/OWNER-ANWENDUNG.md`). This lane names the producer
and builds its checker half.

## 1. The design question, precisely

Three facts constrain the answer before any design:

1. `eigner_nie_erzeugt` (`grammatik/Grammatik/Syntax.lean:149`): no signature
   produces an owner mark -- `(m, s) ∉ (sigNr n).produziert` for every `m`
   with `m ∈ eigner t`.
2. Linearity (`M2` in the checker, `Marken.lean` cuts C1/C3): a mark is never
   duplicated and never moves across threads.
3. The applied theorems (`Typen.lean` §5, `Geteilt.lean` §10): an owner mark
   held anywhere traces back to the entry's initial holdings
   (`Signatur.anfang`); from empty holdings no call sequence ever holds one.

So the FIRST live value of an owner mark cannot come from any signature
production or any duplication step. It must enter as an initial holding or as
a foreign assumption -- and the checker names no initial holdings and verifies
no entry dispatch. The question: **which surface shape introduces the first
mark such that (i) exactly one introduction exists per mark, (ii) every later
holder receives it through the linear handoff, and (iii) no second live value
can arise?**

The task suggests "the arena/table declaration or an explicit `mint` at boot".
I measured both against the surface syntax and rejected them: a declaration
names no thread, so a declaration-minted mark has no expressible first holder
-- every holder needs a linear parameter, and the root has no caller to take
it from. A new `mint` statement would be a new word (vocabulary ratchet) for
the same unnameable root. The shape that works with the vocabulary that stands
is the one the language already uses for every other unproducible value: **a
foreign body**.

## 2. The producer (built)

- **Who mints the first mark:** exactly one body-less (foreign) signature per
  mark type returning the bare mark without taking it --
  `extern fn erste() -> Marke` (axioms and syscalls count as foreign too). A
  foreign body is a named assumption, like every device promise -- which is
  where the project goal puts it ("a Gabbro user proves only their own logic
  plus named hardware assumptions"). The declaration itself mints nothing.
- **How it is transferred:** the ordinary linear handoff (`M2`: exactly once
  per path, never doubled): `let m = erste()` creates, passing `m` to a
  `consumes`-callee moves, passing to a borrower lends, `return m` forwards.
  Move-only this lane: borrowing back across a call (`consumes` plus `allocs`)
  stays refused (see §5).
- **Why no second owner can arise:** one mint (D266 refuses the second), no
  signature (re)production (D266 refuses `allocs` of the mark and bodied
  returns without the mark -- the checker half of `eigner_nie_erzeugt`), no
  duplication (M2, untouched). One live value per mark, hence one owner.
- **The guard:** every WRITE to an owner-guarded carrier holds the mark (D267):
  bodied functions at their body sites (assignment/`publish`/`exchange`
  targets, direct or through a pointer parameter), foreign signatures at their
  declared touches. An `effects` line alone is the call-graph hull, not an
  access. `spec fn` is exempt, like under `H007`.

## 3. What was built (names)

Checker (`crates/gabbro-check/src/kbedingung.rs`, function `eigner`,
structs `EignerTabelle`, `Stelle`, helpers `nackter_name`, `haelt_marke`,
`zeiger_ziel` -- all new codes fire from this one file, so
`pruefe-kennungen.py` stays green):

- `D265` -- `owner M` names no declared `linear` type.
- `D266` -- mint discipline: second foreign mint, any `allocs M`, any bodied
  function returning `M` without taking it. Forwarding (taking `M` and
  returning it, bodied or foreign) stays silent.
- `D267` -- a toucher without the mark (bodied: write sites; foreign:
  declared `reads`/`writes`/`consumes`/`publishes` touches).
- `D026` -- kept, with byte-identical text: fires while the story is
  INCOMPLETE (no minter, or a minter no guarded access exercises); silent
  where `D265`-`D267` fire (one fault, one refusal) and LIFTED where the
  producer is complete (mark linear, exactly one minter, no other production,
  at least one guarded touch, every touch holds). Two tables may share one
  mark; the lift is per table.

Pass register (`crates/gabbro-check/src/saetze.rs`): `d.ownermarkislinear`
(`D265`), `d.ownermintdiscipline` (`D266`), `d.owneraccessholdsmark` (`D267`);
the `d.eignerbrauchtgeschicht` (`D026`) entry now names the lift.

Corpus (reserved numbers used: diagnostic codes `D265`-`D267`, gifts
`932`-`935`, example `114`; `D268`/`D269` and example `115` left unused):

- `beispiele/114-owner-with-producer.gab` -- 7 items, 0 errors, 0 hints;
  emits, `cc -std=c11 -Wall -Wextra -Werror -fsyntax-only` accepts.
- `beispiele/gift/932-second-minter.gab` -- 6 items, exactly `D266`.
- `beispiele/gift/933-write-without-mark.gab` -- 5 items, exactly `D267`.
- `beispiele/gift/934-owner-without-linear-mark.gab` -- 3 items, exactly
  `D265`.
- `beispiele/gift/935-allocs-of-owner-mark.gab` -- 5 items, exactly `D266`.
- Controls unchanged: `gift/694` (3 items, exactly `D026`), `gift/778`
  (5 items, exactly `D026`), `gift/779` (7 items, exactly `D026`).

Tests (`crates/gabbro-check/tests/paesse.rs`, 5 new):
`eigner_braucht_lineare_marke_d265`, `eigner_erzeuger_disziplin_d266`
(incl. the forwarding counter-direction), `eigner_zugriff_haelt_marke_d267`
(incl. pointer-mediated touch, foreign touch, and the full-producer lift),
`eigner_unvollstaendig_bleibt_d026` (the 694/778/779 shapes inline),
`eigner_marke_teilt_sich_kein_besitz` (shared mark: touched table lifts,
untouched table keeps `D026`).

Docs: `dokumente/SYNTAX.md` §9 comment, the `owner m` grammar-table row, and
the §19 checklist item (producer stands; residuals named). `README.md` /
`DONE.md` register lines bumped where the guardians pointed (see §4). No new
words, no EBNF change (`pruefe-wortschatz.py`: 240/240, speech probes ok;
`pruefe-syntax.sh`: `SYNTAX: ALL PASS`).

No Lean files were added or edited (rule 5/6 CUTS-block and `#print axioms`
do not apply: there is nothing new to list). The needed Lean statements are
in §5.

## 4. Verification (measured, not asserted)

- `./cargo-pruef`: `== exit 0; failing tests: 0` (767 passed summed over
  suites, 0 failed).
- `./lean-bau`: `== lake exit code: 0`, `== 0 error line(s) in the COMPLETE
  output`, `Build completed successfully`.
- `./emission-pruef`: `EMISSION: ALL PASS -- 35 durchgestochen, 240 von 240
  uebersetzen`.
- `python3 instrumente/pruefe-saetze.py`: exit 0 (`55 ohne Satz`, mark met;
  the 3 new codes are registered).
- `python3 instrumente/pruefe-kennungen.py`: `ALL PASS` (372 codes).
- `python3 instrumente/pruefe-englisch.py`: my delta is zero (feeder count
  back at the booked 23 after rewording one Satz sentence that named the Lean
  `darf`; comment count unchanged at 7949). The comment ratchet itself
  (7949 vs 7905 booked) was ALREADY broken on the clean tree before my lane
  (measured via `git stash`); the 44 excess lines are other lanes', not fixed
  here.
- `python3 instrumente/pruefe-todo.py`: 18 -> 10 findings. Fixed: the 6
  README + 2 DONE stale numbers my lane moved (96 examples, 644 gifts/poisons,
  372 diagnostics, 767 tests) plus 2 pre-existing EBNF counts the guardian
  measures itself (177 rules, 240 terminals). Left: 10 pre-existing TODO.md
  findings (stale Kennzahlen/EBNF figures, 2 undated strikethroughs) in a file
  I never touched.
- `pruefe-widerruf.py`, `pruefe-deckung.py`, `pruefe-konstrukte.py`,
  `pruefe-sondendeckung.py`: green.
- `cargo build --tests` warnings: the one in my code (`mut` closure) fixed;
  3 remaining snake-case warnings in `tests/referenz.rs` are pre-existing.
- `pruefe-syntax.sh` main branch `SYNTAX: ALL PASS`; its `Warnungen` stage
  aborts in this shell (`cargo` not on PATH there -- environmental, exit 2 =
  not measured; warnings verified zero-from-me through the queue slot
  instead).

## 5. What remains open (CUTS)

1. **Reads inside bodied functions.** `D267` covers writes (plus foreign
   reads). A bodied function READING an owner table without the mark is not
   refused -- no read-site walk exists in this pass. The Satz vorbehalt books
   it; the Lean `darf` covers the whole `braucht`.
2. **Borrowing back across a call.** `consumes m` + `allocs m` of an owner
   mark is refused (move-only). Admitting the balanced borrow needs a Lean
   amendment -- stated, not built (shared files untouched): weaken
   `eigner_nie_erzeugt` from "no production" to "no NET production",
   i.e. `forall n t m s, m ∈ eigner t -> (m, s) ∈ (sigNr n).produziert ->
   (m, s) ∈ (sigNr n).konsumiert`. The checker half would then allow
   `allocs M` iff the same signature also consumes an `M` parameter; M2
   keeps exactly-one-live.
3. **The `own`-pointer path.** `ptr<…, own>` table access (`zeiger_hat_waechter`
   territory) is covered for WRITES through the pointer-parameter resolution
   in `D267` (pinned by test); the full sugar story
   (`consumes m … allocs m`, "the mark is borrowed for the call and comes
   back") needs (2).
4. **Short-name matching.** Marks, tables and signatures match by short name
   across modules, like the legacy `D026`. Same-name marks in two modules of
   one unit are a merge-time question, undecided here.
5. **The `D026` message text** ("who mints the FIRST mark is unwritten") is
   now approximate for the minter-without-guarded-access shape (778/779): a
   minter IS named there; what is missing is the exercised guard. Kept
   byte-identical deliberately so the three control probes do not churn.
6. **Pass-register row** (`README.md` line 160: "95 sentences ... 228
   diagnostic codes") was not touched: its populations are unclear to me
   (152 `Satz` structs vs 95 sentences) and no guardian tracks them. It may
   need a recount by its owner.

## 6. On the task

Nothing in the task was wrong, but one hint proved unbuildable as stated: a
table-declaration (or boot-statement) mint leaves the first holder
unnameable -- every holder needs a linear parameter and the declaration names
no thread. The foreign-body minter answers the same question with the
vocabulary that stands, and matches the project goal (named assumptions) and
`PLAN-ERWEITUNG.md` §0c.4 ("the mark exists once"). Gift/example/code budgets
all sufficed with room (`D268`/`D269`, example `115` unused). Design inputs
read: `SATZKARTE.md` (§§7/13), `OWNER-ANWENDUNG.md`, `PLAN-ERWEITUNG.md`
(§0c.4, §3), `SYNTAX.md` §9/§19; `PLAN-SYSCALL.md`/`PLAN-BITS.md` carry no
owner content. Of ~90 `messung/muse` reports only the owner one was read;
the rest is cited, not claimed.
