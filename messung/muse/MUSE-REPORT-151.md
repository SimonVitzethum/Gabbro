# MUSE-REPORT-151: the `owner` producer (D026)

Lane 151 (D026 / owner producer), plus review round 151b (single-mint
execution, read half). The `owner m` clause is refused as `D026`
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
- **Why no second owner can arise:** one mint declaration (D266 refuses the
  second), one mint EXECUTION (D268: exactly one static site, outside every
  loop, in a root nothing calls, started at most once -- see below), no
  signature (re)production (D266 refuses `allocs` of the mark and bodied
  returns without the mark -- the checker half of `eigner_nie_erzeugt`), no
  duplication (M2, untouched). One live value per mark, hence one owner.
- **The guard:** every access to an owner-guarded carrier -- read or write --
  holds the mark (D267): bodied functions at their body sites
  (assignment/`publish`/`exchange` targets plus reads through the very walk
  `E010` reads, `wirkungen::lese_orte`, direct or through a pointer
  parameter), foreign signatures at their declared touches. An `effects` line
  alone is the call-graph hull, not an access. `spec fn` is exempt, like under
  `H007`.

## 2b. Why the single mint executes once (D268, review round)

The reviewer refused the first version: `D266` stops the second minter
DECLARATION, but the ONE minter called twice (`let a = erste(); let b =
erste();`, a call in a loop, in a twice-called function, in a twice-started
root) mints two live marks. The fix holds the mint SITE, since the mint
executes exactly when its site executes:

- exactly ONE static call site of the minter in the unit -- a second site is
  a second live mark (D268a);
- the site stands outside every loop form (`traverse`/`retry`/`forever`,
  including a `retry … until` predicate, which evaluates on every pass) --
  a site inside repeats per pass (D268b);
- the enclosing root is called from NO call site (it is an entry: the reverse
  call-graph lookup over `aufrufgraph::erhebe_mit`, which includes contract
  calls -- and contract-position calls TO the minter count as sites, since a
  contract calling the minter executes it) (D268c);
- the root is started at most once: no two thread starts (`concurrent`
  members, `entry` dispatch roots via `kontexte::erhebe`, `boot` dispatch --
  the same pool `startexklusiv.rs` reads) name it (D268d);
- the minter's address is never taken (`&erste`): a mint behind a pointer may
  execute any number of times (D268e).

The count is closed-world. A unit with no starts at all is a library: zero
starts is accepted, and re-invocation of its root from outside the unit is
the importer's duty, like every `pub fn` called twice. A boot step counts as
a site under a caller-free root (boot runs once). An interrupt entry accepted
as a singly-started root may still re-fire at runtime -- the checker cannot
count interrupts; booked as residual below.

## 3. What was built (names)

Checker (`crates/gabbro-check/src/kbedingung.rs`, function `eigner`,
structs `EignerTabelle`, `Stelle`, helpers `nackter_name`, `haelt_marke`,
`zeiger_ziel` -- all new codes fire from this one file, so
`pruefe-kennungen.py` stays green):

- `D265` -- `owner M` names no declared `linear` type.
- `D266` -- mint discipline: second foreign mint, any `allocs M`, any bodied
  function returning `M` without taking it. Forwarding (taking `M` and
  returning it, bodied or foreign) stays silent.
- `D267` -- a toucher without the mark (bodied: write sites AND read sites
  through `wirkungen::lese_orte`, the E010 walk; foreign: declared
  `reads`/`writes`/`consumes`/`publishes` touches).
- `D268` -- a second mint execution: second static site, site in a loop,
  minting root with a caller, minting root named by two starts, taken minter
  address. The lift needs exactly one mint execution.
- `D026` -- kept, with byte-identical text: fires while the story is
  INCOMPLETE (no minter, no mint execution, or a minter no guarded access
  exercises); silent where `D265`-`D268` fire (one fault, one refusal) and
  LIFTED where the producer is complete (mark linear, exactly one minter
  executed exactly once, no other production, at least one guarded touch,
  every touch holds). Two tables may share one mark; the lift is per table
  (and a minter nobody calls lifts neither).

Pass register (`crates/gabbro-check/src/saetze.rs`): `d.ownermarkislinear`
(`D265`), `d.ownermintdiscipline` (`D266`), `d.owneraccessholdsmark` (`D267`,
reads included), `d.ownermintisingle` (`D268`); the `d.eignerbrauchtgeschicht`
(`D026`) entry now names the lift.

Corpus (reserved numbers used: diagnostic codes `D265`-`D268`, gifts
`932`-`935`, examples `114`-`115`; `D269` left unused):

- `beispiele/114-owner-with-producer.gab` -- 7 items, 0 errors, 0 hints;
  emits, `cc -std=c11 -Wall -Wextra -Werror -fsyntax-only` accepts.
- `beispiele/115-owner-read-with-producer.gab` -- the read path under the
  mark plus the single mint executed once (`D268` silent); 7 items, 0 errors,
  0 hints; emits, `cc` accepts.
- `beispiele/gift/932-second-minter.gab` -- 6 items, exactly `D266`.
- `beispiele/gift/933-write-without-mark.gab` -- 5 items, exactly `D267`.
- `beispiele/gift/934-owner-without-linear-mark.gab` -- 3 items, exactly
  `D265`.
- `beispiele/gift/935-allocs-of-owner-mark.gab` -- 5 items, exactly `D266`.
- Controls unchanged: `gift/694` (3 items, exactly `D026`), `gift/778`
  (5 items, exactly `D026`), `gift/779` (7 items, exactly `D026`).

Tests (`crates/gabbro-check/tests/paesse.rs`, 11 new): `eigner_braucht_lineare_marke_d265`, `eigner_erzeuger_disziplin_d266`
(incl. the forwarding counter-direction), `eigner_zugriff_haelt_marke_d267`
(incl. pointer-mediated touch, foreign touch, and the full-producer lift),
`eigner_unvollstaendig_bleibt_d026` (the 694/778/779 shapes inline),
`eigner_marke_teilt_sich_kein_besitz` (a minter nobody calls lifts neither
table), `eigner_zweiter_aufruf_d268`, `eigner_aufruf_in_schleife_d268`,
`eigner_gerufene_wurzel_d268`, `eigner_zweimal_gestartet_d268` (incl. the
singly-started counter-direction), `eigner_adresse_genommen_d268`,
`eigner_lesen_haelt_marke_d267` (read falls without the mark; held read
silent, file form pinned as `beispiele/115`). No gift numbers were left, so
the D268 shapes stand inline per the review.

Docs: `dokumente/SYNTAX.md` §9 comment, the `owner m` grammar-table row, and
the §19 checklist item (producer stands; residuals named). `README.md` /
`DONE.md` register lines bumped where the guardians pointed (see §4). No new
words, no EBNF change (`pruefe-wortschatz.py`: 240/240, speech probes ok;
`pruefe-syntax.sh`: `SYNTAX: ALL PASS`).

No Lean files were added or edited (rule 5/6 CUTS-block and `#print axioms`
do not apply: there is nothing new to list). The needed Lean statements are
in §5.

## 4. Verification (measured, not asserted)

- `./cargo-pruef`: `== exit 0; failing tests: 0` (773 passed summed over
  suites, 0 failed).
- `./lean-bau`: `== lake exit code: 0`, `== 0 error line(s) in the COMPLETE
  output`, `Build completed successfully`.
- `./emission-pruef`: `EMISSION: ALL PASS` (re-run after 151b, see below).
- `python3 instrumente/pruefe-saetze.py`: exit 0 (the 4 new codes are
  registered; `55 ohne Satz` mark met).
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

1. **Borrowing back across a call.** `consumes m` + `allocs m` of an owner
   mark is refused (move-only). Admitting the balanced borrow needs a Lean
   amendment -- stated, not built (shared files untouched): weaken
   `eigner_nie_erzeugt` from "no production" to "no NET production",
   i.e. `forall n t m s, m ∈ eigner t -> (m, s) ∈ (sigNr n).produziert ->
   (m, s) ∈ (sigNr n).konsumiert`. The checker half would then allow
   `allocs M` iff the same signature also consumes an `M` parameter; M2
   keeps exactly-one-live.
2. **The `own`-pointer path.** `ptr<…, own>` table access is covered for
   WRITES and READS through the pointer-parameter resolution in `D267`
   (pinned by test); the full sugar story (`consumes m … allocs m`, "the mark
   is borrowed for the call and comes back") needs (1).
3. **Short-name matching.** Marks, tables and signatures match by short name
   across modules for D265-D267, like the legacy `D026`; D268 resolves through
   the call graph (qualified keys). Same-name minters in two modules of one
   unit resolve per caller module -- two modules defining one mark name is a
   merge-time question, undecided here.
4. **Interrupt re-entry.** A singly-started `entry` root accepted by D268(d)
   may still re-fire at runtime (two interrupts, two mints). The checker
   cannot count interrupts; that half is a named-environment question, not a
   second static site.
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
all sufficed with room (`D269` unused; no gift numbers were left for the D268
shapes, so they stand as inline tests per the review). Design inputs
read: `SATZKARTE.md` (§§7/13), `OWNER-ANWENDUNG.md`, `PLAN-ERWEITUNG.md`
(§0c.4, §3), `SYNTAX.md` §9/§19; `PLAN-SYSCALL.md`/`PLAN-BITS.md` carry no
owner content. Of ~90 `messung/muse` reports only the owner one was read;
the rest is cited, not claimed.

Review round 151b accepted the design and refused the merge: the single
minter called twice mints two live marks (condition (iii) unmet). Fixed with
`D268` above -- the smallest countable rule: the mint executes exactly when
its site executes, so one site, outside loops, in an uncalled root, started
at most once. Closed CUTS item 1 in the same round (reads through the E010
walk). `beispiele/115` is the positive for both.
