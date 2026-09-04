# Gegenprobe zu F03 -- standing adversary of `worktree-agent-a7460ff215795e662`

## REFRAME (mid-task correction from the coordinator) -- everything below the line was
## superseded before the lane produced a single commit

My first pass at this brief checked whether `F03.gab`'s 18 refusals were faithful
transcriptions of `../caprock-messbasis`. **That is the wrong question and always was.**
Fidelity to caprock is the fifth mark's question and it is already answered; `H` counts
*hanging plumbing obligations*, and whether Gabbro's own machinery (`crates/`) can lower
`F03` **unchanged** has nothing to do with whether the excerpt matches caprock. Correcting
`F03.gab` would be the third instance of the SAME mistake this tree has already made twice
(2026-09-03 rewrite; 2026-09-04's `zaehle-pflichten.py` reclassification, refuted same-day in
`messung/AUDIT-K100-2026-09-04.md`) -- *changing the object being measured*. **The lane is
now forbidden to touch `messung/fragmente/F03.gab` at all**, and my job is:

1. `git diff master -- messung/fragmente/F03.gab` is **EMPTY at every commit** -- checked
   first, every time.
2. Re-derive each of the lane's verdicts from the actual pass code in `crates/` -- not from
   caprock.
3. Three verdicts only: **plumbing** (pass/generator repair, no new grammar, no rule
   weakened) / **a rule decision** (Gabbro would have to stop refusing -- a previous lane may
   already have measured that refusal as RIGHT) / **the program is wrong** (a self-contained
   type error in `F03.gab`, not fixable by any amount of Gabbro-side work without touching the
   frozen file).
4. Running count of **plumbing** verdicts -- flag loudly and early if it is zero.
5. Watch for the refuted move returning: a verdict that rests on the total ERROR COUNT rather
   than the REASON each one fires is the same defect `AUDIT-K100-2026-09-04.md` found in
   `zaehle-pflichten.py`.
6. No guardian (`zaehle-pflichten.py`'s classifier especially) may be made green by changing
   what it measures.

Ground truth is now `crates/gabbro-check/src/*.rs` (the passes) and
`messung/AUDIT-K100-2026-09-04.md` + `messung/DREI-FRAGMENTABSAGEN.md` (prior measurements on
these exact rules) -- **not** `../caprock-messbasis`, which no longer matters for this
question.

---

## Baseline (still valid): the 18, unchanged

```
ssh ki-pc-fisch-101 'cd gabbro-gegen && export PATH=$HOME/.cargo/bin:$PATH && ./target/debug/gabbro pruefe messung/fragmente/F03.gab'
```
27 items, **18 errors**, 1 hint (the `E009` hint at 158:9 is not one of the 18).

| # | code | line:col |
|---|---|---|
| 1-5 | N035 | 151:21, 152:21, 153:21, 154:21, 155:21 |
| 6 | M124 | 175:34 |
| 7 | M140 | 194:25 (`q` arg, `TidQueue` value vs `ptr<...>TidQueue`) |
| 8 | M124 | 197:38 |
| 9 | M140 | 200:16 (return, `u32` vs `ptr<...>Frame`) |
| 10 | M124 | 204:54 |
| 11 | M140 | 204:13 (`f` arg) |
| 12 | M140 | 205:13 (`f` arg) |
| 13 | M101 | 208:33 (missing narrow) |
| 14 | M143 | 210:8 (`owner_core` arity) |
| 15 | M140 | 210:19 (`d` arg, `SchedOps`) |
| 16 | M140 | 211:16 (return) |
| 17 | M140 | 214:12 (return) |
| 18 | H011 | 170:33 |

## My own independent re-derivation, done BEFORE any lane commit exists to check

Read directly, pass by pass, in `crates/gabbro-check/src/`:

### N035 x5 (#1-5) -- **rule decision, and it is already measured RIGHT**

`crates/gabbro-check/src/namen.rs:574-619` (`fnptr_traegt_seinen_vertrag`): a `fn(...)` type
with no `effects`/`costs` is refused because `E008` needs the effect hull to be compositional
across indirect calls and `K001` needs a cost bound for one. This is a hard requirement with a
real soundness purpose, not a gap in coverage.

**Already measured**, not just theorized: `messung/DREI-FRAGMENTABSAGEN.md`, section "P-b --
`N035`: der Vertrag ist Pflicht, und er wird GELESEN" (2026-08-31) ran six probes showing both
halves (`effects`, `costs`) are read by real consumers (`K001`, `E008`), backed by three poison
probes and three mutations in the catalogue since 2026-08-21. Verdict there: *"nichts an
N035"* -- nothing to build, the rule stands. The fix for `F03.gab` would be adding the
contract to the five `fn(...)` field lines themselves (`type SchedOps`, :150-156) -- a
**rewrite** of a frozen line, forbidden regardless of the `H`/plumbing question.
**No plumbing route exists** (the checker REFUSES, it does not merely lack an emitter arm --
plumbing requires the checker to already accept the file, per `zaehle-pflichten.py`'s own
docstring and `AUDIT-K100-2026-09-04.md` §1.1's own table). Weakening N035 was measured and
explicitly rejected. **Verdict: rule decision, stands as correct, does not lower.**

### M124 x3 (#6, #8, #10) -- **rule decision, and it is already measured RIGHT**

`crates/gabbro-check/src/m1.rs:678-699`: a `reason` value may only appear at one of four
doors (return, match subject, same-reason comparison, argument at a parameter DECLARED as
that reason). `set_reg`'s third parameter is declared `w: u64`, not `IpcResult`, so
`IpcResult::ErrQuiescing`/`ErrEpFull`/`Ok` as arguments there fail all four doors.

**Already measured**: `messung/DREI-FRAGMENTABSAGEN.md`, section "P-c -- `M124`" (2026-08-31).
The candidate fix (a "number projection" letting a `reason` decay to its literal number at a
value position) was explicitly evaluated and rejected on two independent grounds: (a) zero
sites in the entire corpus project a reason enum onto a raw number where the corresponding
real declaration is a plain scalar (Regel B), and (b) the frozen `reason IpcResult`'s numbers
have ALREADY drifted from the live encoding it would be projected onto (`ErrBadCap = 2` vs
measured `1` elsewhere) -- building the projection would silently carry a wrong number.
Verdict there: *"M124 ist eine richtige Absage"* (a correct refusal). **No plumbing route**
(checker refuses, not merely missing an emitter arm); the language feature that would lower
it was deliberately not built, for a measured reason. **Verdict: rule decision, stands as
correct, does not lower.**

### M140 x7 (#7, #9, #11, #12, #15, #16, #17) -- **the program is wrong**

`crates/gabbro-check/src/m1.rs:3563-3607` (`gestalt_passt`): compares the callee's DECLARED
slot type against the value's actual type; on a shape mismatch it refuses with the message
seen in all 7. This is a pure type-shape comparison against what the SAME FILE itself
declares -- not an external fact.

Checked each of the 7 individually, since the AUDIT-K100 report's own summary table
(*"`frame_of` is declared `-> u32` ... used where `ptr<...>Frame` is required"*) covers only
5 of the 7 precisely:
- #9, #11, #12, #16, #17 (200:16, 204:13, 205:13, 211:16, 214:12): all Frame-shaped, exactly
  as the audit describes -- `block_current`/`switch_to`/`frame_of` (extern decls, :227-241)
  return `u32`, while `call`'s own return type (:161) and the `f` parameter type (:161, :219)
  are `ptr<...>Frame`. Self-inconsistent within the file: the file both asserts frames are a
  `ptr<...>Frame` (input positions) and a bare `u32` (output/return positions) for the same
  underlying handle.
- #7 (194:25): a DIFFERENT root cause -- `enqueue`'s extern decl (:225) takes
  `q: ptr<...>TidQueue`, and the call site (:194) passes `e.slots[core].senders`, a bare
  `TidQueue` value (a field read through a pointer, not itself a pointer). Gabbro's lexer has
  no address-of operator at all (`grep -n '"&"' crates/gabbro-syntax/src/lex.rs` finds only
  bitwise-AND) -- there is no construct ANYWHERE in the grammar to form a `ptr<...>T` from an
  inner place of an already-pointed-to record. This makes #7 arguably closer to needing a NEW
  grammar production than to a same-file type inconsistency -- but since "new grammar
  production" is explicitly excluded from plumbing too, the practical verdict (does not lower
  without either touching the file or a language change) is unaffected either way. Flagging
  the audit's table as imprecise here, not wrong in effect.
- #15 (210:19): also different -- this is `owner_core`'s FABRICATED first parameter
  (`d: ptr<...>SchedOps`, extern decl :234-235) that the call site `owner_core(picked)` (:210,
  one argument) never supplies; positional matching puts `picked` (a `u32`) into slot `d`.
  Root cause is shared with M143 below, not with the Frame cluster.

**All 7 are self-contained type errors provable from `F03.gab`'s own text against its own
declarations** -- no fact from outside the file is needed to see the mismatch, and no pass
change can reconcile two declarations the SAME file gives for the same handle without
weakening `M140` (which is exactly the boundary check `m1.rs:3600-3604`'s own comment names as
load-bearing against emitting C that will not compile). **Verdict: the program is wrong.**

### M143 x1 (#14) -- **the program is wrong**

`crates/gabbro-check/src/m1.rs:2287-2308`: arity is compared against `sig.parameter.len()`,
the callee's OWN declared signature. `owner_core` is declared with 2 parameters at
`F03.gab:234-235` and called with 1 argument at `F03.gab:210`, in the SAME FILE. This is a
direct, provable self-contradiction -- exactly the coordinator's own worked example.
**Verdict: the program is wrong.**

### M101 x1 (#13) -- **the program is wrong**

`crates/gabbro-check/src/m1.rs:3713-3727`: `q.passt_in(&z)` fails when the source range does
not fit inside the target's. `caller` (from `current_id`, plain `u32`, full range) is assigned
into `e.slots[core].caller`, an `option index into Threads` whose underlying range excludes
the reserved sentinel (`0 .. 4294967294`, i.e. `u32::MAX` reserved for `None`). No `narrow`
proves `caller != 0xffff_ffff` first. `M101`'s own stated purpose (`m1.rs:3728-3729`, "every
operation must stay inside the range of its result type") is a core soundness rule, not a
coverage gap -- weakening it would let a genuinely unproven range claim through.
**Verdict: the program is wrong** (a missing `narrow`, and adding one would mean editing the
frozen file).

### H011 x1 (#18) -- **the program is wrong**

`crates/gabbro-check/src/geteilt.rs:411-467`: `locks SCHEDS` in `call`'s effects list is
redeemed only by (a) a `locks` block in the body, (b) `requires Held(SCHEDS)`, or (c) a
callee whose own hull carries `locks SCHEDS`. None of the three holds -- `call`'s body never
locks, declares no `Held`, and every extern callee (`set_reg`, `enqueue`, etc.) declares only
`reads`/`writes`. **`F03.gab`'s own header (lines 82-97, already in the tree before this
lane) agrees**: *"H011 bleibt danach stehen, und das ist der Ertrag"* (H011 remains standing,
and that is the yield) -- the effects clause over-promises what the body does.
**Verdict: the program is wrong**, and the file already says so about itself.

## Running count

**Plumbing: 0 of 18, by my own independent re-derivation, before any lane commit exists.**
**Saying this loudly and early, per instruction: every one of the 18 is either a rule already
measured RIGHT (N035, M124 -- 8 of 18) or a self-contained type error in the frozen file
(M140, M143, M101, H011 -- 10 of 18). None requires only "a generator or pass repair" with no
new grammar and no rule change.** This is not a surprising result by itself -- `F03` is
refused by the CHECKER on all 18, and plumbing (by the tree's own established definition,
`AUDIT-K100-2026-09-04.md` §1.1's table) requires the checker to already ACCEPT the file. A
file refused 18 ways cannot have a nonzero plumbing count under that definition unless the
lane finds a genuine checker BUG (a pass computing something wrong about what the file itself
says, independent of caprock or of any rule's correctness) -- which I have not found in any of
the 6 passes read above. **Watching hard for the lane to manufacture a "plumbing" verdict by
either (a) treating an already-decided rule (N035/M124) as open again, or (b) mis-citing a
pass's behavior.**

## Per-finding verdicts (lane's own commits, checked against the above)

### Lane commit `8be0e40` -- "A file with ZERO checker errors that the emitter refuses BY
### NAME -- H's criterion is wrong in the other direction too"

**`git diff master -- messung/fragmente/F03.gab`: still EMPTY.** `git show --stat 8be0e40`
touches only the new file `messung/proben/probe-queue-traverse-checks-clean-and-has-no-lowering.gab`
(72 insertions) -- **F03.gab is not in the diff.** Protocol holds.

This commit does not yet classify any of the 18 individually -- it establishes a 19th,
separate fact: `gabbro pruefe` never shows a `C001` that `gabbro emit` does. Checked every
claim in it independently, all hold:

- **The probe file itself.** Copied it to `gabbro-gegen` on the server and ran it myself:
  `./target/debug/gabbro pruefe qprobe.gab` -> `5 items, 0 errors, 0 hints`.
  `./target/debug/gabbro emit qprobe.gab` -> `exit 1`,
  `error: [C001] qprobe.gab:65:5: no lowering: \`queue\` -- «B10»: ...` -- **matches the
  commit message verbatim.**
- **`F03.gab` under `emit`, not just `pruefe`.** `./target/debug/gabbro emit
  messung/fragmente/F03.gab 2>&1 | grep -c "^error:"` -> **19**, and the 19th line is
  `error: [C001] messung/fragmente/F03.gab:185:5: no lowering: \`queue\` -- «B10»: ...` --
  **matches exactly.** `gabbro pruefe` on the same file still reports only 18 -- confirmed,
  `C001` is genuinely invisible to the checker run the whole task is built on.
- **`crates/gabbro-check/src/emit.rs:8639`.** Read the whole `traverse` emit function
  (`emit.rs:8453-8674`). `Domaene::Schlange(_) => { "..." }` is one match arm among several;
  the arms above it (`SlotsVon`, `NachfahrenVon`, `VorfahrenVon`) contain real lowering code
  and an early `return`, while `Schlange`, `AbbildungenVon`, `KetteIn`, `FelderVon`, `Threads`
  all just produce a message string that falls through to one shared `weigere(absagen,
  s.span, grund);` after the `match`. **Confirmed unconditional**: there is no branch inside
  the `Schlange` arm on `by consuming` vs. anything else -- the commit's characterization
  ("no arm is being withheld") is accurate.
- **`instrumente/zaehle-pflichten.py`:326-330.** The two-line criterion is real, quoted
  correctly (off by ~3 lines -- the `PLUMBING.`/`NOTATION.` lines are at 329/332, the
  preceding "THE CRITERION" header a few lines above 326 -- immaterial). **Important context
  the commit message does not spell out but I checked**: `absenkungsklasse`'s docstring
  (`:373-393`) says this exact split was **already refuted same-day** by
  `AUDIT-K100-2026-09-04.md` and `locker` now **defaults to `True`** (the old, undivided
  rule) -- so today's actual `H` does NOT run through the `n == 0` branch by default. The
  lane's probe deliberately calls `absenkungsklasse(..., locker=False)` to exercise the
  **non-default, already-discredited** strict mode and show it is ALSO wrong, symmetrically
  to the `AUDIT-K100` finding about the `> 0` branch. This is an honest, clearly-scoped
  methodological point ("this is the other half of the audit"), not a claim that current `H`
  is live-miscounting via this path -- read carefully to be sure of the distinction, and it
  holds up.
- **Commit `645ddca` reference.** Read it in full: 2026-09-03, a parallel lane pierced F03 by
  REWRITING the queue-traverse loop (`by consuming` -> `by unvisited` over `elems of`, with a
  `static mut` accumulator) to get it to emit -- rejected because the rewrite silently changed
  the protocol (caprock's `call` drains the found receiver out of the queue at
  `caprock-ipc/src/lib.rs:625`; the rewrite left the queue untouched). This matches what I
  independently verified against caprock directly in my (superseded) first pass. The lane
  cites this correctly as PRECEDENT for why `C001` at `F03.gab:185` stays open rather than
  getting "fixed" by a rewrite -- it does not propose touching the loop itself. **No violation
  of the untouchable-protocol concern; the citation is accurate and the file is untouched.**

**Verdict on this commit: holds up under independent re-derivation, no caprock-fidelity
argument smuggled in, F03.gab untouched, count-vs-reason distinction respected (it explicitly
extends the AUDIT-K100 reason-not-count argument rather than reintroducing a count-based
one).** Watching for whether the lane goes on to classify the actual 18, and for whether this
19th fact (`C001`) gets conflated with the 18 rather than kept as separate context.

---

## FINDING, in its own right: `F03` is quoted as "18 errors" and that number depends on
## which command you run

This is not a footnote to verifying the lane's commit -- it is mine, independently
reproduced, and it matters beyond this pairing. **The tree has been quoting `18 errors` as
`F03`'s state for two days** (`AUDIT-K100-2026-09-04.md` heads its own §1.5 with exactly that
count, sourced from `gabbro pruefe`). But:

    ./target/debug/gabbro pruefe messung/fragmente/F03.gab   ->  18 errors
    ./target/debug/gabbro emit   messung/fragmente/F03.gab   ->  19 errors (same 18 + C001 at :185)

Reproduced on my own build, independent of the lane's. **`zaehle-pflichten.py::_pruefe_fehler`
runs `pruefe`, never `emit`** -- so `H`'s ledger structurally cannot see the 19th.

**Self-correction, checked before acting on it.** I first wrote that six documents quote
"18 errors" for `F03` (`AUDIT-K100`, `BERICHT-H0.md`, `PLAN-HARDWARE.md`,
`PLAN-VOLLSTAENDIGKEIT.md`, `W24-FRAGMENTE.md`, `ERZEUGERREST.md`) -- that was imprecise, and
I checked each rather than repeat it. Only `AUDIT-K100-2026-09-04.md` literally says `18
errors` (it is dated today and the number is live). `BERICHT-H0.md` (27, at commit `3b17d9a`),
`PLAN-HARDWARE.md` (27, in a table with sibling rows already struck through and corrected),
`PLAN-VOLLSTAENDIGKEIT.md` (19) and `W24-FRAGMENTE.md` (19, measured 2026-08-30, and already
distinguishing `pruefe`/`emit`/`cc` in its own columns) each carry an OLDER, dated count from
before `Frame`/`RegNr` were declared on 2026-09-03 and closed the nine `N040`s that separated
27/19 from today's 18. `ERZEUGERREST.md` does not assert a current count at all -- it only
flags that `BERICHT-H0.md`'s `27` mislabeled a hint as an eighth error code, a point that
stands regardless of today's number. **Corrected all five live documents that misstate or
understate today's state** (`AUDIT-K100`, `BERICHT-H0.md`, `PLAN-HARDWARE.md`,
`PLAN-VOLLSTAENDIGKEIT.md`, `W24-FRAGMENTE.md`) with a dated annotation each giving today's
pair (`pruefe` 18 / `emit` 19) and the command that produced it, using each document's own
existing correction convention (strikethrough + **BERICHTIGT**, or a blockquote note) rather
than silently overwriting a historical measurement -- none of the old numbers were erased.
Also added a documentation-only note (comments, no logic touched) at
`instrumente/zaehle-pflichten.py`, immediately above `_pruefe_fehler`, naming the structural
fact where the measure is defined rather than only where the number is quoted: this function
runs `pruefe` and never `emit`, so an emitter-only refusal is invisible to `H` by
construction. **Not repaired** -- the classifier itself is untouched, per instruction; this
names the blind spot, it does not patch it.

**The gap is not a rounding error -- it is a whole refusal class (emitter
lowering) that the checker-only number is blind to by construction**, and it would stay blind
even if all 18 checker errors vanished tomorrow.

## The concrete shape of a "plumbing" checker error -- and whether one exists among the 18

The coordinator asked me to say what a checker error would have to look like to earn a
**plumbing** verdict, not just assert the count. Here it is, stated so it can be checked
against and not just believed:

**A checker-reported (`gabbro pruefe`) error can never be plumbing, structurally, and here is
why rather than by definition-quoting.** `gabbro pruefe` accepting a file (`0 errors`) IS the
statement "every fact this program makes about itself has been proven or is not required
here" -- effects, costs, ranges, arities, reason-doors, lock redemptions, all of it. An error
from `pruefe` means the checker found a fact the program NEEDS and does not have (or a fact
it has that is false). At that point there is nothing "merely missing" for an emitter arm to
supply -- the emitter's job starts from an ALREADY-VALIDATED program and turns validated facts
into C; it has no machinery to invent a missing proof. So plumbing requires the OPPOSITE
starting condition: `gabbro pruefe` returns `0 errors` and `gabbro emit` STILL refuses, over a
construct whose meaning is already fully and unambiguously pinned down by something the type
system tracks formally (not assumed, not guessed) -- an unwritten arm over an
already-decided case. `D21` (`messung/ERZEUGERREST.md:1101`, cited by the lane) is exactly
this shape: `forever()` already pushes the retry label `emit.rs::retry` needs; `leave`/`next`
needed the identical push and nobody had wired it. Nothing to decide, nothing assumed --
purely unwritten.

**None of `F03`'s 18 have this shape, and it is not a coincidence -- it follows from what
`gabbro pruefe` returning an ERROR means.** All 18 are `pruefe`-time refusals. **Plumbing was
never reachable for any of the 18, by the structure of the question itself, not by how the
cases happened to fall.** This sharpens "0 of 18" from a count into a statement about the
category: it could not have been anything else once every one of the 18 is confirmed to come
from `gabbro pruefe`, not from a downstream generator gap.

**Which moves the real test to the 19th error -- the one genuinely on the emitter side.**
`emit.rs:8639`, `Domaene::Schlange(_)`, the `queue ... by consuming` refusal. This is the one
place in the whole file where "is an arm merely missing" is even a coherent question, because
it is the one error `pruefe` does not raise -- `gabbro pruefe` accepts the construct as
well-typed; only `emit` refuses it.

### Is `Domaene::Schlange`'s `C001` plumbing? Checked against the pass, not taken on the lane's word.

The lane's own commits assert this is «B10» and open, but do not show the mechanism -- so I
read it myself. `crates/gabbro-check/src/domaene.rs:85-101` (the cost pass's domain-bound
function):

```rust
// **`queue place` -- die Schranke steht im Verbund, nicht in einer Tabelle.**
// Eine Warteschlange ist in Gabbro ein gewoehnlicher Verbund mit **genau einem
// Feldarray** (`TidQueue = { buf : [u32; 32], head, tail, count }`). Damit ist
// ihre Schranke die Laenge dieses Arrays, und zwar eindeutig...
Domaene::Schlange(o) => return self.arraylaenge_im_verbund(o),
```

This is the ONLY machinery anywhere in `crates/` that interprets a "queue"-shaped record, and
it exists purely to produce a cost UPPER BOUND. It does **not** identify `head`/`tail`/`count`
as anything at all -- it finds "the one array field" and stops. This is not my inference --
it is already measured and written down, independent of this lane, in
`messung/K001-DOMAENENSCHRANKE.md` §8.1 (2026-08-31), the `queue p` row:

> *"abgeleitet als OBERE Schranke, mit einer ANGENOMMENEN Zuordnung -- dass das einzige Array
> der Puffer der Warteschlange IST, prueft nichts... Die Warteschlange haelt zur Laufzeit
> hoechstens n, nicht notwendig n."*
> (derived as an UPPER bound, with an ASSUMED correspondence -- that the one array actually
> IS the queue's buffer is checked by nothing... the queue holds AT MOST n at runtime, not
> necessarily n.)

**This is the load-bearing fact, and I verified it against the source rather than the
document alone.** Consequence: to write a plumbing emitter arm for `queue ... by consuming`,
the generator would need to know which of the array's `n` cells are actually LIVE (occupied)
right now, to visit only those -- and nothing in the type system says which OTHER fields (if
any) are the head/tail/count bookkeeping for that array. The only two ways to proceed from
here are:

1. **Iterate the raw backing array unconditionally** (treat `queue` as `elems of buf`). This
   is mechanically simple and needs no new grammar -- but it is not a faithful lowering of
   "queue": a `TidQueue` with `count < 32` has stale/garbage entries outside its logical
   window, and visiting all 32 slots regardless of occupancy computes something the source
   program did not ask for. Confirmed the same way the lane confirmed the M140 cast
   objection: this would COMPILE and RUN and produce a wrong answer silently -- exactly the
   failure mode `emit.rs:2506`'s own comment refuses ("a generator that guesses undoes every
   pass in front of it"), and I checked this exact line and text myself, independent of the
   lane's citation of it for a different error.
2. **Recognize `head`/`tail`/`count` by field-name convention.** Also guessing -- nothing
   declares that fields with those names play those roles, and a differently-shaped queue
   record would silently do the wrong thing or fail to match at all.

**Neither route is plumbing.** The genuinely non-guessing fix is a NEW declaration form that
formally binds an array field to explicit head/tail/count roles (something closer to how
`table` formally structures `count N` and slots) -- which is a language change, i.e. bucket
2 (a rule decision), not bucket 1. **Verdict, independently derived: `Domaene::Schlange`'s
`C001` is not plumbing either.** So the answer to "is plumbing reachable anywhere in `F03`,
checker side or emitter side" is **no, on both sides, for two different and independently
checkable reasons**: the 18 are refused before the emitter is ever reached (structural), and
the 19th is refused because the one fact the emitter would need is explicitly assumed, not
derived, by the tree's own prior measurement (substantive). **`H`'s question, for `F03`, does
not turn on a missing generator arm anywhere in the file.**

---

## Lane commit `aa119ff` -- "Three holes in yesterday's classification closed"

**`git diff master -- messung/fragmente/F03.gab`: still EMPTY.** Confirmed before reading
anything else. All three claims checked and reproduced independently, all hold:

1. **The cast objection** (could a cast make `M140`/`M143` plumbing?). Cited `emit.rs:2506` --
   read it myself: it is the `weigere()` helper EVERY `C001` (and, per its placement, the
   shared refusal philosophy) routes through, carrying exactly the quoted note verbatim
   ("the emitter refuses by name instead of emitting something plausible -- a generator that
   guesses undoes every pass in front of it"). The argument -- a `(Frame *)` cast over a
   truncated `u32` on a 64-bit target fabricates a bad address, and `M143`'s missing argument
   has nothing to cast -- is sound and matches my own reasoning about the M140/M143 cluster
   from the previous commit.
2. **`N035` reachability.** Reproduced verbatim: `grep -n "dienste\." messung/fragmente/F03.gab`
   -> no output (exit 1) on my own checkout. Confirms nowhere in the file does `call`'s body
   invoke a `SchedOps` field as an indirect call (`dienste.current_id(...)` etc.) -- every
   call is to a top-level `extern fn` instead. This independently confirms what I had
   separately derived (F03.gab's own header, «B8»): the five `fn(...)` fields of `type
   SchedOps` are dead in this fragment, so satisfying `N035` on them changes nothing about
   the emitted C.
3. **The `fragment3` attribution.** Reproduced: `grep -n 'lauf "fragment[0-9]'
   instrumente/pruefe-emission.sh` -> nine runs (`fragment1,2,4,5,6,7,8,9,10`), no
   `fragment3`. Matches `645ddca`'s own account (renamed to `ipcfastpath` for the rejected
   rewrite) and `AUDIT-K100`'s "nine, not ten" denominator.

**All three hold. No F03.gab edit, no count-based reasoning reintroduced, no guardian
redefined.**

_(polling `git log --oneline master..worktree-agent-a7460ff215795e662` directly now, per
coordinator instruction, in addition to the background monitor)_

---

## Lane commit `108f186` -- `messung/KLASSEN-F03-2026-09-04.md`, the full row-by-row table

**`git diff master -- messung/fragmente/F03.gab`: still EMPTY.** Read the whole new document
and independently re-checked every load-bearing citation and measurement in it, not just the
headline count.

**The row-by-row table's verdicts, independent of mine:** N035x5 -> 2, M124x3 -> 2, M140#7
(:194) -> **2 (grammar production)**, M140 the other six + M143 + M101 + H011 -> 3, plus the
C001 at :185 -> **2 (grammar production)**. **9 rule-decision, 9 program-is-wrong, 0
plumbing among the 18 -- and the lane independently reaches the SAME split I derived before
reading this file** (my own tally: N035x5 + M124x3 + M140#7 = 9 rule-decision; the rest = 9
program-is-wrong). **Two independent derivations, same numbers, same two odd-ones-out
(M140#7 and the C001) reclassified out of their naive buckets into "grammar production" for
the same underlying reason -- convergence worth noting, not just agreement to wave through.**

Checked every citation and measurement, not sampled:

- **`crates/gabbro-syntax/src/parse.rs`:1477-1489 (M140 #7).** Read it myself: `&` is handled
  in `unary()`, takes only a `pfad` (path), yields `ExprArt::FnWert` -- with the comment,
  quoted verbatim by the lane and confirmed byte-for-byte: *"There is no address-of an
  expression in Gabbro, and that there is none is the reason `ptr` carries a provenance at
  all."* **This independently confirms the same grammar gap I had already found from the
  lexer side** (`grep '"&"' lex.rs` finding only bitwise-AND) before this commit landed --
  now confirmed from the parser side too, and it is the SAME underlying fact, not two
  different pieces of evidence dressed up as two.
- **The `cc` compilation claims for the M140/M143 cluster.** Reproduced independently, own
  scratch files, own `cc` invocation (`cc -std=c11 -Wall -Wextra -Werror`): `m140.c`
  (`Frame *call(...) { return block_current(...); }` with `block_current` declared `->
  uint32_t`) fails with `-Wint-conversion` exactly as quoted; `m143.c`
  (`owner_core(picked)` against a two-parameter declaration) fails with BOTH
  `-Wint-conversion` AND "too few arguments ... expected 2, have 1" exactly as quoted. **Both
  reproduce, independent build, independent files.**
- **Commit `918cca0`, cited three times, read in full.** Confirms all three uses: (a) the
  `N035` no-default-is-sound argument (a slot promising `writes summe`/100 ops called from a
  body promising `pure`/4 ops trips both `E008` and `K001` -- a concrete constructed case,
  not an assertion); (b) `table Threads` measured to make `M101` WORSE (18 -> 19, both
  assignments fail instead of one) -- an experiment that came out against the fix, reported
  anyway; (c) the `beispiele/gift/293` claim for `M124`.
- **`beispiele/gift/293-grund-an-fremdem-parameter.gab`**, read in full: `extern fn nimm(x :
  u32) ...; nimm(Status::Ok);` -- **byte-for-byte the shape** `F03` writes
  (`set_reg(f, SYSNO_RESULT, IpcResult::ErrQuiescing)`, a reason value at a `u32`
  parameter). Confirmed: this is a genuine, pre-existing poison probe for exactly this
  rule, not a shape invented for this argument.
- **Function names in the citation table**, spot-checked against not just line numbers but
  actual identifiers: `grundstellung` at `m1.rs`:573 (confirmed), `ruf_roh` at `m1.rs`:2168
  (confirmed), `pass_mit` at `geteilt.rs`:202 (confirmed), `fnptr_traegt_seinen_vertrag` at
  `namen.rs`:588 (confirmed, checked in an earlier round), `gestalt_passt`/`passt` at
  `m1.rs`:3563/3609 (confirmed, checked in an earlier round). **Every function name in the
  table is real and at the cited line -- these are not decorative citations.**

**Everything in `108f186` holds up under independent re-derivation.** No caprock-fidelity
argument reappears, no guardian is touched, `F03.gab` stays byte-identical, and the two
"grammar production" reclassifications (M140 #7, the queue `C001`) are the same conclusion I
reached independently through a different route (the cost-pass's own "assumed
correspondence" admission in `K001-DOMAENENSCHRANKE.md` for the queue case, the lexer's
missing `&` token for the address-of case) before reading this commit.

---

## Attacking my own conclusion: was plumbing EVER reachable for a `pruefe`-time error?

The coordinator's challenge, stated precisely: agreement between two independently-derived
conclusions is weaker evidence than it feels, and my claim (*"plumbing was never structurally
reachable for a `pruefe`-time error"*) is the stronger of the two and the one to break. Test:
go through every documented `D`-numbered emitter repair (`D1`-`D6`, `D19`-`D22`, plus `D15`-`D18`
which sit in the same catalog and are the same shape of evidence) and ask, for each, whether
`pruefe` was already refusing BEFORE the repair. **One counterexample -- a repair that
discharged an obligation over a file `pruefe` was refusing -- breaks the claim.**

Catalog: `messung/ERZEUGERDEFEKTE.md` (`D1`-`D6`) and `messung/ERZEUGERREST.md` (`D15`-`D22`),
both dated, both carrying `before`/`after` stage tables. Read every one, not sampled:

| defect | `pruefe` BEFORE the repair | source |
|---|---|---|
| `D1` | `3 items, 0 errors, 0 hints` | `ERZEUGERDEFEKTE.md`:21 |
| `D2` | `5 items, 0 errors, 0 hints` | `ERZEUGERDEFEKTE.md`:22 |
| `D3` | `2 items, 0 errors, 0 hints` | `ERZEUGERDEFEKTE.md`:23 |
| `D4` | `2 items, 0 errors, 0 hints` | `ERZEUGERDEFEKTE.md`:24 |
| `D5` | `2 items, 0 errors, 0 hints` | `ERZEUGERDEFEKTE.md`:25 |
| `D6` | `2 items, 0 errors, 0 hints` | `ERZEUGERDEFEKTE.md`:26 |
| `D16` | `4 items, 0 errors, 0 hints` | `ERZEUGERREST.md`:380 |
| `D17` | `4 items, 0 errors, 0 hints` | `ERZEUGERREST.md`:397 |
| `D19` | `4 items, 0 errors, 0 hints` | `ERZEUGERREST.md`:857 |
| `D20` | narrowing already `M1`-proved, no refusal at all | `ERZEUGERREST.md`:1021-1040 |
| `D21` | *"the checker accepts ... with zero errors"* | `ERZEUGERREST.md`:1101-1105 |
| `D22` | `5 items, 0 errors, 0 hints` | `ERZEUGERREST.md`:1184-1186 |
| **`D15`** | **refuses (`N007` -- a bit past the width)** | `ERZEUGERREST.md`:362 |

**Nine (D16/17/19/20/21/22) plus the six of D1-D6: fifteen of sixteen checked entries had
`pruefe` already at 0 errors.** `D15` is the one that does not, and I read it in full,
including the load-bearing comment IN THE SOURCE (`crates/gabbro-check/src/emit.rs:9391-9403`,
still there, verbatim, dated 2026-09-03) rather than trusting the document's paraphrase.

### `D15`, in full: a real complication, not a full counterexample

`reg X : u64 @0x0 fields { A @[4294967295:0] }` -- `pruefe` refuses this **by name**, at the
declaration, citing `N007` (a bit position past the width -- confirmed a real checker rule,
`crates/gabbro-check/src/bitlage.rs:93/102`). **And the emitter's own arithmetic panicked
anyway**: `hi - lo + 1` computed in `u32` (`Geraet::felder` stores the span as `u32`), so
`4294967295 - 0 + 1` overflows and the debug build panics -- *`attempt to add with overflow`,
`emit.rs:9403`* -- reproduced verbatim from the current source's own comment, not just the
document. **The repair widened the arithmetic to `u128`** -- confirmed live in the current
tree, `emit.rs:3856/4443/4496` all now compute `(1u128 << (hi - lo + 1)) - 1` rather than the
old `u32` form.

**What this proves, and what it does not.** It proves the emitter's machinery is NOT gated
behind "only runs if `pruefe` accepted" -- the source comment says it outright: *"the panic
still happened, because `command_emit` runs the whole back end before it reads the verdict,
and this expression is reached from a function body while the refusal sits at the
declaration."* This is a genuine, measured correction to something I asserted earlier in this
document (*"the emitter's job starts from an ALREADY-VALIDATED program ... it has no
machinery to invent a missing proof"*) -- that phrasing implied the emitter's code path is
simply not reached for refused input, and `D15` shows plainly that it is: the whole backend
runs regardless, and only the FINAL reported verdict depends on whether the checker already
found an error.

**But it does not prove a lowering obligation was ever discharged over refused input.**
Before the repair: `pruefe` refuses, `emit` panics, no C exists. After the repair: `pruefe`
STILL refuses (the stage table says so explicitly -- "unchanged"), `emit` produces "the
refusal, and no panic" -- still no C exists, still no obligation discharged. **The fix
replaced a crash with a correct, graceful refusal of a file whose refusal was already right**
(`N007` is a true fact about the program -- a bit position that does not exist). Nothing
about `F03`'s situation resembles this: none of `F03`'s 18 involve the emitter crashing, and
none would be "fixed" by hardening a panic into a clean error, because they are already
clean, reported refusals.

### The claim, restated more carefully

**Not "the emitter never runs over refused input" -- `D15` shows it does.** The defensible
claim is narrower and survives the test: *of sixteen documented emitter repairs, in the
one case where `pruefe` was already refusing, the repair did not and could not make the file
lower -- it made the tool fail more honestly at exactly the same refusal.* **Zero of sixteen
historical repairs ever turned a `pruefe`-refused file into a successfully-lowering one.**
That is the actual load-bearing fact behind "plumbing was never reachable for a `pruefe`-time
error," and it is now checked against real history rather than argued from the definition of
"checker error" alone. The single partial exception (`D15`) sharpens the claim rather than
breaking it: it shows precisely which part of my earlier reasoning was too strong (emitter
reachability) while leaving the part that matters for `H` (obligation dischargeability)
intact.

_(One more note on method, since the coordinator flagged it: `instrumente/fuzze-erzeuger.py`
itself defines its fuzzed population as `angenommen = (pruefe errors == 0 and not panic)`
(`:763`) and explicitly separates out "refused by the checker" cases from the population it
studies for emitter defects (`:1385-1387`). So the sixteen-case catalog is not an unbiased
sample of "all emitter repairs ever" -- its own search tool is built to look at `pruefe`-clean
input first. `D15` is the one entry that escaped that filter, found by hand rather than by the
sweep, which is itself worth noting: the one counterexample-shaped case in the whole catalog
came from outside the methodology that produced the other fifteen.)*
