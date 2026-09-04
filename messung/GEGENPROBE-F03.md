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

_(polling continues via background monitor -- next commits will be appended below)_
