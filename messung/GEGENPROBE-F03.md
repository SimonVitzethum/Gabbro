# Gegenprobe zu F03 -- standing adversary of `worktree-agent-a7460ff215795e662`

Counter-check of the lane running on branch `worktree-agent-a7460ff215795e662`. Its task:
classify each of the 18 checker errors in `messung/fragmente/F03.gab` as **transcription
error** (caprock says something different -- correctable) or **language gap** (the excerpt
is faithful and Gabbro refuses -- stays). Written and committed live, one section per
finding, as the lane's commits land.

Ground truth: `../caprock-messbasis/crates/caprock-ipc/src/lib.rs` (867 lines, read in
full). Baseline re-run by me, independent of the lane's tree:

```
ssh ki-pc-fisch-101 'cd gabbro-gegen && export PATH=$HOME/.cargo/bin:$PATH && ./target/debug/gabbro pruefe messung/fragmente/F03.gab'
```
(own server directory `gabbro-gegen`, built from `master` at `4e08b94`)

Result: **27 items, 18 errors, 1 hint** -- confirmed, matches the task's premise. Full list
of the 18, by line:

| # | code | line:col | message |
|---|---|---|---|
| 1 | N035 | 151:21 | `fn(#1) -> ...` declares no `effects` and no `costs` |
| 2 | N035 | 152:21 | `fn(#1) -> ...` declares no `effects` and no `costs` |
| 3 | N035 | 153:21 | `fn(#1,#2) -> ...` declares no `effects` and no `costs` |
| 4 | N035 | 154:21 | `fn(#1,#2,#3) -> ...` declares no `effects` and no `costs` |
| 5 | N035 | 155:21 | `fn(#1) -> ...` declares no `effects` and no `costs` |
| 6 | M124 | 175:34 | a reason value cannot stand here (`IpcResult::ErrQuiescing` as arg) |
| 7 | M140 | 194:25 | argument `q` requires `ptr<...> TidQueue`, value has `TidQueue` |
| 8 | M124 | 197:38 | a reason value cannot stand here (`IpcResult::ErrEpFull` as arg) |
| 9 | M140 | 200:16 | return requires `ptr<...> Frame`, value has `u32` |
| 10 | M124 | 204:54 | a reason value cannot stand here (`IpcResult::Ok` as arg) |
| 11 | M140 | 204:13 | argument `f` requires `ptr<...> Frame`, value has `u32` |
| 12 | M140 | 205:13 | argument `f` requires `ptr<...> Frame`, value has `u32` |
| 13 | M101 | 208:33 | assignment requires `u32 in 0..4294967294`, value has `u32` |
| 14 | M143 | 210:8 | `owner_core` declares 2 params, call passes 1 |
| 15 | M140 | 210:19 | argument `d` requires `ptr<...> SchedOps`, value has `u32 in 0..4294967294` |
| 16 | M140 | 211:16 | return requires `ptr<...> Frame`, value has `u32` |
| 17 | M140 | 214:12 | return requires `ptr<...> Frame`, value has `u32` |
| 18 | H011 | 170:33 | `call` declares `locks SCHEDS` but never takes it |

(The `E009` at 158:9 is a **hint**, not one of the 18 errors, and is excluded.)

## Untouchable protocol -- read and confirmed BEFORE any lane commit

`../caprock-messbasis/crates/caprock-ipc/src/lib.rs:625-643`:

```rust
while let Some(server) = self.receivers.dequeue() {
    let Some(sframe) = ops.frame_of(server) else {
        continue; // toter Empfänger -> Eintrag verwerfen, nächsten versuchen
    };
    transfer(frame, sframe);
    frame_set_reg(sframe, reg::SYSNO_RESULT, result::OK);
    frame_set_reg(sframe, reg::EP_BADGE, 0);
    self.caller = Some(caller);
    self.reply_owner = Some(server); // dieser Server schuldet die Antwort
    return if caprock_sched::owner_core(server) == Some(core) {
        ops.switch_to(core, frame, server) // intra-Kern: direkt zum Server
    } else {
        ops.unblock(server); // anderer Kern: Server dort wecken (+IPI)
        ops.block_current(core, frame) // Aufrufer blockiert, nächster lokaler Thread
    };
}
```

Confirmed: `call` drains DEAD entries (the `let-else continue`) but **returns at the first
LIVE receiver** -- it does not drain the whole queue. Any correction that makes `call`
(or the excerpt's `traverse ... by consuming` loop at F03.gab:185-191) behave differently
from this is commit `645ddca` repeated, and I will stop and report immediately if I see it.

Note for context (not yet a finding, just read): `dokumente/FRAGMENTE.md`:673-676 (source of
the excerpt, "«B10»") already documents that the draft's `traverse ... by consuming` form
drains the WHOLE queue because `traverse` has no `break` -- i.e. F03.gab's own loop is
already known, on record, to diverge from caprock's early-return here. That divergence is
pre-existing in the frozen excerpt and is not itself one of the 18 checker errors (the
checker does not flag it) -- but it means F03.gab is already NOT 100% behaviourally
faithful to caprock at this one point, independent of anything the lane does. Flagged here
so I do not mistake a correction of THIS specific gap (turning `by consuming` into an
early-exit form) for scope creep -- it would in fact be restoring fidelity, not breaking
the protocol, PROVIDED it still returns at the first live receiver and does not change
`call`'s signature/effects in a way that contradicts the lock reality below.

## Running count

**Language gap: 0 of 18 checked so far. Transcription error: 0 of 18 checked so far.**
(Lane has not yet landed a commit on `worktree-agent-a7460ff215795e662` as of this writing --
branch tip is still `4e08b94`, identical to `master`. Polling continues.)

## Preliminary independent read (mine, before seeing any lane claim)

Not a verdict -- a hypothesis to test the lane's claims against:

- **#1-5 (N035, SchedOps fn-pointer fields)**: `type SchedOps` mirrors a Rust `&mut dyn
  SchedOps` trait object; Rust method signatures carry no `effects`/`costs` clause at all --
  there is no caprock line that could settle this by disagreeing with the excerpt. Expect
  **language gap** unless the lane finds an actual line-level mismatch (e.g. wrong arity/types
  against the real `SchedOps` trait, which lives in `caprock-sched`, not `caprock-ipc`).
- **#6, #8, #10 (M124, reason-as-argument)**: caprock passes `result::OK` / `result::ERR_EP_FULL`
  etc. as plain `u64` constants into `frame_set_reg(frame, reg, value)` -- Rust has no
  restricted-use enum matching Gabbro's `reason` doors (return/match/==). This looks
  structural to Gabbro's type system, not a copying mistake. Expect **language gap**.
- **#18 (H011, `locks SCHEDS` never taken)**: caprock's own module comment (lib.rs:15-16)
  states plainly: "Die Methoden hier operieren jeweils auf einem Objekt (`&mut self`) ohne
  eigenes Locking; das Locking + die Sperrordnung besorgt der Kernel/Dispatch." `call` itself
  never takes a lock in caprock -- confirming the excerpt's effects clause (`locks SCHEDS`)
  was added by whoever drafted the Gabbro version, not lifted from caprock. This is the one
  most likely to be an honest reclassification-worthy transcription add-on -- but F03.gab's
  own header (lines 82-97) already argues this is a real finding ABOUT the excerpt (the
  effects clause over-promises), which is its own third thing, not cleanly either box. Watching
  for how the lane handles this one specifically.
- **#7, #9, #11, #12, #15, #16, #17 (M140, record/pointer and Frame/u32 mismatches)**: these
  look like consequences of `Frame`/`RegNr` being ADDED types (F03.gab:63-72, marked
  "ERGAENZT (2026-09-03)") that the excerpt's calls were never adjusted to match syntactically
  (pointer vs value passing). This is not "caprock says something different" in the sense of
  disagreeing content -- it is an internal consistency question inside the Gabbro excerpt.
  Watching closely for whether the lane manufactures a caprock citation here that doesn't
  actually settle anything.
- **#13 (M101, `Some(caller)` range)**: F03.gab's own header (lines 24-27, dated before
  2026-08-25) already calls this a "Gabbro" (i.e. language-gap-shaped) finding: the assignment
  target's range excludes `0xffff_ffff` (`KEIN_SERVER`'s sentinel), which the *producer*
  (`current_id`) knows nothing about narrowing away. Expect **language gap**.
- **#14 (M143, `owner_core` arity)**: F03.gab declares `owner_core(d, t)` (2 params, line 234)
  but calls it as `owner_core(picked)` (1 arg, line 210) -- matches the ORIGINAL excerpt in
  `dokumente/FRAGMENTE.md`:695 verbatim (`if owner_core(picked) == core`), which is itself
  copying caprock's `caprock_sched::owner_core(server) == Some(core)` (lib.rs:637) -- a
  **free function taking one argument** in caprock. The extern declaration in F03.gab added a
  `d: ptr<...> SchedOps` first parameter that has no counterpart in the real signature. This
  smells like a genuine candidate for **transcription error**: the excerpt's own extern
  signature (not caprock, not the call site) is what is wrong, and correcting the SIGNATURE
  (drop the `d` parameter, since `owner_core` in caprock is a bare free function, not a method
  on `SchedOps`) would fix it without touching the faithfully-copied call site. Priority check
  once the lane addresses this one.

## Per-finding verdicts (filled in as the lane's commits land)

_(none yet -- branch `worktree-agent-a7460ff215795e662` has produced no commits beyond
`master` as of this writing)_
