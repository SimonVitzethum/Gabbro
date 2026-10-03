# MUSE-REPORT-848: Composition closing — guard-page closing

## Task
Close thread-stack guard pages to fault delivery: overflow hits the guard
and refuses instead of corrupting neighbours. Compose already-accepted
modules into one checked closing step; never re-prove internals, never
duplicate an interpreter or executor. Target: `ComposeGuardPages_verbindung`
with companion `ComposeGuardPages_verbindung_zeuge` (jointly inhabited,
non-degenerate, memory-changing reached run).

## What was done
New file `grammatik/Grammatik/X86/ComposeGuardPages.lean` (owned) plus one
import line in `grammatik/Grammatik.lean` (owned). No other files touched.
No diagnostic/gift/example/CLI numbers, no MARKE_EMIT changes, no
source/checker/Spec/goal/emitter edits, no friend-reserved optimiser files.

Producer/consumer interface closed: producers are the accepted fetched
stack steps (`StackExecution.byteschritt_geholt_call/push` and guard
refusals `byteschritt_geholt_call_wache/push_wache`), the accepted
step-level guard facts (`StackUnwind.wache_push/call_verweigert`), the
accepted frame-save facts (`Stapel.sichereWort_rahmen`) and the accepted
store facts (`Speicher.write64_rahmen`,
`write64_verweigert_kein_effekt`); consumer is fault delivery (loud
`byteschritt .verweigert` with no store outcome) plus neighbour
preservation.

## Exact new names
- `wachenCallWeiter`, `wachenPushWeiter` — fetched call/push success legs
  (reuse `byteschritt_geholt_call/push`).
- `wachenCallVerweigert`, `wachenPushVerweigert` — fetched guard refusals
  (reuse `byteschritt_geholt_call_wache/push_wache`).
- `wachenSchrittPushVerweigert`, `wachenSchrittCallVerweigert` —
  decoder-independent step-level refusals (reuse
  `wache_push/call_verweigert`).
- `wachenNachbarBleibt` — in-frame save preserves neighbour bytes (reuse
  `sichereWort_rahmen`).
- `wachenVerweigertOhneEffekt` — guard store has no outcome (reuse
  `write64_verweigert_kein_effekt`).
- `wachenRetVerweigert` — return into a guard (non-executable) address
  refuses the next byte step (reuse
  `byteschritt_geholt_ret_nicht_ausfuehrbar`).
- `ComposeGuardPages_verbindung` — six-leg generic closing conjunction.
- `ComposeGuardPages_verbindung_zeuge` — joint companion witness.
- Witness helpers (owned by this lane): `wachePushSpeicher`, `wachePushS`,
  `wachePush_geholt`, `wachePush_exe`, `wachePush_guard` (fetched
  push-guard case, reusing the accepted nested-run code shape and guard
  shape; the accepted call-guard `wacheNestS` and return `retNestS`
  witnesses are reused by name, not rebuilt).

The witness shows: a reached memory-changing run through the composed
call step (zero becomes the return address below the old top, via
`writeBytesN_hit`), the fetched push step, planted call/push guard
refusals each with no store outcome, a fetched return into a guard
address refusing the next byte step, and a checked frame save preserving
its neighbour slot (slot 1 written, slot 0 byte-equal). Non-degeneracy:
executable code window plus writable stack cell with an actually stored
word (the analogue of a written table); refusal legs use the same code
bytes with write-protected stacks.

## Verification
- `./lean-probe grammatik/Grammatik/X86/ComposeGuardPages.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau`: `Build completed successfully (511 jobs)`, whole project
  green; every new theorem depends only on standard axioms (subset of
  `[propext, Classical.choice, Quot.sound]`). `gabbro_ziel` axioms
  unchanged (this lane adds no goal-level statement).
- Every premise of every new theorem is used (each leg applies its
  accepted producer to all its premises); no `sorry`/`admit`/`axiom`/
  `native_decide`/`unsafe`; no Prop-typed premises; no weakened
  conclusions.

## What remains open (CUTS, owning lanes named)
- No source correspondence (source/Bridge lanes), no hardware
  correspondence/silicon (hardware lanes), no TSO/GX bridge (TSO bridge
  lanes), no ABI/loader/entry/relocation/cost/final-image claim, no
  callee-save/entry contracts.
- `verweigert` is the absence of a transition, never termination;
  architectural faults keep their own channel (`DecodeFault`).
- The file states nothing the task did not ask for; I believe nothing in
  the task is wrong. One judgement call to record: the task's TARGET named
  only the closing theorem; its statement shape (six-leg conjunction over
  arbitrary admitted inputs) is mine, following the `ComposeDecodeExec` /
  `ComposeImageFetch` pattern. The push-guard fetched witness had no
  accepted concrete instance, so I planted one new minimal witness
  (`wachePushS`) from accepted shapes rather than assuming the leg.
