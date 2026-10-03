# MUSE-REPORT-998: Exact review of author 848 (guard-page closing)

## Task
Report-only exact review of author 848 (Composition closing: guard-page
closing). Own only this file; no source or live-control changes.

## Identity and snapshot
- Clone verified: /home/simon/Dokumente/gabbro-muse/a998, branch muse/998,
  HEAD b040b155159f47629542b0083e2f0a8a607f2b4c, tree clean.
- b040b155 equals the SNAPSHOT base. The candidate branch itself was not
  fetched (no network, no other clones per task); review is over the pinned
  snapshot files (.tmp/review/author-848/): OWNER-TASK.md, PATCH.diff (541
  lines), the full candidate file, MUSE-REPORT-848.md, BUILD-EVIDENCE.json.
- Base context check: the PATCH import hunk anchors on
  `import Grammatik.X86.ComposeImageFetch` as the last line of base
  grammatik/Grammatik.lean — confirmed present. The diff surface is exactly
  the 3 SNAPSHOT files.

CANDIDATE: 848 c1eed54d487dca2a122f1db97c566aaac699b9e2

VERDICT: ACCEPT

## What the candidate contains
New file grammatik/Grammatik/X86/ComposeGuardPages.lean (435 lines) plus one
import line in grammatik/Grammatik.lean. Nine thin wrapper legs over accepted
producers, one six-leg closing conjunction
`ComposeGuardPages_verbindung`, one joint witness
`ComposeGuardPages_verbindung_zeuge` with new helpers `wachePushSpeicher`,
`wachePushS`, `wachePush_geholt`, `wachePush_exe`, `wachePush_guard`. No
diagnostic/gift/example/CLI numbers, no MARKE changes, no
source/checker/Spec/goal/emitter edits, no friend-reserved optimiser files.

## Independent verification (read-only, against base b040b155)
- All 9 reused producers exist in base with byte-identical signatures and
  argument order: StackExecution.lean `byteschritt_geholt_call` (39),
  `byteschritt_geholt_push` (65), `byteschritt_geholt_call_wache` (141),
  `byteschritt_geholt_push_wache` (165),
  `byteschritt_geholt_ret_nicht_ausfuehrbar` (191); StackUnwind.lean
  `wache_push_verweigert` (338), `wache_call_verweigert` (351);
  Stapel.lean `sichereWort_rahmen` (130); Speicher.lean
  `write64_verweigert_kein_effekt` (272). Signatures re-read, not trusted
  from the report.
- Every wrapper passes ALL its premises positionally to its producer; no
  premise dropped, no conclusion renamed from a premise, no Prop-typed
  premise, no `intro _` / `have _ :=`.
- Forbidden-token scan of the candidate file: zero real hits (matches are
  only the substring "admitted" in prose and "#print axioms" lines). No
  `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`. `decide` use matches the
  accepted-witness pattern (e.g. `nest_call_geholt`).
- Witness coherence checked: `wachePushS` keeps nestS0 registers (rip 4096,
  rsp 8192, so rsp-8 = 8184) with byte 80 (`push rax`, 1 byte) at 4096,
  14-byte zero suffix, executable window 4096..4111, uniformly
  non-writable memory — so fetch/exe/guard `decide` goals are well-formed
  and mirror the accepted call-guard `wacheNestS` shape. Memory change is
  genuine: `hmem` reduces via `nest_rsp0`, `writeBytesN_hit`,
  `addrOff_null` to a concrete byte inequality closed by `decide`
  (stored return word 4101 over a zero byte). All other witness components
  (`nestS0/S1/Disp/M1/Mp`, `nest_*`, `wacheNest_*`, `retNest_*`,
  `speicherZeuge`/`rahmenZeuge`, `nest_rsp0/rsp1`, `nest_call/push_schreibt`,
  `writeBytesN_hit`, `ohneUmbruch_addrs`, `zeuge_schreibbar8`) exist in base.
- Architecture (not just green): byte forms, widths, REX/register effects,
  pre-fault behaviour and canonical-execution interaction are all inherited
  unchanged from the accepted producers — nothing re-encoded, no invented
  determinism, no zeroed/ignored defined effect (success legs carry the
  exact stored word through `m`/`schrittCall`/`schrittPush`). Refusal legs
  pair loud `byteschritt .verweigert` with `write64 ≠ some m'`, i.e. the
  store has no outcome, so neighbour corruption is excluded by construction
  rather than assumed. Step-level `wachenSchritt*` legs are proved as
  decoder-independent extras, not smuggled into the closing claim. TSO/GX,
  silicon correspondence, source correspondence, ABI/loader/entry/cost are
  explicitly CUT with owning lanes named; `verweigert` is absence of a
  transition, with `DecodeFault` kept as the separate channel.
- Build evidence (author's, complete): final `./lean-probe` 0 errors with
  all 11 theorems printing standard axioms (subset of
  `[propext, Classical.choice, Quot.sound]`); `./lean-bau` "Build completed
  successfully (511 jobs)". One intermediate red probe (unknown tactic plus
  two unsolved goals) is documented mid-history and resolved before the
  final green commit — honest process, not a defect. I ran no build myself:
  reproducing it would require placing candidate source in my tree, which
  the "own only this report, no source" rule forbids; signature-level
  verification above plus the complete-output evidence stands in its place.

## Bounded acceptance
Accepts exactly: the six-leg generic guard-page closing over arbitrary
admitted inputs (fetched call/push success with correct stored word;
fetched call/push guard refusal each with no store outcome; fetched return
into a non-executable guard refusing the next byte step; in-frame save
preserving neighbour bytes) plus the joint non-degenerate witness with a
reached memory-changing run and planted refusals. No full-bridge,
no hardware, no source, no TSO claim — the file's CUTS state this precisely.

## Remaining open (not repairs)
Per the file's CUTS: source correspondence, hardware/silicon
correspondence, TSO/GX bridge, ABI/loader/entry/relocation/cost/final-image,
callee-save/entry contracts. Nothing in the owner task looks wrong; the
closing-statement shape (six-leg conjunction) follows the
`ComposeDecodeExec`/`ComposeImageFetch` pattern as the author records.

## Last build result
No build run in this lane (report-only review; tree untouched and clean).
Evidence relied on: author's `./lean-bau` "Build completed successfully
(511 jobs)" with standard `gabbro_ziel`-compatible axioms.
