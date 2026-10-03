# MUSE-REPORT-920: exact review of author 770 (indirect CALL provenance)

## CANDIDATE

CANDIDATE: 770 8f64c2f3abfd62902c8f090fe63a767188ef2aba

## VERDICT

VERDICT: ACCEPT (bounded, as scoped below)

## Task reviewed

Lane 770: per-call indirect `CALL r/m64` target provenance for function-pointer
and entry-fn values under the N575-N577 discipline, with pinned bytes, reusing
the accepted lane-680 forms and dispatcher; no new decoders/interpreters, no
source/checker/emitter edits, no new numbers, no MARKE changes.

## What I inspected

- Exact pinned snapshot files in `.tmp/review/author-770/`: `OWNER-TASK.md`,
  `MUSE-REPORT-770.md`, `PATCH.diff` (562 lines), `BUILD-EVIDENCE.json, and
  `grammatik/Grammatik/X86/IndirectCallProv.lean` (459 lines), plus the local
  reference `.tmp/HARDWARE-REFERENCES/REFERENCES.json` and
  `intel-instruction-reference.txt`.
- Base check: snapshot `base` is `56537272a31df3de5d9b7898bbade91c3de817b8`;
  this clone's HEAD is the identical hash (verified via `git rev-parse HEAD`).
  Review is on the exact base. Working tree was clean before and after.
- PATCH scope: only `MUSE-REPORT-770.md` (new), `grammatik/Grammatik.lean`
  (single appended import line), `grammatik/Grammatik/X86/IndirectCallProv.lean`
  (new). No source/checker/Spec/goal/emitter edits, no friend-reserved files.

## Independent reproduction (queued wrapper, read-only)

- `./lean-probe .tmp/review/author-770/grammatik/Grammatik/X86/IndirectCallProv.lean`
  in this clone: `== 0 error(s) in the COMPLETE output; exit 0`. The exact
  snapshot file typechecks against this clone's accepted parents. No tree
  files were touched for this (snapshot probed in place; no staging needed).
- Axiom output reproduced exactly as claimed: admission/frame/pin/refusal
  theorems `[propext]` or axiom-free; both connection theorems and both
  witnesses `[propext, Quot.sound]`; no `sorryAx` anywhere.

## Architecture checks (not just green)

- Byte forms, verified against the local Intel snapshot: `FF D0` is opcode
  `FF` with ModRM `D0` = mod 3, reg `/2`, rm `rax` (register-indirect CALL
  through rax, length 2); `REX.W FF 93` + disp32-16 is mod 2, reg `/2`, rm
  `rbx` (memory-indirect CALL through `[rbx+16]`, length 7). The snapshot text
  confirms `FF /2 CALL r/m64: call near, absolute indirect` and lists
  `CALL (FF /2)` as an indirect branch. Refusal `FF C0` (mod 3, reg `/0`)
  is `INC rax`, correctly not an indirect arm.
- Register/width/flag semantics: the frame theorem keeps every register except
  `rsp` and preserves flags. `CALL` pushes next-RIP and branches; it modifies
  no flags, so the frame is the architecturally correct one. No invented
  determinism: undefined-flag state is untouched, not zeroed.
- Operands and memory order: the register connection lands on the pre-state
  register word; the memory connection reads the target word from the
  pre-state effective address first (`hrd`) and pushes second (`hwr`), so no
  target fault is speculated away. Return-word read-back is proved, not
  assumed. This matches the accepted `callRegSchritt_erfolg` /
  `callMemSchritt_erfolg` constructors, which both exist in this clone's
  `IndirectControlHardwareForms.lean` together with every reused name
  (`encodeIndReg`, `encodeIndMem`, `decodeIndirekt`,
  `zielOhneHerkunft_fuehrt_aus`, `indS0/indS1/indM1`, `memS0/memS1/memM1`,
  `memS0_liest`, `indKette_zeuge`, `memCall_zeuge`, `read64_nach_write64`,
  `effAddr`, `lesbar8/schreibbar8`, `laengeOk` — all confirmed present).
- Gates: `CALL r/m64` is base ISA; no feature, MXCSR, or interrupt-enable gate
  applies, and the file adds none. TSO/GX is explicitly NOT claimed (per-access
  target-to-W/GX simulation is OPEN); the author proves register/flag framing
  plus return-word read-back instead and books the rest as CUTS. Correct and
  honest boundary, no fake closure.
- Provenance vs execution separation: `rufProvOk` is validator data; the file
  states an unadmitted target still executes at step level, citing the
  accepted separation `zielOhneHerkunft_fuehrt_aus`. No hardware fault is
  invented for off-table targets.
- N575-N577: named origin of the two provenances only (`fnZeiger` must be a
  decoded start, `eintrittFn` a listed entry). No theorem speaks about Gabbro
  source, contracts, the checker, or the emitter. Occurrences of `N575-N577`
  are comment-only (2 matches). No desired-correctness premise, no guarantee
  weakening.
- Premise use: no `intro _`, no `have _ :=`, no `sorry`/`admit`/`axiom`/
  `native_decide`/`unsafe` in the file (grep-confirmed; only English
  "admitted" matches). Both connection theorems use every premise to select
  the accepted success constructor, fix the successor, and discharge
  read-back plus origin membership.
- Witnesses: `IndirectCallProv_verbindung_zeuge` (TARGET companion) holds
  jointly on the fetched `CALL rbx` state with the memory difference at 8184
  projected from `indKette_zeuge`; `IndirectCallProv_verbindung_eintritt_zeuge`
  holds jointly on the fetched RSP-based memory call with the difference at
  8192 projected from `memCall_zeuge`. Both are reached, memory-changing,
  non-degenerate runs reusing fetched executable-byte states. Pin/refusal
  theorems are closed `decide`s (2 acceptances, off-table/unknown-site/origin-
  mismatch refusals, `/0` neighbour refusal), each falsifiable by construction.
- CUTS block is precise: no new decoding/execution, no silicon claim beyond
  the stated SDM headings, no source/checker bridge, no TSO/concurrency/cost/
  time/termination, no whole-image/loader/ABI/entry/budget connection.
  Matches what the file actually does.

## Bounded acceptance

ACCEPT covers: the per-call provenance admission with row/origin guarantees;
the two execution connections with return-word read-back; the
register/flag frame; the closed byte pins and provenance refusals; the two
joint memory-changing witnesses. It does NOT cover TSO/GX, concurrency,
source/checker bridging, whole-image or loader/ABI/entry/budget connection,
all explicitly booked as CUTS.

## Last wrapper result

`./lean-probe .tmp/review/author-770/grammatik/Grammatik/X86/IndirectCallProv.lean`:
`== 0 error(s) in the COMPLETE output; exit 0` (axiom lines as listed above).

## Open / notes

- Nothing in the candidate needs repair. One task-phrase note (already raised
  by the author): the owner task asks for "asynchronous/TSO effects for every
  form claimed", which no lane can close while the per-access target-to-W/GX
  simulation is OPEN; proving framing + read-back and booking TSO as CUTS is
  the correct response, not a defect.
- The author's BUILD-EVIDENCE shows an honest development trace (intermediate
  2-error probe state, two transient missing-olean full-build flakes with no
  file change between retry and green). No action needed.
- This review owned and changed only `MUSE-REPORT-920.md`; no source or live
  control files were modified.
