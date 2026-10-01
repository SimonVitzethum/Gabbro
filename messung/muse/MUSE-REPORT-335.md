# MUSE-REPORT-335: Reviewed organisation plan A1 — NarrowOps

Lane 335, wave A1 author. Branch `muse/335`. pwd/toplevel verified
`/home/simon/Dokumente/gabbro-muse/a335`.

## What was done

New module `grammatik/Grammatik/X86/NarrowOps.lean` (~690 lines with CUTS
and `#print axioms` per theorem), plus one additive import line at the end
of `grammatik/Grammatik.lean`. Nothing else touched: no source checker,
Spec, goal, central `Typen`, Rust, emitter, docs, or friend-reserved path.

The module provides 8/16/32-bit narrow load/store/move helpers with
zero/sign-extension and a proved mask discipline, exactly as the
reviewer-approved A1 direction asks:

- Register merge `mergeRegNarrow` with the architectural upper-bit rule:
  8/16-bit writes preserve the unaffected upper bits, a 32-bit write
  carries exactly the low-32 truncation (upper32 cleared), 64-bit is the
  full word. Generic 32-bit fit fact; 8/16-bit preservation pinned
  concretely (`probe_mergeRegNarrow_8/16`).
- Extension `extendNarrow` over an explicit `ExtendMode` (zero/sign),
  reusing canonical `trunc`/`sext`; generic fit facts via a local
  truncation bridge (`narrowMaskMod`, `narrowTruncMod`).
- Profile admission `narrowAdmitted` (alignment `isAligned`,
  single-carrier `crossesCarrier`, canonical byte permissions) with four
  generic refusal theorems. The Bool is validator/profile admission, NOT
  a hardware fault: ordinary unaligned accesses still work through the
  canonical memory ops.
- State helpers `loadNarrow`, `storeNarrow`, `moveNarrow`,
  `loadNarrowExtend`, reusing `readBreite`/`writeBreite`, `regSet`,
  `effAddr`. The 64-bit case of each is definitionally the existing
  64-bit operation (`loadNarrow_b64_isRead64`,
  `storeNarrow_b64_isWrite64`, `moveNarrow_b64`) — the one target
  semantics extended, no duplicated evaluator of the 14 pilot forms.
  Every helper preserves flags like architectural MOV; no narrow flag
  snapshot exists (booked in CUTS). RIP is unchanged (lengths come from
  decoding only; no narrow decode exists).
- Pre-state addressing `loadNarrowAtBase`/`storeNarrowAtBase` over
  `effAddr` with `rfl` links.
- Loud signedness guard `narrowGuard` (`SignKind.unknown` demands the
  check), extension-form gate `extendFormOk` with refusal theorem.
- Permission-only scalar fallbacks `scalarFallbackRead8/16/32/64` plus
  the pinned unaligned-fallback probe (`probe_fallback_unaligned`:
  admission refuses at 8193, the scalar 32-bit read still answers).
- Witness `spillFillWitness`: aligned 32-bit spill of `0x01020304` at
  8192 through `storeNarrow`, 32-bit fill through `loadNarrow`, 8-bit
  agreement (`0x04`, via `spillFillAgree`), and an observable memory
  change. Non-degenerate: real store-changing execution on real memory.
- Refusal probes: `probe_narrowAdmitted_unaligned`,
  `probe_crossesCarrier_pin`, `probe_extendFormOk`.

## Exact new names

Defs: `mergeRegNarrow`, `ExtendMode`, `extendNarrow`, `isAligned`,
`crossesCarrier`, `narrowAdmitted`, `loadNarrow`, `storeNarrow`,
`moveNarrow`, `loadNarrowExtend`, `extendFormOk`, `loadNarrowAtBase`,
`storeNarrowAtBase`, `SignKind`, `narrowGuard`, `spillVal`,
`spillRegFile`, `spillFlags`, `spillState`, `spillAfter`.
Theorems: `mergeRegNarrow_b64/b32/b32_fits`, `extendNarrow_zero/sign/
zero_fits`, `narrowMaskMod`, `narrowTruncMod`,
`probe_mergeRegNarrow_8/16`, `probe_extendNarrow`,
`narrowAdmitted_needsAligned/needsCarrier/needsReadable/needsWritable`,
`permReadable/permWritable`, `probe_narrowAdmitted_ok/unaligned`,
`probe_crossesCarrier_pin`, `loadNarrow_success/refused/flags/memory`,
`storeNarrow_success/refused/flags/regs`,
`loadNarrowExtend_success`, `moveNarrow_flags/memory/b64`,
`loadNarrow_b64_isRead64`, `storeNarrow_b64_isWrite64`,
`storeNarrow_frame_b32`, `storeNarrow_readback_b32`,
`loadNarrowAtBase_eq`, `storeNarrowAtBase_eq`, `narrowGuard_unknown/
signed/unsigned`, `extendFormNeedsNarrower`, `probe_extendFormOk`,
`scalarFallbackRead8/16/32/64`, `probe_fallback_unaligned`,
`readBreite_b32_eq`, `readBreite_b8_eq`, `writeBreite_b32_eq`,
`spillFillAgree`, `spillVal_trunc/low`, `spillFillWitness`.

## Verification

- `./lean-probe grammatik/Grammatik/X86/NarrowOps.lean`: 0 errors.
- Full `./lean-bau`: `exit 0`, 0 error lines, `Build completed
  successfully (386 jobs)`, last line `✔ [385/386] Built Grammatik`.
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` (word-boundary
  grep clean; remaining hits are `admitted` in prose and `#print`).
- Every `#print axioms` is within the standard set (subsets of
  `propext`, `Classical.choice`, `Quot.sound`); several probes depend on
  no axioms at all.
- Goal intact by construction: `git status` shows only the new module
  plus one import line; no Zielsatz/Spec/checker file touched, and the
  whole tree (including Zielsatz) rebuilt green. The `#print axioms
  gabbro_ziel` lines in `Zielsatz/BeweisAtomar.lean` are untouched.
- Every theorem uses all its premises (checked by hand; `rw` with named
  equations counts as use; no `intro _` / `have _ :=` anywhere).
- All identifiers and comments in this module are English.

## What remains open (also in the file CUTS)

No narrow encoding/decoding (no new `Befehl`; pilot codec is 64-bit
only per BYTE-PILOT.md — REX/modrm patterns inspected as context).
No narrow ALU flag snapshots. The fully generic 8/16-bit merge
upper-preservation BitVec identity is pinned concretely, not proved
generically. No atomicity/TSO/GX claim (lanes 274/284 own the bridge).
No source correspondence (lane 277) and no substitute for lane 287's
pending shared IR. No hardware verification and no cost/time transfer.
RIP advance for narrow forms waits on a future narrow decode.

## Task feedback (things I believe are off)

- The dep line names `Speicher (lesbar8)`: correct, it exists and is
  reused via `lesbarN`/`schreibbarN`/`readBreite`/`writeBreite`.
- The dep line names `Codec (REX/modrm patterns)`: inspected — the
  patterns exist but cover only the 14 64-bit pilot forms (BYTE-PILOT.md
  explicitly excludes 32-bit operands). There is nothing to reuse for
  narrow semantics without inventing an encoding, so this module
  imports no codec and books encodings as OPEN. If the reviewer
  expected a codec contribution, that expectation conflicts with the
  pilot contract and with the no-invented-behaviour rule.
- "Refusal: unaligned or cross-footprint narrow access refused by the
  Bool" is implemented as *profile admission* with a certified scalar
  fallback, per the safety correction (actual x86 allows many unaligned
  ordinary accesses). A reader expecting refusal-as-hardware-fault
  should read the correction note, not the headline.
- No `ZEUGE:` target line was given, and no theorem here quantifies
  over source syntax, so HARD RULE 13 has no mechanical trigger; the
  joint memory-changing witness is `spillFillWitness` (plus
  `spillFillAgree`, the fallback probes, and the concrete merge pins).
