# MUSE-REPORT-566: Conditional forms bytes to accepted control execution

Lane 566, branch `muse/566`, clone `/home/simon/Dokumente/gabbro-muse/a566`.
Owned files only: `grammatik/Grammatik/X86/ControlCodec.lean` (new, 1057 lines),
`grammatik/Grammatik.lean` (one additive import line), this report.

## What was done

Connected the accepted register-only conditional-select evaluators
(`ControlFlow.setCCAnwenden`, `ControlFlow.cmovAnwenden`, plus the
`ConditionalMove` lemmas and witnesses) to real canonical x86-64 bytes,
without touching any pilot file. New module `Grammatik.X86.ControlCodec`:

- Byte shapes: SETcc `REX 0F 90+cc /0 mod=3` (`encodeSetCC`), CMOVcc
  `REX.W 0F 40+cc /r mod=3`, reg=destination (`encodeCmov`). The profile
  always emits REX on SETcc so byte registers are uniformly
  spl/bpl/sil/dil/r8b-r15b (never ah/ch/dh/bh).
- Decoders parsing REX / condition / ModRM / actual length
  (`decodeSetCCNach`/`decodeSetCC`, `decodeCmovNach`/`decodeCmov`), with
  generic round trips (`roundtrip_setCC`: 256 cases; `roundtrip_cmov`:
  4096 cases, needs `set_option maxHeartbeats 4000000 in`, same as the
  `Codec` pilot round trips) and decoder-length inversions
  (`decodeSetCC_laenge`, `decodeCmov_laenge`: success consumes exactly
  4 bytes).
- Byte steps reusing the accepted evaluators (`setccSchrittBytes`,
  `cmovSchrittBytes`); `cmovSchrittBytes_gleich` proves the CMOVcc byte
  step IS the accepted `cmovSchritt` at the actual length. Value theorems
  reuse `cmovAnwenden_genommen_wert` / `_nicht_wert`; source-free frame
  (flags, memory, RIP, untouched registers) proved per step.
- End-to-end theorems (`setccBytes_endzuende`, `cmovBytes_genommen`,
  `cmovBytes_nicht`): decode success fixes the consumed length at 4
  actual bytes, the step at that length gives value + frame. Every
  premise is used (decode via the length inversion).
- Pins: `pin_setCC_r9b[_dekode]` (`SETE r9b` = `41 0F 94 /0`),
  `pin_cmov_r9_r15[_dekode]` (`CMOVe r9,r15` = `4D 0F 44 /r`),
  `pin_cmovBytes_taken`, `pin_setccBytes_untaken` (taken split reused
  from `cmov_witness_unterscheidet`).
- Refusals: `mut_setCC_bedingung` (0x95 decodes to observably `ne`),
  reg-field/mode/REX refusals, both truncations, empty input, plus
  collision pins `ours_refuses_movReg/push_r8/jumpIf/ret`.
- Dispatch: `CondForm`/`Dispatched`/`dispatch` (pilot first, then SETcc,
  then CMOVcc). Generic pilot-refusal of every new byte string over any
  suffix (`pilot_refuses_setCC`, `pilot_refuses_cmov`, via disjoint `0F`
  second-byte ranges: pilot `0x80-0x8F`, CMOV `0x40-0x4F`, SETcc
  `0x90-0x9F`), agreement theorems (`dispatch_pilot`,
  `dispatch_setCC`, `dispatch_cmov`) and byte routing
  (`dispatch_setCC_bytes`, `dispatch_cmov_bytes`,
  `dispatch_pilot_bytes`, with `setCC_refuses_cmov` and
  `decodeSetCC_fremd_rex` for the middle stage).
- Joint witnesses `cmovBytes_genommen_zeuge`,
  `setccBytes_endzuende_zeuge`: concrete decode + step + a stored word
  that reads back and observably changes a byte + a planted truncation
  refusal.

No memory-CMOV arm and no indirect-target arm exist anywhere: the
accepted fault-keeping `cmovMemSchritt` is reused, never re-decided.
No `Befehl` constructor added; no source/checker/Spec/goal/emitter
change; no friend-file edit.

## Checks

- `./lean-probe grammatik/Grammatik/X86/ControlCodec.lean`:
  `== 0 error(s) in the COMPLETE output`.
- `./lean-bau`: `Build completed successfully (428 jobs).`
- `#print axioms`: every theorem depends at most on
  `propext, Classical.choice, Quot.sound` (the goal-axiom set); most on
  `propext` alone or nothing. No `sorry`/`admit`/`axiom`/`native_decide`
  (one `set_option maxHeartbeats` scoped to `roundtrip_cmov`, as in
  `Codec.lean`).
- No premises over source syntax (`Vertrag`/`Stmt`/etc.) and no
  `ZEUGE:` targets in the task; the two `_zeuge` companions cover the
  main run theorems with jointly instantiated concrete decode + reached
  memory-changing execution + planted refusals.

## What remains open (also in CUTS)

- No hardware correspondence: byte shapes follow the Intel manual
  (SETcc `/0`, CMOVcc reg=destination), checked here as
  self-consistency only, not silicon.
- No generic ours-refuses-pilot theorem (only the four overlapping
  pilot forms pinned). Routing is still unambiguous: dispatch is
  pilot-first and the generic pilot-refuses-ours direction is proved.
- No source/IR/checker/emitter/goal, TSO/GX, concurrency, cost or time
  claim; all facts sequential over one `Speicher`.

## Producer/consumer interface and next integration

- Producers (reused, untouched): `Codec` byte helpers
  (`regCode/codeReg/condCode/codeCond/natByte/byteNat/rexByte/modrmReg`,
  `decode`, `roundtrip`), `ControlFlow`/`ConditionalMove` evaluators,
  lemmas and witnesses.
- Consumers: `dispatch` + `dispatch_*_bytes` give the next integrator a
  proved byte-string router (pilot meaning preserved, new forms fall
  through); `setccBytes_endzuende` / `cmovBytes_genommen/nicht` give
  byte-anchored value+frame facts; the two `_zeuge` give regression
  witnesses with memory change and planted refusals.
- Measurable next step: a loaded-image walker feeding actual executable
  bytes through `dispatch` (decode coverage owns the walker), then the
  per-access TSO bridge (needs the accepted 567/570 interfaces, not
  invented here).

## Task remarks

Nothing in the task looks wrong. One clarification I had to decide
myself: since the pilot `Befehl` has no conditional-select constructor
(by design, and lane-owned files forbid touching it), the byte path
lives in the new module with its own `CondForm` vocabulary and a
pilot-first `dispatch`, rather than as new `Codec` rows. The report
states this as interface, not as a claim about the pilot.
