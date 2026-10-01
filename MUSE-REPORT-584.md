# MUSE-REPORT-584: Independent exact-candidate connection review of 566

Lane 584, branch `muse/584`, clone `/home/simon/Dokumente/gabbro-muse/a584`.
Owned file only: this report. Candidate reviewed from
`.tmp/review/` (SNAPSHOT head `bb60709…`, task, report, build evidence,
full candidate file copy) plus a temporary reproduction in my own clone
(candidate file + one import line, removed afterwards; tree verified clean).

CANDIDATE: 566 bb60709666f19fae087924f21b6335ec1dbee71c

## What was checked

Candidate scope (matches its task and SNAPSHOT file list): new module
`grammatik/Grammatik/X86/ControlCodec.lean` (1057 lines), one additive
`import Grammatik.X86.ControlCodec` in `grammatik/Grammatik.lean`, no
other file touched. No `Befehl` constructor, no source/checker/Spec/goal/
emitter change, no friend-file edit — confirmed by reading the full file
and the PATCH header.

Producer/consumer connection (all names resolved in the accepted tree):
`Codec` byte helpers (`regCode`/`codeReg`/`condCode`/`codeCond`/`natByte`/
`byteNat`/`rexByte`/`modrmReg`, `decode`/`decodeRex`/`roundtrip`),
`ControlFlow` evaluators (`setCCAnwenden`, `cmovAnwenden`, `cmovSchritt`,
`cmovMemSchritt`, `bedingung`, `setCCByte`, `setLowByte`, `witTrue`/
`witFalse`, `witSpeicher`, `wit_schreibbar8`/`wit_lesbar8`) and
`ConditionalMove` lemmas/witnesses (`cmovAnwenden_genommen_wert`,
`cmovAnwenden_nicht_wert`, `cmovAnwenden_fremd`,
`cmov_witness_unterscheidet`, `cmov_speicher_zeuge`). Every reuse is a
real application of the accepted definition, not a copy: byte steps wrap
exactly the accepted evaluators plus the actual-length RIP advance, and
`cmovSchrittBytes_gleich` proves the byte step IS the accepted
`cmovSchritt` at the actual length. One inelegance, not a defect: the
equality carries the length in `⟨.movReg64 dst src, len⟩`; I read
`cmovSchritt` (`ControlFlow.lean:86-89`) and it consumes only
`d.laenge`, so the inert `.movReg64` payload is never read. Sound.

Byte-shape correctness (independent arithmetic, not just trusting
`decide`): `condCode .e = 4`, `.ne = 5` (`Codec.lean:35-39`) give
`0x94` = SETe, `0x95` = SETne, `0x44` = CMOVe; `pin_setCC_r9b`
(`41 0F 94 C1`: REX.B, ModRM mod=3 reg=0 rm=1+B=r9) and
`pin_cmov_r9_r15` (`4D 0F 44 CF`: REX.WRB, mod=3 reg=1=r9 rm=7=r15)
decode to the claimed registers. `mut_setCC_bedingung` (0x95 decodes to
observably `ne`) is a genuine mutation distinction, not a silent same.

Vacuity / weakening checks: every end-to-end theorem uses all premises
(decode via the length inversions `decodeSetCC_laenge`/
`decodeCmov_laenge`, step at `pfx.length - rest.length`); no conclusion
restates a premise; no contract parameters quantified away (no source
contracts involved); no `intro _`/discarded premises found; frame
theorems prove flags/memory/RIP/untouched registers per step, and both
steps provably never touch memory (source-free frame). No memory-CMOV
arm and no indirect-target arm exist in either decoder (mod=3 enforced,
`codeReg` over register indices only); `cmovMemSchritt` is referenced
only as reused background, never re-decided — no fault-speculation
claim. Dispatch reuses `Codec.decode` pilot-first with generic
pilot-refuses-ours theorems over any suffix (`pilot_refuses_setCC`,
`pilot_refuses_cmov`); the reverse direction is pinned on four
byte-overlapping pilot forms (`ours_refuses_movReg/push_r8/jumpIf/ret`)
plus the middle-stage `setCC_refuses_cmov`/`decodeSetCC_fremd_rex` —
routing is unambiguous, and the report/CUTS honestly label the full
14-form reverse generic as open. No guessed ISA beyond the two
Intel-manual opcode rows, which are checked as self-consistency (round
trips over all 256 SETcc / 4096 CMOVcc combinations, pins, refusals),
and CUTS explicitly disclaims hardware correspondence.

Witnesses: `cmovBytes_genommen_zeuge` and `setccBytes_endzuende_zeuge`
jointly instantiate concrete decode + step, pair the conclusion with a
real memory change (write64/read64 round trip with a proved byte-level
difference, values 20 and 1 respectively), and plant a truncation
refusal. No source-syntax premises exist here (no `Vertrag`/`Stmt`/…),
and the owner task names no `ZEUGE:` targets, so the mechanical
inhabitation rule does not trigger; the witnesses still meet the
task's joint non-degenerate standard at this layer (X86-state
execution, not source runs — correctly not claimed otherwise).

Hygiene: no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` in the
candidate (grep over the candidate file: zero hits); one scoped
`set_option maxHeartbeats 4000000 in` on `roundtrip_cmov`, same pattern
as the pilot round trips. CUTS block present and accurate; `#print
axioms` for all 56 theorems present in-file.

## Reproduction (queued wrappers, current master 6a26f772)

The candidate base (8596f83e) predates 10 newer X86 modules, so I
reproduced on current master: copied the candidate file into my clone,
appended the one import line, ran the checks, then removed both
(tree verified clean via empty `git status`).

- `./lean-probe grammatik/Grammatik/X86/ControlCodec.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- Axioms reprinted from the probe: every theorem within
  `propext, Classical.choice, Quot.sound`; `dispatch_pilot_bytes`
  uses all three (inherits pilot `roundtrip`), most use `propext`
  alone or nothing. Standard goal-axiom set, no excess.
- `./lean-bau`: `Build completed successfully (438 jobs).`
- Name-collision grep for the candidate's definitions
  (`decodeSetCC`, `decodeCmov`, `CondForm`, `Dispatched`,
  `encodeSetCC`, `encodeCmov`, step names) against all other X86
  modules: zero hits — merges without conflict (only the
  `Grammatik.lean` import union for the merger).

Last `./lean-bau` result line: `Build completed successfully (438 jobs).`

## What remains open (accepted as open, all labelled in CUTS)

No hardware correspondence; no generic ours-refuses-pilot theorem (four
pins only); no source/IR/checker/emitter/goal claim; no TSO/GX,
concurrency, cost or time claim. The bounded accepted claim is:
register-only SETcc/CMOVcc canonical bytes decode (generic round trips,
exact-4-byte consumption) and execute through exactly the accepted
evaluators with value + source-free frame, routed collision-free past
the pilot. That is a real producer/consumer connection, not decoration.

Nothing in the owner task looks wrong. One clarification the author had
to decide (new `CondForm` vocabulary + pilot-first `dispatch` instead
of new `Codec` rows, since the pilot `Befehl` has no conditional-select
constructor by design) is stated as interface, not as a pilot claim —
correct handling.

## Minimal repairs

None required.

VERDICT: ACCEPT
