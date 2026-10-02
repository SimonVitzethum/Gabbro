# MUSE-REPORT-667: Exact review of author 666 (integer width and compact encoding rows)

CANDIDATE: 666 e0b372cbc0af00adf8001cf96dddeee5a890a3f6
VERDICT: ACCEPT

Acceptance is bounded; details and exact OPEN scope below.

## What was reviewed

- Pinned snapshot: `.tmp/review/SNAPSHOT.json` (author 666, base `1d08711`, `clean: true`).
- Exact files: `MUSE-REPORT-666.md`, `grammatik/Grammatik.lean` (one additive import line), `grammatik/Grammatik/X86/IntegerHardwareForms.lean` (1544 lines).
- Exact task: `.tmp/review/author-666/OWNER-TASK.md` (lane 666 credit line) and the full `PATCH.diff` (1643 lines).
- Build provenance: `.tmp/review/author-666/BUILD-EVIDENCE.json` (incremental `lean-probe` trace with real intermediate errors fixed, final probe 0 errors, `lean-bau` exit 0, 460 jobs).
- Reference checked: clone-local `.tmp/HARDWARE-REFERENCES/` — `REFERENCES.json` (Intel SDM combined vols 1-4, edition 325462-093US Sept 2026, sha256 `a4a62e...`) plus the extracted `intel-instruction-reference.txt`. AMD snapshot unavailable (404); no AMD claim is made anywhere.

## Architecture verification (independent, against the manual)

- Opcodes/digits/direction, all confirmed in the extracted Intel text: AND `21 /r` MR (Vol. 2A 3-59 table), OR `09 /r` MR (Vol. 2B 4-162 table), TEST `85 /r` MR (4-721/722), NOT `F7 /2` / NEG `F7 /3` (4-159/4-162), group-1 immediates ADD `/0`, OR `/1`, AND `/4`, SUB `/5`, XOR `/6`, CMP `/7` with `81` wide / `83` compact (ADD 3-14, AND 3-59, OR 4-164, SUB 4-686, CMP 3-162, XOR 6-41 rows). Digit `/2` (ADC) and `/3` (SBB) explicitly refuse — safe direction, recorded.
- Register/implicit operands: ModRM `reg=src, r/m=dst` for the MR rows verified against the operand-encoding rows; `encodeIntHw`/`decodeIntHwModrm` agree (hand-checked pins: AND rax,rcx = `48 21 C8`; TEST rax,rax = `48 85 C0`; NEG r9 = `49 F7 D9`; `add rax,1` = `48 83 C0 01`; `add rax,256` = `48 81 C0 00 01 00 00`; `cmp rax,-1` = `48 83 F8 FF`; `and eax,1` = `40 83 E0 01`). AND value pin `12 & 10 = 8` rechecked by hand.
- Flag semantics: AND/OR/TEST reuse `logikFlags` (OF/CF cleared, SF/ZF/PF from result, AF `none`); manual states "The state of the AF flag is undefined" for all three (AND 3-60, OR 4-163, TEST 4-721) — the `inthw_logik_af_none` observation abstraction (AF is `none`, never read as false) is the sound treatment, and no consumer reads AF (branch adapters read only ZF via `inthw_test_zf`/`inthw_cmp_e` and signed-less via `inthw_cmp_l`). NOT preserves flags exactly (manual: no flags affected). NEG/ADD/SUB use the defined snapshots (`negWf`/`add64`/`sub64` with `stepImm_add_af` producing `some (afAdd ...)`), satisfying the task's "abstraction or defined production" requirement per row.
- Width discipline: 32-bit zero-upper derived generically from accepted `mergeRegNarrow_b32_fits`; 64-bit full word; 8/16-bit value semantics proved with codec rows honestly empty (OPEN, refused — safe direction). No 16-bit immediate rows, no `66` prefix admission, no high-byte registers: all refuse.
- REX discipline: only `48/49/4C/4D` (b64) and `40/41/44/45` (b32) admitted; REX.X variants, REX.R-over-group-digit (`f7ok=false`), missing REX, and `mod != 3` all refuse. REX.X refusal on mod=3 register rows is incompleteness (hardware ignores X without SIB), never unsound.
- Sign extension: immediates are one int32 with architectural sign extension (`immWort` via `sext .b32`); encoder picks imm8 (`0x83`, 4 bytes) exactly iff `immPasst8` (`kompakt_add_feuert` is an iff); manual confirms "sign-extended" for every `83` and REX.W `81` row checked.
- Pre-fault/memory/TSO: register and register-immediate rows touch no memory — proved by `stepIntHw_speicher` and `stepImm_speicher`; fetch paths mirror `fetchDekodiert` (decode actual `geholt` window, length-consistency equation, `laengeOk`, `ausfuehrbarN` admission) with `fetchIntHw_erfolg`/`fetchIntHwImm_erfolg`. No memory operands, no LOCK claim, no MXCSR/feature/interrupt gates needed for these base-ISA forms. No TSO/GX bridge is claimed (CUTS says sequential single-`Speicher` facts only).
- Canonical reuse: no new word/register/state types, no `Befehl` change, no duplicated arithmetic evaluator — all values route to accepted `andB`/`orB`/`notB`/`negW`/`and64`/`or64`/`add64`/`sub64` producers. No ExtendedExecution575 edit (correct: outside OWN); `decode_exec_*` selection theorems plus memory-freedom and branch adapters are the wired producer interface for lanes 660/664/branch-validator, as the task's "export adapters" clause requires.
- No integer-to-pointer conversion anywhere; `hardwareHalt`/divide-trap untouched (no DIV row claimed).

## Lean hygiene and claim boundaries

- No `sorry`/`admit` (tactic)/`axiom`/`native_decide`/`unsafe`: the only grep hits are English "admits"/"admit" inside comments. `lean-probe` 0 errors, `sorryAx` count 0, axioms per evidence are `[propext]`, `[propext, Quot.sound]`, or the standard triple only.
- Every major premise is used (spot-checked `stepIntHw_*`, `stepImm_*`, length/width guards); no conclusion restates a premise; no contract quantification (no `Vertrag`/`Stmt` premises at all — hardware rows over `Zustand`, so rule 13's program-syntax inhabitation does not trigger; the joint witness `inthw_zeuge` follows the X86-lane joint-witness practice).
- Witness is non-degenerate and joint: decoded AND bytes step `12 -> 8`, fetched-byte stepper agrees from actual memory, pilot `store64` carries 8 into the data cell with an observable byte change (`read64 = some 8`, byte `0 -> 8`, wrong-length same-row refusal pinned), plus NEG `sMin` overflow, compact (4B) vs wide (7B) choice, and truncated/wrong-opcode/MulDiv-digit/REX.X/no-REX/ADC-digit/32-bit-arithmetic refusals — jointly instantiated in one theorem.
- CUTS block is precise and matches the file: no hardware correspondence claimed (canonical-subset self-consistency only), missing manual provenance honestly recorded (bundle was absent from the author clone; this review closed the opcode/flag/sign-extension facts against edition 093 above), and the OPEN list (b8/b16 codec, 32-bit ADD/SUB/CMP, ADC/SBB, memory-operand forms, INC/DEC, full immediate length-soundness, source/TSO/ABI/entry/cost) is exact.

## Bounded acceptance (not silently reduced, not REPAIR)

1. Wide-immediate strict-length check (`d.laenge != immDecLaenge d.op -> none`) refuses hardware-legal non-compact wide encodings of small values. Refusal is the sound direction; coverage is narrower than silicon. Recorded as part of the OPEN immediate-length item.
2. Permission gate is proved in the success direction (`fetch*_erfolg` requires `ausfuehrbarN`); a `decide` pin for the no-execute refusal direction is absent. Gate exists and mirrors `fetchDekodiert`; suggested follow-up pin, not a soundness defect.
3. Full immediate encode/decode round trip is pinned only by instances, not a general theorem. Same category as (1): incompleteness, honestly recorded.

No guarantee is weakened, no desired simulation is assumed, no undefined state is given invented determinism, and no defined effect is zeroed or ignored. The `Grammatik.lean` diff is the single additive import; `gabbro_ziel` cone files are untouched.

## Task feedback

The lane-666 file is truncated mid-sentence in rule 14's tail ("every..."), same as the author's report notes; the witness obligation was still met via the joint-witness pattern. The hardware-reference bundle should be staged into author clones (it was present only in reviewer clones); this review supplied the missing provenance check instead of blocking on it.
