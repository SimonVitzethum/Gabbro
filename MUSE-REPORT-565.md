# MUSE-REPORT-565: Scalar SSE2 bytes to accepted FP execution

Lane 565, clone `/home/simon/Dokumente/gabbro-muse/a565`, branch `muse/565`.
Owned files only: `grammatik/Grammatik/X86/ScalarFloatCodec.lean` (new, ~670 lines),
`grammatik/Grammatik.lean` (one additive import line), this report.

## Repair continuation (review 583 verdict REPAIR, applied)

Independent review (lane 583, MUSE-REPORT-583) accepted the bounded proof
claim but found an integration conflict: lane 597's merged
`VectorCodec.lean` defines `xmmCode` and `xmmCode_lt` in the same
namespace, so the umbrella build fails with a duplicate environment
entry. Applied the reviewer's recommended minimal repair: in
`ScalarFloatCodec.lean`, `def xmmCode` -> `def fpXmmCode` and
`theorem xmmCode_lt` -> `theorem fpXmmCode_lt`, with all 16 use sites
(encoders, round-trip premises and proofs, `#print` lines) updated
mechanically. No statement logic changed; the `< 8` low-operand
premises keep their exact meaning. The non-colliding
`codeXmmLow_xmmCode` kept its name. Re-verified: `./lean-probe` 0
errors, `./lean-bau` green (428 jobs, repeated), goal axioms unchanged,
all 40 axiom prints within the standard set. Correction to the first
report: the file proves 40 items with axiom prints, not 39.

## What was done

Connected the accepted `ScalarFloat` semantics (`FpBefehl` / `FpDecodiert` /
`fpSchritt`, lane 340) to a canonical scalar SSE2 DOUBLE byte subset: MOVSD
register/load/store plus one arithmetic register form (ADDSD). No existing
theorem was changed; nothing outside the three owned paths was touched.

- **§1 encoders** (`fpEncodeMovsdRR`, `fpEncodeAddsdRR`, `fpEncodeMovsdLade`,
  `fpEncodeMovsdSpeichere`): F2 prefix (242), 0F escape, opcodes 10/11/58,
  ModRM mod=11 (reg=destination convention of 0F 10/58) and mod=10 disp32 with
  the pilot SIB rule. Total over registers via the low three code bits.
- **§2 independent decoder** (`fpDecode`, `fpDecodeRest`): parses prefix,
  escape, opcode, ModRM and disp32 from the byte list and rebuilds register
  values plus consumed length (4 for register, 8/9 for memory forms). Its only
  input is `List Byte`; no caller-supplied `FpDecodiert` is ever accepted.
- **§3 round trips** (`fpRoundtrip_movsdRR`, `fpRoundtrip_addsdRR`,
  `fpRoundtrip_movsdLade`, `fpRoundtrip_movsdSpeichere`): decode inverts encode
  on low operands over any suffix; decoded length is the consumed prefix.
- **§4 refusals**: wrong prefix (`fpDecode_falschesPraefix`, F3),
  UCOMISD prefix (`fpDecode_sechsundsechzig_verweigert`, 66), REX prefix
  (`fpDecode_rex_verweigert`), three truncations
  (`fpDecode_abgeschnitten_praefix/opcode/modrm/disp`), non-canonical ModRM
  mod=1 (`fpDecode_modEins_verweigert`), non-canonical register store
  (`fpDecode_speichereRegister_verweigert`), memory ADDSD opcode outside the
  subset although modelled (`fpDecode_addsdSpeicher_verweigert`), and refused
  MXCSR (`fpCodec_profil_verweigert` from `fpSchritt_profil_verweigert`).
- **§5 fetch and byte step** (`fpGeholt`, `fpFetchDekodiert`,
  `FpByteAusgang`, `fpByteschritt`): fetch reads actual bytes at the core RIP
  from the state's own memory (executable prefix, cap 15, reusing `geholt`),
  checks length consistency, `laengeOk` and execute permission
  (`fpFetchDekodiert_erfolg` pins all three), then runs `fpSchritt`.
  `fpByteschritt` takes only the state. Refused MXCSR refuses the byte step
  (`fpByteschritt_profil_verweigert`).
- **§6 execution from fetched bytes, derived from `fpSchritt`** (nothing
  redefined): `fpByteschritt_schritt` (byte-step runs the accepted step),
  `fpByteschritt_addsdRR_rechnet` (model sum into the low half),
  `fpByteschritt_addsdRR_klasse` (class-level source-model agreement, no
  payload), `fpByteschritt_addsdRR_hoch` (upper half kept),
  `fpByteschritt_movsdRR_flags/fp/gpr` (pilot flags, control word and GPR
  file preserved).
- **§7 joint witness** (`fpCodecInstr`, `fpCodecSpeicher`, `fpCodecXmm`,
  `fpCodecKern`, `fpCodecT`, `fpCodecSpeicherNach`, `fpCodecT2`,
  `fpCodec_fetch`, `fpCodec_schreib`, `fpCodec_schritt`, `fpCodec_liest`,
  `fpCodec_aendert`, `fpCodec_bytes_zeuge`): the 8 canonical store bytes sit
  executable at RIP 4096 with `xmm0 = +inf`; the reached `fpByteschritt`
  stores `+inf` at `[rax] = 8192`, the word reads back, one memory byte
  observably changed, profile admitted throughout. `fpCodec_bytes_zeuge` is
  the jointly instantiated non-degenerate witness (reached memory-changing
  step; planted refusals sit beside it in §4).
- Shared-embedding explanation: the canonical pilot `Zustand` lives on as
  `FpZustand.kern`; pilot steps run via `laufAlt` (XMM/MXCSR untouched,
  proved in `ScalarFloat`); FP steps run via `fpSchritt` on the same state,
  and §6 pins the FP direction (moves keep GPRs/flags/control word).
  Recorded in the file CUTS block.

## Verification

- `./lean-probe grammatik/Grammatik/X86/ScalarFloatCodec.lean`: **0 errors**,
  repeatedly (10+ green runs).
- `./lean-bau`: **Build completed successfully (428 jobs)**, repeatedly.
- `#print axioms` for all 39 theorems: only `propext`, `Classical.choice`,
  `Quot.sound`, or none.
- Goal intact: `#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel` gives
  exactly `[propext, Classical.choice, Quot.sound]`.
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` in the new file.

## What remains open (also in the file CUTS)

REX prefix and high XMM/GPR reachability from bytes; byte forms for memory
arithmetic, UCOMISD, and conversions; TSO/GX consumption of the footprints;
validator-skeleton admission of the new forms; any source-level bridge beyond
the reused `fpRechne`/`gleitRechne` link. No hardware correspondence is
claimed: byte shapes are stated from the Intel SDM opcode map as an
implementation contract in the style of BYTE-PILOT.md.

Producer/consumer interface: producers are `fpDecode`, the four round trips,
`fpFetchDekodiert_erfolg`, and `fpByteschritt_schritt`; consumers are the
validator skeleton (admission of the four forms), the TSO bridge (per-access
footprints), and the source bridge (via `fpRechne_klasse`). Measurable next
integration: decode one more form (memory ADDSD or UCOMISD) through the same
fetch/execute/witness chain, or wire `fpFetchDekodiert` shapes into
`ValidatorSkeleton` admission.

## Task points I state plainly

- "Pin bytes from the repository selected profile/manual evidence": the
  repository (BYTE-PILOT.md and the pilot codec) contains no SSE byte
  evidence at all, so there was nothing to pin against. I stated the four
  shapes from the Intel SDM opcode map as an implementation contract,
  exactly how BYTE-PILOT.md states the integer pilot, and marked the
  non-correspondence in CUTS. No guessed architecture beyond that contract.
- Rule 13 does not literally apply: no theorem here quantifies over
  `Vertrag`/`Stmt`/`Endblock`/`ErgExpr`/`Expr`/`Args`, and the task names no
  `ZEUGE:` target. `fpCodec_bytes_zeuge` covers the intent (joint,
  non-degenerate, memory-changing, with refusals).
- `fpCodec_aendert` and the fetch-window facts are closed `decide`
  evaluations over kernel-computable definitions, not `native_decide`.

## Apparatus findings (for the coordinator, not the proof)

- `xs[i]'h` GetElem notation on a computed index hit elaborator
  `maximum recursion depth`; `List.getD` with an `if` guard elaborates and
  kernel-evaluates fine.
- A multi-line `{ base with field := ... }` structure update failed to parse
  ("unexpected identifier; expected '}'") where the identical one-line form
  parses; cause unknown, worth one controlled reproduction.
- `lean-probe`/`lean-bau` hit `failed to create thread` (exit 134) on roughly
  one third of runs during this lane, independent of file correctness; every
  such run was retried to a clean verdict, and the final build is green.
- Probe error locations occasionally attribute a failing tactic block to a
  nearby line; the goal state itself was always accurate.
