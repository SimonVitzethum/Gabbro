# MUSE-REPORT-338: Reviewed organisation plan A4 — ControlFlow

Lane 338, 2026-10-01. Owns only `grammatik/Grammatik/X86/ControlFlow.lean`
(new, 500 lines), one additive import at the end of
`grammatik/Grammatik.lean`, and this report.

## What was done

Implemented plan row A4 as pure Lean extensions over the canonical pilot
vocabulary, reusing (never duplicating) the existing 14-form evaluator:

- `setCCWort` / `setCCByte` / `setLowByte` / `setCCAnwenden`: SETcc value
  (1 iff the condition holds over the flag snapshot) applied to the low
  byte of the destination, upper 56 bits preserved (`setLowByte_hoch`,
  `setLowByte_tief`), flags and memory untouched
  (`setCCAnwenden_flags`, `setCCAnwenden_speicher`).
- `cmovAnwenden` / `cmovSchritt`: register CMOVcc from pre-state source
  under the pre-state flag snapshot, flags and memory framed, RIP from
  decoded `Decodiert.laenge` only (`cmovSchritt_genommen`).
- `cmovMemSchritt`: faulting CMOVcc-memory reads FIRST through the
  permission-checked `read64`, then selects. `cmovMem_feheler_bleibt`
  proves the fault is kept on the untaken path (no speculation), with the
  untaken-path premise used in the conclusion; `cmovMemSchritt_flags`
  frames flags on success.
- `leaAnwenden` / `leaSchritt`: LEA writes the pre-state effective
  address (`effAddr` = pre-state base + sign-extended displacement), no
  memory touched, flags preserved, decoded-length step
  (`leaSchritt_erfolg`).
- `direktZiel rip len disp = ripNach rip len + dispWort disp`, i.e.
  `target = virtual_next_RIP + sign_extend(disp)`, with reuse equations
  for the existing steps: `direktZiel_jump32`, `direktZiel_jumpIf32_genommen`,
  `direktZiel_jumpIf32_nicht` (fall-through), `direktZiel_call32`.
- `direktZielOk starts eintraege rip len disp : Bool` (validator/profile
  admission, documented as NOT a hardware fault) with
  `direktZielOk_garantiert`: admitted targets are decoded instruction
  starts or listed entries.
- Witnesses: `cmov_witness_unterscheidet` (same state shape, `rax = 20`
  under `zf = true`, `rax = 10` under `zf = false` for condition `.e`)
  and the joint memory-changing `cmov_speicher_zeuge` (flag-selected word
  stored at 8192, reads back 20, byte observably changed from zero; built
  on `read64_nach_write64` / `writeBytesN_hit` / `addrOff_null` like the
  `Bild` witness, plus `wit_lesbar8` / `wit_schreibbar8`).
- Refusals proved concretely by `decide`: `ziel_mitte_verweigert` (4103
  between starts 4096/4101), `ziel_daten_verweigert` (8192 is data),
  `ziel_aussen_verweigert` (4201 off-image), plus the positive
  `ziel_anfang_akzeptiert` (disp 0 lands on 4101).
- Joint `_zeuge` companions, each instantiating all premises on concrete
  values together with the memory-changing run: `setCC_zeuge`,
  `cmovSchritt_genommen_zeuge`, `cmovMem_feheler_bleibt_zeuge`,
  `leaSchritt_erfolg_zeuge`, `direktZiel_jump32_zeuge`,
  `direktZielOk_garantiert_zeuge`.

## Verification

- `./lean-probe grammatik/Grammatik/X86/ControlFlow.lean`: 0 errors.
- `./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`,
  `Build completed successfully (386 jobs).`
- Axiom probe: `gabbro_ziel` still depends on exactly
  `[propext, Classical.choice, Quot.sound]`. All new theorems depend on
  subsets (mostly `[propext, Quot.sound]`, several on no axioms at all).
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; no `Prop`-typed
  premise; every premise is used (the unused-`hbed` warning was fixed by
  carrying the untaken-path fact into the conclusion); English only.

## What remains open (CUTS, also in the file)

No new instruction bytes/decoder rows/`Befehl` constructors (`Typen.lean`
untouched); no hardware correspondence (permission-checked
`read64`/`write64` outcomes, not silicon); no alignment admission imposed
(actual behaviour; profile alignment stays validator-side with a
certified scalar fallback, owned elsewhere); narrow-32 upper clearing not
modelled (only 8-bit preservation; lane A1 owns narrow widths); no
indirect-target certificates (jump tables, indirect branches, returns,
`entry fn` stay with image work); `starts`/`eintraege` are checked inputs
and their decoded-start producer is an OPEN consumer interface; no
source, TSO/GX, concurrency, gate/OS-contract, cost, time or termination
claim. Full final-byte/source/hardware correspondence stays OPEN.

## Notes on the task text

- The task's "length from decoding only" is met structurally: every step
  takes `Decodiert` and gates on `laengeOk d.laenge`; nothing takes an
  emitter length.
- One toolchain parser fact hit: struct-update values spanning a newline
  after a field comma are rejected (the same fact `Ausfuehrung.lean`
  works around); single-line updates used throughout.
- Nothing in the task was found to be wrong; the safety corrections were
  followed as documented above (admission Bool vs hardware fault, no
  alignment invented, pre-state evaluation, no stop renaming, no
  indirect-legality borrowing, no cost/time claims).
