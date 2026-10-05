# MUSE-REPORT-1319: 8-bit operand forms across the new integer families

Lane 1319, clone `/home/simon/Dokumente/gabbro-muse/a1319`, branch `muse/1319`.
Owned files only: `grammatik/Grammatik/X86/IntByteForms.lean` (new),
`grammatik/Grammatik.lean` (one import line), this report.
No existing file was otherwise touched; no model was copied.

## What was built

NEW file `grammatik/Grammatik/X86/IntByteForms.lean` (~1000 lines),
connecting 8-bit operand forms across the rotate, ADC/SBB/INC/DEC and
XCHG families through ONE new register-selection function, reusing
every accepted definition unchanged (`codeReg`, `mergeRegNarrow`,
`rolB`/`rorB`/`rclB`/`rcrB`, `adcWert`/`sbbWert`/`incWert`/`decWert`
+ flag snapshots, `rotEncode`/`decodeRot`, `carryEncode`/`decodeCarry`,
`projZustand`/`setKernVonFp`/`hwWitStart`, TSO `issueByte`/`loadByte`/
`flushKern`).

### §1 Byte-register selection (NEW definition)

- `byteZielReg : Nat → Bool → Option Register` — full code + REX flag
  to register: 0-3 always AL/CL/DL/BL; 4-7 SPL/BPL/SIL/DIL with REX,
  refused without (AH/CH/DH/BH, outside the `Register` vocabulary);
  8-15 R8B-R15B only with REX; ≥16 refused.
- `byteZielReg_tief` (agreement with accepted `codeReg` on codes 0-3),
  `byteZielReg_rex_schalter`, `byteZielReg_hochbyte_verweigert`,
  `byteZielReg_erweitert`, `byteZielReg_ausserhalb`.

### §2 Merge discipline (accepted `mergeRegNarrow .b8`, never a second merge)

- `byteMerge_tief_hoch`, `byteMerge_nie_nullerweitert`,
  `byteMerge_kontrast_b32` (decide pins: low byte taken, upper kept,
  never zero-extended, unlike 32-bit).
- `byteZulaessig` + `byteZulaessig_antwort` / `byteZulaessig_verweigert`.

### §3 Family lifts (thin wrappers fixing `.b8`, agreements are `rfl`)

- `byteRol`/`byteRor`/`byteRcl`/`byteRcr` over `rolB`/`rorB`/`rclB`/`rcrB`;
  `byteAdc`/`byteSbb`/`byteInc`/`byteDec` over the carry evaluators;
  `byteXchgWert` (low-byte swap under the accepted merge) + pin.
  Each with a `..._agreement` theorem.

### §4 Rotate 8-bit through the accepted codec

- `byteRotRundgang8_eins`, `byteRotRundgang8_cl`: admitted forms
  round-trip via `rotRoundtrip_reg_eins`/`_cl` with the selector
  admission beside the bytes.
- `byteRot_ah_befund` (FINDING, see below).

### §5 Carry 8-bit rows

- `byteZulaessig_niedrig8` (no-REX admission = the four low registers).
- `byteCarryRundgang_adc8`/`_sbb8`/`_inc8`/`_dec8`: round trip on
  admitted codes through the accepted codec.
- `byteCarry_hochbyte_befund` (accepted `hochbyteCode` refusal agrees
  with the selector).

### §6 8-bit exchange (opcode 86H, register-direct)

- `byteXchgBrauchtRex`, `byteXchgRex` (bare 0x40, REX.W stays clear),
  `encodeByteXchg`, `decodeByteXchg` (parses bytes, optional REX).
- `byteXchgRundgang`: all 256 pairs round-trip by `rfl` over any suffix.
- `byteXchg_pin_niedrig`, `byteXchg_pin_rex40`,
  `byteXchg_hochbyte_verweigert`, `byteXchg_sonde_verweigert`.

### §7-8 Family step + equations

- `ByteFamOp`, `ByteFamEreignis` (op + REX + length), `byteOpZulaessig`,
  `byteFamSchritt` (length gate, admission gate, 7 arms over the
  accepted evaluators; XCHG merges crossed low bytes, flags untouched).
- `byteFam_rol_erfolg`/`_ror_`/`_adc_`/`_sbb_`/`_inc_`/`_dec_`/`_xchg_erfolg`,
  `byteFam_laenge_misslungen`, `byteFam_unzulaessig_misslungen`,
  `byteFamSchritt_speicher`, `byteFamSchritt_rip`.

### §9 Machine adapter

- `adapterByteFam : HwAdapter ByteFamEreignis` (accepted API shape).
- `adapterByteFam_wf` (HwWf preserved), `adapterByteFam_ok`,
  `adapterByteFam_proj`, `adapterByteFam_verweigert_bei_laenge`,
  `adapterByteFam_verweigert_ohne_zulassung`.

### §10 Joint witness + `_zeuge`

- `byteWitE0`/`byteWitE1` (INC AL / DEC CL), `byteWitM1`/`byteWitM2`
  through the adapter on `hwWitStart`, accessors, TSO issue/flush defs.
- Pins by `decide`: `byteWit_m1_rax` (AL 5→6), `byteWit_m1_rip`,
  `byteWit_m1_mem_still`, `byteWit_m2_rcx` (CL→0xFF),
  `byteWit_m1_tiefbyte`, `byteWit_weiterleitung` (owner forwards 6),
  `byteWit_fremd_alt` (core 1 reads 0), `byteWit_spuelung_aendert_speicher`.
- `byteFam_zeuge` joins all premises (HwWf, two-core family steps,
  memory stillness, owner-only forwarding, memory-changing drain).

## Check results

- `./lean-probe grammatik/Grammatik/X86/IntByteForms.lean`:
  `== 0 error(s) in the COMPLETE output`.
- `./lean-bau` (full project, with the new import):
  `Build completed successfully (688 jobs).`
- `#print axioms`: every main theorem depends only on
  `[propext]` or `[propext, Quot.sound]` — no `sorryAx`, no new axiom,
  no `Classical.choice` needed.
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` in the new file.

## Findings (recorded, not hidden)

1. **Accepted rotate-codec gap** (`byteRot_ah_befund`): the accepted
   rotate codec encodes 8-bit `.rsp` with NO REX and decodes it back to
   `.rsp`; on silicon those bytes mean AH, not SPL. The accepted files
   are untouched; the selector side stays refused here. The carry codec
   does NOT share the gap (its `hochbyteCode` refuses by name).
2. **8-bit XCHG has no accepted evaluator or codec** (accepted
   `xchgSchritt` swaps whole 64-bit words): value + 86H codec are new
   here, pinned and self-consistent, no hardware correspondence claimed.
3. **`IntSignXchg` is not in this tree**, so no 8-bit form of it is
   connected (task named it conditionally: "if merged").
4. The family plug is register-only by construction; 8-bit memory forms
   are TSO byte events (witness issues/drains through the accepted TSO
   equations). No bridge to W/GX is claimed.

## What remains open (see CUTS)

No hardware correspondence beyond self-consistency; no LOCK/RMW path;
no 8-bit memory forms at the plug; no SIB/addressed forms; no W/GX
bridge. The rotate AH rows need an owner for the accepted-file repair
(this lane only records the finding).

## Task remarks

- The MECHANISM paragraph asks for "at least two cores where the
  family touches memory": the family is register-only (memory refused
  at the plug, as in the accepted carry/rotate adapters), so two cores
  take family steps and the memory leg is the TSO issue/flush — the
  `_zeuge` joins all of it. A memory-touching family step would
  contradict the register-plug discipline; I state this plainly.
- Parser note for followers: in this toolchain a struct-update field
  value that is a nested application (`f (g x) ...`) fails to parse
  inside `match` arms (`unexpected token '('; expected '}'`); binding
  with `let` first and keeping all fields on one line works. A leftover
  scratch file `.tmp/scratch-parse.lean` documents the probes (untracked,
  unimported; `rm` is permission-blocked from this lane).

## Silicon references

Clone-local `.tmp/HARDWARE-REFERENCES/` (`intel-instruction-reference.txt`,
edition 093US): REX semantics incl. SPL-with-REX / AH-without, 86H XCHG
with flags unaffected. No AMD manual in the clone: no AMD provenance
claimed, undefined behaviour stays free (rule 17).
