# MUSE-REPORT-564: Shift operations byte decoder and execution connection

## What was done

New file `grammatik/Grammatik/X86/ShiftCodec.lean` (~720 lines) plus one
additive umbrella import in `grammatik/Grammatik.lean`. It connects the
accepted `ShiftLogic` value operations (`shlB`/`shrB`/`sarB` at `.b64`,
`SchiebeNachweis`/`SchiebeGueltig`) to a bounded canonical byte
decoder/encoder for two 64-bit register-direct forms:

- shift-by-immediate-8 (`REX.W C1 /r ib`, opcode byte 193), length 4;
- shift-by-CL (`REX.W D3 /r`, opcode byte 211), length 3.

Only REX.W rows with R = 0 (72/73) are admitted; REX.R rows (76/77)
would rewrite the Group-2 extension digit and are refused. Only
register-direct ModRM (mod = 3) with digits /4 (SHL), /5 (SHR), /7
(SAR) is admitted. Only these admitted rows count as connected.

## New definitions

`ShiftRichtung` (shl/shr/sar), `richtungFeld`, `ShiftForm`
(imm/cl), `encodeShift`, `shiftLaenge`, `feldRichtung`,
`decodeShiftModrm`, `decodeShiftOp`, `decodeShift`, `richtungOp`,
`richtungWert`, `shiftZaehler`, `richtungNachweis`, `shiftNachweis`,
`shiftFlags`, `shiftDst`, `ShiftDecodiert`, `shiftSchritt`,
witness state `shiftKetteProg/Bytes/Exec/Daten/Reg`,
`shiftZeugenFlags`, `shiftKetteStart`, `shiftKetteEnde`.

## New theorems

- Routing/reuse: `richtungWert_routen` (against `shiftOpWert`),
  `feldRichtung_richtungFeld`, `shiftFlags_gueltig` (snapshot satisfies
  `SchiebeGueltig`; overflow pinned exactly at masked count one).
- Codec: `encodeShift_laenge`, `encodeShift_len_ok`, `shiftLaenge_ok`,
  `roundtripShiftImm` (needs `n < 256`, discharged by the byte round
  trip), `roundtripShiftCl`, `roundtripShiftImm_len_ok`,
  `roundtripShiftCl_len_ok` (decoded length + suffix consistency).
- Dispatch (neither decoder rewritten): `pilot_verweigert_shift`
  (generic over `ShiftForm` + suffix), `shift_verweigert_pilot`
  (generic over all 14 pilot `Befehl` constructors + suffix).
- Step: `shiftSchritt_laenge` (refusal), `shiftSchritt_laenge_eq`,
  `shiftSchritt_null` (zero masked count: RIP advances, flags/registers
  untouched, no snapshot installed), `shiftSchritt_weiter`,
  `shiftSchritt_speicher`, `shiftSchritt_rip`, `shiftSchritt_fremd`,
  `shiftSchritt_flags`, `shiftSchritt_null_flags`,
  `shiftSchritt_wert`, `shiftSchritt_nachweis_gueltig`.
- Probes: `pin_shift_imm_rax[_dekode]`, `pin_shift_imm_r9[_dekode]`,
  `pin_shift_cl_rcx[_dekode]`, `probe_zaehler_null/eins`,
  `probe_gross_ueber_byte` (imm 65 masks to 1 through bytes),
  `probe_schiebe_werte`, `sonde_abgeschnitten` (5 truncations),
  `sonde_mutation` (REX.R, /0 digit, mod-2 refuse; opcode flip
  imm->CL with length change; digit flip SHL->SHR),
  `probe_laenge_falsch`.
- Joint witness: `shift_kette_dekode`, `shift_kette_schritt`
  (rax 1->2, rip +4, CF false), `shift_kette_speicher` (decoded shift
  chained into the existing pilot `store64` step: data cell reads 2,
  byte observably changed from zero, plus a length-mismatch refusal).

## Verification

- `./lean-probe grammatik/Grammatik/X86/ShiftCodec.lean`: 0 errors.
- `./lean-bau`: `Build completed successfully (428 jobs).`
- `./lean-probe grammatik/Grammatik/Zielsatz/BeweisAtomar.lean`:
  `gabbro_ziel` and all siblings depend only on
  `[propext, Classical.choice, Quot.sound]` (unchanged).
- All `#print axioms` in the new file: `[propext]`,
  `[propext, Quot.sound]`, or no axioms. No `sorry`/`admit`/`axiom`/
  `native_decide`/`unsafe` anywhere in the new file.

## What remains open (CUTS in file)

No hardware correspondence (rows are self-consistent canonical bytes,
not verified against silicon); no source correspondence, TSO bridge,
whole-image coverage, cost transfer, or entry/ABI/relocation claim;
narrow widths, memory-operand shifts and rotates stay open.

## Notes on the task

- Nothing in the task text looks wrong. Two findings worth recording:
  (1) `decodeShiftOp` first checked the ModRM byte before the opcode,
  which made refusal of REX-prefixed pilot rows depend on operand
  bytes; restructured to check the opcode first (behaviour-identical,
  refusal set unchanged). (2) `decodeShift` matches one byte at a time
  so one-byte pilot rows refuse without touching the suffix (needed for
  the generic `shift_verweigert_pilot` with a variable suffix).
- Rule-13 note: no theorem here quantifies over source syntax
  (`Vertrag`/`Stmt`/`Endblock`/`ErgExpr`/`Expr`/`Args`) and the task
  names no `ZEUGE:` target; the joint witness
  (`shift_kette_dekode/schritt/speicher`) instantiates form, bytes and
  state concretely with a real two-step memory-changing execution plus
  planted refusals, covering the intent.
- Producer/consumer interface: producers (`encodeShift`,
  `roundtripShift*`, `pilot_verweigert_shift`) offer canonical rows;
  consumers (`decodeShift`, `shiftSchritt`, `shift_verweigert_pilot`,
  `shiftSchritt_nachweis_gueltig`) take only actual bytes/state.
  Measurable next integration: feed `fetchDekodiert`-style executable
  fetch into `decodeShift`/`shiftSchritt` (needs a consumer that
  dispatches REX-C1/D3 rows to this decoder while keeping the pilot
  refusal theorems as the dispatch contract).
