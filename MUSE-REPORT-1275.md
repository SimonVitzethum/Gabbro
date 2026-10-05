# MUSE-REPORT-1275: ADC, SBB, INC, DEC

- Lane: 1275, clone `/home/simon/Dokumente/gabbro-muse/a1275`, branch `muse/1275`
- Candidate HEAD: `c9032ab1` ("TSO memory path, witness, CUTS")
- Owned files only: `grammatik/Grammatik/X86/IntCarryForms.lean` (2293 lines),
  `grammatik/Grammatik.lean` (one appended import line), this report.
- Date: 2026-10-05. Role: author (no reviewer verdict is mine to give).

## Status

The deliverable is COMPLETE at module level: `./lean-probe
grammatik/Grammatik/X86/IntCarryForms.lean` ends with
`== 0 error(s) in the COMPLETE output; exit 0`, and every `#print
axioms` in the file reports a subset of `[propext, Classical.choice,
Quot.sound]` (no `sorry`/`admit`/`axiom`/`native_decide` anywhere).

`./lean-bau` (full `grammatik/` build) is RED at the root `Grammatik`
target for an environmental reason proven independent of this lane:
with my import line temporarily commented out (master-state root),
the same target fails identically. Three consecutive runs failed on
three DIFFERENT missing files (`Lean/Linter/UnusedSimpArgs.ir`,
`Lean/Meta/Tactic/BVDecide/Normalize/IntToBitVec.olean.private` in
the toolchain dir, `OptCoalesceMove.olean` in this clone's `.lake`),
all at `Grammatik.lean:44:0`, while all 657/658 other targets
(including `IntCarryForms.lean`) build. Missing-file nondeterminism
plus a clean control run = broken/racing build cache or concurrent
toolchain interference, not this lane's source. Last `./lean-bau`
result line: `error: build failed`.

## What was built (all in `IntCarryForms.lean`, namespace `Gabbro.Grammatik.X86`)

Style follows the accepted models: value/step/codec shape from
`MulDiv.lean`/`MulDivCodec.lean`, flag classes from
`ArchitecturalFlags.lean`, machine connection from
`HwMulDivWidth.lean`. Reused unchanged, never redefined: `addB`,
`subB`, `trunc`, `mergeRegNarrow`, `add64`, `sub64`, `afAdd`,
`afSub`, `negB_b64` (ShiftLogic), `u128` (MulDiv), `rexByte`,
`modrmReg`, `codeReg`, `byteNat`, `natByte`, `parseLe32`,
`leBytes32` (Codec), `issueListe`, `issueByte`, `loadByte`,
`flushKern` + lemmas (TSO), `effAddr`, `regSet`, `ripNach`,
`laengeOk`, `dispLaenge` via `DispArt` (`AddressEncoding`; my first
version defined a second `dispLaenge`, caught by `lean-bau`, fixed by
reuse through `dispArtVonMod`), `decodeExt`, `stepExt`, `extLen`,
`HwMaschine`, `HwWf`, `projZustand`, `setKernVonFp`,
`setKernDaten_wf`, `setTso_wf`, `HwAdapter`, `HwRegAusgang`,
`decide` pins for refusals.

- §1 values/flags: `adcEingang`, `adcWert`, `adcTrag`, `adcUeberlauf`,
  `adcHilf`, `adcFlags`, `sbbWert`, `sbbEntleihn`, `sbbUeberlauf`,
  `sbbHilf`, `sbbFlags`, `incWert`, `decWert`, `incUeberlauf`,
  `decUeberlauf`, `incHilf`, `decHilf`, `incFlags`, `decFlags`;
  theorems `adcEingang_werte`, `adcEingang_true`,
  `adcEingang_false`, `trunc_b64_nat`, `adcWert_b64_ohne`,
  `adcTrag_b64_ohne`, `adcHilf_b64_ohne`, `adcUeberlauf_b64_ohne`,
  `adcFlags_b64_ohne` (ADC/CF=0 IS `add64`), `sbbWert_b64_ohne`,
  `sbbEntleihn_b64_ohne`, `sbbHilf_b64_ohne`,
  `sbbUeberlauf_b64_ohne`, `sbbFlags_b64_ohne` (SBB/CF=0 IS
  `sub64`), `incFlags_cf`, `decFlags_cf` (CF preserved, `rfl`),
  `adcWert_fits`, `sbbWert_fits`, `probe_adc_wert`,
  `probe_sbb_wert`, `probe_incdec_wert`.
- §2 register step: `CarryKlasse`, `CarryBefehl`, `CarryDecodiert`,
  `CarryErgebnis`, `carrySchreibe`, `carrySchritt`; equations
  `carry_adc_erfolg`, `carry_sbb_erfolg`, `carry_adcImm_erfolg`,
  `carry_sbbImm_erfolg`, `carry_inc_erfolg`, `carry_dec_erfolg`,
  `carry_laenge_misslungen`; `carrySchritt_speicher`,
  `carry_inc_schritt_cf`, `carry_dec_schritt_cf`,
  `carry_adc64_ohne_schritt`, `carry_sbb64_ohne_schritt`; bridges
  `eingang_wort_nat`, `adcWert_b64_nat`, `adcTrag_b64_nat`,
  `sbbWert_b64_nat`, `sbbEntleihn_b64_nat`; chains `adc_kette_128`
  (ADD then ADC = 128-bit sum, final CF = carry out),
  `sbb_kette_128` (SUB then SBB = 128-bit difference, final CF =
  borrow out), both over reused `u128`.
- §3 codec: `MemKlasse`, `CarryMem` (with `basis` full base code),
  `CarryInstr`, `carryBreite` + `carryBreite_rexW`/`_16`/`_32`,
  `hochbyteCode` + `probe_hochbyteCode`, `imm8Wert`, `imm16Wert`,
  `imm32Wert`, `imm8Sext`, `parseLe16`, `canonImm`,
  `decodeCarryReg`, `decodeCarryIndee`, `immLies`, `immLenOf`,
  `decodeGruppe1Reg`, `decodeGruppe1`, `decodeCarryModrm`,
  `decodeCarryIncDecModrm`, `decodeCarryOp`, `decodeCarry`
  (10/11/12/13, 14/15, 18/19/1A/1B, 1C/1D, 80/81/83 /2//3, FE/FF
  /0//1; widths via REX.W/66H; mod=11 register path else TSO
  memory descriptor; one REX or 66H(+REX) prefix); `AblehnGrund`,
  `istPraefixByte`, `dispArtVonMod`, `immKindVon`, `praefixOp`,
  `hochbyteGrund`, `ohneRexForm`, `ablehnGrundTief`,
  `ablehnGrund`; `rexByte0`, `carryPrefix`, `carryEncode`;
  round trips `roundtrip_adcReg64/32/16`, `roundtrip_sbbReg64/32/16`,
  `roundtrip_incReg64/32/16`, `roundtrip_decReg64/32/16`,
  `roundtrip_adcImm64/32/16`, `roundtrip_sbbImm64/32/16` (all
  `cases … <;> rfl`); 12 decode pins `pin_decode_*`, 21 refusal
  pins `pin_nichts_*` (incl. `pin_nichts_b8Asym`: 8-bit high-byte
  codes encode but never decode), 19 reason pins `pin_grund_*`
  (every refusal pairs with its constructor), 19 no-shadow pins
  `ext_weist_carry*_zurueck` (unified chain refuses every row).
- §4-5 machine: `CarryHwInstr`, `decodeCarryHw`,
  `decodeCarryHw_prefers_ext`, `decodeCarryHw_carry`,
  `decodeCarryHw_nichts`, `carryHwLen`, `pin_hw_pilot_ret`,
  `pin_hw_adcReg32`, `carryHwSchritt`, `carryHwSchritt_ext`,
  `carryHwSchritt_reg_ok`, `carryHwSchritt_reg_verweigert`,
  `carryHwSchritt_mem_verweigert`, `adapterCarry`,
  `adapterCarry_ok`, `adapterCarry_verweigert`,
  `adapterCarry_mem_none`, `adapterCarry_verweigert_bei_laenge`,
  `adapterCarry_wf`.
- §6 memory path: `breitenEintraege` (over the truncated word by
  construction), `carryMemAusgabe`, `carryMemAusgabe_puffer`,
  `carryMemAusgabe_kein_speicher`, `carryMemAusgabe_wf`,
  `disp8zu32`, `carryDisp32`, `carryMemAdr`,
  `carryMemAdr_verweigert_mod3`, `carryMemAdr_verweigert_sib`,
  `carryMemAdr_verweigert_ripRel`, `carryMemAdr_ok`.
- §7 witness `carryHw_zeuge`: core 0 ADC 17+5=22 no carry, core 1
  SBB 17-5=12 no borrow (`carryWit*`), family memory issue buffers
  one entry with memory still, owner-only forwarding, drain
  0→42 observed from both cores, `HwWf`, memory-plug/length/
  high-byte refusals beside it. Helpers `carryWitReg`,
  `carryWitKern`, `carryWitStart`, `carryWitStart_wf`,
  `carryWitOutAdd`, `carryWitOutSub`, `carryWitRegOut`,
  `carryWitCfOut`, `carryWit_add_rax`, `carryWit_add_cf`,
  `carryWit_sub_rax`, `carryWit_sub_cf`, `carryWitAdr`,
  `carryWitMem1`, `carryWitBufLen`, `carryWitMemByte`,
  `carryWit_mem_puffer`, `carryWit_mem_still`, `carryWitTso0`,
  `carryWitTso1`, `carryWitEigen`, `carryWitFremd`,
  `carryWitTso2`, `carryWitNachFlush`, `carryWitFremdNach`,
  `carryWit_anfang_null`, `carryWit_weiterleitung`,
  `carryWit_fremd_alt`, `carryWit_spuelung_aendert_speicher`,
  `carryWit_fremd_neu`.

## Provenance (SDM)

Opcode map, REX.W/66H width selection, high-byte rule, imm8/imm32
and disp8 sign extension, Group extensions, and the ADC/SBB
(all six flags) vs INC/DEC (CF preserved) rows follow Intel SDM
325462-093US as recorded in the repo extracts
(`.tmp/HARDWARE-REFERENCES/`) and `ArchitecturalFlags.lean`. No
new silicon facts introduced; every assumption is named in CUTS.
No hardware correspondence beyond self-consistency is claimed.

## Open (see CUTS in the file)

Full `lean-bau` green (blocked environmentally, evidence above);
no W/GX bridge; no LOCK/SIB/RIP-relative path; no REX-context
high-byte reason; no 8-bit generic encode round trip; no full
`ablehnGrund` classifier agreement.

## Task notes

- The task says the family has no model yet and asks for agreement
  with "the family's accepted evaluator": there was none to lift,
  so the 64-bit agreements target the canonical `add64`/`sub64`
  snapshots instead. Nothing in the task text itself proved wrong;
  the opcode list (incl. 12/13, 1A/1B and the 64-bit one-byte
  refusal) checks against the SDM map.
- Rule 13's table language does not apply (no Gabbro syntax in any
  premise); `carryHw_zeuge` joins all machine-level premises with a
  memory-changing run instead.
- Two toolchain facts for the coordinator: (1) multi-line record
  updates of the form used here do not parse in this repo's Lean —
  keep `{ s with … }` updates single-line; (2) `simp only` does not
  reduce `if True/False` — use full `simp` after `unfold` for
  if-chains, and `rw` cannot rewrite under `decide` (dependent
  instance) — `simp` + `congr 1` closes `decide R = decide R`.

Co-Authored-By: muse-agent-1275 <muse-agent-1275@noreply.invalid>
