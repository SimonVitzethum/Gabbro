# MUSE-REPORT-1273: Rotates ROL, ROR, RCL, RCR

Lane 1273, clone `/home/simon/Dokumente/gabbro-muse/a1273`, branch `muse/1273`.
Owned files: `grammatik/Grammatik/X86/IntRotate.lean` (new, ~2610 lines),
`grammatik/Grammatik.lean` (one import line appended), this report.
No other file touched.

## Status: complete, green, review repair applied

- Last `./lean-probe grammatik/Grammatik/X86/IntRotate.lean`: **0 errors**.
- Last `./lean-bau`: **Build completed successfully (659 jobs)**,
  including the new `import Grammatik.X86.IntRotate`.
- Independent exact review (lane 1274, candidate 77780bb9):
  VERDICT REPAIR with one finding R1 (REX.W precedence over 66h
  in `rotBreite`). Repaired: REX.W now takes precedence for wide
  forms (silicon direction), pinned by `pin_rot_rexw_ueber_66`
  (`[102, 72, 209, 192]` decodes 64-bit, length 4); the encoder
  never emits the combination, so no round trip or pin breaks.
  Re-probed green and re-built green after the repair.
- `#print axioms` for every new theorem: only `propext`, `Quot.sound`,
  or no axioms. No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`
  (the four `admit` substrings in the file are English words inside
  doc comments, which the merge gate strips before matching).
- Commits on `muse/1273`: 218bf592 (value core), dba5ac4c (iterated
  inverses + word level), f77a55bd (flags), 751c1e71 (codec),
  9dda16e7 (mem round trips), 64b15f22 (family step),
  bc3cd0f6 (dispatcher), 04a08a65 (adapter + outcome). This report
  and the final CUTS/axioms/import ride in the closing commit.

## What was built (exact names)

Value core (§0-§1): `RotOp`, `feldRotOp`, `rotOpFeld`,
`feldRotOp_rotOpFeld`, `rotMaske` (reused `schiebeZaehler`: 5 bits
below 64, 6 at 64), `rotEff` (masked mod width), `rclEff` (masked
mod width-plus-one), single-bit `rol1Nat`/`ror1Nat`/`rcl1Nat`/
`rcr1Nat` over Nat, iterated `rolNat`/`rorNat`/`rclNat`/`rcrNat`
(left ops peel innermost first, right ops outermost first, so each
inverse direction meets the single-step inverse exactly once),
word wrappers `rolB`/`rorB`/`rclB`/`rcrB`,
`rotMaske_periode_schmal`, `probe_rot_werte`.

Proofs (§2-§4): exact single-step shapes (`rol1Nat_char`,
`rcl1Nat_char`, `ror1Nat_char`, `rcr1Nat_char`), single-step
inverses both ways (`ror1Nat_rol1Nat`, `rol1Nat_ror1Nat`,
`rcr1Nat_rcl1Nat`, `rcl1Nat_rcr1Nat`) proved symbolically in
`bits` (no giant literals; `omega` cannot commute nonlinear
atoms or divide by atoms, so the proofs use explicit
`Nat.div_add_mod`/`mul_comm`/`add_mul_mod_self` chains),
`divTopBit_lt_two`, `modTwo_mul_pow_le`, range bounds
(`rol1Nat_lt`, `ror1Nat_lt`, `rcl1Nat_lt`, `rcr1Nat_lt`,
`rorNat_lt`, `rolNat_lt`, `rcrNat_lt`, `rclNat_lt`), iterated
inverses (`rorNat_rolNat`, `rolNat_rorNat`, `rcrNat_rclNat`,
`rclNat_rcrNat`), truncation bridges (`trunc_toNat_lt`,
`breite_pos`, `trunc_ofNat_lt`, `trunc_ofNat_toNat`,
`trunc_ofNat_toNat'`, `decide_div_eq_toNat`,
`split_roundtrip_nat`), word identities (`rolB_null`,
`rorB_null`, `rolB_breite_ident`, `rorB_breite_ident`,
`rclB_null`, `rcrB_null`) and word inverses (`rol_ror_inverse`,
`ror_rol_inverse`, `rcl_rcr_inverse`, `rcr_rcl_inverse`).

Flags (§5): `RotNachweis`, `rotNachweis`, `rotNachweis_wert`,
`rotNachweis_ueberlauf`, `rotLeer`, `RotGueltig`, `rotFlags`,
`rotFlags_null`, `rotFlags_gueltig`, `probe_rot_flags`. CF is
the last rotated-out bit (ROL result low bit, ROR sign bit,
RCL/RCR new carry); OF only at masked count 1 (ROL sign
change, ROR top-bit pair, RCL sign change, RCR original sign);
SF/ZF/AF/PF kept; zero effective count keeps every flag; the
executable snapshot keeps the incoming OF bit where undefined
(documented admissible member, not hardware truth).

Codec (§6-§7): `RotQuelle`, `RotOperand`, `RotForm`,
`RotDecodiert`, `RotPraefix`, `rotNimmRex`, `rotNimmPraefix`,
`rotBreite`, `rotModrm`, `rotGruppe`, `rotGruppeImm`,
`rotNachOpcode`, `decodeRot`, `rotOpcode`, `rotPraefixBytes`,
`rotImmTail`, `rotSibTail`, `rotEncode`, `rotLaenge`,
`rotEncode_laenge`, `rotPraefixBytes_len`, `rotImmTail_len`,
`rotSibTail_len`, `rotEncode_len_ok`, `rotLaenge_ok`,
generic register round trips (`rotRoundtrip_reg_eins`,
`rotRoundtrip_reg_cl`, `rotRoundtrip_reg_imm8/16/32/64`) and
memory round trips (`rotRoundtrip_mem_eins8/16/32/64`,
`_cl8/16/32/64`, `_imm8/16/32/64`, one theorem per width and
source: each command stays inside the heartbeat budget),
5 pinned SDM byte rows (`pin_rot_rol8_eins`,
`pin_rot_ror64_cl`, `pin_rot_rcl16_imm`, `pin_rot_rcr32_mem`,
`pin_rot_rol64_weit`) and 12 named refusals (`rot_nichts_lock`,
`_digit_vier`, `_modus_null`, `_modus_eins`,
`_sechzehn_bei_byte`, `_rex_w_bei_byte`, `_rex_r`, `_rex_x`,
`_unbekannt`, `_leer`, `_opcode_allein`, `_imm_kurz`).

Step (§8): `rotZaehler`, `RotErgebnis` (no halt arm),
`rotSchritt`, `rot_reg_erfolg`, `rot_leer_rip`,
`rot_mem_verweigert`, `rot_laenge_misslungen`,
`rot_laenge_falsch`, `rotSchritt_speicher`,
`rotMemNachweis`, `rotMemNachweis_reg_nichts`,
`rot_mem_erfolg`, `rotIssueKette`, `rotMemIssue`.

Dispatcher (§9): `RotHwInstr`, `decodeRotHw`, `rotHwLen`,
`decodeRotHw_prefers_ext`, `decodeRotHw_rot`,
`decodeRotHw_nichts`, five `ext_weist_rot*_zurueck` no-shadow
pins, `pin_rotHw_pilot_ret`, `pin_rotHw_rol8`,
`pin_rotHw_ror64`, `pin_rotHw_rcl16`, `pin_rotHw_rcr32`,
`pin_rotHw_ext_shift`, `rotHw_nichts_lock`.

Adapter + outcome (§10): `adapterRot`, `adapterRot_wf`,
`adapterRot_ok`, `adapterRot_proj`,
`adapterRot_verweigert_bei_laenge`,
`adapterRot_verweigert_bei_mem`, `rotHwRegSchritt`,
`rotHwRegSchritt_weiter`, `rotHwRegSchritt_verweigert`,
`rotHwRegSchritt_nie_halt`, `rotHwRegSchritt_weiter_wf`.

Witness (§11): `rotHwWitReg0/1`, `rotHwWitKern`,
`rotHwWitStart`, `rotHwWitStart_wf`, `rotHwOutRol/Ror`,
`rotHwRegOut/CfOut/OfOut`, value/flag pins
(`rotHw_rol_rax/cf/of`, `rotHw_ror_rbx/cf/of`),
`rotHwWitMemW`, `rotHw_mem_wert`,
`rotHwWitAdr0/1`, `rotHwWitTso0/1/1b/2`,
`rotHwWitEigen0/Fremd0/Eigen1/Fremd1/NachFlush/FremdNach`,
`rotHw_anfang_null`, `rotHw_weiterleitung0`,
`rotHw_fremd_alt0`, `rotHw_weiterleitung1`,
`rotHw_fremd_alt1`, `rotHw_spuelung_aendert_speicher`,
`rotHw_fremd_neu`, `rotHw_schlechte_laenge_verweigert`,
`rotHw_mem_adapter_verweigert`, and the joint
`rotHw_zeuge` (two family steps, memory-form value, two
owner-only forwarded family bytes, drain 0 -> 3, refusals).

## Provenance (SDM, per task)

Checked against the supplied Intel SDM extracts: group
opcodes D0/D1/D2/D3/C0/C1 with digits /0 ROL, /1 ROR, /2 RCL,
/3 RCR; count masking 5 bits (6 with REX.W); RCL/RCR count
modulo width-plus-one; CF = last bit rotated out; OF defined
only at count 1; SF/ZF/AF/PF unaffected; count 0 no flags;
8/16-bit merge with 32-bit zero-extension. The accepted
ShiftCodec layering (shared group opcodes, disjoint digits
/4 /5 /7 vs /0-/3, shift rows keep the unified arm) is reused
as the opcode-disjointness evidence. No silicon proof beyond
self-consistency is claimed (see CUTS).

## What remains open (see CUTS)

Hardware correspondence; canonical-subset refusals (mod 0/1,
ah/bh/ch/dh, 66h and REX.W on byte forms, REX.R/X, LOCK);
no source/IR/ABI/loader/entry/budget link; no per-access W/GX
simulation; no whole-word atomicity beyond byte drains;
multi-byte drain-to-`writeBreite` agreement open; no timing;
dispatcher/adapter-level connection only (not in
`decodeExt`/`stepExt`); no W/GX bridge.

## Task remarks

Nothing in the task is wrong. Two readings worth recording:
(1) "the 8/16-bit RCL/RCR count modulo (width+1)" is
implemented for all widths as masked-count mod (bits+1),
which coincides at 8/16 bits and is the natural general form.
(2) "OF defined ONLY for a masked count of 1" uses the
masked count (`rotMaske`), not the effective count; at
masked 1 the effective count is 1 at every width, so both
readings agree. Heartbeat note: one theorem per
width-and-source for round trips (each command has its own
200k budget); a single 256-goal `simp` command exhausts it.
`omega` cannot divide by atoms or commute nonlinear atoms;
the Nat proofs use explicit rewrite chains instead.
`a == b = true` does not parse; parenthesize the `==`.
