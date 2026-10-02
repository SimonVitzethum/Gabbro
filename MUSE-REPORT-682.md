# MUSE-REPORT-682: MXCSR control byte execution (LDMXCSR/STMXCSR)

## What was done

New module `grammatik/Grammatik/X86/FpControlHardwareForms.lean` (~1310 lines,
81 theorems, 0 `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`), plus the
additive umbrella import in `grammatik/Grammatik.lean`. Nothing else touched:
no change to `ScalarFloat`, entry profiles, or any source/checker/Spec file.

Exact selected legacy forms `NP 0F AE /2` (LDMXCSR m32) and `NP 0F AE /3`
(STMXCSR m32), decoded from fetched bytes and executed over the reused
canonical `FpZustand`/byte memory:

- Codec (§4): `0F AE` escape, ModRM mod 10 + disp32 with the pilot SIB rule,
  reg fields 2/3, optional `F0` LOCK prefix decoding to a locked form;
  generic round trips (`mxcsrRoundtrip_ld/st`), encoder lengths, LOCK pins,
  register-ModRM/wrong-field/wrong-opcode/truncation/lone-LOCK refusals.
- Checks (§§1-2): reserved bits 16-31 unconditional (`mxcsrReserviertFrei`);
  DAZ availability and writable-bit mask as PROFILE data
  (`MxcsrProfil`: modern `0xFFFF`/DAZ vs legacy `0xFFBF`/no-DAZ);
  feature/control gates (`MxcsrSteuerung`: SSE, CR0.EM/TS, CR4.OSFXSR).
- Step (§3): `mxcsrSchritt` with outcomes `weiter | fehlerGP | fehlerUD |
  verweigert`. LDMXCSR installs the full four-byte word via `read32`
  (never an 8-byte load); STMXCSR stores via `write32` with reserved bits
  zeroed (never an 8-byte store). Full equations + frames (flags, GPRs,
  XMM, memory, permissions, four-byte footprint).
- Fetch + byte step (§5) from actual executable memory (`geholt` reuse)
  with length/permission admission; adapter boundary (§6) for lanes
  660/670/672/674: input `(FpZustand, MxcsrProfil, MxcsrSteuerung)` via
  `mxcsrByteschritt`, output `MxcsrAusgang` with `mxcsrKind` and the
  `mxcsrSpeicherNach/mxcsrWortNach/mxcsrRipNach` observation accessors.
- Witness fragment (§7): `LDMXCSR [rax]` then `STMXCSR [rax+4]` from real
  code bytes; load installs `0x1FBF` (control change), store writes it at
  `0x2004` (memory change + read-back), neighbor/code bytes and control
  across the store preserved, past-image refusal.
- Negatives (§8, each one varied leg): reserved-bit #GP, LOCK #UD, gate
  #UD (OS gate and silicon), DAZ-without-support #GP, missing 4th-byte
  permission store/load refusals; positives: FTZ word loads fine but stays
  source-inadmissible (`mxcsrPos_ftz_weiter_aber_unzulässig`), reset-word
  load establishes admission. Joint non-degenerate witness
  `mxcsr_gelenk_zeuge`.

## Provenance checked

Intel SDM 325462-093US (Sept 2026), local `.tmp/HARDWARE-REFERENCES/`
(sha256-verified): LDMXCSR `NP 0F AE /2`, `MXCSR := m32`, reset `1F80H`,
`#GP for reserved bits` (Vol. 2A 3-538/3-539); STMXCSR `NP 0F AE /3`,
`m32 := MXCSR`, reserved stored as `0s` (Vol. 2B 4-676); MXCSR layout
bits 0-5/6/7-12/13-14/15/16-31 with `#GP` on nonzero reserved write and
DAZ-without-support `#GP` (Vol. 1 §10.2.3 Fig. 10-3, §§10.2.3.4/11.6.6).
AMD retrieval failed upstream; no AMD provenance claimed. Missing
composition listed in CUTS: no VEX/REX/mod-0-1 forms, no FXSAVE/FXRSTOR,
partial MXCSR save is not full XMM/YMM context preservation (672/674/660).

## Verification

- `./lean-probe grammatik/Grammatik/X86/FpControlHardwareForms.lean`:
  `== 0 error(s) ..., exit 0`.
- `./lean-bau`: `Build completed successfully (463 jobs)`.
- `#print axioms` for every main theorem: only `propext`,
  `Classical.choice`, `Quot.sound` (subset of the `gabbro_ziel` set).
- Every premise of every theorem is used; no Prop-typed premises; no
  existing theorem weakened; struct literals kept single-line per the
  toolchain rule.

## Open / for consumers

- Lanes 660/670/672/674 own integration on their side of the §6 adapter.
- Model merges silicon #UD (EM/OSFXSR) vs #NM (TS) as one `fehlerUD`
  (CUTS). MXCSR_MASK instance values are example profile data; silicon
  values come from FXSAVE on the target. No TSO/tearing, timing, cost,
  or source-lowering claim (CUTS).
- Belief note: the task text arrived truncated at rule 13/adapter detail;
  the module follows the visible requirements (exact forms, four-byte
  effects, reserved/profile checks, fault precision, witnesses, adapter
  exports, English, gates green). If a hidden ZEUGE target name was
  required beyond `mxcsr_gelenk_zeuge`, it could not be seen.
