# MUSE-REPORT-1365: Decoder rows for the system and privileged instructions

## What was done

New file `grammatik/Grammatik/X86/SystemDecode.lean` (namespace
`Gabbro.Grammatik.X86`, ~710 lines), plus one import line appended to
`grammatik/Grammatik.lean`. Byte decode of what `HwSystemForms.lean`
models but the capstone chain cannot read (report 1339: IRET is a
decode gap, not a semantics gap).

Content:
- `SysExtra` (9 deferred rows: int3, int1, cld, std, rdtscp, xgetbv,
  rdmsr, wrmsr, rdpmc) and `SysDecodiert` (9 fixed modelled forms +
  `intN : Nat` + `extra`), with `sysFormOfRow` mapping every modelled
  row to its accepted `SysFormArt` (reused unchanged, never redefined)
  and extras to `none`.
- `sysDecode`: 21 byte shapes (HLT F4, CLI FA, STI FB, IRET CF, IRETQ
  48 CF, INT CD ib, PAUSE F3 90, CPUID 0F A2, RDTSC 0F 31, SYSCALL
  0F 05, SYSRET 0F 07, SYSRETQ 48 0F 07, plus the 9 deferred rows);
  truncated inputs refuse. Per-row pins (`sysDecode_*`, INT schematic
  over every vector byte).
- `sysEncode` with `sysRoundTrip` (decoding inverts encoding on every
  row up to the INT vector-byte wrap `sysNorm`) and `sysEncode_laengen`.
- `kapDecodeSys` over `kapDecode` (`SysKette.alt`/`sys`): exact
  agreement on every byte string the old chain decodes
  (`kapDecodeSys_alt`, schematic), refusal where both refuse
  (`kapDecodeSys_nichts`), old-chain refusal pinned per row
  (`kapDecode_nimmt_*_nicht`, 23 `decide`s — zero overlaps found),
  and one-taking of every new row (`kapSys_*`, incl. INT vectors 2/3).
- Lowering `sysEreignisOfRow` (INT vector from the instruction, inputs
  otherwise unchanged, extras to `none`) with per-row pins and the
  schematic `sysEreignis_extra`.
- `HwAdapter` plug `adapterSysDecode` in the style of `HwMulDivWidth`:
  exact agreement with the accepted `adapterSystem` on lowered events
  (`adapterSysDecode_ok`), refusal of every deferred row
  (`adapterSysDecode_extra`), and well-formedness preservation
  (`adapterSystem_wf`, `adapterSysDecode_wf` — only core data and
  memory move).
- Execution: `sysWit_hlt_halt0` (the HLT byte halts witness core 0),
  `sysEreignis_intN2_wit`, and the joint `sysDecode_zeuge` (21 chain
  pins + HLT halts + INT 2 lowers and reaches the handler on both
  cores + INT frame byte in memory + TSO drain 0-to-42 + freestanding
  SYSCALL #UD + CPL-3 HLT #GP; reuses `sysWit_int_rip`,
  `sysWit_int_frame_rip`, `sysWit_int1_rip`,
  `sysWit_spuelung_aendert_speicher`, `sysWit_ud_frei`,
  `sysWit_gp_hlt`).
- CUTS block and `#print axioms` for the 9 main theorems: all depend
  only on `[propext]` or `[propext, Quot.sound]` (subset of the
  standard trio). No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.

Last `./lean-bau` result line:
`== exit 0; 0 error line(s) in the COMPLETE output` /
`Build completed successfully (709 jobs).`
`./lean-probe` on the file: `== 0 error(s) in the COMPLETE output; exit 0`.
`python3 instrumente/lean-layout.py --check`: every folder at most 20
entries; all 851 Lean files placed.

## Names of new definitions/theorems

`SysExtra`, `SysDecodiert`, `sysFormOfRow`, `sysDecode`,
`sysDecode_hlt/cli/sti/iret/iretq/pause/cpuid/rdtsc/syscall/sysret/sysretq`,
`sysDecode_intN`, `sysDecode_int3/int1/cld/std/rdtscp/xgetbv/rdmsr/wrmsr/rdpmc`,
`sysDecode_leer`, `sysDecode_int/esc/rex_abgeschnitten`, `sysEncode`,
`sysNorm`, `sysRoundTrip`, `sysEncode_laengen`, `SysKette`,
`kapDecodeSys`, `kapDecodeSys_alt/nichts`,
`kapDecode_nimmt_*_nicht` (23), `kapSys_*` (22 incl. `kapSys_intN2/3`,
`kapSys_leer`), `sysEreignisOfRow`, `sysEreignis_hlt/cli/sti/pause/cpuid/rdtsc/iret/syscall/sysret`,
`sysEreignis_intN`, `sysEreignis_extra`, `adapterSysDecode`,
`adapterSysDecode_ok/extra/wf`, `adapterSystem_wf`,
`sysWit_hlt_halt0`, `sysEreignis_intN2_wit`, `sysDecode_zeuge`.

## What remains open

- Wiring into the built chain: add a `sys` arm for `sysDecode` in
  last position of `kapDecode` (`HwKapsteinDecoder.lean`, after the
  `avx2` arm). Deliberately NOT done here (existing files may not be
  edited by this lane); the `kapDecodeSys_*` theorems state the exact
  required behaviour for the maintainer.
- The 9 deferred rows need accepted evaluators (their own lanes);
  PREFETCHh/W need `AddressEncoding` + hint semantics; SYSENTER/SYSEXIT,
  CLTS, INVD/WBINVD, SMSW/LMSW, CR/DR moves are uncovered.
- `lean-layout --apply` (merge gate) moves this module to
  `Befehle/System/` per rule `^System\w+$` and rewrites the import.
- No W/GX bridge, no timing/serialisation claims (named assumptions
  of `HwSystemForms`).

## What I believe is wrong in the task

- The family list names WRMSR/RDMSR/0F 30/32 among modelled rows, but
  no accepted evaluator exists for them (`HwSystemForms` covers only
  10 forms; the 0F00 ledger marks them `verweigert`/`fehlt`). I decode
  them as explicit deferred refusals instead of inventing semantics
  (rule 16: reuse, don't duplicate; no silicon proof of a new model).
- CONTEXT (para 28) describes the generic adapter-lane mechanism; the
  ledger-style proof obligations (para 26: round trip, extended chain,
  agreement, refusals, witness) are what I implemented.
- Rule 13 (`_zeuge` for ∀-over-syntax premises) does not trigger: all
  theorems are closed byte equations plus one joint closed witness
  (`sysDecode_zeuge` joins all rows with the reached run); no theorem
  quantifies over program syntax and the task names no `ZEUGE:` target.

## Repair analysis after the failed integration gate (2026-10-06)

Gate evidence: `RuntimeError: goal axiom check failed`. The integration
lean build itself was green (`Build completed successfully (709 jobs)`)
and every `SystemDecode` axiom line is standard (`[propext]` or
`[propext, Quot.sound]`). The single error is infrastructural: the
gate's axiom-check step could not load
`Grammatik/Zielsatz/BeweisAtomar.olean` because that object file
`does not exist` in the gate's environment
(`/home/fisch/gabbro-lean-heute/...`).

Diagnosis: apparatus failure, not a module defect. A missing build
artifact on the integration host cannot be caused by this lane (a new
leaf module plus one import line; the gate's own build was green), and
nothing in the owned files can repair it. This matches the documented
stale-cache pitfall class (missing/incompatible `.lake` artifacts
produce errors about the apparatus, not the tree).

Local re-verification in this clone (unchanged tree since `6a67cc7f`):
- `./lean-probe grammatik/Grammatik/X86/SystemDecode.lean`:
  `== 0 error(s) ...; exit 0`, axioms standard (see above).
- `./lean-bau`: `== exit 0; 0 error line(s)` /
  `Build completed successfully (709 jobs)`.
- `grammatik/.lake/build/lib/lean/Grammatik/Zielsatz/BeweisAtomar.olean`
  exists here (full local builds produce it).
- `git status` shows only the three owned paths; `Zielsatz/` untouched,
  so `gabbro_ziel` and its axiom set are unaffected by this lane.
- (One `./lean-bau` attempt timed out with no output while the Lean
  slot was busy elsewhere; no slot lock remained and the retry passed.
  No duplicate builds were launched.)

Repair applied: none to the Lean sources (a code change against an
infra failure would be dishonest and could only risk guarantees).
What the gate needs: rebuild/refresh the build cache on the
integration host so the axiom check can load every module, then
re-run; a fresh independent review of the changed commit is still
required. No acceptance of the full source/binary chain is claimed
here.
