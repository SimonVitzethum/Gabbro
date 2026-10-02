# MUSE-REPORT-660: Coherent multicore architectural execution

Clone: `/home/simon/Dokumente/gabbro-muse/a660`, branch `muse/660`.
Owned files only: `grammatik/Grammatik/X86/HardwareExecution.lean` (new, 902 lines),
`grammatik/Grammatik.lean` (one additive import line), this report.

## What was built

One coherent selected composition in `Gabbro.Grammatik.X86`:

- Data: `HwKern` (per-core register/flags/RIP/XMM/FP-context, NO memory),
  `HwMaschine` (ONE shared `Speicher`, per-core data, per-core TSO buffers,
  one `HwProfil`, per-core `BereitProfil`).
- Projections: `tsoAnsicht`, `projZustand`, `projFp` with proved agreement
  (`projZustand_speicher`, `projFp_speicher`, `kerne_ein_speicher`,
  `tsoAnsicht_speicher`, `tsoAnsicht_puffer`) — coherence proved, not assumed.
- Well-formedness: `HwWf` (admitted features have silicon), `hwWf_aus_zugelassen`
  from `merkmalZugelassen_heisst_beide`; updates `setKernDaten`/`setTso`/`setKernVonFp`
  preserve it (`setKernDaten_wf`, `setTso_wf`, `hwSchritt_wf`).
- Steps: `HwEreignis` (`regAusf`/`leseBeob`/`schreibAusgabe`/`spülung`/`verweigert`)
  and `HwSchritt` with cases `reg` (memory-unchanged gate `hmem`), `lade`
  (`loadByte`), `gibAus` (`issueByte`), `spüle` (`flushKern` + head evidence),
  `fehler` (fetch refusal). Correspondence: `hwGibAus_kein_speicher`
  (pointwise, via `issue_kein_speicher`), `hwWeiterleitung` (via `load_nach_issue`),
  `hwSpülung_schreibt` (via `flush_schreibt_kopf`).
- Embeddings: `hwLaufAlt_some`/`hwLaufAlt_none`, `hwPilot_weiter`,
  `hwPilot_verweigert`, `hwPilot_kein_halt`, `hwMuldiv_halt` — all from the
  accepted selection lemmas, no copied refinement premise.
- Word discipline: `issueListe` with `issueListe_haengt_an`/`issueListe_kein_speicher`
  (induction), `hwWortAusgabe` (eight byte issues, never SC `write64`) with
  `hwWortAusgabe_puffer`/`hwWortAusgabe_kein_speicher`; refusals
  `hwTeilwort_keine_gruppe`, `hwGruppe_verweigert_bei_fremdeintrag`,
  `hwGruppe_schliesst_lock_aus` (via `gruppe_verweigert_lock`); LOCK refused
  (`hwLockAnfrage` = none, `hwLock_verweigert`).
- Computable register step: `HwRegAusgang`, `hwByteschrittReg` (fetch from actual
  bytes + `stepExt` + re-embed), `hwByteschrittReg_rechtfertigt` (justifies
  `HwSchritt.reg` under the `hmem` gate), `hwByteschrittReg_verweigert`,
  `hwVec_ohne_os_verweigert` (via `stepVector_profil_verweigert`).
- Joint witness (§8–§10): `hwWitStart` (core 0 fetches narrow `mov32rr` + scalar
  `movsdRR` from actual executable memory; core 1 idles on non-executable memory),
  `hwWitO1`/`hwWitO2` observations (RIP 4096→4099→4103, rax 5→9, xmm0 low→7,
  memory still, buffers empty), TSO chain (`hwWitTso1`, `hwWitLoadEigen`=42,
  `hwWitLoadFremd`=0, `hwWitTso2`, `hwWitNachFlush`=42, `hwWitFremdNachFlush`=42),
  refusals (code load/issue none, core-1 verweigert, overlap/tearing no-group),
  `hwWit_zeuge` joining 11 closed facts. The drain changes ACTUAL shared memory
  0 → 42 (non-degenerate, memory-changing reached run).
- Adapters (§11): `HwAdapter`, `verweigertAdapter`/`verweigertAdapter_verweigert`,
  `adapterLocked662` (refused, `SperrBefehl`), `adapterInteger666` (register-path
  plug, `ExtInstr`), `adapterFp668` (register-path plug, `FpDecodiert`),
  `adapterFault670` (refused, `MulDivDecodiert` — halt is an outcome, not a state),
  `adapterInterrupt672` (refused `Unit` default; no accepted async vocabulary, no
  event type fixed). Sequential integration order 666→668→662→670→672 documented
  in the file.

## Checks

- `./lean-probe grammatik/Grammatik/X86/HardwareExecution.lean`: 0 errors.
- `./lean-bau` (full project): `Build completed successfully (460 jobs).`
- Axioms of new results: `propext` and `propext, Quot.sound` only (subset of the
  `gabbro_ziel` standard; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`).
- No premise of any theorem is unused; no conclusion restates a premise; no
  `Prop`-typed premise types; every `cases`/`match` is on accepted equations.

## Manual provenance (Intel SDM 325462-093US, local extracted text)

Checked, provenance only (no hardware correspondence claimed):
- `MOVSD—Move Scalar Double Precision Floating-Point Values` opcode table
  (extract offset 8893877; F2 0F 10/11 forms) — the scalar row the witness fetches.
  Not confused with the string `MOVSD` (offset 605407).
- `SETCC` Operation/Flags-Affected/`#GP(0)` block (offset 5917798) — control row.
- `DIV—Unsigned Divide` index row (offset 2201248) — divide-trap carrier.
- `LOCK—Assert LOCK# Signal Prefix` (offset 808380) — LOCK refused, not modelled.
- `Memory Ordering Instructions` TOC §10.4.6 (offset 102422) — TSO/fence scope
  marker; no silicon timing proved.
- Reference snapshot: `.tmp/HARDWARE-REFERENCES/REFERENCES.json`
  (sha256 `a4a62e6a…f321`, verified 2026-10-02). No AMD snapshot available.

## Coverage table (grounded in actual constructors)

| Family (constructor) | Composition | Witness/fetch pin |
|---|---|---|
| pilot `Befehl` (14 forms, `Codec`/`Ausfuehrung`) | generic via `ExtInstr.pilot` + `hwPilot_*` | fetch-refusal only (core 1); success pins inherited from lane 575 |
| narrow `NarrowOp`: mov32rr/movzx8/movsx8/store32 | generic via `.narrow` | `mov32rr` fetched+stepped (rax 5→9); other 3 rows NOT stepped here |
| muldiv `MulDiv…` | generic via `.muldiv`; halt carried (`hwMuldiv_halt`) | NOT stepped here (stops covered by embedding only) |
| shift `ShiftForm` | generic via `.shift` | NOT stepped here |
| SETcc/CMOVcc (`Bedingung`) | generic via `.setcc`/`.cmov` | NOT stepped here |
| scalar FP `FpBefehl` (15 forms) | generic via `.fp` | `movsdRR` fetched+stepped (xmm0 low→7); other 14 rows NOT stepped here |
| packed int `VectorOp`: pxorRR/paddqRR | generic via `.vec` | refusal only (`hwVec_ohne_os_verweigert`); no success step here |
| TSO byte issue/load/flush/fence-ready | `HwSchritt` + lifted lemmas | issue/forward/foreign/drain all observed; `zaunBereit` NOT wired to a step |
| word group `WortGruppe`/`FremdFrei` | guarded, never SC-substituted | structural + overlap + tearing refusals observed |
| LOCK `SperrBefehl` | explicitly refused | `hwLock_verweigert` on witness |
| faults/interrupts/timing | divide halt carried; rest refused/absent | fault = permission `none`s; no interrupt step |

Missing required rows (OPEN, not claimed): all narrow/shift/setcc/cmov/muldiv/FP/vector
success steps beyond the two witness forms; LOCK RMW path; fence-step wiring;
per-access TSO→W/GX simulation; source/IR/ABI/loader/entry/budget links;
interrupt/async steps; any timing claim. This skeleton does NOT complete the
hardware model — §11 lists the producer order that stays OPEN.

## Open / findings

- The `HwSchritt.reg` `hmem` gate is a proof obligation per form; only the two
  witness forms discharge it end-to-end (via accepted memory-silence lemmas).
  Producers 666/668 must discharge it per claimed row or route via issue events.
- `adapterInterrupt672` fixes no event type (none accepted exists); the 672
  producer must supply it — recorded as obstruction, not a silent assumption.
- Nothing in the lane task looked wrong; the "14 pilot forms are insufficient"
  priority is met by composing over the full `ExtInstr` chain (8 families) while
  honestly pinning only 2 new success rows plus refusals — the table above marks
  every unstepped row as missing rather than claiming it.
