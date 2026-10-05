# MUSE-REPORT-1205: Loaded image per-family reached fetch instances

Lane 1205, follow-up of lane 1179 (`HwBildFamilien.lean`).
Branch `muse/1205` in clone `/home/simon/Dokumente/gabbro-muse/a1205`.
Own files only: `grammatik/Grammatik/X86/HwBildInstanzen.lean`,
`grammatik/Grammatik.lean` (one import line), this report.

## What was done

New file `grammatik/Grammatik/X86/HwBildInstanzen.lean` (~1640 lines):
six small loaded images (muldiv 3 bytes, shift/setcc/cmov/fp 4 bytes,
vec 5 bytes; execute-only code section, readable/writable 8-byte data
section, profile-48 acceptance by `decide`) on `hwBildStart`-style
two-core machines (core 0 fetches at the code base `0x101000`, core 1
idles on the data page `0x102000`, empty TSO buffers, `basisHw` /
`basisBereit`). Every accepted definition is reused unchanged; nothing
is redefined. Pinned rows are exactly lane 1179's rows.

Per family F in {muldiv, shift, setcc, cmov, fp, vec} (prestates:
muldiv rax=6/rcx=7; shift rax=21; setcc rax=10 with ZF set; cmov
rax=5/rcx=9 with ZF set; fp xmm1.low=7; vec xmm0=all-ones,
xmm1.low=7):

- image defs: `instDatei_F`, `instCode_F`, `instDaten_F`, `instBild_F`,
  `instReg_F` (integer families) / `instXmm_F` (fp, vec),
  `instKern_F`, `instStart_F`; shared `instAdr` (`0x102000`);
- `inst_wohlgeformt_F`: `wohlgeformt .p48 instBild_F = true` (`decide`);
- `instStart_wf_F`: `HwWf instStart_F` (via `hwWf_aus_zugelassen`);
- `inst_fetch_F`: concrete `fetchExt` success with `rest = []`
  (`decide`);
- `inst_rip_F`, `inst_wert_F`: RIP advance and value observers
  (`decide`): MUL rax=42/rdx=0; SHL rax=42; SETcc rax=1 (taken);
  CMOV rax=9 (taken); MOVSD xmm0.low=7; PXOR low lane
  `0xFFFFFFFFFFFFFFF8`;
- `inst_mem_still_F`, `inst_puffer_leer_F`: register-path memory and
  buffer silence (`decide`);
- `instT_F` / `instKernNach_F` (shift, setcc, cmov factored): explicit
  successors built only from accepted apply-functions;
- `inst_schritt_F`: exact agreement via `stepExt_muldiv_ok` +
  `md_mul_erfolg`, `stepExt_shift` + `shiftSchritt_weiter`,
  `stepExt_setcc`/`stepExt_cmov` + byte-step applications,
  `stepExt_fp` + `fpSchritt_movsdRR`, `stepExt_vec` +
  `stepVector_pxor`;
- `inst_mem_F` (`rfl`) and `inst_reg_F`: the `HwSchritt.reg`
  embedding with the memory-unchanged gate;
- TSO stage (`instTso1_F`, `instLoadEigen_F`, `instLoadFremd_F`,
  `instTso2_F`, `instNachFlush_F`, `instFremdNachFlush_F` defs):
  `inst_anfang_null_F`, `inst_weiterleitung_F` (owner reads 42),
  `inst_fremd_alt_F` (core 1 reads 0),
  `inst_spuelung_aendert_speicher_F` (drain installs 42 in ACTUAL
  shared memory), `inst_fremd_neu_F` (core 1 reads 42) — all `decide`;
- `inst_kern1_verweigert_F` (core 1 on non-executable data, via
  `hwBild_ohne_exec_verweigert`) and the dark mapping
  (`instBildDunkel_F`, `instDunkel_F`, `inst_dunkel_fetch_F` is
  `fetchExt = none` by `decide`, `inst_dunkel_verweigert_F` via
  `hwByteschrittReg_verweigert`);
- `instZeugeProp_F` (the witness proposition as a `Prop` def) and
  `inst_zeuge_F` (12-way conjunction).

Closing: `adapterInstanzen` (`:= adapterInteger666`) with
`adapterInstanzen_vereinbarung`, `adapterInstanzen_verweigert`,
`adapterInstanzen_halt_verweigert` (mirroring `adapterBild_*`);
`instSchritt_wf` (lifts `hwSchritt_wf`); `instAlle_zeuge` (six-way
conjunction of the per-family witnesses). CUTS block and `#print
axioms` for all 23 main theorems.

Axioms: `inst_fetch_*` depend on `[propext]` only; all others on
`[propext, Quot.sound]` — within the standard set, no
`Classical.choice` needed. No `sorry`/`admit`/`axiom`/
`native_decide`/`unsafe` anywhere in the file.

## Verification

- `./lean-probe grammatik/Grammatik/X86/HwBildInstanzen.lean`:
  `== 0 error(s) in the COMPLETE output` (final state).
- `./lean-bau`: `Build completed successfully (627 jobs).`
  (includes the new module through the appended import).

## What remains open (not claimed)

As listed in the file's CUTS block: no hardware correspondence
(self-consistency only); the six pinned rows are register-only, so
each witness's memory change comes from the TSO issue/drain stage
(the family's own store forms, e.g. `movsdSpeichere`, must use the
issue path, never the `reg` plug); no per-access target-to-W/GX
simulation, no whole-word atomicity beyond reused guards, no
source/IR/ABI/loader/entry/budget link, no LOCK RMW path, no full
W/GX bridge.

## Notes on the task (all complied with, no deviation)

- "Two cores where the family touches memory": each machine has core
  0 issuing/draining at the shared data cell and core 1 observing via
  `loadByte` (plus refusing its own fetch) — both cores touch the
  same shared memory in every witness.
- "A memory-changing step where the family can write": the pinned rows
  are all register-only by the accepted semantics (proved silent via
  `hwMemOut`/`hwBufOut`), so the memory-changing step is the TSO
  issue/drain stage per machine; the fp witness documents why the
  family's store form is excluded from the `reg` plug. This is stated
  honestly in each witness doc and in CUTS rather than manufacturing a
  family store step.
- One mechanical finding for future lanes: a multi-line function
  application placed directly after `with kern :=` in a structure
  update failed to parse (`unexpected token '('`), while the same
  application factored into its own `def` parses fine (shift
  successor). No semantic content; recorded in case someone hits it
  again.
- Rule-13 `_zeuge` companions: no theorem here has a universal
  quantification over program syntax as a premise, so no mechanical
  `_zeuge` is required; the task's requested `_zeuge` witnesses are
  provided as `inst_zeuge_F` (per family) and `instAlle_zeuge`
  (joint), each non-degenerate (two cores, drain changes actual
  shared memory 0 to 42).
