# MUSE-REPORT-1157 — Pipeline calls: stack params, callee-saved, return values

## Clone / branch

- Clone `/home/simon/Dokumente/gabbro-muse/a1157`, branch `muse/1157` — verified.
- Owned files only: `grammatik/Grammatik/X86/PipelineCalls.lean` (new),
  `grammatik/Grammatik.lean` (one import line appended), this report.

## What was built

New file `grammatik/Grammatik/X86/PipelineCalls.lean` (541 lines), extending
the register-only ABI of `PipelineEntry.lean` over reused canonical
vocabulary only (`Stapel`, `CallAlign16`, `StackExecution`; no new machine,
no new decoder row, no second IR, no source interpreter):

- Validator `rufOk` (layout fit inside 64 bits, exact stack-arg count
  `nArgs - 6`, six callee-save words, no red zone) with `rufOk_teile`,
  `rufOk_argSchranke` (via `argStapel_schranke`),
  `rufOk_getrennt` (via `gerettet_stapel_getrennt`).
- Parameter places `rufParam_orte` (six System V registers via `argReg`,
  rest on the stack), return register `rufErgebnisReg`/`rufErgebnis_ist_rax`
  (`rax`), six named callee-saved registers
  `calleeGerettet`/`calleeGerettet_sechs`.
- Red-zone refusal (`rufRotVerbot`, `rufRotVerbot_verweigert/_frei`,
  `pipeline_ruf_verweigert_rot`) and recursion-budget refusal
  (`rekursionOk`, `rekursion_verweigert`, `rekursion_erlaubt`).
- Frame correctness `pipeline_ruf_rahmen`: admitted setup carries every
  stack argument (`sichereListe_ladeListe_rundreise`), the caller result
  word (`sichere_lade_ergebnis_rundreise` + new region induction
  `ladeErgebnis_nach_sichererListe`), untouched callee-save slots
  (`sichereListe_rahmen_fremd`), red-zone freedom.
- Byte-gate correctness `pipeline_ruf_gate`: fetched aligned call bytes
  step through `byteschritt_geholt_call` with a one-word drop and offset 8
  (`rsp8_versatz8`).
- Refusals `pipeline_ruf_verweigert_fehlalign/_rot/_schranke` plus four
  planted `decide`/`reuse` probes (`rufProbe_fehlalign/_rot/_rekursion/
  _schranke`).
- Joint witness `pipeline_ruf_rahmen_zeuge` on a seven-argument call
  (frame `{0,64}`, layout `{1,6,1}`, result word 9 at slot 0, arg word 42
  at slot 7, observed zero-to-9 byte change, reload, aligned site,
  admitted recursion, misaligned refusal twin).
- `CUTS` and `#print axioms` for every definition/theorem. Axioms are a
  subset of `[propext, Classical.choice, Quot.sound]` (standard);
  no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` anywhere.

## Last build result

`./lean-bau` (2026-10-05): `Build completed successfully (608 jobs).`
`./lean-probe grammatik/Grammatik/X86/PipelineCalls.lean`: 0 errors.
Note: two intermediate `./lean-bau` runs failed transiently (first a
`failed to create thread` resource abort in the root import-all step,
then two stale-olean reads from that crashed run); the next run rebuilt
the artifacts and the final run is fully green. No source file was
changed to obtain this.

## What remains open / honest weaknesses

- The task asks for "the call's `execBlock`/function-contract result equals
  the byte-level run". Delivered is weaker: the callee body is abstracted
  as a result-word write (`sichereErgebnis`), and callee-side preservation
  of the six registers is a caller-visible frame consequence, not a proved
  callee run. A source-level call correspondence (real `execBlock` +
  executed callee bytes) stays OPEN; the CUTS say exactly this.
- The `_zeuge` is machine-level (memory-changing reached saves) rather
  than source-level (no tables): the file has no premises over program
  syntax, so no mechanical inhabitation duty applies, but the task text
  asks for a non-degenerate program witness in the source sense.
- The TSO spill-privacy leg is cited (`ComposeSpillPrivacy_verbindung`),
  not re-proved; the push/pop restoration leg is cited
  (`ComposeStackAbi_verbindung`,
  `geholt_verschachtelt_wiederhergestellt`), not redone.
- Recursion bound is a stated number; who enforces it at run time is OPEN.

## Task feedback

- The task's `ComposeSpillPrivacy` reference resolves at the frame level
  only through `Stapel` primitives; a byte-connected per-access spill
  story needs the TSO-bridge interfaces (owners 573/574), which are still
  open — the file documents this instead of assuming the bridge.
- Nothing else in the task looks wrong; the six-register limit, red-zone
  ban and budget refusal all mapped to existing accepted vocabulary
  (`argReg`, `rotZoneImRahmen`-style refusal, `decide` budget).
