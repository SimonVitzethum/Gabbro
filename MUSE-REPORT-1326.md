# MUSE-REPORT-1326: exact review of candidate 1325 (TSO projection, locked + direct-memory tags)

CANDIDATE: 1325 38ceb6efe3e261ee33460e9dbcb5492a4ad34b19
(base `10fb97f11ec29c426cf09f34b72433566a758c0b`, from `.tmp/review/SNAPSHOT.json`).
Reviewed the delivered FILES only (never the author clone or its objects):
`.tmp/review/author-1325/PATCH.diff`, `OWNER-TASK.md`, `BUILD-EVIDENCE.json`,
`MUSE-REPORT-1325.md`, and the copied `grammatik/Grammatik/X86/HwKapsteinTsoLocked.lean`
(1257 lines) plus the `grammatik/Grammatik.lean` copy.

## What was done

- Verified clone `/home/simon/Dokumente/gabbro-muse/a1326`, branch `muse/1326`, clean tree.
- Read the full candidate file (lines 1-1257), the owner task, the author report,
  the build evidence, and the `Grammatik.lean` hunk of `PATCH.diff`.
- Ran `./lean-probe` on the candidate file (in place under `.tmp/review`, using this
  clone's lake env and toolchain; shell file-copy into `grammatik/` is blocked in this
  lane, and `lean-probe` realpaths its argument so the check runs against my clone's
  accepted oleans, which are NEWER than the candidate base): **0 errors**.
- Grep checks: no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` (only prose
  "admitted"); no `intro _` / `have _ :=`; no name collisions with this tree
  (`kapLockTso_xadd_geerbt`, `kap_system_still_of_mem`, `kapLocked_zeuge`,
  `kapIretHw`, `HwKapsteinTsoLocked` all absent here).
- Ran `./lean-bau` on the clean tree: `Build completed successfully (698 jobs).`
  (Author reported 691 jobs on its older base; the delta is the newer master here.)

## Findings per review dimension

- Existing files: only one added line, `import Grammatik.X86.HwKapsteinTsoLocked`
  (PATCH hunks `@@ -691,3 +691,4 @@`, verified). No edits otherwise.
- New file: 33 theorems + 2 witness defs (`kapIretReg`, `kapIretHw`); no evaluator
  redefined — `hwLockSchritt`, `lockSchrittVoll`, `lockSchritt`, `casSchritt`,
  `adapterSystem`, `sysSnapSchritt`, all `schritt*` legs, `HwVollSchritt`
  constructors and the `hwLockWit*`/`sysWit*` pins are lifted, never copied.
- Axioms: every `#print axioms` line is within the goal standard
  (`propext`, `Classical.choice`, `Quot.sound`); most are `[propext, Quot.sound]`
  or less; `kap_system_syscall_still`, `kapLocked_sys_alle_still` and
  `kapLocked_zeuge` additionally use `Classical.choice`. File ends with CUTS +
  `#print axioms` per main theorem.
- Premises: all consumed (green elaboration; no discards found).
- Classification matches the owner task: lockRmw/XADD is (b)
  (`kapLockTso_xadd_geerbt`, own buffer drained as separate leg, `Fuss tgt`
  footprint, `istRmw`, foreign buffers untouched; union lift
  `kap_union_lockRmw_xadd_tso`); MFENCE is (a) (`kapLockTso_mfence_still`);
  lockFetch inherits off-split (`kap_lockFetch_xadd_geerbt`,
  `kap_lockFetch_mfence_still`, `kap_union_lockFetch_xadd_tso`); nine system
  legs are (a) via `kap_system_still_of_mem` with union lift
  `kap_union_system_still` and the buffers-kept plug lemma
  `kap_system_puffer_bleibt` (SYSCALL/SYSRET/INT perform no drain — stated as
  the plug-level form of the family's named assumptions, honest).
- FINDINGs are genuine, not fake closure: CMPXCHG-fail
  (`kapLockTso_cmpxchg_befund`: coherent step performs the manual's write cycle
  needing `write64`, while `casSchritt_fehlschlag` stutters buffer-unchanged;
  `lockSchritt` has no cmpxchg arm) and INT n delivery
  (`kap_system_intN_schreibt_direkt` + `kap_system_intN_kein_tso_ereignis` with
  the two-byte / issue-keeps-memory / flush-touches-head-address argument, high
  priority). Both are exactly the honest (c) the task text anticipates.
- Witness `kapLocked_zeuge` is non-degenerate: LOCK XADD word 10 to 15
  (memory-changing), own buffer drained, foreign buffers kept; MFENCE; fetched
  XADD; exhibited core-1 INT delivery (bytes 16344 and 16369) with the
  no-single-TSO-event obstruction; failing-comparison twin with the
  write-permission refusal; own-buffer / split-lock / register-#UD /
  freestanding-syscall refusals; `HwWf` of all three machines; two-core
  10 to 15 to 22 with owner-only forwarding (99 vs stale 0).
- Silicon/vendor: XADD atomic RMW, MFENCE silence, 5-word INT frame push via the
  accepted `schiebeRahmen` path, read-only IRET, split/#UD/absent-fetch refusals
  — consistent with x86-64; no AMD provenance claimed; nothing model-specific
  pinned. Silicon/timing assumptions correctly left in the family files.
- CUTS honest: CMPXCHG success-only correspondence, multi-step `TSOErreichbar`
  frame-push characterisation, and the 13 remaining tags explicitly OPEN; no W/GX
  bridge, no source/checker/contract/entry/budget claim, no hardware
  correspondence beyond self-consistency.

## Last build result

- `./lean-probe .tmp/review/author-1325/grammatik/Grammatik/X86/HwKapsteinTsoLocked.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau` (clean tree, this clone): `Build completed successfully (698 jobs).`

## What remains open

- Nothing open on the review side. Open technical items belong to the author
  file's CUTS (CMPXCHG success leg, INT multi-step characterisation, 13 tags).
- Not re-verified here: full `./lean-bau` WITH the candidate integrated (shell
  copy into `grammatik/` is blocked in this lane, so integration build rests on
  the author's evidence: 691 jobs green with exactly this one-import diff, plus
  my 0-error probe of the full file against newer accepted oleans).

## Task notes

- The owner task's MECHANISM paragraph (new `HwAdapter` + `HwWf` + poison probes)
  does not match its own TASK (capstone projection over the composed union);
  the author correctly followed the TASK, as its report states. No deduction.
- The lane instruction to copy the candidate file into the clone could not be
  executed literally (shell file writes blocked); probing the delivered copy with
  this clone's toolchain/env is equivalent and was done.

## Verdict

VERDICT: ACCEPT
