# MUSE-REPORT-895: Optimiser rule — return-path selection (lane 895)

Clone `/home/simon/Dokumente/gabbro-muse/a895`, branch `muse/895` — verified before work.

## What was done

New file `grammatik/Grammatik/X86/OptRetPathSel.lean` (~540 lines), plus the
one-line import at the end of `grammatik/Grammatik.lean`. It states the
DESIGN section 7 "Layout / allocation" row combined with section 3A
("callee-saved restores on all paths, checked per call/return") as a generic
rule lemma over arbitrary registers and values, over the reused canonical
machine vocabulary (`Typen`, `Speicher`, `Ausfuehrung`, `StackUnwind`) plus
the `eD`/`eP` source fixture for the joint witness. No new machine, no new
decoder row, no new instruction, no source/checker/Spec/goal/emitter change,
no new diagnostic/gift/example/CLI numbers, no MARKE_EMIT change, no
friend-reserved optimiser files touched.

Exact certificate shape (`RetPfadCert`): layer-A local rewrite record
(`pfade` selected return paths, `epilog` shared epilogue, `gesichert` entry
save form) plus layer-B/C validator-recomputed citations carried as checked
data (`alleOk`, `epilogOk`, `fremdOk`, `farbeOk`). Admission
`retPfadZulassen` is the conjunction of all four citations with the per-path
check `retPaarOk` (tail is `pop64 r` + `ret`), the save-shape equation and
the epilogue-shape equation.

## New definitions/theorems (all in `Gabbro.Grammatik.X86`)

- `retPaarOk`, `RetPfadCert`, `retPfadZulassen`, `retPaar_aus_zulassung`
  (admission pins restore pair + save/epilogue shapes; every conjunct used)
- Refusals (all loud `false`): `retPfadVerweigert_fehlend` (missing restore),
  `retPfadVerweigert_keinRet` (missing return), `retPfadVerweigert_fremd`
  (address-taken/overlap, DESIGN failure cases), `retPfadVerweigert_farbe`
  (colouring/liveness mismatch)
- `retPfadCertW`, probes `probe_retPfadZulassen_ok/_fehlend/_fremd` (by decide)
- `retPfad_wert_erhalten` (same-register save/restore keeps value + stack top,
  arbitrary values, via accepted `push_pop_wiederhergestellt`)
- `OptRetPathSel_flags` (flags survive call/save/restore/return)
- `OptRetPathSel_verbindung` (TARGET: admitted selection keeps callee-saved
  value, stack top, return address, all permission maps; the arbitrary taken
  restore register is pinned by the admission — `hz` is load-bearing)
- Witness chain `zeugRmp`, `zeugRS2`, `zeugRS3`, `zeugRS4` (same-register
  `rbx` save/restore/return over the accepted call frame)
- `OptRetPathSel_verbindung_zeuge` (TARGET companion: all premises jointly on
  the `rbx` chain with memory-changing call, restored top/value by the
  connection, plus `(eD.signatur eSetze).schreibt () = true` and a reached
  `eP` run moving slot 0 from `0` to `5` with `≠` and log membership)

## Last build result

`./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`,
`Build completed successfully (511 jobs)`. Axioms: at most
`[propext, Classical.choice, Quot.sound]` (witness only; connection itself
`[propext, Quot.sound]`). `gabbro_ziel` files untouched.

## What remains open (see CUTS in the file)

1. The tail rewrite itself (selected-path `pop/ret` tail replaced by a jump
   to the shared epilogue) is recorded in the certificate but its step
   correspondence is NOT proved — only the taken path's restore pair is
   pinned and connected. Short-branch selection stays with
   `BranchLayout`/`Rel8Reach`.
2. Source-side legs stay with owner lanes (no source bridge invented here):
   contracts at their place, call-log order (`AufrufOpt`), entry duties,
   budget exhaustion timing, TSO/GX concurrency bridge, `CostSummary` work
   bound. The pilot `Befehl` vocabulary has no FP form, so the rule cannot
   alter FP state; scalar-FP correspondence (DESIGN section 4) stays with
   its lane. No silicon correspondence is claimed.

## Where the task as written is weaker than it sounds

- "Prove preservation including IEEE, contracts, call logs, concurrency and
  budget": at this level only the machine half is provable (value, flags,
  stack top, return address, permission maps, loud refusals, no new faulting
  form). The listed source/concurrency/cost legs are recorded as OPEN with
  named owners rather than proved — proving them here without the source
  bridge would be fabrication.
- "Read the single accepted IR" and "the invariant/effect exports": neither
  exists in the tree (no `IR.lean`; `EffectExport`/`DutyExport`/`FpExport`
  are DESIGN-proposed names). I read `TableLayout`, `CostSummary`,
  `SpillPrivate` (spill admission), `AufrufOpt` (call-log obligation) and
  followed the accepted `CallAlign16`/`StackUnwind` proof patterns instead.
- Every theorem premise is used by its proof (checked by construction:
  admission via extraction, steps via accepted lemmas, `hz` pins `dst = r`).
