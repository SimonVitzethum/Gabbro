# MUSE-REPORT-1197: Pipeline block-level table reads and scaled-index addressing

Lane 1197, clone `/home/simon/Dokumente/gabbro-muse/a1197`, branch `muse/1197`.
Owns only `grammatik/Grammatik/X86/PipelineBlockTables.lean`,
`grammatik/Grammatik.lean` (one appended import line), this report.
Head after this turn: repair of review 1198 (R1 witnesses, R2 header
narrowing, R3 fresh build evidence).

## Result: green, committed

- `./lean-probe grammatik/Grammatik/X86/PipelineBlockTables.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`
  (one pre-existing linter warning: unused `Λ'` binder at
  `senkStmtSkal_korrekt_slot`; harmless).
- `./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`,
  `Build completed successfully (627 jobs).`
  This clone's base predates current master (reviewer measures 687 jobs
  without the candidate); rebase onto current master is the merge gate's
  job — this lane has no fetch, and the candidate touches only its 3 owned
  files.
- `#print axioms` for every main theorem including the four new witnesses:
  only `propext`, `Classical.choice`, `Quot.sound` (the goal-theorem
  standard), machine-checked in the probe output above, not on word.
  No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe` anywhere in the
  new file (grep: only prose "admitted" plus `#print axioms` lines).

## What was built (all in the new file, existing files untouched)

Follow-up of lane 1159 (`PipelineTables.lean`): constant-index reads/writes
are lane 1159's domain and are refused here; this file covers variable-index
reads `x := T[k].f` at block level with run-time scaled addressing
`B + k * Z + O` over pilot instructions only. No second IR, no second source
interpreter, no per-program rule. Everything reuses accepted definitions
(`TabAnker`/`feldAdr`/`tabLayout`/`WorldRep`, `PipeCfg`/`cfgOk`/`abbOf`/
`EnvRepr`/`kanon`/`lauf_zu_laufBytes`/`Entspricht`/`worldRep_lese`,
`skaliertAddr`, `skalaOk`/`basisKeinForm`/`adrOk`, machine steps).

1. Word bridges and doubling: `intWort_nat`, `natAdresse_add`,
   `natAdresse_mul`, `verdoppeln` (def), `add64_wert`, `pow2_zero`,
   `pow2_succ`, `verdoppeln_lauf`, `verdoppeln_gerade`.
2. Scales: `skalExp` (def; admitted strides 1/2/4/8 with doubling counts
   0/1/2/3), `skalExp_sound`, `skalaOk_pos`, `skalaOk_inv`,
   `skalAdresse` (def), `skalAdresse_feldAdr`.
3. Scaled chunk: `skalRest`/`skalChunk` (defs; base materialisation, index
   doubling, two pilot adds, pilot `load64` with zero displacement),
   `skaliertAddr_natAdresse` (computed address IS the reused `skaliertAddr`
   plus offset), `skalRest_gerade`, `skalChunk_gerade`, `lauf_cons`,
   `skalRest_lauf`, `skalChunk_lauf` (full framing: memory kept, all but the
   two working registers kept).
4. Read lowering: `idxVarG?` (def) + `idxVarG?_eval`, `senkSkalLesen` (def;
   `.slot`/`.durch` at a variable index, anchor base/stride/offset present,
   integer field, admitted scale, index register not `rsp`, pilot load form
   admitted; everything else `none`), `leseSkalOk` (def; checked runtime
   bound premise), `senkSkalLesen_korrekt` (both arms),
   `senkSkalLesen_durch_slot` (pointer-through reads lower exactly like
   direct reads).
5. Refusals, each with a joint `_zeuge` over the non-degenerate lane-1159
   witness program (table-writing `zeV`, memory-changing `zeRunChangeProof`):
   `senkSkalLesen_nichtvar_slot` (constant/computed index; witness
   `zeReadSlot`), `senkSkalLesen_ohne_basis` (`ankerLeer`, `zeReadVar`),
   `senkSkalLesen_ohne_zeile` (`ankerOhneZeile`), `senkSkalLesen_ohne_feld`
   (`ankerOhneFeld`), `senkSkalLesen_falsche_zeile` (non-1/2/4/8 stride;
   witness `zeA` with 16-byte stride, `ankerSkala8` for the positive shape),
   `senkSkalLesen_rsp_index` (`cfgRsp`), `senkSkalLesen_falsche_basis`
   (`cfgRbp`), plus the seven `.durch` corollaries by rewriting with the
   bridge (`senkSkalLesen_nichtvar_durch`, `..._ohne_basis_durch`,
   `..._ohne_zeile_durch`, `..._ohne_feld_durch`,
   `..._falsche_zeile_durch`, `..._rsp_index_durch`,
   `..._falsche_basis_durch`), each with its `_zeuge`
   (`zeReadDurch`, `zeReadDurchVar`).
6. Block-level statements: `envGet_set_eq`, `envGet_set_idx`,
   `abbOf_cong`, `getN_idx_eq` (environment/index helpers),
   `stmtSkalOk` (def; bound + register freshness),
   `blockSkalOk` (def; per-read bound and freshness plus the
   no-read-after-write guard over a `written : Nat → Prop` set),
   `blockSkalOkNil` (def; top level, nothing written),
   `senkStmtSkal`/`senkBlockSkal` (defs; chunk plus publish move),
   `senkStmtSkal_korrekt_slot`, `senkStmtSkal_korrekt_durch`
   (against the real `execStmt` outcome, world and environment represented),
   `senkStmtSkal_korrekt` (dispatcher), `senkStmtSkal_gerade`
   (straight-line shape for the byte-level lift).
7. Correctness witnesses (R1 repair, all joint over the non-degenerate
   lane-1159 program plus the stride-8 anchor, all green with standard
   axioms): `senkSkalLesen_korrekt_zeuge` (single-variable context,
   `rhoSkal1`, `envReprSkal1`, `worldRepSkal8` via rechecked `tabOkSkal8`/
   `tabWeltSkal8`, `bndSkal1`, `lowSkal1`), `senkStmtSkal_korrekt_slot_zeuge`
   and `senkStmtSkal_korrekt_durch_zeuge` (two-variable context `ctxSkal2`
   with target `xSkal2` in `r10` and index `ySkal2` in `r11` under
   `cfgSkal2`/`cfgSkal2Ok`; `rhoSkal2`, `regSkal2`, `stSkal2`,
   `envReprSkal2`, `hbSkal2`, `frSkal2`, `bndSkal2`/`bndDurchSkal2`,
   `lowStmtSkal2`/`lowDurchSkal2`, anchor facts `hB8`/`hZ8`/`hO8`,
   pointer `ptrSkal2`), `senkStmtSkal_korrekt_zeuge` (dispatcher on the
   same joint premises). The lowered programs stay existential (`⟨_, rfl⟩`
   closes the lowering equation by kernel reduction); every stated premise
   is instantiated jointly, nothing weakened.

## Review-1198 resolutions

- R1 (missing `_zeuge` for correctness theorems): DONE, §7 above. Each of
  `senkSkalLesen_korrekt`, `senkStmtSkal_korrekt_slot`,
  `senkStmtSkal_korrekt_durch`, `senkStmtSkal_korrekt` now has a `_zeuge`
  companion instantiating all premises jointly with the table-writing
  program (`zeHw`) and the memory-changing run (`zeRunChangeProof`).
- R2 (fetched-bytes closing theorem missing): header narrowed as the review
  explicitly allows ("or narrow the header to what is proved"). The file
  header now promises statement-level correctness only; the fetched-bytes
  closing theorem stays OPEN in CUTS with the exact missing piece (see
  §Open). No overclaim remains: `laufBytes`/`CodeAt` appear only in the
  reuse-list prose for the straight-line shape lemma's purpose.
- R3 (no full-build evidence, stale base): fresh `./lean-bau` result line
  recorded above (exit 0, 627 jobs, this clone). Rebase onto current master
  cannot be done from this lane (no fetch; `git checkout`/`reset` denied by
  the lane permission profile) and belongs to the serial merge gate, which
  re-checks build and axioms mechanically at integration.
- R4 (axioms taken on word): addressed — the probe output carried all
  `info:` axiom lines (standard axioms only, no `sorryAx`); the merge gate
  still re-checks them at integration, as it should.

## Open (CUTS in the file says exactly this)

- The fetched-bytes block closing theorem over `laufBytes`/`CodeAt` in the
  style of `pipeline_correct_entry`. Attempted and removed again while red
  (never committed red): after one statement the rest-block premise is
  stated at the old environment (`blockSkalOk c ρ w' rest`) but the
  induction hypothesis needs it at the new environment (`ρ.set x v`).
  Missing: an environment-agreement transport lemma (`blockSkalOk c ρ₀ w
  b → blockSkalOk c ρ₁ w b` when `ρ₁` agrees with `ρ₀` outside `w`,
  provable from the committed `envGet_set_idx` since the `¬written` guard
  keeps every remaining read off the written set) plus per-shape casing of
  the nested-match `blockSkalOk` like the dispatcher; and, once proved, its
  `_zeuge`, which needs a code region holding the lowered chunk bytes with
  a `CodeAt` proof. Estimated 3-6 more full-file probes at 5-10 min each.

## Notes on the task and the apparatus

- Nothing in the task statement looks wrong. The `written`-guard design
  for `blockSkalOk` is my own addition; it typechecks and is committed;
  only its consumer (the closing theorem) is open.
- This turn's repair findings (for the next author): `leseSkalOk` is
  Prop-valued, so its witness needs `unfold`+`simp only`+`decide`, not a
  bare `by decide`; `senkStmtSkal_korrekt_durch` has no `Λ'` binder (reads
  keep `Λ`) while the slot version does — pass `(Λ' := [])` only there;
  inline `.ptrOf ...` leaves metavariables in the statement, so the witness
  pointer is a named def (`ptrSkal2`); a second `feldOff` from another
  namespace shadows the pipeline one here, so the anchor fact uses
  `PipelineTables.feldOff` qualified. `⟨_, rfl⟩` closes all four lowering
  equations and both `execStmt` outcomes are consumed from the theorems.
- Standing apparatus notes: the file-edit tool cannot match two lines
  containing `Λ Λ'` (invisible character difference), so byte-level
  repairs use the explicitly allowed `sed` fallback, verified by probe;
  `git checkout --` is denied in this lane, so red work is removed
  surgically, never committed; full-file probes take 5-10 minutes.
- Rust out of scope as instructed; no emission counters touched
  (lowering is Lean-only, no new `.gab` example was minted).
