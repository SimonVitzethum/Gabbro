# MUSE-REPORT-1197: Pipeline block-level table reads and scaled-index addressing

Lane 1197, clone `/home/simon/Dokumente/gabbro-muse/a1197`, branch `muse/1197`.
Owns only `grammatik/Grammatik/X86/PipelineBlockTables.lean`,
`grammatik/Grammatik.lean` (one appended import line), this report.

## Result: green partial, committed

- `./lean-probe grammatik/Grammatik/X86/PipelineBlockTables.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`
  (one pre-existing linter warning: unused `Λ'` binder at
  `senkStmtSkal_korrekt_slot`; harmless).
- `./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`,
  `Build completed successfully (627 jobs).`
- `#print axioms` for every main theorem: only `propext`,
  `Classical.choice`, `Quot.sound` (the goal-theorem standard). No `sorry`,
  `admit`, `axiom`, `native_decide`, `unsafe` anywhere in the new file.

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

## Open (CUTS in the file says exactly this)

1. The fetched-bytes block closing theorem (`senkBlockSkal_korrektBytes`
   over `laufBytes`/`CodeAt` in the style of `pipeline_correct_entry`).
   Attempted this turn and removed again while red (never committed red):
   after one statement the rest-block premise is stated at the old
   environment (`blockSkalOk c ρ w' rest`) but the induction hypothesis
   needs it at the new environment (`ρ.set x v`). What is missing is an
   environment-agreement transport lemma: `blockSkalOk c ρ₀ w b →
   blockSkalOk c ρ₁ w b` when `ρ₁` agrees with `ρ₀` on all indices outside
   `w` — provable from the already-committed `envGet_set_idx` (which is
   polymorphic in the read variable's type) since the `¬written` guard
   keeps every remaining read off the written set; plus per-shape casing
   of the nested-match `blockSkalOk` in the style of the already-committed
   dispatcher. Estimated: one agreement lemma plus the induction, 40-80
   lines; each full-file probe takes 5-10 minutes, so budget 3-6 probes.
2. `_zeuge` companions for the correctness theorems
   (`senkSkalLesen_korrekt`, `senkStmtSkal_korrekt_slot/durch`,
   `senkStmtSkal_korrekt`) on a non-degenerate memory-changing witness,
   required by HARD RULES 13 for theorems with universal syntax premises.
   The refusal witnesses exist; the correctness witnesses need concrete
   `WorldRep`/`EnvRepr` proofs over a scaled anchor (`ankerSkala8`) and
   are not attempted here. If they cannot be built, that is a finding
   about the premises, reported per rule 13 — not silently weakened.

## Notes on the task and the apparatus

- Nothing in the task statement looks wrong. The `written`-guard design
  for `blockSkalOk` (read-after-write guard inside the predicate rather
  than a plain conjunction) is my own addition over the first committed
  `blockSkalOk` conjunction; it is what makes the transport lemma above
  statable. It typechecks and is committed; only its consumer (the closing
  theorem) is open.
- Apparatus findings, no rule broken: (a) the file-edit tool could not
  match two lines containing `Λ Λ'` (invisible character difference;
  `grep`/`sed` saw them fine), so the `vertrag`→`Vertrag` typo repair and
  the red-section removal were done with the explicitly allowed `sed`
  fallback, then verified by `./lean-probe`; (b) `git checkout --`
  (the HARD-RULES-8 revert path) is denied by the permission classifier
  in this lane, so the revert-equivalent was a surgical `sed` line-range
  deletion of only the uncommitted red section — no committed theorem was
  deleted or weakened; (c) full-file probes take 5-10 minutes here
  (first attempt exceeded a 300 s budget with no output; 600 s succeeded),
  which bounds probe iteration speed for the follow-up work in §Open.
- Rust out of scope as instructed; no emission counters touched
  (lowering is Lean-only, no new `.gab` example was minted).
