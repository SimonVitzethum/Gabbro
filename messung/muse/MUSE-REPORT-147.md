# MUSE-REPORT-147

Lane 147, sixth parallel wave. Ghost-template library (T5 of
`dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md`).

## Review rework (2026-09-14): semantics-tied second half

Reviewer verdict on the first half: NOT mergeable as T5. The
measurement (21 templates, corpus counts, Isabelle table) stays, but
the Lean theorems were stated over self-invented abstract models
unconnected to Gabbro's semantics, and every witness conjoined an
unrelated run fact as decoration. Accepted without reservation.

What changed:
- `SchablonenT5.lean` keeps the 21 abstract cores, but its header now
  says "abstract cores (not tied to the semantics)" and all 21
  witnesses lost their `refB` conjuncts (pure-concrete instantiations
  only).
- NEW `grammatik/Grammatik/SchablonenT5Sem.lean` states the 6
  most-used templates over the project's actual semantics
  (`Expr`/`eval`, `execStmt`, `World`/`Ereignis`/`offen`,
  `EmitLay.trec_count`), premises = generator-emitted shape,
  conclusions = discharged obligations, witnesses = concrete
  `refD`/`refP` programs with premises by `decide`/computation and
  conclusions about that program's run. Five tied, one precisely
  skipped (`entry.abdruck`: no entry-path syntax, no register file
  in `World`, no preserves/clobbers sets in `Deklaration`).
- Found and fixed a real soundness bug in my own work: `semW0` was
  defined AFTER its uses, and uses before the definition were
  silently elaborated as free variables, making every computation
  vacuous (a stuck `sorry` in the normal form gave it away). Moved
  the definition first; all witnesses re-verified green.

## What I did

Measured first, then proved. The template library is
`crates/gabbro-check/src/schablonen.rs`: 21 entries (`RATSCHE`).
Before this lane, all machine-checked proofs were Isabelle
(`beweise/*.thy`, 10 of 21 at `Bewiesen`, 3 carried unproved, 8
designed) and NONE of the 21 had a Lean proof. After this lane, all 21
have a Lean soundness core in one new file,
`grammatik/Grammatik/SchablonenT5.lean` (1136 lines, 56 theorems,
21 `NAME_zeuge`), each core over a small abstract model of the
template with every premise consumed by its proof, each witness
instantiating ALL premises JOINTLY on concrete values plus the
NON-DEGENERATE reference run (`refB_erreicht` + `refB_schreibt`:
table `konto` written by `einzahlen`, slot `0 -> 100`).

Corpus use was counted over `beispiele/` (whole-word line counts,
2026-09-13) and determined the proof order: table/count 370/354,
locks 292, device 130, option 90, entry 89, clobbers 80, format 58,
preserves 41, transition 34, exchange 31, accumulates/mappings 23,
consuming 13, group 10, reset 9, restrict 5, induction 3, transset 2,
`ops.suche`/`state.reset`-as-`finde` 0 (candidate, no generator yet).

## Before/after table (S# = `gabbro schablonen` order)

| S# | Template | Isabelle | Lean abstract (`SchablonenT5`) | Tied to semantics (`SchablonenT5Sem`) |
|---|---|---|---|---|
| S21 | restrict.alleinzugriff | proved | `single_root` + zeuge | no (out of the top-6 scope) |
| S20 | option.sonderwert | carried | `option_code_injective` (+`optWord_none/some`) + zeuge | YES: `sonderwert_disjoint` + `sonderwert_schranke` + zeuge on `refIdxEin` in `some` (word half has no counterpart: no machine-word lowering) |
| S1 | consuming.ordnung | proved | `consume_shrinks` + zeuge | no (out of scope) |
| S2 | consuming.umhaengen | designed (blanket REFUTED) | `rehang_can_cycle` (cycle exhibit) + zeuge | no (out of scope) |
| S3 | consuming.leermenge | proved | `consume_empty_at` + zeuge | no (out of scope) |
| S4 | table.ops.erhaltung | carried | `table_ops_keep` + zeuge | no (out of scope) |
| S5 | table.induktion | proved | `table_induction` + `induct_edge_in_type` + zeuge | no (out of scope) |
| S6 | transition.transset | designed | `joint_move_hidden` + zeuge | no (out of scope) |
| S7 | exchange.rmw | designed | `rmw_chain_order` + zeuge | no (out of scope) |
| S8 | accumulates.monoid | proved | `merge_swap_invariant` + zeuge | no (out of scope) |
| S9 | walk.mappings | designed | `walk_hits_mapping` + zeuge | no (out of scope) |
| S10 | format.roundtrip | proved | `format_roundtrip` + `format_separate` + zeuge | no (out of scope) |
| S11 | entry.abdruck | designed | `entry_keeps` + `entry_clobbers` + zeuge | SKIPPED with reason (§6 of the file): no entry-path syntax, no register file in `World`, no preserves/clobbers in `Deklaration` |
| S12 | device.konstruktor | proved | `device_cells_separate` + `device_bank_separate` + zeuge | HALF: `device_lese_frame_slots/globs` + zeuge (trace reads preserve memory); layout arithmetic skipped (no address cells in `World`) |
| S13 | table.indexschranke | proved | `index_bound_holds` + zeuge | YES: `indexschranke_eval` over `Expr`/`eval` + zeuge on `refIdxEin` fired by the run (occupancy half has no counterpart: slots total) |
| S14 | table.absenkung | proved | `lowering_stays_in_array` + zeuge | YES: `absenkung_index_im_feld` + `absenkung_zu_kurz` + `absenkung_zu_lang` over `EmitLay.trec_count` + zeuge on `refIdxEin` + `refEL` (`m = N = 2` by `rfl`) |
| S15 | ops.suche | designed (candidate) | `op_search_keeps` + `op_search_first` + zeuge | no (out of scope) |
| S16 | state.reset | designed (candidate) | `reset_from_clean` + `reset_rejects_held` + zeuge | no (out of scope) |
| S17 | verbund.konstruktor | proved | `record_ctor_unique` + zeuge | no (out of scope) |
| S18 | gruppe.ops | designed | `group_ops_compose` + zeuge | no (out of scope) |
| S19 | gruppe.sperrabdruck | carried | `lock_order_no_reentry` + `group_move_middle_free` + `group_move_no_exit` + zeuge | YES: `waitEdges`/`wohlgeordnet`/`ketteR` + `kette_steigt` + `kein_wartezyklus` + `sperrabdruck_form` + computed `fragLocks` fragment (take/write-under-lock/give-back, memory moved) + zeuge (locale parts (b)/(c) have no `execStmt` counterpart) |

Supporting definitions (all in `SchablonenT5.lean`): `idxGilt`,
`optWord`, `fieldStore`/`fieldWrite`/`fieldRead`, `GAct`/`gexec`/`gfold`,
`regFile`/`regRun`, `jointMove`/`jointTrace`, `runRmw`, `ptEntry`/
`carriesMapping`/`mappingsOf`, `rehang`, `treset`, `opSearch`
(private helpers: `entry_keeps_aux`, `entry_same_aux`,
`table_ops_keep_aux`, `op_search_keeps_all`).
New in `SchablonenT5Sem.lean` (semantics-tied): `semW0`,
`waitEdges`/`wohlgeordnet`/`ketteR`, `fragLocks` (+`fragHr`,
`ausgangSpur`, `ausgangWelt`).
`grammatik/Grammatik.lean` gains two import lines
(`Grammatik.SchablonenT5`, `Grammatik.SchablonenT5Sem`); no other
file touched. Nothing outside `grammatik/` + this report.

## Last `./lean-bau` result line

`== lake exit code: 0` / `Build completed successfully (114 jobs).`
(`./lean-probe` on both new files: 0 errors; `#print axioms` shows
only Lean's standard `propext`/`Classical.choice`/`Quot.sound` -- the
same triple as the `refB` fixture theorems; no `sorry`/`axiom`/
`native_decide`/`unsafe` anywhere.)

## What remains open

Tied half (`SchablonenT5Sem.lean` CUTS has the full list): the
checker-side premise establishment per program (`M103` for the index
type, `C001` for `m = N` via the `EmitLay` certificate, `U003`/`U005`
for `wohlgeordnet`, `H006` for each `locks`) is assumed at each use
site; the tied theorems take exactly those shapes as premises.
Abstract half (`SchablonenT5.lean` CUTS): unchanged from before,
minus the removed run conjuncts.
Deliberate weakenings vs the Isabelle counterparts, stated in CUTS:
`format` is proved over one-cell-per-field (bit disjointness assumed);
`verbund` proves `count = 1` + key `Nodup`, not the executable
read-out equation; `accumulates` proves adjacent-swap invariance, not
the quiescent-point agreement; `consuming.umhaengen` exhibits the
cycle (that IS the template content: refuted, not open). Two proof
attempts failed and were reworked: tactic `induction ... generalizing`
reorders auto-reverted hypotheses unpredictably (fixed with structural
recursion in `table_ops_keep_aux`/`op_search_keeps_all`); a first
`table_induction_zeuge` used the unbounded successor relation and
`omega` correctly refused the unprovable bound (fixed with
`a + 1 = b /\ b < 2`).
New findings from the rework: (a) `entry.abdruck` is not statable in
the current model (see §6 of the Sem file); (b) the `option` word
half and the `device` layout arithmetic likewise have no counterpart;
(c) definitions used before their definition site are silently
elaborated as free variables -- every new file should keep shared
concrete values above their first use, and `#print axioms` should be
re-read after any move (a stuck `sorry` in a normal form is the
tell).

## What I believe is wrong in the task

1. "about 16 of 20" is stale: the register holds 21 templates, 10 of
   them Isabelle-proved. The remaining work was 11 never-proved plus
   10 never-ported-to-Lean; this lane covers all 21 at core level.
2. "each template with its soundness lemma and a NAME_zeuge on a
   non-degenerate instance (rule 13)": superseded by the review.
   The tied witnesses now instantiate each template's premises on a
   REAL program (`refIdxEin`/`refWriteStAt`/`fragLocks` over `refD`,
   `refEL` over `kontoLay`) with premises by `decide`/computation
   and conclusions about that program's run (`refB_erreicht` +
   `refB_schreibt` where the run fires the witnessed site). The one
   exception shape is documented per case: impossibility conclusions
   (`kein_wartezyklus`) witness the satisfiable premise (the chain)
   and discharge closed chains, not a contradictory conjunction.
3. The corpus counts above double-count: `table`/`count`/`locks` lines
   include comments and gift probes. The ORDER is still right (table >
   locks > device > option > entry > format > ...), the absolute
   numbers are not sizes of anything.
