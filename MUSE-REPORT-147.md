# MUSE-REPORT-147

Lane 147, sixth parallel wave. Ghost-template library (T5 of
`dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md`).

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

| S# | Template | Isabelle | Lean before | Lean after (this lane) |
|---|---|---|---|---|
| S21 | restrict.alleinzugriff | proved | none | `single_root` + zeuge |
| S20 | option.sonderwert | carried | none | `option_code_injective` (+`optWord_none/some`) + zeuge |
| S1 | consuming.ordnung | proved | none | `consume_shrinks` + zeuge |
| S2 | consuming.umhaengen | designed (blanket REFUTED) | none | `rehang_can_cycle` (cycle exhibit) + zeuge |
| S3 | consuming.leermenge | proved | none | `consume_empty_at` + zeuge |
| S4 | table.ops.erhaltung | carried | none | `table_ops_keep` + zeuge |
| S5 | table.induktion | proved | none | `table_induction` + `induct_edge_in_type` + zeuge |
| S6 | transition.transset | designed | none | `joint_move_hidden` + zeuge |
| S7 | exchange.rmw | designed | none | `rmw_chain_order` + zeuge |
| S8 | accumulates.monoid | proved | none | `merge_swap_invariant` + zeuge |
| S9 | walk.mappings | designed | none | `walk_hits_mapping` + zeuge |
| S10 | format.roundtrip | proved | none | `format_roundtrip` + `format_separate` + zeuge |
| S11 | entry.abdruck | designed | none | `entry_keeps` + `entry_clobbers` + zeuge |
| S12 | device.konstruktor | proved | none | `device_cells_separate` + `device_bank_separate` + zeuge |
| S13 | table.indexschranke | proved | none | `index_bound_holds` + zeuge |
| S14 | table.absenkung | proved | none | `lowering_stays_in_array` + zeuge |
| S15 | ops.suche | designed (candidate) | none | `op_search_keeps` + `op_search_first` + zeuge |
| S16 | state.reset | designed (candidate) | none | `reset_from_clean` + `reset_rejects_held` + zeuge |
| S17 | verbund.konstruktor | proved | none | `record_ctor_unique` + zeuge |
| S18 | gruppe.ops | designed | none | `group_ops_compose` + zeuge |
| S19 | gruppe.sperrabdruck | carried | none | `lock_order_no_reentry` + `group_move_middle_free` + `group_move_no_exit` + zeuge |

Supporting definitions (all in `SchablonenT5.lean`): `idxGilt`,
`optWord`, `fieldStore`/`fieldWrite`/`fieldRead`, `GAct`/`gexec`/`gfold`,
`regFile`/`regRun`, `jointMove`/`jointTrace`, `runRmw`, `ptEntry`/
`carriesMapping`/`mappingsOf`, `rehang`, `treset`, `opSearch`
(private helpers: `entry_keeps_aux`, `entry_same_aux`,
`table_ops_keep_aux`, `op_search_keeps_all`).
`grammatik/Grammatik.lean` gains one import line
(`Grammatik.SchablonenT5`); no other file touched.

## Last `./lean-bau` result line

`== lake exit code: 0` / `Build completed successfully (113 jobs).`
(`./lean-probe` on the file: 0 errors; `#print axioms` shows only
Lean's standard `propext`/`Classical.choice`/`Quot.sound` -- the
`choice`/`Quot` come from the imported `refB` fixture proofs and core
`List` lemmas, not from this file; no `sorry`/`axiom`/`native_decide`/
`unsafe` anywhere.)

## What remains open

Everything listed in the file's `CUTS` block -- per template, the
checker/emitter-side premise establishment (`M103`, `M106`/`M107`,
`C001`, `N008`/`N009`, `U003`/`U005`/`U006`/`H006`, `E008`/`E010`,
`emit::darf_restrict`, Pass 8) is assumed, and the hardware/axiom side
(layouts = device, atomicity, held-footprint exclusion) is assumed.
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

## What I believe is wrong in the task

1. "about 16 of 20" is stale: the register holds 21 templates, 10 of
   them Isabelle-proved. The remaining work was 11 never-proved plus
   10 never-ported-to-Lean; this lane covers all 21 at core level.
2. "each template with its soundness lemma and a NAME_zeuge on a
   non-degenerate instance (rule 13)": rule 13 mechanically requires
   witnesses only for syntax-quantified premises or `ZEUGE:` targets
   (this task has neither), but I added all 21 anyway as instructed.
   Note the witnesses for impossibility-shaped halves (e.g. the
   disjointness conclusions) instantiate the inhabitable premises plus
   the run, not the jointly-contradictory full hypothesis set -- that
   set is contradictory by design.
3. The corpus counts above double-count: `table`/`count`/`locks` lines
   include comments and gift probes. The ORDER is still right (table >
   locks > device > option > entry > format > ...), the absolute
   numbers are not sizes of anything.
