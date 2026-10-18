/- Part 3 of 3 of `SchablonenT5` (split by instrumente/teile/lean-teilen.py; the umbrella `SchablonenT5.lean` imports all parts). -/
import Grammatik.Bausteine.Schablonen.SchablonenT5.T2

namespace Gabbro.Grammatik

/-! ## CUTS:
  - All 21 templates of `crates/gabbro-check/src/schablonen.rs` have a
    Lean soundness core in this file (previously: 0 of 21 in Lean; 10 of
    21 in Isabelle `grammatik/Beweise/*.thy`). Each core is proved over a small
    abstract model of the template, every premise is consumed by its
    proof, and every template has a `NAME_zeuge` instantiating ALL
    premises JOINTLY on concrete values only (no run link: the
    former `refB` conjuncts were removed as decoration on 2026-09-14
    review).
  - What is NOT proved (per template, weaker than the Isabelle
    counterpart where noted):
    (1) `table.indexschranke`: the checker side (`M103` establishes
    `hN`/`hZ` per program) is assumed, not proved.
    (2) `table.absenkung`: `m = N` comes from `C001`, assumed.
    (3) `option.sonderwert`: the arithmetic ON an index (no generated
    computation hits the special value) is a statement about `emit.rs`,
    not proved.
    (4) `verbund.konstruktor`: `deckt` comes from `M106`/`M107`,
    assumed; the executable read-out (`liest ... = some v`) is not
    stated -- only `count = 1` plus key `Nodup`, which is what makes
    read-out unambiguous.
    (5) `device.konstruktor`: declared layouts = device layouts is an
    axiom-layer assumption; `stride 0` refusal (`N010`) is assumed.
    (6) `format.roundtrip`: proved over one-cell-per-field; the
    bit-level disjointness (`trennt`, `N008`) this rests on is assumed;
    variable lengths are out of scope (fixed case only).
    (7) `gruppe.sperrabdruck`: the axiom-layer premise (a held
    footprint keeps foreign cores out) is presupposed; (b) is the
    negative exhibit, not a preservation proof.
    (8) `entry.abdruck`: the hardware meaning of registers and the
    stack switch (undefined word) are not modelled.
    (9) `transition.transset`: the observer footprint is named by
    premise; who holds the lock on multicore is outside the model.
    (10) `exchange.rmw`: purity holds by construction (body IS a
    function); atomicity is an axiom-layer assumption, not proved.
    (11) `accumulates.monoid`: only adjacent-swap invariance (the
    order-independence core); the quiescent-point agreement with the
    atomic RMW chain and the per-operator units are not proved.
    (12) `walk.mappings`: meeting holds by construction (filter);
    whether the generator builds it, and large pages above full depth,
    are open.
    (13,14) `consuming.ordnung/leermenge`: finite-list level only; the
    well-founded order itself and `waehlt_minimal` are assumed.
    (15) `consuming.umhaengen`: the refutation exhibit only (as the
    template demands: the blanket version is refuted, not open).
    (16) `gruppe.ops`: preservation composes; the per-operation base
    cases for real group operations are not proved.
    (17) `state.reset`: single-flag model; the M2 linearity context is
    assumed.
    (18) `restrict.alleinzugriff`: H1 holds by construction (access IS
    a rooted pair); H2a/H2b are folded into one `hOnly` premise whose
    checker establishment (`emit::darf_restrict`, language shape) is
    assumed; `own`-exclusivity stays a language decision.
    (19) `table.induktion`: well-foundedness is a hypothesis; the
    generator side (two edge premises per `chain(a,b)`) is assumed.
    (20) `table.ops.erhaltung`: the per-operation preservation `h`
    (Teil II by hand) is a premise, not a result; the emitted-C step
    (`relabel` lowering branches) is not modelled.
    (21) `ops.suche`: construct has no generator; the multi-edge order
    is assumed.
  - No theorem quantifies over program syntax (`Vertrag`/`Stmt`/sic),
    so no conclusion claims a Gabbro semantics; the models are
    explicitly abstract (`fieldStore`, `regFile`, `GAct`, ...).
-/

#print axioms Gabbro.Grammatik.idxGilt
#print axioms Gabbro.Grammatik.index_bound_holds
#print axioms Gabbro.Grammatik.index_bound_zeuge
#print axioms Gabbro.Grammatik.lowering_stays_in_array
#print axioms Gabbro.Grammatik.lowering_stays_in_array_zeuge
#print axioms Gabbro.Grammatik.optWord
#print axioms Gabbro.Grammatik.optWord_none
#print axioms Gabbro.Grammatik.optWord_some
#print axioms Gabbro.Grammatik.option_code_injective
#print axioms Gabbro.Grammatik.option_code_injective_zeuge
#print axioms Gabbro.Grammatik.record_ctor_unique
#print axioms Gabbro.Grammatik.record_ctor_unique_zeuge
#print axioms Gabbro.Grammatik.device_cells_separate
#print axioms Gabbro.Grammatik.device_bank_separate
#print axioms Gabbro.Grammatik.device_cells_separate_zeuge
#print axioms Gabbro.Grammatik.fieldWrite
#print axioms Gabbro.Grammatik.fieldRead
#print axioms Gabbro.Grammatik.format_roundtrip
#print axioms Gabbro.Grammatik.format_separate
#print axioms Gabbro.Grammatik.format_roundtrip_zeuge
#print axioms Gabbro.Grammatik.lock_order_no_reentry
#print axioms Gabbro.Grammatik.group_move_middle_free
#print axioms Gabbro.Grammatik.gexec
#print axioms Gabbro.Grammatik.gfold
#print axioms Gabbro.Grammatik.group_move_no_exit
#print axioms Gabbro.Grammatik.lock_order_no_reentry_zeuge
#print axioms Gabbro.Grammatik.regRun
#print axioms Gabbro.Grammatik.entry_keeps
#print axioms Gabbro.Grammatik.entry_clobbers
#print axioms Gabbro.Grammatik.entry_keeps_zeuge
#print axioms Gabbro.Grammatik.jointMove
#print axioms Gabbro.Grammatik.jointTrace
#print axioms Gabbro.Grammatik.joint_move_hidden
#print axioms Gabbro.Grammatik.joint_move_hidden_zeuge
#print axioms Gabbro.Grammatik.runRmw
#print axioms Gabbro.Grammatik.rmw_chain_order
#print axioms Gabbro.Grammatik.rmw_chain_order_zeuge
#print axioms Gabbro.Grammatik.merge_swap_invariant
#print axioms Gabbro.Grammatik.merge_swap_invariant_zeuge
#print axioms Gabbro.Grammatik.mappingsOf
#print axioms Gabbro.Grammatik.walk_hits_mapping
#print axioms Gabbro.Grammatik.walk_hits_mapping_zeuge
#print axioms Gabbro.Grammatik.consume_shrinks
#print axioms Gabbro.Grammatik.consume_shrinks_zeuge
#print axioms Gabbro.Grammatik.consume_empty_at
#print axioms Gabbro.Grammatik.consume_empty_at_zeuge
#print axioms Gabbro.Grammatik.rehang
#print axioms Gabbro.Grammatik.rehang_can_cycle
#print axioms Gabbro.Grammatik.rehang_can_cycle_zeuge
#print axioms Gabbro.Grammatik.group_ops_compose
#print axioms Gabbro.Grammatik.group_ops_compose_zeuge
#print axioms Gabbro.Grammatik.treset
#print axioms Gabbro.Grammatik.reset_from_clean
#print axioms Gabbro.Grammatik.reset_rejects_held
#print axioms Gabbro.Grammatik.reset_from_clean_zeuge
#print axioms Gabbro.Grammatik.single_root
#print axioms Gabbro.Grammatik.single_root_zeuge
#print axioms Gabbro.Grammatik.table_induction
#print axioms Gabbro.Grammatik.induct_edge_in_type
#print axioms Gabbro.Grammatik.table_induction_zeuge
#print axioms Gabbro.Grammatik.table_ops_keep
#print axioms Gabbro.Grammatik.table_ops_keep_zeuge
#print axioms Gabbro.Grammatik.opSearch
#print axioms Gabbro.Grammatik.op_search_keeps
#print axioms Gabbro.Grammatik.op_search_first
#print axioms Gabbro.Grammatik.op_search_zeuge


end Gabbro.Grammatik
