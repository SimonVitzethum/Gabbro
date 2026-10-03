# MUSE-REPORT-878: linear-scan allocation rule (OptAllocLinear)

## What was done

New file `grammatik/Grammatik/X86/OptAllocLinear.lean` (~630 lines) plus the
one-line import in `grammatik/Grammatik.lean`. It states the linear-scan
register-allocation optimisation as a generic rule lemma over arbitrary
carried values with validator-decided side conditions, over reused
canonical vocabulary only (`Typen`, `Syntax`, `Semantik`, `Gleitkomma`,
`X86.Typen`, `X86.Wort`, `ReferenzB`, `X86.RegisterInterference`,
`X86.Stapel`). No new IR, no source/checker/Spec/goal/emitter edits, no new
diagnostic/gift/example/CLI numbers, no MARKE_EMIT changes, no
friend-reserved optimiser files touched.

Certificate shape (local rewrite record plus recomputed analysis
citations): scan order (`order`), colouring (`zu : Assign`, register or
spill-slot homes), cited fusions (`fus : List (Nat x Nat)`, 16-byte units
as adjacent 8-byte slot pairs), recomputed live sets per point
(`leb`), frame depth (`depth`). Admission is one decided `Bool`,
`allocOk` = scan + pair + fusion + liveness + home checks.

## Exact new names

Defs: `Interval`, `intervalsOverlap`, `Home`, `Assign`, `homeOf`,
`homesDiffer`, `startOf`, `orderSorted`, `allocScanOk`, `allocPairOk`,
`allocFusedOk`, `coversPt`, `allocLiveOk`, `homeInFrame`, `allocHomeOk`,
`allocOk`, `spillAnzahl`, `zeugenIvs`, `zeugenOrdnung`, `zeugenLeb`.

Theorems: `probe_overlap_yes/no`, `allocOk_scan/pair/fused/live/home`,
`allocSeparate`, `overlapHasPoint`, `regSet_liestEigen`,
`allocSchreibt_bleibt`, `heimBeobachter_bleibt`, `allocSpill_behält`,
`gleitHeim_behält`, `allocWort_rund`, `probe_spillAnzahl_null/zwei`,
`spillAnzahl_schranke`, `spillfrei_ohneVerkehr`,
`allocVerweigert_gleichesReg/rsp/gemeinsamerSlot/fusion`,
`allocPositiv_reg/slotOhneFusion/geteilterSlot`,
`allocFused_verweigert`,
`OptAllocLinear_verbindung` with companion
`OptAllocLinear_verbindung_zeuge` (jointly inhabited on `refD` with the
memory-changing reached run `MB`: writer `refEin_schreibt`, `refB_erreicht`,
`refB_schreibt`).

Precise refusal case: a cited fused 16-byte spill unit covering two
overlapping carriers refuses the whole admission (general theorem
`allocFused_verweigert` plus decided instance `allocVerweigert_fusion`).
Adjacent spill slots WITHOUT a cited fusion stay allowed
(`allocPositiv_slotOhneFusion`); non-overlapping carriers may share one
slot (`allocPositiv_geteilterSlot`).

Preservation proved: source values (`eval` of both bound literals),
distinct homes with scan-ordered writes keeping both words (registers,
total file) and spill reload through permission-checked `read64`
(fault leg), width-exact word round-trip, `gleitPasst` agreement for
carried floats (IEEE leg, never re-rounded), generic observer agreement
`heimBeobachter_bleibt` (contracts as `Bool` observers, log entries as
observers into any type), counted/bounded spill traffic with a proved
zero-traffic spill-free case (budget leg).

## Last build result

`./lean-bau`: `Build completed successfully (511 jobs).`
`./lean-probe grammatik/Grammatik/X86/OptAllocLinear.lean`:
`== 0 error(s) in the COMPLETE output`.
`OptAllocLinear_verbindung` and `_zeuge` depend only on
`[propext, Classical.choice, Quot.sound]` (the standard `gabbro_ziel` set).
No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; every premise is used.

## What remains open (see CUTS in the file)

No source-syntax rewrite leg (`execEnd` equality across homings):
allocation is backend-only, so this needs the accepted lowering
(IR-287 interface), waited for, not invented. No per-access TSO/GX
bridge from slot-index separation to footprint disjointness. No
machine-work transfer of `spillAnzahl` into a `CostSummary` bound.
Place-level contracts, log-append, TSO-step and work-bound legs wait for
the same lowering; value/home-level preservation is proved.

## Finding / task remark

While proving `overlapHasPoint` I found the bare endpoint comparison
admits empty intervals (`[50, 40)` "overlaps" everything but shares no
point), so the theorem takes explicit non-emptiness premises; the
certificate check itself does not enforce non-emptiness (recorded in
CUTS). This is a deliberate fail-open note, not a soundness hole in the
refusals: every refusal and the separation lemma hold regardless.

A second remark: the task asks for contract/call-log/concurrency/budget
preservation "proved"; the machine-level legs of these genuinely need
the accepted lowering and are precise obstructions (bounded connection
proved, filed as CUTS), not full proofs. The report states this plainly
per hard rule 4.
