# MUSE-REPORT-275: SSA and optimisation validation architecture

Lane 275, wave A. Branch `muse/275`, model opencode-go/muse-spark-1.3-contributor.
Owned file: `dokumente/x86/IR-VALIDIERUNG.md` (new). No other file touched.

## What was done

Wrote the owned spec file (8 sections, ~400 lines): ONE shared SSA/CFG
representation (SCFG: functions/blocks/straight-line ops + terminator, SSA
values with explicit `phi`, memory sequenced through an explicit token so
reordering claims are syntactically checkable), ONE three-layer certificate
interface (A local rewrite records citing a reviewed rule register with
re-decided side conditions; B recomputed dataflow/CFG facts — availability,
liveness, dominators, block/edge maps for inlining/unrolling/LICM, token
re-threading; C source-computed duty/effect binding exported from Lean),
legality + proof obligations for all nine starter optimisations
(const/copy propagation, DCE incl. faults, CSE/loads, selective inlining,
regalloc with private spills, peephole lowering, LICM, bounded unrolling,
selective independent-lane SIMD) plus cross-cutting FP-rounding/order and
stop/atomic/lock/cost/progress rules, the generic-validator fit (finite local
checking, recomputed-not-trusted dataflow, CFG maps, block stuttering with
ranking, allocation inside the same validator, no per-program Lean rules),
required exported interfaces (`DutyExport`, `EffectExport`, `AtomicExport`,
`FpExport`, `CostExport`, `LowerMap`) with suggested phase-B file ownership,
a worked copy-propagation certificate over arbitrary operand values, explicit
non-goals (speculative faulting motion, unknown-overlap reordering,
atomic/fence/lock motion, FP reassociation, interprocedural facts without a
map, address-dependent rewrites, heuristics, link-time claims), and a phase-B
review checklist. Separated soundness from profitability throughout (bad
heuristic costs speed, never correctness).

## Sources read

`dokumente/x86/WELLE-A.md` (contract), `grammatik/Grammatik/X86/Typen.lean`
(canonical vocabulary: registers, Breite, Flags with `af = none`, Speicher,
Zustand, pilot `Befehl`), `dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md` §§0–5
(chain, T1–T5, TSO-bridge and trust requirements) plus §6 `korrOk` precedent
(structural decidable check, soundness by induction, A2 `parseC` discipline),
`grammatik/Grammatik/Syntax.lean` (Signatur effects, haelt/boden, V.schreibt
guards), `Budget.lean` (Op.cost/totalCost), `KorrespondenzAllg.lean`
(`korrOk` statement/soundness shape), wave-A owner table and gate rules.

## Definitions/theorems added

None (docs-only architecture task; no Lean file, no Rust code, no new source
construct, diagnostic, probe, example or CLI switch; MARKE_EMIT untouched).

## Build/check outcome

Docs-only task: no Lean or cargo run required by the wave rules (file/claim
checks instead). `git status` shows exactly one new file,
`dokumente/x86/IR-VALIDIERUNG.md`; `git diff --stat` empty otherwise (no
modification to Typen.lean, goal statements, semantics, checker, emit.rs,
TODO/AGENTS/SATZKARTE, ledgers or C templates). No build wrapper run; nothing
to be red. Claim check: every cross-reference in the document names a file
or section verified to exist during writing (WELLE-A.md, PLAN-
UEBERSETZUNGSVALIDIERUNG.md §§0–6, Typen.lean constructors, Syntax.lean
`schreibt`/`boden`, Budget.lean costs, KorrespondenzAllg `korrOk`,
`NutzerPflichtA`/footprint rule, IEEE model, `GabbroZielVerbund`).

## What remains open

Phase-B formalisation and proofs (owners in the document §5): SCFG syntax +
semantics refining to P/GX, `check_C` + generic soundness theorem, reviewed
rule register with per-rule generic lemmas + witnesses, regalloc freshness-
commutation against the lane-274 TSO relation, SIMD profile with lanes 274 +
278, source→SCFG lowering + duty exports (lane 277), layout/ABI binding
(lane 276). Wave-A sibling lanes were not read in full; interface seams
(rule-register format, exact export wire format, TSO table shape) need joint
review with lanes 274/276/277/278 before phase B starts.

## Believed-wrong items in the task

None. The task scope (one shared representation, no competing frontend/
semantics, profitability separated, FP/stop/atomic/lock/cost/progress
preserved, generic validator, exported interfaces + ownership, example
certificate, non-local-rewriting limits, no mini-language theorem) is fully
addressed; the "no unrelated SSA theorem" constraint is honoured by adding
no Lean at all and stating the refinement requirement explicitly.
