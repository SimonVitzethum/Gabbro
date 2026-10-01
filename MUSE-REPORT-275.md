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

## Review repairs (2026-10-01, second commit on this branch)

The reviewer required five repairs in the owned document. All five are
applied (second commit); no Lean/Rust changes, owned files only.

1. **§2.4 was unsound (free initial graph, duty-only binding, assumed
   refinement).** The theorem now quantifies over the FULL source-computed
   unit `E` (`Kette.E` shape), requires `lowerOk(E, G0) = true` for the
   initial graph (Lean-computed or Rust-proposed + proved lowering checker,
   §1.3), per-step `check_C(Ci, G(i-1), Gi, E) = true` over the whole
   optimisation sequence, and `layoutOk(Gn, B, Img) = true` for the final
   decoded bytes/image (lane-276 binding). The refinement is proved via the
   per-access bridge and the §3 lemmas, not assumed. The §5 closing-theorem
   paragraph now names the same E-anchored chain.
2. **CSE/memory motion ignored other threads' writes.** §3 item 3 rewritten:
   load elimination/reordering now needs a validator-decided global
   interleaving condition (exclusive ownership, held-lock stability checked
   over ALL functions' effect exports, or immutability including
   foreign/device writers); atomics/MMIO/volatile/foreign-observable memory
   are ineligible without an exact per-access concurrent equivalence
   theorem; disjoint local objects never license moving a shared access
   across publication/fence/acquire/release/lock boundaries. The §2.2 token
   check now states token-order is necessary but not sufficient; §3 items 2
   and 7 and §7 item 2 updated to cite item 3 (this also fixed the wrong
   cross-reference: item 8 is unrolling, not a motion rule).
3. **SIMD lacked fault-order/visibility/tearing/FP-status obligations.**
   §3 item 9 now carries all four as independently-refusing obligations plus
   a CONDITIONAL REFUSAL: until the generic vector correspondence (lanes
   274+278) is proved, only pure non-trapping integer lanes over proved
   private-or-immutable memory pass, each citing the pending theorem.
   §7 item 9 records the same refusal as a non-goal.
   SUPERSEDED by the second review below: no SIMD is admitted on a pending
   theorem at all, including this candidate.
4. **Cost treatment audited into three levels** (§1.2, §3 item 11, §5.1
   `CostExport`, §6 example, §8 checklist): (a) source budget semantics
   (re-summed, NOT x86 costing), (b) measured target work (opaque,
   profitability only), (c) proved machine-work bound (OPEN obligation with
   lane 278, cited not assumed — no closing theorem claims budget transfer
   until it closes). Declining an optimisation never weakens a bound.
5. **Inlining call-log/`FolgeG` + cross-references.** §3 item 4 now requires
   explicit ghost call/return event reconstruction (direct AND indirect
   calls, actual values incl. reason-channel outcome) with identical ghost
   logs as the legality condition for a changed physical call count; §2.2
   CFG-mapping bullet carries the ghost records; §8 checklist has the
   corresponding item.

## Second review repairs (third commit on this branch)

Two precise claim fixes; no Lean/Rust changes, owned files only.

1. **No SIMD admission on a pending theorem (§3 item 9, §7 item 9, §8,
   CUTS).** The previous "admissible remainder citing the pending theorem"
   was wrong: a pending correspondence admits nothing. Now ALL SIMD
   validation is refused until a generic vector-correspondence rule for
   (a)–(d) is actually proved; the pure/private non-trapping integer
   candidate is first in the proof queue (prioritised), accepted only after
   its proof closes.
2. **Budget-exhaustion stops need ghost accounting (§3 item 11(a), §6
   example, §8, CUTS).** The previous "preserved because no transformation
   adds/removes stops, validator re-sums" was wrong: removing an op fires a
   later exhaustion stop later or never, duplicating one fires it earlier —
   counter-decrement timing itself matters. Now the phase-B proof must carry
   an explicit ghost source-budget accounting correspondence (eliminated
   steps as accounted zero-cost ghosts, duplicated steps with earlier-stop
   displacement proved harmless, stuttering steps consuming explicitly), or
   keep physical/source budget semantics separate with a proved transfer.
   Until then, exhaustion-stop preservation is OPEN; the §6 example notes
   its re-sum is a mismatch check only; no source guarantee weakened.

### Proposals vs implemented facts vs open obligations

- IMPLEMENTED FACTS (in this lane's scope): the wave-A vocabulary
  (`Typen.lean`), the plan §§0–5, the `korrOk`/A2 precedents — all cited,
  none modified. This lane's output is a reviewed specification, committed.
- PROPOSALS (this document's content, to be judged in phase-B review):
  SCFG shape, the A/B/C certificate interface, the `lowerOk`/`check_C`/
  `layoutOk` checker shapes, the rule register, ghost events, the three
  cost levels, file ownership.
- OPEN OBLIGATIONS (explicit in the document's CUTS and §8, not claimed):
  every Lean definition, rule lemma, checker Bool, refinement theorem,
  lowering checker, per-access concurrent equivalence, vector
  correspondence (no SIMD admitted before it), ghost-event preservation
  proof, ghost source-budget accounting correspondence (or proved
  physical/source separation with transfer) for budget-exhaustion stops,
  machine-work bound with lane 278, and lane-276 image binding.
  A sibling-lane interface review (274/276/277/278 seams) is still needed
  before phase B.

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
