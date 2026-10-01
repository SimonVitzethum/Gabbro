# Shared SSA / control-flow representation and certificate architecture

*Lane 275, wave A. Owner file for the optimisation-validation half of the direct
x86-64 plan (`dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md` §§0–5, contract
`dokumente/x86/WELLE-A.md`). Status: architecture specification, not an
implementation or a proof. No Lean file, no Rust code, no new source construct,
diagnostic, probe or CLI switch is added here.*

## 0. Position in the chain

The end chain (§0 of the plan) is:

```
source text -- Lean parser/elaborator --> model program P, obligations
     |
     +-- untrusted Rust backend --> final x86-64 image + certificate
                                            |
                              Lean decoding and validation
                                            |
                       generic refinement theorem to P / GX
                                            |
                              existing goal theorem
```

Optimisations sit entirely in the untrusted middle arrow. This document fixes:

1. ONE shared SSA/control-flow representation (the vocabulary every optimisation
   certificate speaks, §1);
2. ONE certificate interface tying source-computed Lean `P`/`GX` judgements to
   the target (§2);
3. the legality and proof obligations of each starter optimisation (§3);
4. how the pieces fit a generic validator with no trusted Rust and no
   per-program Lean rules (§4);
5. required exported interfaces and suggested phase-B file ownership (§5);
6. a worked example certificate (§6);
7. what local rewriting cannot handle (§7).

What this document is NOT: a second source language, a second concurrency
model, a new register/instruction model (canonical vocabulary stays
`grammatik/Grammatik/X86/Typen.lean`, namespace `Gabbro.Grammatik.X86`), or a
theorem about a self-invented mini-language presented as source correspondence.
Any Lean formalisation of §§1–2 must refine against `P` (via `rufAt` /
`execStmt` / `exec`) and against the per-access TSO bridge (lane 274), never
against its own syntax alone.

Two separations govern everything below:

- **Semantic soundness vs optimisation profitability.** Soundness (the
  transformation preserves every observable the goal theorem claims) is proved
  once per transformation FAMILY in Lean, over arbitrary programs. Profitability
  (the transformation fires only when a cost model says it helps) is an
  untrusted Rust heuristic: a bad heuristic costs speed, never correctness,
  because the validator rechecks the certificate. No cost estimate is ever a
  soundness premise.
- **Source-computed judgements vs target facts.** Typing, effects
  (`Signatur.schreibt` / `gschreibt`, `V.schreibt` guards in `Syntax.lean`),
  declared costs (`Budget.lean`: `Op.cost`, `totalCost`), lock ranks, FP
  ranges, atomic orderings and user duties are computed in Lean FROM THE SOURCE
  (T3, GabbroV bridge) and EXPORTED to the validator as checked data. The Rust
  backend may attach hints; Lean reconstructs or rechecks every obligation
  through a proved checker, exactly as `korrOk` (`KorrespondenzAllg.lean`) does
  for the C chain: structural, decidable (`decide`-settled), soundness by
  induction at every call depth.

## 1. The shared representation: SCFG

### 1.1 Why one representation

Nine starter optimisations (constant/copy propagation, DCE, CSE, selective
inlining, register allocation with private spills, peephole lowering, LICM,
bounded unrolling, selective independent-lane SIMD) must not each invent a
private IR with a private correspondence proof: that is nine trust paths and
nine chances to disagree about what a memory access is. There is ONE shared
representation, called here **SCFG** (SSA control-flow graph), owned by phase B
(suggested home §5). Every optimisation certificate is a claim *about a pair
of SCFG graphs* (before/after) plus *a mapping into validated machine bytes*;
the generic validator checks the claim, and ONE generic refinement theorem
lifts checked SCFG pairs to model correspondence.

### 1.2 Shape (requirements on the phase-B formalisation, not the definition)

SCFG is deliberately small. Requirements:

- **Functions, blocks, straight-line bodies.** A unit is a list of functions;
  a function is a labelled list of basic blocks; a block is a straight-line
  list of operations plus ONE terminator (branch, conditional branch, call,
  return, stop/trap). No nested regions, no irreducible control flow in the
  checked form: the Rust frontend normalises to reducible CFG (loop headers
  identified); irreducible input is refused, not miscompiled.
- **SSA values, versioned.** Every pure value has exactly one definition
  (SSA name `v<n>`); merges carry explicit `phi` nodes at block entries.
  Memory is NOT in SSA: memory operations sequence through an explicit memory
  token (or chain), so that reordering claims must exhibit the token
  threading. This is the load-bearing design decision: it makes memory
  dependence syntactically visible to a finite checker instead of hiding it
  in alias analysis the validator would have to trust.
- **Operations, closed set.** Each op is one of:
  - pure computation: integer arithmetic/logic/shift at a declared width,
    FP scalar op with explicit rounding mode (see §3.10), comparisons,
    `phi`, moves/copies;
  - memory: load/store at a declared width and alignment through a named
    object reference (stack slot, global/table cell, region handle — never a
    bare integer; int→ptr conversion does not enter the language);
  - concurrency/synchronisation: atomic load/store/RMW with explicit source
    ordering, fence, lock acquire/release, thread start/join markers;
  - control-relevant: call (named callee + arg list + memory token in/out),
    `assume`/`check` markers carrying source duty references (see §2.3),
    stop/trap with a stop class (hardware, flag, budget, `nieZurueck` —
    matching `FortschrittG`'s stop kinds).
- **Types on every value.** Width (`Breite`-like, extended to b8/b16/b32/b64
  per §2 of the plan), signedness where the source knew it, FP kind
  (f32/f64) with rounding mode, pointer-with-object (pointee object +
  extent reference). Unknown signedness is explicit (`unknown`), and then
  the source policy applies: fall back to the LOUD check (emit the lower
  `narrow` guard), never silently drop it.
- **Costs attached, not trusted — three levels.** Each op carries its
  declared source cost (`Op.cost` analogue, level (a) of §3 item 11) and
  each block its sum; the validator re-sums (profitability hints never
  change the sum). Measured target work (level (b)) travels with the
  certificate opaquely and is never read by any soundness argument. The
  proved machine-work bound (level (c)) is a separate phase-B obligation
  with lane 278, not a consequence of re-summing (a).
- **Source anchors.** Every op optionally carries its source span: the
  `Stmt`/`Block`/`Endblock` node it was lowered from (a Lean-computed
  `D`/`P` reference, see §2). Anchors are REQUIRED on memory ops, calls,
  checks, atomics, lock ops and stops; pure arithmetic may leave them empty
  (recomputed identities need none).

### 1.3 What SCFG is lowered from, and to

- **Lowering source → SCFG** is a Lean function (phase B, lane 277's
  `QUELLBRUECKE` closes it): from the FULL source-computed unit `E`
  (code `P` plus checker data, lock invariants, axiom ensures, declared
  starts, initial memory — the `Kette.E` shape) to the initial graph
  `G0 = lower(E)`, proved to preserve `execStmt`/`exec` outcomes on the
  covered fragment. There is NO free initial graph: `G0` is either computed
  by this Lean function (correct by construction) or proposed by Rust and
  admitted only through a PROVED lowering checker `lowerOk(E, G0) = true`
  that decides node-by-node correspondence against `E` (the `korrOk`
  discipline applied to the first step). The Rust backend does NOT define
  the source semantics; a Rust-side "lowering" without a passing `lowerOk`
  is refused, never used as a worklist.
- **Lowering SCFG → machine bytes** is validated per §4: each SCFG op maps
  to a validated instruction sequence (decoder-checked bytes, lane 272's
  `Ausfuehrung.lean` semantics), register allocation maps SSA names to
  registers/spills (§3.5), and block layout maps CFG edges to
  `jump32`/`jumpIf32`/`call32`/`ret` displacements resolved against the
  final image (lane 276's `IMAGE-ABI` owns addresses/relocations; SCFG owns
  only the graph).

## 2. The certificate interface

One certificate kind, three layers. The Rust backend emits all three; Lean
checks all three; NOTHING else about the optimisation is trusted.

### 2.1 Layer A — local rewrite certificate

For peephole-style (single-block, bounded-window) steps: a list of rewrite
records. Each record:

```
{ block, window_before : List Op, window_after : List Op,
  rule_id, substitution, side_conditions_checked }
```

- `rule_id` names a rule in the REVIEWED rule register (phase-B Lean file;
  each rule a proved lemma `window_before ⊑ window_after` over ARBITRARY
  operand values — see the example §6).
- `substitution` instantiates the rule's metavariables; `side_conditions_checked`
  is the DECIDED evidence (boolean checks the validator re-runs): e.g. "def
  dominates use", "no intervening memory-token op", "widths equal", "FP
  rounding mode identical", "target register not live".
- Soundness shape (phase-B theorem, per rule, generic): for all states
  related before the window, every execution of `window_after` ends related
  to some execution of `window_after`'s source-model counterpart — with the
  memory token, flags/registers touched, fault behaviour and stop class
  preserved exactly (see §3 per family).

### 2.2 Layer B — dataflow/CFG certificate

For propagation, DCE, CSE, LICM, unrolling, inlining: claims that are not
local to a window. Each certificate entry is one of:

- **Available-value fact** (`avail at point p: v = expr over SSA names`):
  checked against a FORWARD decided analysis the validator RE-RUNS from the
  graph (not from Rust's claimed fixpoint): the validator computes
  reaching-definitions / available-expressions itself, structurally over the
  finite block list, and each rewrite site must cite a fact the recomputed
  analysis confirms. Rust's bitsets are hints that select the check order
  only.
- **Liveness fact** (`live at point p: set of SSA names`): same discipline,
  BACKWARD recomputation; DCE sites cite deadness the validator confirms.
- **CFG mapping** (for inlining, unrolling, LICM code motion): an explicit
  block/edge map old→new (inlining: callee blocks spliced with fresh SSA
  renames + return-block wiring + the §3-item-4 ghost call/return event
  records; unrolling: iteration copies indexed
  `0..k-1` + remainder; LICM: hoisted op + new preheader edge). The
  validator checks: every old edge has an image, every new edge comes from
  the map or the documented insertion, `phi` nodes at merge points are
  complete over the new predecessor list, and loop headers keep exactly one
  back edge.
- **Memory-token threading check** (all motion/duplication): the validator
  re-threads the token through the new graph and refuses if any load/store/
  atomic/call changed its relative order against another token op except
  where a cited commutativity lemma applies. Token-order preservation is
  NECESSARY but NOT SUFFICIENT under concurrency: it says nothing about
  another thread's writes. Every elimination or reordering of a memory read
  additionally needs one of §3 item 3's global interleaving conditions
  (exclusive ownership, held-lock stability, or immutability), decided by
  the validator from object references, whole-unit effect exports and lock
  data. Atomics, MMIO/device addresses, volatile-marked sites and
  foreign-observable memory never commute by token reasoning alone.

### 2.3 Layer C — duty/effect binding

Every certificate carries, per function, the source-computed data it must
respect (exported by Lean from `P`, never invented by Rust):

```
{ writes : Tab → Bool, gwrites : Glob → Bool,     -- from Signatur/V
  held_locks : List Lock, floor : Option Int,       -- haelt / boden
  duties : List DutyRef,   -- check/assume markers with their Lean-computed obligations
  fp_modes : rounding-mode scope,                  -- §3.10
  atomics : per-site ordering + footprint,         -- NutzerPflichtA / footprint rule
  costs : per-op declared costs + block sums }     -- Budget.lean
```

The validator checks each transformed op against this binding: a store to a
table the signature does not write is refused; a dropped `check` marker is
refused; a changed FP mode is refused; a weakened atomic ordering is refused;
a cost sum the certificate misreports is recomputed (refusal on mismatch, so
cost transfer reads validator-checked numbers).

### 2.4 Certificate soundness statement (phase-B proof obligation)

One generic theorem (not per program, not per optimisation instance). Its
premises bind BOTH ends to the source: the initial graph, every
optimisation step, and the final decoded bytes/image. There is no free
initial graph, no duty-only source binding, and no assumed refinement —
the refinement itself is proved through the per-access bridge (§4.3) and
the rule/motion lemmas (§3).

> For every source-computed unit `E` (the FULL declaration: code `P`,
> checker data, lock invariants, axiom ensures, declared starts, initial
> memory), let `G0` be the initial SCFG graph with `lowerOk(E, G0) = true`
> (decided: Lean-computed, or Rust-proposed and checker-validated per
> §1.3). For every optimisation sequence `G0 → … → Gn` with per-step
> certificates `C1 … Cn`, and every final image `Img` with decoded bytes
> `B`, if each `check_C(Ci, G(i-1), Gi, E) = true` and
> `layoutOk(Gn, B, Img) = true` (decoded bytes validate against `Gn`
> plus the lane-276 image/address/relocation binding), then every machine
> execution of `Img` refines some `GX` execution admitted by `E`'s model
> semantics with identical: memory footprint order (modulo proved
> commutations under §3 item 3's interleaving conditions), atomic
> observations, lock discipline, fault / stop outcomes, contract check
> outcomes at actual values, call-log order (`FolgeG`, via §3 item 4's
> ghost events), FP results bit-for-bit with control status (via §3
> item 9's obligations), and the three-level cost treatment of §3
> item 11.

Per-program instances (concrete `E`, `G0 … Gn`, `C1 … Cn`, `B`, `Img`)
are WITNESSES exercising the theorem, exactly as `kette_104_zeuge`
exercises `schlusssatz`.

## 3. Legality and proof obligations per starter optimisation

Each item names: the allowed certificate layers, the legality condition (what
the validator decides), and the proof obligation (what the phase-B Lean proof
shows, generically). "Profitability" (when to fire) is NEVER a legality
condition.

1. **Constant propagation (incl. copy propagation).** Layers A+B.
   Legality: every replaced use cites a validator-recomputed `avail`
   fact (`v = lit k` / `v = w`); the definition dominates the use on every
   CFG path (recomputed dominators); no intervening redefinition; width and
   signedness/unknown-ness preserved (an `unknown`-signed source keeps its
   `narrow` guard — propagation may not delete it).
   Prove: substitution of an available value preserves `exec` outcomes
   (pure-op congruence over arbitrary values; the cited fact rules out the
   only divergence source).
2. **Dead-code elimination, including faults.** Layers A+B.
   Legality: the removed op is pure (no memory token, no atomic, no call,
   no check/assume, no stop/trap, no FP op that can trap under the bound
   mode — see §3.10) AND its result is validator-confirmed dead at that
   point; stores/loads are never "dead" by liveness alone (address faults
   and ordering are observable — removal needs the concurrent-access proof
   of item 3's load rule or not at all).
   Prove: removing a pure dead op preserves states modulo the dead name
   (frame lemma); removing anything else is refused, so the faultSTOP
   behaviour (`hardware` vs `logik` classes, `Budget` stops) is unchanged
   by construction. Explicitly: a trapping op (divide, FP with traps
   enabled, bounds-checked access) is NOT pure for this rule even if its
   value is dead.
3. **CSE / redundant loads.** Layer B (+A for the rewrite record).
   Legality (ALL must hold, validator-decided):
   (a) the reused value cites a validator-recomputed `avail` fact for the
   identical expression — for pure (non-memory) expressions this suffices;
   (b) for LOADS additionally: same object reference, same width/alignment,
   no intervening token op on a possibly-overlapping object (validator
   re-threads the token; overlap decided from object + extent data,
   conservative `unknown-overlap ⇒ refuse`) — AND one of the following
   global interleaving conditions, because no thread-local token fact rules
   out another thread's write:
     - proved EXCLUSIVE OWNERSHIP: the object is thread-private (stack
       frame, fresh spill, unshared region) with no publication path on any
       path to the reuse site; or
     - HELD-LOCK STABILITY: a lock covering the object (declared in the
       footprint/lock data, layer C) is held continuously from the first
       load to the reuse, and every writer in the unit writes only while
       holding the same lock (checked from the effect exports of ALL
       functions — a whole-unit condition, not a local one); or
     - IMMUTABLE MEMORY: the object is read-only after initialisation
       (constant table, code, sealed write-once region) with no writer in
       any thread, including foreign/device writers named in the unit's
       bindings;
   (c) INELIGIBLE without an exact per-access concurrent equivalence
   theorem: atomic accesses, MMIO/device addresses, volatile-marked sites,
   and foreign-call-observable memory. Disjoint LOCAL objects alone never
   permit moving a SHARED access across publication (`publish`), a fence,
   or an acquire/release or lock boundary — release/acquire edges are
   ordering, and a load hoisted above the acquire that published its object
   reads a different GX execution.
   Prove: expression identity ⇒ value identity for pure ops (arbitrary
   operands); load identity ⇒ same read under the token-order premise PLUS
   the cited interleaving condition (no intervening write by ANY thread —
   ownership/lock/immutability is the proof's premise, discharged per
   instance by validator-checked evidence and proved once generically
   against the W/GX interleaving semantics, never against single-threaded
   memory).
4. **Selective inlining.** Layer B (+C duties).
   Legality: explicit block map (caller blocks + renamed callee blocks +
   return wiring); SSA renames fresh (validator checks capture-freedom);
   callee's duty list ⊆ caller's admitted duties at that site
   (`requires`/`ensures` markers preserved in order; `writes` footprint of
   callee ⊆ caller's declared `writes`; lock floor respected — callee
   taking a lock below the caller's floor is refused); recursion guarded
   by the `decreases`/depth discipline (no unguarded self-inline; bounded
   expansion only, else refuse); call-log preservation: the certificate
   carries an explicit GHOST-EVENT reconstruction — the inlined graph emits
   ghost call/return events (callee identity, actual argument values,
   return value, reason-channel outcome) in the source call-log order, for
   direct AND indirect calls. A changed physical call count with identical
   ghost logs is the legality condition; asserting identical contracts
   without the ghost events is refused, because contracts hold at their
   place (entry/return) with the actual values.
   Prove: call/return correspondence (argument passing + return-value +
   token threading = the `bsem_bindCall` shape lifted to SCFG); duties
   checked at the inlined site exactly as at a call; ghost events make the
   inlined execution's observable call log equal to the source's (same
   entries, same order, same values) — hence the `FolgeG` leg (order of
   calls in every thread's call log) and the entry/return contract legs
   transfer unchanged.
5. **Register allocation and private spills.** Layers A+C (+B map).
   Legality: a colouring map SSA-name → (register | spill slot) with:
   interfering live ranges differ (validator recomputes liveness and
   checks); spill slots are FRESH private objects (function frame, never
   address-taken, never named by any source extent — so no new sharing,
   no new race, no aliasing with any token op); spill loads/stores thread
   the token as ordinary frame accesses; callee-saved registers
   saved/restored on every path (validator checks the entry/exit edge
   pairs); flags clobbered only where dead.
   Prove: allocation is a renaming + private-memory introduction; private
   slots commute with all source-observable accesses (freshness ⇒
   disjointness ⇒ commutation with every interleaving — the per-access TSO
   bridge consumes exactly this lemma); observable register state at
   calls/returns matches the ABI map (lane 276 checks the bytes).
6. **Peephole lowering / instruction selection.** Layer A.
   Legality: each window cites a rule in the reviewed register; side
   conditions re-decided (widths, flag liveness for flag-setting forms,
   displacement fits signed-32, no memory-token op inside a pure rule's
   window).
   Prove (per rule, generic, arbitrary operands): window equivalence
   including flags touched, fault behaviour (e.g. `div` traps preserved —
   a peephole may not replace a trapping op by a non-trapping sequence
   with different `hardware`-stop behaviour), and cost annotation
   (the new window's declared cost is validator-recomputed, never claimed).
7. **LICM (loop-invariant code motion).** Layer B.
   Legality: the hoisted op is pure w.r.t. the loop (all operands defined
   outside or themselves hoisted; validator-recomputed invariance), the
   op cannot trap/stop in a way the loop might have avoided (speculative
   hoisting of a possibly-faulting op past the guard is REFUSED unless the
   op is proved non-faulting over its hoisted inputs — range evidence from
   source-computed facts, rechecked), memory-token ops hoist only under
   item 3's global interleaving evidence (ownership/lock/immutability,
   validator-decided — local disjointness alone never suffices for shared
   accesses), atomics/locks/calls/checks never
   hoist.
   Prove: hoisting = evaluation at an earlier point with identical inputs
   (invariance premise) + no new fault path (non-faulting premise); loop
   iteration count and exit values unchanged (header/back-edge structure
   preserved by the CFG-map check).
8. **Bounded loop unrolling.** Layer B.
   Legality: explicit unroll factor `k` + trip-count evidence (constant
   bound, or guarded remainder/overflow path preserved — the remainder
   block and its edge are part of the map, validator-checked); body
   duplicated `k` times with fresh SSA names; `phi` nodes at the remainder
   join complete; memory-token ops duplicated in order (each copy threads
   the token — unrolling never fuses two token ops into one); loop-carried
   values threaded through the copies.
   Prove: `k`-fold body concatenation = `k` iterations (induction on the
   block semantics, generic in the body); remainder path covers the
   non-multiple case; no new non-termination (bounded ⇒ the unrolled
   prefix terminates iff the first `k` iterations did; the loop-back edge
   keeps the original exit condition).
9. **Selective independent-lane SIMD.** Layers A+B+C.
   Legality (ALL must hold, validator-decided): lanes provably independent
   (per-lane object references disjoint — vectorised loop over one object
   with stride ≥ width, extent-checked; gather/scatter REFUSED in the
   starter profile); lane count × element width = vector width with
   alignment evidence (aligned or explicitly unaligned form —
   widths/alignments from the TSO-bridge atomicity table, lane 274);
   FP lanes keep per-lane rounding mode and exception/NaN behaviour
   IDENTICAL to scalar (no reassociation, no fast-math: `a+b+c` stays
   left-associated per lane; NaN payload/quieting per the IEEE mapping,
   lane 278; FP traps disabled or identically masked); no cross-lane
   token op inside the vectorised body; remainder (tail) loop preserved
   unless the trip count is a proved multiple; AND the four obligations
   below, each-capable of refusing independently:
   (a) FAULT ORDER: a fault/stop in lane `i+1` must not become visible
   ahead of lane `i`'s model outcome — masked-off lanes take the scalar
   fault path, faulting lanes retire in lane order, tails/faults that
   cannot be ordered take the scalar path;
   (b) VISIBILITY: the vector store's visibility order against concurrent
   observers must equal the scalar sequence's (no lane's write observably
   overtakes an earlier lane's where scalar order is observable; the
   per-access TSO bridge decides the exact rule — until it does, shared
   vector stores are refused);
   (c) TEARING: vector load/store tearing behaviour must equal the scalar
   sequence's — full-vector atomicity only where the bridge table grants
   it for that width/alignment, otherwise refused (or scalar tail);
   (d) FP CONTROL STATUS: the FP control/mask word and sticky exception
   flags after the vector op must equal the scalar sequence's outcome
   (per-lane exceptions combined in lane order; masked-off lanes
   contribute nothing; no flag a scalar lane would not set).
   CONDITIONAL REFUSAL: until the generic vector correspondence covering
   (a)–(d) is proved (lanes 274+278), vectorising faulting, volatile,
   atomic, MMIO or FP-trapping bodies is refused outright; the only
   admissible remainder is pure non-trapping integer lanes over
   validator-proved private-or-immutable memory with proved tail handling,
   each certificate citing the pending theorem as an OPEN obligation.
   Prove: lane-wise equivalence (each lane = the scalar op at those
   operands, arbitrary values) + independence (disjoint footprints ⇒ any
   interleaving linearises lane by lane, under item 3's interleaving
   conditions — lane-disjointness alone is not enough for shared objects)
   + fault-order preservation + visibility/tearing equivalence against the
   bridge table + FP control-status identity, each as a generic lemma over
   arbitrary lane values.
10. **Cross-cutting: FP rounding and order (applies to 1, 3, 6, 7, 9).**
    Original rounding mode and evaluation order are part of the checked
    state. Propagation/CSE/peephole/LICM may not reassociate FP ops, fuse
    multiply-add silently, narrow/widen precision, or move an FP op across
    a rounding-mode scope boundary (validator carries the mode scope from
    layer C). SIMD keeps lane associativity. The IEEE mapping (lane 278)
    is the reference; anything it does not cover is refused.
11. **Cross-cutting: stop behaviour, atomics, locks, costs, progress
    (applies to all).**
    - Stops: every op's stop class is checked data; no transformation
      deletes, introduces, or reclasses a stop (`hardware` stays
      `hardware`: fault elimination is not an optimisation).
    - Atomics: ordering only ever stays equal (never weakened); RMW
      success/failure distinctness preserved; no motion across a fence or
      lock op; observations cited in `NutzerPflichtA` terms (values a
      shared-atomic read may return) are preserved as a SET, never
      narrowed.
    - Locks: acquire/release pairs preserved on every path; no motion of
      any op into or out of a locked region except pure SSA ops under the
      token rule with the lock held at both points; ranks/floors
      rechecked (layer C).
    - Costs (three levels, never mixed):
      (a) SOURCE BUDGET semantics: `Op.cost`/`totalCost` (`Budget.lean`) —
      model-level stop/budget behaviour the goal theorem claims. Preserved
      because no transformation adds, removes or reclasses a stop, and the
      validator re-sums the declared costs (mismatch ⇒ refusal).
      Re-summing (a) is NOT x86 runtime costing;
      (b) MEASURED TARGET WORK: instruction counts, cycle estimates,
      profiler data — untrusted Rust-side numbers guiding profitability
      ONLY, never a soundness premise and never the bound;
      (c) PROVED MACHINE-WORK BOUND: the number a cost-transfer theorem may
      use — a Lean-proved bound from validated machine steps to model
      budget, consuming only validator-checked graphs plus named hardware
      bounds (lane 278's timing interface, cited but NOT assumed: until
      lane 278's bounds are proved, (c) is an OPEN obligation and no closing
      theorem claims budget transfer).
      Declining an optimisation (profitability says "no") keeps the original
      graph and its bounds — a declined transformation never weakens any
      bound.
    - Progress: CFG-map checks preserve every exit edge; unrolling keeps
      the exit condition; DCE never removes a spin/wait's load (token +
      atomic ⇒ not pure ⇒ refused); internal machine steps introduced by
      lowering (spill code, vector prologues) stutter only under the
      progress argument of §4.3.

## 4. How the validator fits together (no trusted Rust, no per-program rules)

### 4.1 Finite local rewrite checking

Layer-A rules quantify over arbitrary operand values but each rule instance
is FINITE: a bounded window, a substitution, decidable side conditions. The
validator needs no solver and no search: it looks up `rule_id`, applies the
substitution, re-decides the side conditions, and compares syntactic windows.
Soundness of the RULE is the proved lemma; soundness of the INSTANCE is
computation (`decide`). This is the `korrOk` precedent carried over: the
C-chain check walks every body with its printed rows and decides statement
by statement; the SCFG validator walks every block/window with its rewrite
record and decides window by window.

### 4.2 Dataflow certificates without trusted analysis

Rust ships its dataflow RESULTS as hints (bitsets, dominator trees, alias
answers). The validator treats every hint as a worklist seed and RECOMPUTES
the analysis from the graph with its own proved transfer functions over the
finite block/name sets:

- forward facts (availability, reaching definitions, invariance) by
  structural iteration to a fixpoint the validator itself detects
  (finiteness ⇒ termination, no fuel trusted);
- backward liveness likewise;
- each rewrite site then cites a recomputed fact — a wrong hint only costs
  time (recomputation rejects the site), never correctness.

The analysis transfer functions are proved sound against SCFG block
semantics once (phase B); every instance reuses that proof.

### 4.3 CFG mapping and block stuttering

Motion/duplication certificates give the block/edge map explicitly (§2.2).
The validator checks map totality/shape syntactically. Semantically, refined
blocks may take several machine steps for one model step (spill code, vector
prologue, lowered multi-instruction sequences): this is BLOCK STUTTERING —
proved via a step-indexed (stuttering) refinement: the new graph's steps map
to zero-or-one old-graph steps, with a ranking argument (bounded sequence
length, statically known from the window/map) ruling out infinite stutter.
Divergence introduction is thereby refused by shape: every inserted sequence
is straight-line and finite, loop structure changes only via the checked
unroll/inline maps, and no map creates a new back edge.

### 4.4 Register allocation inside the same validator

Allocation is not a separate trusted pass: it is a certificate (colouring
map + spill object declarations + save/restore edge evidence, §3 item 5)
checked by the same validator binary. Its distinctive proof burden —
private-spill freshness ⇒ disjointness ⇒ commutation with all concurrent
observations — is discharged once generically against the TSO-bridge memory
relation (lane 274's per-access table), then applied per instance by
computation (freshness is syntactic: the spill object appears in no source
extent and no other allocation map).

### 4.5 Why no per-program Lean rule is ever needed

Rules quantify over syntax/values (`∀ windows`, `∀ expressions`, `∀ colourings
satisfying the side conditions`); INSTANCES supply the values. Lean checks
the instance by reduction; the human reviews the rule. A certificate that
required a fresh Lean proof per compiled program would be a second compiler
written in tactics — refused as an architecture. Witness programs with
concrete certificates exercise the generic theorems and populate the test
corpus; they determine nothing about acceptance.

## 5. Required exported interfaces and suggested phase-B ownership

### 5.1 Lean-exported interfaces (computed from source, consumed by validator)

| Interface | Content | Producer (exists / to build) |
|---|---|---|
| `DutyExport` | per-function duty markers: checks, assumes, `requires`/`ensures` references, stop classes | Lean elaborator + GabbroV bridge (extend by construct) |
| `EffectExport` | `writes`/`gwrites`, consumes/produces marks, lock `haelt` + `boden` | `Syntax.lean` signatures → exporter |
| `AtomicExport` | per-site ordering, footprint objects, `NutzerPflichtA` value sets | footprint rule + `NutzerPflichtA` (O25c) |
| `FpExport` | rounding-mode scopes, FP op sites with widths | IEEE model (`Gleitkomma*.lean`) |
| `CostExport` | level (a) declared costs + block sums (validator-resummed); level (b) measured work carried opaquely, never read by soundness; level (c) machine-work bound — OPEN obligation with lane 278 | `Budget.lean` (`Op.cost`, `totalCost`) for (a); (b)/(c) new |
| `LowerMap` | source-node → SCFG-op anchors (memory/call/check/atomic/lock/stop) | new Lean lowering (lane 277 with this lane's §1) |

Wire format: Lean-computed data printers (same discipline as `corrlean.rs`'s
`KCert` section: one line per function, exporter map included, layout from
the emitter) — but consumed by the SCFG validator, not by `korrOk`. The
printer stays untrusted; the validator re-parses and re-checks (the A2
precedent: `parseC` + guardian re-emit comparison).

### 5.2 Suggested phase-B file ownership (one topic per file/lane)

| File / area | Content | Note |
|---|---|---|
| `grammatik/Grammatik/X86/SCFG.lean` | SCFG syntax + block semantics over `exec`-shaped worlds | needs Lean; refines to `P`, not standalone |
| `grammatik/Grammatik/X86/SCFGZert.lean` | layer A/B/C checkers (`check_C`) + soundness framework | `korrOk` discipline: structural, `decide`-settled |
| `grammatik/Grammatik/X86/OptRegeln.lean` | reviewed rule register (peephole + motion lemmas) | one lemma per rule, arbitrary operands |
| `grammatik/Grammatik/X86/RegAllok.lean` | colouring/spill certificate + freshness-commutation lemma | consumes lane-274 memory relation |
| `grammatik/Grammatik/X86/SIMDProfil.lean` | vector profile: widths, alignment, lane-independence rule | jointly with lanes 274 + 278 |
| `crates/gabbro-check/src/x86/scfg.rs` | untrusted SCFG builder + certificate emitter (hints only) | unwired until Lean side reviewed (wave-A rule) |
| `dokumente/x86/QUELLBRUECKE.md` (lane 277) | source→SCFG lowering proof, duty-export wiring | closes §5.1 `LowerMap` + `DutyExport` |
| `dokumente/x86/TSO-GX-BRUECKE.md` (lane 274) | per-access TSO table, spill-freshness consumer lemma | §3 items 5/9 depend on it |
| `dokumente/x86/FLOAT-ZEIT.md` (lane 278) | IEEE mapping, trap/mask scope, cost-bound interface | §3 items 10/11 depend on it |
| `dokumente/x86/IMAGE-ABI.md` (lane 276) | block layout, displacement resolution, entry binding | consumes validated SCFG+allocation maps |

Phase-B gating (from the plan §4, order): SCFG syntax/semantics →
decoder+memory relation → pilot through bytes with an altered-bytes refusal
witness → concurrent mappings (spill/SIMD need these) → family extensions →
final-image theorem. Optimiser certificates slot into step 6's closing
theorem as the "untrusted middle arrow with checked certificate" premise —
the `korrOk … = true` hypothesis lifted from C rows to the E-anchored chain
of §2.4 (`lowerOk(E, G0)`, per-step `check_C`, `layoutOk(Gn, B, Img)`).

## 6. Example certificate (transformation over arbitrary operand values)

Copy propagation through a redundant add, generic in the values. Before
(SCFG, one block, memory token `m0 → m1 → m2`):

```
block b0:
  v1 = add w64 a b          [anchor: src Stmt s1]
  v2 = copy w64 v1          [rule copyintro, avail: v1 = add a b]
  v3 = add w64 v2 c         [rewrite site: replace v2 by v1]
  st64 [obj O, +d] v3, m1 → m2
```

Certificate records:

```
A1 { block b0, window_before [v2 = copy v1],
     window_after [], rule_id copyelim,
     subst {v1 ↦ v1, v2 ↦ v2},
     side { def(v1) dominates use, v1 live-through, widths w64 = w64 } }
B1 { avail at (b0, idx 2): v1 = add(a,b),   -- validator recomputes
     avail at (b0, idx 2): v2 = v1,         -- validator recomputes
     token threading unchanged (no token op touched; pure rewrite, so
     §3-item-3 interleaving evidence is not needed — no memory op moved) }
C1 { writes/gwrites/footprint: unchanged (pure ops only);
     costs: before 1+1+1, after 1+0+1, validator-resummed
     (level (a) declared costs; no level-(b)/(c) claim) }
```

`copyelim` (rule register): `∀ w v1 v2 rest, copy v2=v1 followed by a use
of v2 with no intervening def ⊑ substitution [v1/v2]` — proved once over
arbitrary `v1`'s value (expression congruence; the available-value premise
is the validator-checked side condition, not a proof assumption). After:

```
block b0:
  v1 = add w64 a b
  v3 = add w64 v1 c
  st64 [obj O, +d] v3, m1 → m2
```

The validator re-decides domination/availability/widths, re-threads the
token (identical), re-sums costs, and confirms no anchor, duty, atomic,
lock, FP-mode or stop-class field moved. A wrong `subst` (e.g. replacing
across a redefinition) fails the recomputed `avail` fact: refusal, not
miscompilation.

## 7. What local rewriting cannot handle (explicit non-goals)

1. **Speculative faulting motion.** Hoisting a possibly-trapping op above
   its guard, or deleting a fault that the source model produces
   (`hardware`-class outcomes), is not a window rewrite: it needs the
   non-faulting evidence of §3 item 7 or it is refused. Fault behaviour is
   never "optimised".
2. **Memory reordering across unknown overlap, across threads, or across
   publication/acquire/release.** Without the §3-item-3 interleaving
   evidence (exclusive ownership, held-lock stability, immutability) two
   token ops do not commute — even for disjoint local objects when the
   access is shared and a release/acquire edge publishes it. Alias answers
   from Rust are hints; the validator decides overlap AND sharing from
   object references, whole-unit effect exports and lock data, or refuses.
3. **Atomic-order weakening, fence removal, lock-region motion.** No local
   rule weakens an ordering, removes a fence, or moves code across a
   lock/fence boundary. Ever. These are layer-B+C checks with duty
   evidence or refusals.
4. **FP reassociation / precision change / cross-mode motion.** Not
   expressible as a window rule in the starter register; any such rule
   proposal must go through lane 278's IEEE mapping first.
5. **Interprocedural facts without a map.** No propagation, CSE or DCE
   across a call without the call's duty/effect export (layer C) and, for
   motion into/out of a callee, the inlining map. Side exits (`or R`
   reason channels, `Endblock.bindAxiomElse` shapes) are part of the map.
6. **Layout/address-dependent rewrites.** Displacements, code addresses,
   object base addresses and relocation outcomes belong to lane 276: no
   SCFG rule mentions an address constant derived from layout. Position-
   dependent peepholes are refused at this layer.
7. **Profitability and heuristics.** Inlining thresholds, unroll factors
   beyond the evidence, vectorisation cost models, spill heuristics: all
   untrusted, all outside every soundness statement. A heuristic that
   always says "no" yields slow correct code; the architecture prefers
   that to a fast unsound rule.
8. **Whole-program/link-time claims.** Cross-unit optimisation needs the
   second goal statement (`GabbroZielVerbund`) as its enclosing premise;
   this document covers single-unit certificates only. Linking interaction
   is lane 277/274 territory with the O28 obligations.
9. **Vectorisation ahead of its correspondence.** Until the generic vector
   correspondence of §3 item 9 (a)–(d) is proved, vectorising anything but
   pure non-trapping integer lanes over proved private-or-immutable memory
   is refused; each admitted certificate cites the pending theorem openly.

## 8. Review checklist for phase B (acceptance of this architecture)

- [ ] SCFG formalisation refines to `P`/`GX` executions (no standalone
      mini-language theorem presented as correspondence).
- [ ] Initial-graph provenance closed: `G0` Lean-computed or `lowerOk(E, G0)`
      proved; final theorem binds the optimisation sequence AND the decoded
      bytes/image to the full unit `E` (§2.4) — no free initial graph, no
      duty-only binding, no assumed refinement.
- [ ] Every rule lemma quantifies over arbitrary operand values with a
      jointly inhabited non-degenerate source-program witness per gate.
- [ ] Validator recomputes (not trusts) dataflow facts, token threading,
      costs, dominators and liveness.
- [ ] Every load elimination/motion cites ownership, held-lock stability or
      immutability (validator-decided, whole-unit where required);
      atomics/MMIO/volatile/foreign ineligible without an exact per-access
      concurrent equivalence theorem; no shared motion across
      publication/acquire/release on local-disjointness evidence alone.
- [ ] DCE/fault, atomic-ordering, lock-region, FP-mode and stop-class
      refusals each have a planted-defect probe (refused certificate).
- [ ] Inlining carries ghost call/return events (direct and indirect) with
      actual values; call-log order and `FolgeG` verified preserved.
- [ ] Spill-freshness commutation proved against the per-access TSO
      relation (lane 274), not against an abstract memory.
- [ ] SIMD fault order, visibility, tearing and FP control status proved;
      remainder cases covered; conditional refusal recorded until the
      generic vector correspondence (lanes 274+278) closes.
- [ ] Three cost levels separated in every certificate and proof: (a)
      re-summed declared costs, (b) opaque measured work, (c) machine-work
      bound OPEN with lane 278 — declining never weakens a bound.
- [ ] Stuttering/progress argument bounds every inserted straight-line
      sequence; no new back edge without a checked map.
- [ ] `#print axioms` of the generic soundness theorem is the standard
      triple; no `sorry`/`admit`/`native_decide`/new axiom/`unsafe`.

---

*CUTS (this document proves nothing; it specifies): no SCFG Lean definition,
no rule lemma, no checker Bool (`lowerOk`, `check_C`, `layoutOk`), no
refinement theorem, no decoder, no TSO table, no lowering function, no
machine-work bound (c) and no cost-transfer proof is given here. All are
phase-B obligations with the owners in §5. Open until proved: the lowering
checker, the per-access concurrent equivalence for eligible atomics, the
generic vector correspondence (fault order, visibility, tearing, FP control
status), the ghost-event call-log preservation, and lane 278's timing
bounds. The pilot instruction subset stays `Typen.lean`'s `Befehl`; wider
widths/forms, gather/scatter, fast-math and link-time optimisation remain
refused until their lanes close.*
