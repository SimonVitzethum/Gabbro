# MUSE-REPORT-325: High-runtime-performance revision of the direct compiler design

Scope: root `DIRECT-COMPILER-DESIGN.md` only (plus this report). Documentation-only
revision of the accepted lane-323 design (506 lines, ACCEPT per independent review 324)
toward the latest user steering: HIGH RUNTIME PERFORMANCE within a FEASIBLE COMPLETE
SELECTED architectural hardware model, plus fast compilation including mandatory
validation. No source, ledger, Lean, Rust, emitter or central-doc edits. No builds run
(docs-only; no Lean/cargo changes exist to check).

## Factual material checked

- `DIRECT-COMPILER.md` (central ledger; lanes 269–324 states; author-325/reviewer-326 note).
- `lanes/323.md` (original owner task, full), `lanes/325.md` + `lanes/326.md` (this
  revision task and its reviewer task).
- `messung/muse/MUSE-REPORT-324.md` (independent ACCEPT review; per-charge findings all
  PASS; three immaterial nits).
- `dokumente/x86/BYTE-PILOT.md` (full; canonical encodings/lengths; non-canonical refusal).
- `DIRECT-COMPILER-DESIGN.md` prior snapshot (506 lines) as the preserved base.
- Spot-checked `dokumente/x86/EMITTER-INVENTAR.md`, `FLOAT-ZEIT.md` references via the
  existing design's citations (no doc edits there; links re-verified mechanically).

## What changed (506 -> 699 lines, all prose, all PROPOSED/OPEN)

1. Title + header + §0/§1: performance priority stated first. The 14-form pilot is
   declared proof bootstrapping only, never the performance ceiling; no form minimized
   for easy proof; no universally maximal claim across CPUs/workloads.
2. New §2B (efficient encodings/address forms): MOV imm32 zero-extended / sign-extended
   imm32, ADD/SUB/CMP imm8/imm32, disp0/disp8/disp32, base+index*scale+disp, RIP-relative
   image references, short Jcc/JMP + bounded conservative branch/layout relaxation
   (wide-first, fuel-bounded compression rounds; wider form always allowed on exhausted
   fuel; every layout change forces full final-byte re-decode + `layoutOk` revalidation).
   All PROPOSED, not current support; decoder refusal posture unchanged.
3. New §2C (priority/tradeoff table): portable scalar profile, selected high-performance
   CPU profile, exact concurrency/device/interrupt profiles (correctness-enabling, not
   speedup), deferred AVX-512/FMA-as-fusion — with modelling cost vs measured gain vs
   compilation work. Model covers exactly the emitted forms incl. async events; no claim
   the Lean model matches physical silicon.
4. New §3A (scalar selection/allocation/addressing): 3-operand IMUL, LEA for address
   arithmetic, shift semantics, no-speculation DIV, SETcc/CMOV only where measured
   suitable (register-only CMOV first; memory-source CMOV refused until its generic
   unselected-fault proof lands), liveness-aware flags/copies, linear-scan allocation
   with private spills, smallest-first addressing. Bounded fuel; exhausted fuel keeps a
   valid simpler tile.
5. §6 rewritten as first-class SIMD milestone: SSE2 foundation, Tier 1 must beat pilot
   on scalar workloads (measured), Tier 3 AVX2 as optional NAMED-CPU profile with
   CPUID/XCR0/context proofs and SSE2 fallback, BMI/POPCNT/TZCNT/LZCNT only where a
   real workload justifies modelling cost, AVX-512/FMA-as-fusion deferred optional —
   neither excluded nor required. FP contracts unchanged; FMA only for exact permitted
   source semantics; no fast-math.
6. New §7A (performance model/tuning table, tuning-only): latency/throughput/port
   pressure, register pressure, alignment/code size, branch predictability,
   microarchitecture traits — used only to choose among already-valid translations;
   never a proof premise; no pipeline/cache/transistor modelling required. Time
   guarantees stay separate (named conservative hardware assumptions + proved work
   transfer). Tune data versioned in the hardware profile; wrong data slows code only.
7. §10: runtime performance measured on the same workloads as compile speed; mix must
   cover scalar/vector/atomic/memory-bound; codegen baselines (pilot lowering + external
   reference) labelled MEASURED only after implementation; full accepted-image latency
   is the reported figure; safe incrementality measured with refusal probes.
8. §11: high-performance deliverable gates (measured comparisons per feature, SIMD and
   AVX2 gates, no arbitrary instruction counts or timing promises).
9. Review-324 nits repaired: `schnell`/`optimiert` -> English `fast`/`tuned` identifiers;
   stale "lane-272 work" phrasing corrected (272 merged; per-form correspondence OPEN).
   Link recount note (23 vs 26) moot: this revision has 29/29 resolving links.
10. CUTS extended: new sections are intended obligations, not observations; no measured
    performance; no weakened assumption.

## Consistency kept

- §2 14-form pilot table, registers, conditions, memory, permission/fault/flag facts:
  untouched. Planned rows §§3–6 keep mnemonic/forms/reason/priority/OPEN obligations.
- Trust chain unchanged: Lean first, Rust untrusted, `valX86_sound` derived refinement,
  `schluss_x86` takes no refinement premise, default refusal, optional-opt fallback vs
  mandatory-validation refusal, `gabbro_ziel` axioms exact, no program-name rules,
  `FolgeG` ghosts, budget correspondence OPEN, CAS discipline kept.
- No source/hardware/software assumption weakened for speed — stated in header, §2C,
  §7A and CUTS.

## New definitions/theorems

None. Docs-only revision; no Lean file added or changed.

## Last build result

`./lean-bau` not run: documentation-only task with no Lean changes (per task: no
gratuitous builds). Link check: 29/29 relative targets resolve (script over
`DIRECT-COMPILER-DESIGN.md`). German-identifier grep: `schnell`/`optimiert` 0 hits;
`maximal` only in denial sentences. Line count 699.

## CUTS / open

No theorem proved; no decoder/validator/refinement/cost result; no runtime or compiler
speed measured. Reviewer 326 reads the fresh exact snapshot after commit; any findings
it returns on this candidate remain valid requirements for follow-up. No prior-326
findings existed at write time (review 326 is scheduled after this candidate).

## Task-statement remark

Nothing in the task appeared wrong. The (a)–(f) additions mapped cleanly onto the
existing section structure (§2B/2C/3A/6/7A/10/11) without renumbering or weakening.
