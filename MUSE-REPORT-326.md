# MUSE-REPORT-326: Independent high-performance hardware-design revision review

Scope: exact candidate snapshot of lane 325 under `.tmp/review/author-325`
(`DIRECT-COMPILER-DESIGN.md` 698 lines, `MUSE-REPORT-325.md`,
`OWNER-TASK.md`, `PATCH.diff`, `BUILD-EVIDENCE.json`) pinned by
`.tmp/review/SNAPSHOT.json`. Documentation-only review; no Lean, Rust,
emitter, ledger or central-doc edits; no builds run.

## Candidate identity

- Candidate HEAD: `0b4b2bc0d28d24451608043c4c878bc138b70881`
  (owned files only: `DIRECT-COMPILER-DESIGN.md`, `MUSE-REPORT-325.md`;
  `clean: true` per SNAPSHOT.json; BUILD-EVIDENCE.json commits exactly
  those two files).
- Review base: this clone HEAD `55f533ac` (branch `muse/326`).
- Base design: accepted lane-323 plan (506 lines, ACCEPT per review 324);
  this candidate is the user-steered high-performance revision
  (506 -> ~699 lines, all prose, all PROPOSED/OPEN).

## Factual material actually checked

- `grammatik/Grammatik/X86/Typen.lean` (full, 87 lines): 14 `Befehl`
  constructors, 16 registers, 16 `Bedingung` codes, `Flags.af : Option Bool`,
  per-byte `Speicher` + R/W/X, CUTS.
- `dokumente/x86/BYTE-PILOT.md` (full, 31 lines): canonical encodings,
  lengths, non-canonical refusal.
- `messung/muse/MUSE-REPORT-324.md` (full): prior ACCEPT + 3 nits.
- `messung/muse/MUSE-REPORT-272.md` (head + findings): per-form step
  equations proved; decoder/TSo-refinement/correspondence open.
- `DIRECT-COMPILER.md` ledger (lane states 272/274/279/283/291 merged).
- `lanes/325.md` + `lanes/326.md` (owner and reviewer tasks, full).
- Candidate PATCH.diff (full, 458 lines) and MUSE-REPORT-325 (full).
- Mechanical checks over the candidate: 29/29 `](...)` relative links
  resolve (0 bad, external Intel/AMD/LLVM refs excluded); German
  identifier grep (`schnell`/`optimiert`) 0 hits; `maximal` only in
  denial sentences; no fabricated speed numbers; non-ASCII is inherited
  typography (§, em/en dashes, arrows, logic symbols), no German text.

## Per-charge findings

1. High-performance priority without proof minimization: PASS. Title,
   header, §0/§1 state HIGH RUNTIME PERFORMANCE first; 14-form pilot
   declared proof bootstrapping only (§2A kept, §2 untouched); no form
   kept small for easy proof; no universal maximal claim (denials in
   header, §2A, §2C, §6, CUTS).
2. Efficient encodings/address forms (§2B): PASS. MOV imm32
   zero-extending (no REX.W, B8+rd, 5 bytes) with dead-upper-half side
   condition, sign-extended imm32 (REX.W C7 /0), imm8 (83 /n) / imm32
   (81 /n, rax short forms) with sign-extension + per-width flag
   identity, disp0/disp8/disp32 smallest-first, base+index*scale+disp
   (index never rsp), RIP-relative image-only, short Jcc/JMP rel8 with
   layout-stability condition, XOR zero idiom with flag-liveness proof.
   All rows carry explicit width/register/flags/canonical-address/fault
   rules and OPEN status; decoder refusal posture unchanged. Encoding
   facts are standard x86-64 and correctly stated as PROPOSED.
3. Branch/layout relaxation: PASS. Wide-first, fuel-bounded compression
   rounds, valid wider form always allowed on exhausted fuel (build can
   never fail, only stay longer), every layout change forces full
   final-byte re-decode + `layoutOk` revalidation. Bounded and
   compiler-speed safe as the owner task requires.
4. Scalar selection (§3A): PASS. 3-operand IMUL, LEA preference, shift
   count-masking, DIV never speculated/hoisted, SETcc/CMOV only where
   measured suitable with register-only CMOV first and memory-source
   CMOV refused until its generic unselected-fault proof lands,
   liveness-aware flags/copies, linear-scan + private spills +
   smallest-first addressing, fuel-bounded with valid fallback tile.
5. SIMD milestone (§6): PASS. First-class milestone, Tier 1 scalar must
   beat pilot measured, Tier 2 packed-integer with lane-separation +
   atomicity/tearing + private/tail + fault-order gates, Tier 3 AVX2 as
   optional NAMED-CPU profile with CPUID/XCR0/context proofs and SSE2
   fallback, BMI/POPCNT/TZCNT/LZCNT only where a workload justifies
   cost, AVX-512/FMA-as-fusion deferred optional (neither excluded nor
   required). FP contracts unchanged, FMA only for exact permitted
   source semantics, no fast-math. Nothing the language needs is
   dropped (§6 exclusion list retained).
6. Performance model (§7A): PASS. Tuning-only table (latency/throughput/
   port pressure, register pressure, alignment/code size, branch
   predictability, microarchitecture traits) kept in a separate file,
   never imported by proofs; wrong data slows code only. Time
   guarantees stay separate (named conservative assumptions + proved
   work transfer, §9/FLOAT-ZEIT §8). No pipeline/cache/transistor
   modelling required; no timing promise.
7. Priority/tradeoff table (§2C): PASS. Portable scalar, selected-CPU,
   exact concurrency/device/interrupt (correctness-enabling, not
   speedup), deferred rows with modelling cost vs measured gain vs
   compilation work; tuned only on measurement; no silicon-matching
   claim.
8. Invariants/contracts/costs/faults/call logs/TSO/async/full chain:
   PASS. All inherited unchanged: entry-only ranges, writer blackout,
   held-section limits, shared-load reuse discipline, ghost call/return
   events with actual values, per-access TSO refinement (no blanket
   W/DRF-SC, no G-step transaction), O-align/O-access, seq_cst
   over-approximation documented, CAS attempt-bound discipline,
   `FortschrittG` enabledness only, ghost budget correspondence OPEN,
   source-computed exports, `valX86_sound` derived refinement,
   `schluss_x86` takes no refinement premise, `gabbro_ziel` axioms
   exact, no program-name rules, whole-executable coverage with
   refuse-if-unmodelled, M140, N575–N577, N571/N463/N506, f32 bridge
   refusal, OBS-5, `GabbroZielVerbund` linking OPEN.
9. Fast compilation/validation (§§8–9): PASS. Unchanged: bounded fuel
   everywhere, no exponential search, linear-scan default, on-demand
   analyses, deterministic parallel/incremental, caches untrusted,
   hashing no theorem, validator failure refuses, compiler budget
   distinct from source run budget, proved-once executable checkers,
   data certificates, no `native_decide`, kernel-accepted `decide`
   counts.
10. Measurement honesty (§§10–11): PASS. Numbers UNKNOWN, no ms/speedup/
    instruction-count promise; runtime measured on same workloads as
    compile speed; mix must cover scalar/vector/atomic/memory-bound;
    pilot-lowering + external-C baselines labelled MEASURED only after
    implementation; full accepted-image latency reported; few stable
    modes (`fast`/`tuned`) with identical acceptance; per-feature
    measured deliverable gates; no gate passable by a bare count.
11. Pilot exactness: PASS. §2 table matches all 14 constructors,
    mnemonics, forms and BYTE-PILOT lengths; registers/conditions/
    memory/permission/flag facts exact; helpers denied ISA status;
    correspondence OPEN. The §2 rewording ("lane 272 proved the pilot
    vocabulary and execution skeleton, not the chain correspondence")
    preserves the correct posture: chain correspondence genuinely OPEN
    per report-272 §"still open" list; "skeleton" slightly understates
    the proved step equations but claims nothing unproved (nit only).
12. Scope/language/links: PASS. Only the two owned files changed;
    English throughout; prior review-324 nits repaired (`fast`/`tuned`,
    272 phrasing, link count now verifiably 29/29).

## Nits (not material, no repair owed)

- Report-325 says "699 lines"; the candidate file reads 698 lines.
  One-line recount difference, immaterial.
- §2 "execution skeleton" understates report-272's proved per-form
  step equations; posture (correspondence OPEN) is correct, so no
  finding.

## New definitions/theorems

None. Docs-only review; no Lean file added or changed.

## Last build result

`./lean-bau` not run: documentation-only review with no Lean changes;
baseline untouched (same standing as the author lane).

## CUTS

No theorem proved; no decoder/validator/refinement/cost result; no
runtime or compiler speed measured. ACCEPT covers only this bounded
detailed plan, not final translation validation.

CANDIDATE: 325 0b4b2bc0d28d24451608043c4c878bc138b70881
VERDICT: ACCEPT
