# MUSE-REPORT-328: Independent safety-first practical-performance scope review

Scope: this report only (`MUSE-REPORT-328.md`). Documentation-only independent
review of the exact lane-327 candidate under `.tmp/review/author-327`
(`DIRECT-COMPILER-DESIGN.md` 761 lines, `MUSE-REPORT-327.md`, `OWNER-TASK.md`,
`PATCH.diff`, `BUILD-EVIDENCE.json`) pinned by `.tmp/review/SNAPSHOT.json`.
No Lean, Rust, emitter, ledger, design or central-doc edits; no builds run
(docs-only candidate, nothing to build).

## Candidate identity

- Pinned candidate HEAD: `03ab77b03e2f8de9b26f02ec5eb13a177fbcacdc`
  (owned files only: `DIRECT-COMPILER-DESIGN.md`, `MUSE-REPORT-327.md`;
  `clean: true` per SNAPSHOT.json; PATCH.diff touches exactly those two files).
- Review base: this clone HEAD `82e7efb5` (branch `muse/328`); the pinned
  commit is not fetchable here (no network for lanes), so the review reads the
  exact pinned files under `.tmp/review/author-327`, same posture as review 326.
- Base design: lane-325 high-performance revision (ACCEPT per review 326);
  this candidate is the safety-first priority revision (+70/-7 owned diff).

## Factual material actually checked

- Candidate `DIRECT-COMPILER-DESIGN.md` (full, 761 lines) and PATCH.diff
  (full, 216 lines); `MUSE-REPORT-327.md` (full).
- `OWNER-TASK.md` for lane 327 (full) and this lane task.
- `messung/muse/MUSE-REPORT-325.md` + `MUSE-REPORT-326.md` (full).
- `grammatik/Grammatik/X86/Typen.lean` (14 `Befehl` constructors, 16
  registers, 16 `Bedingung` codes, `Flags.af : Option Bool` — all match the
  §2 table); `Ausfuehrung.lean` (`schritt` + per-form theorems present);
  `Codec.lean` (`roundtrip*` + `roundtrip_len_ok` at line 581 present).
- `messung/muse/MUSE-REPORT-272.md`, `MUSE-REPORT-279.md`
  (bounded `schritt` equations proved; generic `roundtrip`/`roundtrip_len_ok`
  proved), `MUSE-REPORT-317.md` (head).
- Mechanical checks over the candidate file: 31/31 `](...)` relative links
  resolve (0 bad; external Intel/AMD/LLVM refs excluded); German-identifier
  grep 0 hits; `maximal`/`maximum` only in denial sentences; `90%` only in
  denial sentences; no speed numbers, no LOC estimates, no fabricated
  measurements.

## Per-charge findings

1. Clear primary priorities: PASS. Header states safety-first first: the
   "last 10%" is qualitative prioritisation, not a number; completion is FULL
   proved validation and FULL safety for EVERY selected profile and EVERY
   source construct. No 90% proof, no 90% safety, no weakened safety level.
2. Essential scope retained: PASS. §2D table keeps scalar lowering (§3),
   immediates/addressing/branches (§2B), allocation/optimisation/`-O3` scopes
   (§§7, 8), IEEE binary64 baseline (§4), language-needed concurrency/atomics/
   fences (§5), emitter-scope calls/ABI/runtime/entry/hardware rows — each
   with proof gate and first-priority rationale.
3. SIMD practical milestone retained: PASS. SSE2 selected integer/scalar-FP +
   AVX2 integer as optional CPU tier stays an Essential row and §6 keeps
   Tiers 1–3 with lane-separation, atomicity/tearing, CPUID/XCR0/context and
   enabled-state gates; the row stays only if its generic proof closes.
4. Deferred scope neither mandatory nor claimed proved: PASS. BMI/POPCNT/
   bit-scan/shuffle, AVX-512, matrix/AMX, APX, crypto/SHA/AES, FMA-as-fusion,
   gather/scatter/compress, cache hints/NT stores/string specialisations are
   Deferred rows with postponement reasons; "do not claim any of it could be
   emitted now" is explicit; FMA-rounding and NT-ordering proof notes are
   stated (no TSO shortcut, no free-optimisation fusion).
5. Per-form obligations + generic final-byte validation: PASS. Admission test
   (7 conjunctive gates) demands observable equivalence with actual
   parameters/results/faults/flags/FP rounding/ordering/async, listed
   state/fault/concurrency/FP/context/enabled-state obligations,
   checker-reuse decision, independent proof plus negative cases, and the
   certified cheaper translation retained until all correspondence/cost/stop
   gates pass. Inherits §§3–6 OPEN rows, `valX86_sound` derived refinement,
   `schluss_x86` with no refinement premise, mandatory full validation.
6. No inferred ensures, no warning downgrade: PASS. Header and §7 keep actual
   parameters/results, never derive `ensures`, refusal never becomes warning;
   mandatory validation failure refuses outright.
7. `-O3`-like not unsafe fast math: PASS. §2D states the hard `-O3`-like plan
   is an effort/quality goal, not external-compiler unsafe fast-math
   equivalence; §4 refusals (contraction, reassociation, RCPSS-for-DIV,
   width promotion) unchanged.
8. Tuning untrusted, fuel fallback certified: PASS. §7A tuning table never a
   proof premise; wrong data slows code only; optional-pass fuel exhaustion
   yields certified cheaper output while required proof failure always
   refuses, never bypasses; caches untrusted; Lean-first mandatory untouched.
9. Pilot status accurate, no full-compiler/hardware claim: PASS. §2 names
   bounded `schritt` equations (lane 272) and codec `roundtrip`/
   `roundtrip_len_ok` (lane 279) as PROVED bounded abstract helpers — verified
   against reports 272/279 and the Lean tree — while physical-hardware/source
   correspondence, per-access TSO bridge and full chain stay OPEN. CUTS
   claims no proof and no measurement.
10. Fast compilation concrete, no guarantee cuts: PASS. Deterministic bounded
    fuel, explicit invalidation, safe incrementality, deterministic
    parallel/parallel-merge, untrusted caches, compiler budget distinct from
    source run budget — all inherited unchanged; stop rule keeps construct
    support complete.
11. Table, links, emitter scope, honesty: PASS. Priority table has
    scope/rationale/gate/postponement columns; 31/31 root-relative links
    resolve; scope is emitter-construct driven, never per example/name
    (admission gate 1, §10 workload mix); §10 numbers UNKNOWN, baselines
    MEASURED only after implementation; English throughout (the one German
    string is the quoted user steering with translation, per the owner task).

## Nits (not material, no repair owed)

- Report-327 says "`maximal` 4 hits"; recount finds 5–6 matching lines, all
  denials. Count differs, posture (no maximal claim) verified correct.

## New definitions/theorems

None. Docs-only review; no Lean file added or changed.

## Last build result

`./lean-bau` not run: documentation-only review with no Lean changes
(per task: no unneeded full builds).

## CUTS / open

No theorem proved; no decoder/validator/refinement/cost result; no runtime or
compiler speed measured. ACCEPT covers only this bounded plan revision, not a
completed compiler or validator.

CANDIDATE: 327 03ab77b03e2f8de9b26f02ec5eb13a177fbcacdc
VERDICT: ACCEPT
