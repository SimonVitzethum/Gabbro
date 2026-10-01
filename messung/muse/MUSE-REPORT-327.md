# MUSE-REPORT-327: Safety-first broad practical-performance prioritisation

Scope: root `DIRECT-COMPILER-DESIGN.md` only (plus this report). Documentation-only
revision of the accepted lane-325 design (ACCEPT per independent review 326) toward
the latest user clarification: "alles wichtige aber die letzten 10% oder so sind
nicht wichtig, sicherheit ist wichtiger" (all important performance features, final
roughly-10% diminishing returns not important; safety has priority). No source,
ledger, Lean, Rust, emitter or central-doc edits. No builds run (docs-only; no
Lean/cargo changes exist to check).

## Factual material checked

- `DIRECT-COMPILER-DESIGN.md` prior snapshot (698 lines) as the preserved base.
- `DIRECT-COMPILER.md` (central ledger; lane states incl. 325/326 merged; scope note
  for author 327 / reviewer 328).
- `messung/muse/MUSE-REPORT-325.md` + `MUSE-REPORT-326.md` (full; per-charge PASS;
  two immaterial nits).
- `lanes/325.md` (owner task, full) and this lane task.
- `messung/muse/MUSE-REPORT-272.md` (bounded `schritt` per-form step equations proved
  in `Ausfuehrung.lean`), `MUSE-REPORT-279.md` (`Codec.lean` generic
  `roundtrip`/`roundtrip_len_ok` proved), `MUSE-REPORT-317.md` (access extraction);
  `grammatik/Grammatik/X86/` file list — to phrase the pilot baseline exactly.
- `BYTE-PILOT`/Typen facts via the existing design's citations (no doc edits there).

## What changed (698 -> 761 lines; +70/-7 owned diff, all prose, all PROPOSED/OPEN)

1. Header: safety-first priority stated first. The "last 10%" is declared qualitative
   user prioritisation, not a number: no quantitative 90% guarantee, no reduced proof
   coverage, no weakened safety level. Completion is defined as FULL proved validation
   and FULL safety of accepted source/final bytes for EVERY selected profile and EVERY
   source construct — never a 90% proof or 90% safety. User logics/contracts unchanged
   (actual parameters/results, no inferred ensures, no refusal-to-warning); named proof
   boundaries stay explicit.
2. Pilot baseline correction (§2): the old "execution skeleton" phrasing is replaced.
   Bounded abstract per-form step equations (`Ausfuehrung.lean` `schritt`, lane 272)
   and the canonical codec round-trip (`Codec.lean`, lane 279) are named as PROVED
   bounded abstract helpers over the canonical vocabulary — not a chain
   correspondence. OPEN remains: physical-hardware/source correspondence (per-form
   execution correspondence vs silicon, per-access TSO bridge into W/GX, full
   source-to-final-bytes chain). No feature of the baseline is fabricated.
3. New §2D (safety-first admission): weakening any safety/contract/budget guarantee for
   speed is REJECTION regardless of measurement; essentials first and complete;
   deferred scope waits for closed essentials AND genuine workload plus affordable
   complete Lean rules; deferred absence affects only code quality, never construct
   support (certified translation always retained); deferred categories are postponed
   scope examples, not a new language/API/implementation task; no universal
   performance figure or exact time number; `-O3`-like stays an effort/quality goal,
   not external-compiler fast-math equivalence.
4. Admission test per proposed family/pass (7 conjunctive gates): generic source-pattern
   need (emitter-construct driven, never per example/name); observable equivalence
   with actual parameters/results/faults/flags/FP rounding/ordering/async; named
   workload benefit AND compiler/check cost; new state/fault/concurrency/FP/context/
   enabled-state obligations; checker-reuse decision; independent proof + negative
   cases; certified cheaper translation retained until all correspondence/cost/stop
   gates pass.
5. Priority table (scope / inclusion rationale / proof gate / postponement reason):
   essential rows (scalar lowering, immediates/addressing/branches, allocation/
   optimisation/`-O3` scopes; IEEE binary64 baseline; language-needed concurrency/
   atomics/fences; emitter-scope calls/ABI/runtime/entry/hardware; SSE2 + AVX2-integer
   CPU-tier SIMD baseline kept as a core goal subject to generic proof and
   enabled-state gates) and deferred rows (selected BMI/POPCNT/bit-scan/shuffle;
   AVX-512, matrix/AMX, APX, crypto/SHA/AES; aggressive FP fusion, exotic
   gather/scatter/compress, cache hints/NT stores/string specialisations — each with
   its FMA-rounding / NT-ordering proof note and "do not claim emittable now").
   Common memory loops take the scalar/vector safe route first.
6. Stop rule: stop broad profile/validation-latency growth without demonstrated
   worthwhile benefit; construct support stays complete; further tuning uses already
   proved translations and measured trait tables, never trusted correctness premises.
   Compiler-speed restatement (deterministic bounded fuel, valid invalidation, safe
   incrementality, mandatory full validation; fuel exhaustion -> certified cheaper
   output; proof failure -> refusal). No microarchitectural pipeline/cache modelling;
   hardware time assumptions named, cost transfer required.
7. Title/intro check: title already says HIGH (not maximum) performance; "maximal"
   appears only in denial sentences (4 hits, all denials). No change needed there.

## Consistency kept

- §2 14-form pilot table, registers, conditions, memory, permission/fault/flag facts:
  untouched. Planned rows §§3–6, §§7–11, trust chain, `valX86_sound` derived
  refinement, `schluss_x86` premise discipline, `gabbro_ziel` axioms, ghost
  call/return events, budget correspondence OPEN, M140/N575–N577/N571/N463/N506,
  f32 bridge refusal, linking OPEN: unchanged.
- Only `DIRECT-COMPILER-DESIGN.md` and this report are staged/committed. Main ledger
  (`DIRECT-COMPILER.md`) remains the primary status record; root-relative links
  verified (31/31 resolve).

## New definitions/theorems

None. Docs-only revision; no Lean file added or changed.

## Last build result

`./lean-bau` not run: documentation-only task with no Lean changes (per task: no
unnecessary full builds). Mechanical checks: 31/31 relative links resolve;
"maximal" only in denials; no speed numbers, no LOC estimates; line count 761.

## CUTS / open

No theorem proved; no decoder/validator/refinement/cost result; no runtime or
compiler speed measured. Reviewer 328 reads the fresh exact snapshot after commit;
any findings it returns on this candidate remain valid requirements for follow-up.

## Task-statement remark

Nothing in the task appeared wrong. The pilot-correction charge was checked against
reports 272/279/317 and the `grammatik/Grammatik/X86/` tree before rewording; the
"no existing bounded step proof" reading is avoided without claiming any chain
correspondence.
