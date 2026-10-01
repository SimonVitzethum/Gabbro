# MUSE-REPORT-324: Independent detailed compiler design review

Scope: exact candidate snapshot of lane 323 under `.tmp/review/author-323`
(`DIRECT-COMPILER-DESIGN.md` 506 lines, `MUSE-REPORT-323.md`,
`OWNER-TASK.md`, `PATCH.diff`, `BUILD-EVIDENCE.json`) pinned by
`.tmp/review/SNAPSHOT.json`. Documentation-only review; no Lean, Rust,
emitter, ledger or central-doc edits; no builds run.

## Candidate identity

- Candidate HEAD: `b1fe932b9dca0af98d4c22adec192188d566896f`
  (three commits per BUILD-EVIDENCE.json, owned files only:
  `DIRECT-COMPILER-DESIGN.md`, `MUSE-REPORT-323.md`).
- Review base: `3c5e40ead05b017330bdba3dfd5a92db0537a3eb`
  (this clone HEAD, clean, branch `muse/324`).

## Factual material actually checked

- `grammatik/Grammatik/X86/Typen.lean` (full, 87 lines):
  14 `Befehl` constructors, 16 registers, 16 `Bedingung` codes,
  `Flags.af : Option Bool`, per-byte `Speicher` + R/W/X, CUTS.
- `dokumente/x86/BYTE-PILOT.md` (full): canonical encodings/lengths.
- `dokumente/x86/EMITTER-INVENTAR.md` (full, 469 lines):
  construct-to-branch scope, never example frequencies.
- `dokumente/x86/FLOAT-ZEIT.md` (full, 819 lines): binary64 model,
  f32-bridge refusal, MXCSR/control-state, three time levels.
- `dokumente/x86/REVIEW-QUELLE-INVARIANTEN.md` (full, 401 lines),
  `dokumente/x86/REVIEW-TSO.md` (full, 425 lines),
  `dokumente/x86/REVIEW-OPT-BINAER.md` (full, 581 lines).
- `DIRECT-COMPILER.md` ledger (states of lanes 269-324),
  plus targeted greps of `QUELLBRUECKE.md` (`valX86_sound` /
  `schluss_x86`, refinement derived never assumed),
  `TSO-GX-BRUECKE.md` (per-access forward simulation),
  `IMAGE-ABI.md` (whole-executable refusal posture).
- Markdown links: all 26 `](...)` relative targets in the candidate
  resolve to existing repo paths; the four primary references
  (Intel SDM, AMD APM vol.3, Intel optimisation manual, two LLVM
  URLs) match the owner task exactly and are framed as modelling
  targets, never as hardware-correspondence evidence.

## Per-charge findings

1. 14-form pilot vs extensions: PASS. §2 table matches all 14
   constructors, mnemonics, widths/forms and BYTE-PILOT lengths
   exactly; registers/conditions/memory/permission/flag facts exact;
   helpers (`Wort`/`Speicher`/width/`Breite`/SIMD helper) correctly
   denied ISA status; fault/flag preservation marked OPEN.
   Planned rows (§§3-6) each carry mnemonic, forms, reason,
   priority and OPEN proof obligations; CMOV unselected-fault,
   indirect-call provenance, LOCK/RMW, fence distinctions,
   alignment/tearing, stack/ABI, M140, N575-N577 all correctly
   scoped as PROPOSED.
2. Invariants/contracts: PASS. Entry-only ranges, writer blackout,
   held-section limits, shared-load reuse only under
   immutable/continuous-exclusive/held-lock proof, local token
   insufficient, ghost call/return events with actual values and
   reason channel, never derive `ensures` — all match the
   source/invariant audit.
3. No overclaim: PASS. §§0/11/CUTS state PROPOSED plan only, no
   closed chain; ISA/concurrency/f32/SIMD/hardware rows all OPEN;
   no GCC parity, no maximal-performance or instruction-count
   target (§2A); `gabbro_ziel` axioms quoted exactly.
4. Final-byte closure: PASS. Chain covers source to FINAL relocated
   bytes, loader, fetched/decoded steps; whole-executable coverage
   incl. driver/bindings/runtime/handwritten entries with
   refuse-if-unmodelled; obligations source-computed
   (`DutyExport` etc.); refinement DERIVED via generic
   `valX86_sound`, closing theorem takes no refinement premise.
5. Optimisation/costs/stops/call-logs: PASS. Inventory with
   premise/certificate/failure/phase; five generic before/after
   examples with counterexamples (avail, C5 guard, CE-2 fault
   hoist, CE-6 flag identity, CE-3 shared reuse); fault/refusal/
   stop order, `FolgeG` ghosts, ghost budget correspondence OPEN,
   machine-work transfer separate; CAS-retry bound discipline kept.
6. Fast compilation: PASS. One typed IR, interned IDs/arenas,
   explicit analysis invalidation, bounded fuel everywhere, no
   exponential search, linear-scan default, on-demand analyses,
   deterministic parallel/incremental design, caches untrusted,
   hashing alone no theorem, validator failure refuses, compiler
   budget distinct from source run budget.
7. Fast Lean checking: PASS. Proved-once executable checkers,
   data certificates not per-program proof scripts, no
   `native_decide`, no trusted Rust verdict, kernel-accepted
   `decide` result counts, no linear-time assumption.
8. Measurement honesty: PASS. Numbers UNKNOWN, no ms promised,
   baseline-after-closure ordering, generated workloads plus
   emitter inventory (examples alone not scope), cold/warm/
   incremental, p50/p95, refusal probes, few stable modes with
   identical acceptance.
9. Inventory scope/language/links: PASS. Scope cites
   EMITTER-INVENTAR §§2-10 constructs, never examples; root file
   `DIRECT-COMPILER-DESIGN.md` is English; all relative links
   resolve; ledger stays primary, design is a plan not a progress
   table.

## Nits (not material, no repair owed)

- §10 proposes German mode names (`schnell`, `optimiert`) in an
  English document; harmless as proposed identifiers.
- Author report says "23 relative links"; recount finds 26
  (repeats included) — all resolve, so immaterial.
- §2 "fault/flag preservation per form is lane-272 work, OPEN"
  while the ledger shows 272 merged: posture correct (chain
  correspondence genuinely OPEN), phrasing slightly stale.

## New definitions/theorems

None. Docs-only review; no Lean file added or changed.

## Last build result

`./lean-bau` not run: documentation-only review with no Lean
changes; baseline untouched (same standing as the author lane).

## CUTS

No theorem proved; no decoder/validator/refinement/cost result;
no runtime or compiler speed measured. ACCEPT covers only this
bounded detailed plan, not final translation validation.

CANDIDATE: 323 b1fe932b9dca0af98d4c22adec192188d566896f
VERDICT: ACCEPT
