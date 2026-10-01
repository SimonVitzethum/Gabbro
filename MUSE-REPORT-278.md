# MUSE-REPORT-278: Floating point and cost preservation

Lane 278, wave A. Model: opencode-go/muse-spark-1.3-contributor. No
delegation, no other model processes.

## What was done

Wrote the owned deliverable `dokumente/x86/FLOAT-ZEIT.md` (new file, only
file touched besides this report): IEEE f32/f64 surface-to-SSE mapping,
MXCSR/rounding, NaN, signed zero, denormal, trap, contraction/FMA and
expression-order obligations with no fast-math relaxation; the three-level
time separation (model steps, checker/certificate costs, hardware timing)
against the exact claimed Ziel conclusions (`ZeitAb`, `ZeitAbX`,
`FortschrittG/F/FX`, `KeinWarteZyklus`, `KernHaltE` preserved as stated);
per-optimisation transfer rules for the starter package; a proposed
checked target cost summary plus concrete hardware-profile data with every
cycle bound marked unproved; generic phase-B definitions/lemmas and
blockers. No source-guarantee change, no checker/emitter change, no new
diagnostic/gift/example numbers, MARKE_EMIT untouched.

Read before writing: `Gleitkomma.lean` (model + theorems + witnesses),
`GleitkommaBits.lean`, `Profil.lean` (keys, witness), `KostenG.lean` fully
(§§1–13 incl. gleit cost rows, `spiegel`/`zusatz`, foreign `fa` layer),
`Zielsatz/Spec.lean` (FortschrittG 1828, KeinWarteZyklus 1840, ZeitAb
1894–1900, ZeitAbX 2210, ZielX 2217, FortschrittFX 2242, zeit-weak 1233,
review package 1239+), `Fortschritt.lean` (BereichG, fadenS_bereich),
`Semantik.lean` (gleitRechne, gleitPasst, gleitRoh, logik bereich),
`Typen.lean` (GFloat=f64, width cut), `Syntax.lean` (GleitOp, gleit
blocks, fllt/flle), `X86/Typen.lean` (no float Befehl), `CFormenF.lean`
(header + gleitkomma_ieee/annexF/F1–F7), `GLEITKOMMA.md`, `PLAN-BITS.md`
§5, `PLAN-UEBERSETZUNGSVALIDIERUNG.md` §§0–5, `WELLE-A.md`, `emit.rs`
(float prelude/lowering excerpts), `manifest.rs` (two float assumptions,
fp_contract key), `kosten.rs` (op unit).

## Repair pass (5 review findings — second commit)

1. **MXCSR per-context.** Removed the inherited "process-global state"
   wording: MXCSR is architectural state per execution context (logical
   CPU); context-switch continuity is software save/restore (binding
   logic), silicon behaviour under the entry value is hardware. Replaced
   the bare stability assumption with checked establishes (entry) +
   preserves (every enumerated `LDMXCSR` site); `STMXCSR` readers
   enumerated; manifest "GLOBAL state" quote annotated as superseded
   (§§4.2.1/7, 7, 8.2, 9, 10.3).
2. **No speculative premises.** Deleted the "hidden micro-fusion"
   hardware assumption (micro-op fusion of separately encoded scalars
   cannot change architecturally visible rounding; only exact
   instruction-level semantics is modelled) and the "correctness-adjacent
   VZEROUPPER" claim (performance only absent a demonstrated ABI
   upper-lane contract) — replaced with exact VEX semantics + explicit
   AVX state obligations (§§4.2.3, 5).
3. **f32 refusal.** Deleted the "compute in the node's width" default rule
   and the innocuous-double-rounding paragraph as solutions: binary64
   semantics vs genuine f32 arithmetic differ numerically. Until path (a)
   (source-width model + reviewed Spec diff) or (b) (proved fragment
   refinement) is proved, every `float` node is refused at exactly this
   bridge; all `SS`/`float` table halves marked proposal-only (§§4.1 note,
   4.3, 9, 10.1).
4. **Enabledness (lane-274 reading).** `FortschrittG` preserved as pure
   enabledness — arbitrarily many enabled retry iterations do not violate
   it; no termination proof demanded. Retry obligations restated as
   separate: finite expansion + honest work accounting (proved attempt
   bound or no work bound; unbounded retry behind a constant refused). No
   fairness/OS premise invented; no time guarantee weakened (§§6.4, 7, 8.1).
5. **NaN audit.** Class-level relaxation made conditional on a named OPEN
   lemma (`nan_payload_unbeobachtbar`: no NaN inhabits `Gleit lo hi`;
   comparisons false on NaN; permission conditional on continued refusal
   of bit-observing forms) plus an explicit sticky-status-flag reservation
   (unobserved-or-matched; SNaN-quieting as the joint case). Payload-
   pinning certificates refused (§§4.1 table, 4.2 traps, 4.3, 7, 8.2, 9,
   10.2).

Also repaired in this pass: the transmitted file was truncated mid-§8.2
(write-size cut); the complete tail (§8.2 finish, §§9 phase-B lemmas, 10
blockers, 11 verification log) is now on disk and committed.

## Exact names of new definitions/theorems

None. Docs-only lane: no Lean file, no theorem, no code change. The
FLOAT-ZEIT.md §10 lists PROPOSED phase-B names only (explicitly
provisional, for the coordinator/reviewers).

## Last check outcome

No `./lean-bau` / `./cargo-pruef` / `./emission-pruef` run: docs-only
task, per the lane scope rules file/claim checks apply, not a gratuitous
build. Claim verification performed instead: every table row and
obligation in FLOAT-ZEIT.md carries its file:line; the two
highest-risk claims were re-checked at write time — (i) pilot
`Befehl` has no float constructor (`X86/Typen.lean:53-68` read
directly), (ii) `ZeitAb`/`ZeitAbX` statements and the
"WEAK / says nothing about waiting" header note
(`Spec.lean:1894-1900, 2210-2215, 1233-1237`) quoted exactly.
Repair-pass verification: full owned doc re-read after all edits
(truncation confirmed repaired — §§9/10/11 present, file ends cleanly);
each finding mapped to its edited paragraphs (§§4.2.1/3/7, 4.1 table
note, 4.3, 5 AVX, 6.4, 7 retry + closing, 8.1 attempt bound, 8.2 FP
control, 9 lemma list, 10 blockers, 11 log); cited model facts
re-confirmed (`Gleitkomma.lean` nan-propagation arms,
`Spec.lean:1828-1831` enabledness disjuncts, `Gleit lo hi` NaN
exclusion). Baseline build state unknown (not measured, left untouched).

## What remains open

Everything in FLOAT-ZEIT.md §§9–10: Typen.lean float-state/Befehl
extension, decoder refusals, per-op correspondence lemmas, TSO
float-access lemmas, cost-summary Bool + soundness, MXCSR save/restore
proof, falsifiers for FTZ/DAZ/mode-stability/fast-math, subnormal
round-trip probe, f32-in-memory correspondence, retry-loop progress
mapping, and all hardware cycle bounds (unproved by design at this
stage). Wave-B gated on reviewed foundations + independent review.

## What I believe is wrong or risky in the task area (findings)

1. `kosten.rs` has no float-named cost arm found by name search
(`Gleit|gleit|Float|float` hit only the "no machine floats" comment);
float `let` costs ride the generic paths. `KostenG.lean` §11 presents
`kostenK` as a reading of `kosten.rs` — the gleit rows of that reading
were NOT re-verified against the Rust arms in this lane. Phase B should
close or record it; the doc marks it open (§10, item 7).
2. The model computes every `Ty.fl` in binary64 including `f32` nodes,
while the target computes `f32` nodes in `float`: the single-rounding
point for `f32` arithmetic is the sharpest soundness edge of §4.3 and
deserves its own lemma, not a paragraph.
3. Mode stability (MXCSR writers) and FTZ/DAZ/fast-math have no
falsifier today (GLEITKOMMA.md §5 items 5–7); carrying them as
validator premises without probes repeats the exact weakness §5
documents. The doc asks for probes, not just premises.
4. Nothing in the lane task is otherwise wrong: the "do not change
source guarantee or emit C forms" constraint was respected; the
wave-A refusal posture (unknown encodings refused, SIMD gated) is
stated in §§4–5.

CUTS: docs only; no proofs, no decoder, no TSO bridge, no image
theorem, no timing bound; line numbers are as-read at write time and
may drift; `kosten.rs`-vs-`kostenK` gleit-arm correspondence not
re-verified (see finding 1).
