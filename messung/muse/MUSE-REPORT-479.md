# MUSE-REPORT-479: Independent exact-candidate review of 431

Lane 479, branch `muse/479`, clone `/home/simon/Dokumente/gabbro-muse/a479` (verified).
Candidate: lane 431, pinned HEAD `c1a41a1a5590af310555057e74ce3da18dca8c28`
(base `2b0d29cffaa7b41971f0820d9a752ec685c00ad6`), 3 files, +590/-0.

## Scope verified

`git diff base..head --stat` confirms exactly the snapshotted files:
`MUSE-REPORT-431.md` (+102), `grammatik/Grammatik.lean` (+1: only the
additive trailing `import Grammatik.X86.ValidationBudget`), and the new
module `grammatik/Grammatik/X86/ValidationBudget.lean` (+487). No deletions,
no touched Spec/goal/Rust/emitter/checker, no friend files. OWN rule holds
for the author.

## Independent reproduction (my clone)

Staged ONLY the supplied candidate `ValidationBudget.lean` into my clone,
ran `./lean-probe`, then deleted it (`git status` clean before this report):
`== 0 error(s) in the COMPLETE output; exit 0`. This reproduces against a
NEWER master than the candidate base, so the module is robust to the current
tree. Axiom prints standard: all `propext`-only, three `rfl` facts
axiom-free, `joint_decode_entry_memory` `[propext, Quot.sound]` via the
reused Bild witness — all within `gabbro_ziel`'s set. (Minor variance: the
author's log shows two axiom-free facts, mine three; elaboration detail only.)

## Semantic checks against canonical definitions

- `decodeFuel` wraps the actual `Codec.decode` (ret `195 -> some (ret,1)`,
  `255 -> none`, both pinned in `Codec.lean`) with a re-checked length gate
  (`d.laenge + rest.length == bs.length && laengeOk`); it assumes no decoder
  correctness — mismatch refuses. No second decoder, no mini-machine.
- `bildEintraegeOkFuel` instantiates the generic entry check with the actual
  `Bild.eintragEnthalten`, the same predicate `wohlgeformt` uses for entries
  (`Bild.lean:270`). No second register.
- Witnesses are genuine `decide` evaluations over real bytes/image:
  single `ret` under fuel 2, fuel-1 timeout refusal, `0xFF` refusal,
  two-`ret`s refused at fuel 2 / accepted at 3 (no leftover bypass),
  `0x1000` contained / `0x5000` refused in `[zeugenCode, zeugenDaten]`.
- Joint witness reuses `Bild.schreibLese_zeuge` for the memory-changing
  conjunct — disclosed in CUTS, not redone. Non-degenerate (real write/read
  with observable byte change).
- Every premise of every theorem is used (read all proofs); no `sorry`,
  `admit`, `axiom`, `native_decide`, `unsafe`, `intro _`, `have _` (grep
  clean); no Prop-typed premise; `decodeFuel_cons_eq` and the `rfl` entry
  unfoldings are genuine definitional equalities (else `rfl` would fail).
- No vacuity: fail-closed (`none`/`false` never validates), full-consumption
  (`validAllFuel_rest`), derived count bounds (`ins.length <= fuel`,
  `es.length <= fuel`), monotonicity, per-entry containment — none restates a
  premise, none quantifies contracts away, no timing/cost/hardware/closure
  claim. CUTS states exactly what is open. Consumer link is real:
  `DIRECT-COMPILER-DESIGN.md` fuel-bounded search with exhausted-budget
  refusal fits the proved facts.
- No duplication: no `decodeFuel`/`validAllFuel`/`entriesOkFuel` anywhere else
  in `grammatik/`; `Byteschritt`'s `laufBytes` fuel runner is a different
  artefact and untouched.

## The `./lean-bau` umbrella crash

Author reports 392/393 with the only failure the import-only `Grammatik`
target, `failed to create thread`, exit 134, plus a control run with the
import commented out failing identically (391/392, same crash). Signature and
control are consistent with worker resource exhaustion under lane load, not a
proof error: the module olean builds (my probe confirms), the diff is purely
additive, and no Zielsatz module imports the new file. I did not rerun the
full umbrella build (long, contends with live lanes); the single-file queued
probe plus the logged control experiment carry the point. Whoever merges
should still see a green `./lean-bau` at merge time per the merge script.

## Defects / repair direction

None blocking. No repair items.

## Re-review of the repaired candidate (second turn, same day)

New pinned HEAD `676b45947ca08accdaa9ebcc6784972dbd20da01` (same base).
`git diff old-head..new-head`: ONLY `MUSE-REPORT-431.md` (+42, integration-gate
response section); `git diff` over `grammatik/` is EMPTY — the Lean module and
the umbrella import are byte-identical to the previously accepted version.
Supplied `.tmp/review/author-431` files verified byte-identical to the new
HEAD (`git show` diff clean for both module and report).

Fresh substantive check in my clone: staged the supplied module file, ran
`./lean-probe` → `== 0 error(s) in the COMPLETE output; exit 0`
(standard axioms on every line), then deleted it (`git status` clean).
The author's 41-entry build evidence confirms the second-turn sequence:
probe 0 errors, `./lean-bau` same umbrella-only failure, grep-clean,
report-only commit. Previous findings stand unchanged; no new proofs to
inspect since no proof changed.

One unchecked nit (not a defect, no verdict impact): the new report section
says "all 27 axiom lines" printed in the gate log — the module contains 28
`#print axioms` lines. The gate log itself was not supplied, so I verified
the green-module part via my own probe, not the line count.

## Verdict (new pinned candidate)

ACCEPT the precisely delivered bounded claim: fail-closed fuel-bounded
decode/entry traversal facts over the canonical decoder and image check,
with derived count bounds, monotonicity, and concrete joint witnesses.
Expressly NOT accepted: full source validation, whole-image closure, timing
or cost claims, hardware claims — none of which the candidate makes.

CANDIDATE: 431 676b45947ca08accdaa9ebcc6784972dbd20da01
VERDICT: ACCEPT
