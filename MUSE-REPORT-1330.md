# MUSE-REPORT-1330: exact review of candidate 1329 (HwKapsteinTsoRest)

Lane 1330, clone `/home/simon/Dokumente/gabbro-muse/a1330`, branch `muse/1330`
(verified: pwd + branch match; tree clean before and after).
CANDIDATE: 1329 `2d172a46beef1263453cc180591a5db102067412`
(from `.tmp/review/SNAPSHOT.json`; author files used AS DELIVERED, pinned
hash never touched: no `git show/log/diff` on it).

## Scope check

SNAPSHOT lists exactly 3 files: `MUSE-REPORT-1329.md`,
`grammatik/Grammatik.lean`, `grammatik/Grammatik/X86/HwKapsteinTsoRest.lean`.
PATCH.diff confirms: report (new), new 745-line Lean file, and exactly ONE
added line in `Grammatik.lean` (`import Grammatik.X86.HwKapsteinTsoRest`).
Trivial note, not a defect: the import is inserted mid-file (before
`HwWcOrdering`) rather than appended at the end; semantically irrelevant.

## Independent verification (in my own tree, HEAD 7e0c5b98)

- `./lean-probe .tmp/review/author-1329/grammatik/Grammatik/X86/HwKapsteinTsoRest.lean`
  (wrapper accepts the delivered path; imports resolve via my project, so NO
  copy into my clone was needed and the tree stayed clean):
  `== 0 error(s) in the COMPLETE output; exit 0`. All 27 theorems elaborate
  on my newer base (author base `10fb97f1`, mine has 696 vs 691 jobs), so
  every referenced accepted name (`kapPlug_int`, `kapPlug_nested`,
  `kap_step_uc/fp/fehler/tor/vec`, `kapStep_port/bild/instanzen`,
  `hwWit_weiterleitung/fremd_alt/spuelung_aendert_speicher`,
  `witNmi_*`, `kap_nested/int_embedded`, …) resolves here too.
- `./lean-bau` on my clean tree: `Build completed successfully (696 jobs).`
- Forbidden tokens: no `sorry`, no `native_decide`, no `unsafe`, no `axiom`
  declaration. The only word-boundary `admit` hits are English prose in two
  doc-comments ("admit no delivery", "loads never admit"), as the author
  report states.
- `#print axioms` for all 27 theorems: `[propext]` or `[propext, Quot.sound]`
  only — subset of the goal-allowed set, no `Classical.choice` needed.
- No new definitions: 27 `theorem`s, zero `def/abbrev/structure/inductive`
  — the family evaluators are lifted, never copied or redefined.
- Every premise is used (hand-checked; device/gate/bus side-conditions are
  all passed into the cited accepted lemmas; `rest_acht_tso` consumes each
  conjunct in its own leg). No premise has type `Prop` itself.
- Refusals are real: `rest_int_verweigert` proves three genuine `= none`
  delivery steps (masked, over-limit, dark-stack) via the accepted witness
  lemmas; FP/tor/vec refusal legs are silent self-loops as classified.
- Witness `rest_zeuge` is non-degenerate: one exhibited union step per rest
  tag, reachability for the eight reaching tags, NMI memory change
  (`m'.mem ≠ …`) with still buffers, owner-only forwarding (`= 42`) with
  foreign staleness (`= 0`) and drain-into-memory on the same TSO model,
  plus the delivery refusals.
- Silicon/vendor-neutral: the file states no new hardware facts, pins no
  silicon values, claims Intel provenance only by citation of the family
  files. No AMD provenance claimed. OK.
- CUTS honest: ends with a `CUTS:` block plus 27 `#print axioms`; the joint
  summary is named `rest_acht_tso` (8 tags, not 10); no W/GX bridge, no
  whole-word/vector atomicity, and no hardware correspondence beyond
  self-consistency are claimed.
- nested/int FINDING independently confirmed in my tree:
  `asyncMasch_puffer_still` (`HwInterrupts.lean:153`) proves delivery leaves
  every store buffer untouched, while `witNmi_aendert_ss`
  (`HwInterrupts.lean:778`) proves the exhibited NMI changes memory. The
  owner-task line "classify delivery as stack-push events" would therefore
  assert a falsehood against the accepted interrupt-lane model; declining it
  and recording the high-priority FINDING (`rest_int_befund`, proved buffer
  silence at single, nested and adapter levels) is exactly the task's option
  (c) and its own "memory write by another path" rule. Correct call.

## What remains open (carried, not defects)

1. `nested`/`int` have no `TSOErreichbar` leg (author's FINDING 1): the
   per-access target-to-W/GX bridge needs a drained-own-buffer guard for
   delivery. Follow-up work, precisely scoped by the proved silence lemmas.
2. Six union tags (lockRmw, isa, addr, muldiv, lockFetch, system) belong to
   other lanes.

## Anything wrong in the task

The owner-task instruction for nested/int ("pushed through the buffer …
classify as stack-push events") is factually wrong about the accepted model
(S3 / `asyncMasch_puffer_still` / direct `write64` path); the author was
right to decline it with reason, and the coordinator should correct that
line for any follow-up lane. Otherwise the review task is sound.

## VERDICT: ACCEPT

CANDIDATE 1329 `2d172a46beef1263453cc180591a5db102067412` is accepted for
merge: green independent probe (0 errors), standard axioms, scope-exact
diff, lifted-not-copied, real refusals, non-degenerate witness, honest
CUTS, no claim beyond the proof. No REPAIR items.
