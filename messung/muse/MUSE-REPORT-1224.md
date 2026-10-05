# MUSE-REPORT-1224: exact re-review of candidate 1223 (valX86_sound decidable part)

CANDIDATE: 1223 dfae53479e3104a4483cc95c13100ff8b899e15b

VERDICT: ACCEPT

## Identity and procedure

- Reviewer clone `/home/simon/Dokumente/gabbro-muse/a1224`, branch `muse/1224`,
  verified; owned file is this report only.
- New pinned snapshot `.tmp/review/SNAPSHOT.json`: author 1223, head
  `dfae53479e3104a4483cc95c13100ff8b899e15b`, base
  `988d75ef42521f5d437a0cb4b9d92b5d5c2e38f2`, clean tree, same three files
  (`MUSE-REPORT-1223.md`, `grammatik/Grammatik.lean`,
  `grammatik/Grammatik/X86/ValidatorSoundPart.lean`).
- Re-reviewed the new snapshot in full, in-clone: `PATCH.diff` (502 lines),
  `MUSE-REPORT-1223.md`, `BUILD-EVIDENCE.json` tail (new re-verification
  entries). Nothing outside this checkout was read.
- Own `./lean-bau` last result line (this checkout, master state):
  `Build completed successfully (641 jobs).`
- This supersedes the previous ACCEPT on `35857f5c...4143`: that snapshot is
  stale after the author repair commit, and this report judges only the new
  head above.

## What changed between the snapshots (delta review)

- Lean content: IDENTICAL. The new file blob is `d493bb75` in both diffs;
  every theorem, proof, comment, CUTS block and `#print axioms` line matches
  the previously reviewed state line for line (full 502-line diff re-read).
  `grammatik/Grammatik.lean` is still exactly one appended import line.
- Report content: the author report gains one section, "Repair diagnosis
  after the failed integration gate (2026-10-05)".
- Evidence content: new final entries re-running `./lean-probe` (0 errors,
  all 21 theorems, standard axioms) and full `./lean-bau` (exit 0,
  `Build completed successfully (640 jobs)`) on the unchanged sources, clean
  tree.
- Therefore every finding of the previous review carries over unchanged; the
  re-review below re-inspects each one against the new snapshot plus the new
  repair-diagnosis claims.

## Checklist findings (all pass on the new head)

1. No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`: none in the new file
   (full diff re-read). Final `#print axioms` are all `[propext]` or
   `[propext, Quot.sound]`. Standard.
2. Existing files untouched except one import line: confirmed on the new
   diff. No theorem deleted or weakened; no other file edited.
3. Every premise used: unchanged proofs, previous theorem-by-theorem check
   stands (validator premise threaded through accepted projections and
   inversions; `valSound_lade_datei` discharges containment via `omega`;
   traversal leg inverts the `validAllFuel` match; W^X consequence
   case-splits with mapping leg and executability premise shaping the
   close). No discard, no `Prop`-typed premise.
4. Family evaluator lifted, never copied: only `valSound_*` packaging plus
   the generic traversal inversion are new; everything else reuses the
   accepted vocabulary (`ValidatorSkeleton`, `ValidationBudget`, `Bild`,
   `LoadedExecution`, `Byteschritt`, `HwLoadedImage`,
   `ValidatorExecution`). Green probe/build confirms all names resolve.
5. Planted refusals really refuse: the two `= false` pins plus the paired
   admission/refusal witness are unchanged and non-vacuous. Admission Bools
   only, never hardware-fault claims.
6. Witness non-degenerate: `valSound_zeuge` unchanged — admission, mutation
   refusal, loaded store step writing 42, `schreibLese_zeuge` write/read
   with `v ≠ 0` and differing bytes, refused interior entry. Single-core
   loaded-image scope remains correct; no multi-core claim exists.
7. Silicon facts: still no silicon model added, nothing new to check
   against hardware references; CUTS still disclaims silicon correspondence.
8. CUTS honest, claim not larger than proof: unchanged CUTS block with
   `valX86_sound_full`, hardware, control flow, relocation, TSO/GX bridge,
   contracts, cost/time, termination OPEN. No W/GX or hardware-correspondence
   claim. Coincidence stays an explicit premise.

## Repair-diagnosis assessment (new material)

- The author reports the integration gate crashed building this module with
  `failed to create thread` (Lean exit 134) and diagnoses a documented
  resource/apparatus failure, taking explicitly NO source change.
- Corroboration inside my snapshot: (a) the Lean sources are byte-identical
  across the two snapshots, so no proof was altered to chase the crash;
  (b) I verified from the full file text that it contains zero `decide`
  calls — proofs are term-mode reuse, `omega`/`simp`/`rfl`, and small
  `generalize`/`cases` inversions, i.e. cheap elaboration with no reason to
  exhaust threads by itself; (c) new evidence entries show green
  re-verification of the unchanged content (probe 0 errors, full build
  640 jobs exit 0). The crash signature is consistent with resource
  exhaustion rather than a content defect.
- Limit of my corroboration, stated plainly: the gate log itself is not in
  my snapshot, so I take the crash signature on report plus the consistent
  signatures above. A fresh integration run in a quiet environment remains
  the coordinator's step (the author requests exactly that); it does not
  block this ACCEPT, since the candidate content is proved green and
  unchanged.
- Refusing to manufacture a source change for a resource crash is the
  correct call under the safety rules; approving the unchanged content does
  not weaken any guarantee.

## Remaining open work (not this candidate's scope)

Unchanged: `valX86_sound_full`, source correspondence, silicon/hardware,
multi-step control flow, relocation re-decode, TSO/GX bridge, contracts,
cost/time, termination — all OPEN in CUTS. Nothing further required of
lane 1223. Next step belongs to the coordinator: fresh integration run of
this exact head.
