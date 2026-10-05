# MUSE-REPORT-1224: exact review of candidate 1223 (valX86_sound decidable part)

CANDIDATE: 1223 35857f5cd52ca440e00604bc47bc36dd84f14143

VERDICT: ACCEPT

## Identity and procedure

- Reviewer clone `/home/simon/Dokumente/gabbro-muse/a1224`, branch `muse/1224`,
  verified; owned file is this report only.
- Pinned snapshot `.tmp/review/SNAPSHOT.json`: author 1223, head
  `35857f5c...4143`, base `988d75ef...e38f`, clean tree, files
  `MUSE-REPORT-1223.md`, `grammatik/Grammatik.lean`,
  `grammatik/Grammatik/X86/ValidatorSoundPart.lean`.
- Reviewed the exact snapshot content in-clone: `PATCH.diff` (472 lines, the
  whole candidate diff), `OWNER-TASK.md`, `MUSE-REPORT-1223.md`,
  `BUILD-EVIDENCE.json`. Nothing outside this checkout was read.
- Own `./lean-bau` last result line (this checkout, master state):
  `Build completed successfully (641 jobs).`
- This supersedes my earlier blocked partial (committed `55f8ee8e`): the pinned
  snapshot is present in-clone under `.tmp/review/`, so the exact review could
  be performed; the substance below replaces the earlier no-result status.

## Checklist findings (all pass)

1. No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`: the new file contains
   none (full diff read). Transient `sorryAx` appearances in the build log are
   intermediate development states only; every final `#print axioms` line is
   `[propext]` or `[propext, Quot.sound]`. Standard.
2. Existing files untouched except one import line: the diff touches only the
   new file, one appended `import Grammatik.X86.ValidatorSoundPart` in
   `grammatik/Grammatik.lean`, and the author report. No theorem deleted or
   weakened; no existing file edited otherwise.
3. Every premise used: checked theorem by theorem. Projections thread `h`
   through the accepted `valX86_wohlgeformt`/`valX86_deckung` and the
   `wohlgeformt_*` inversions; `valSound_lade_datei` discharges file
   containment from the validator premise (`omega` over `hfile`, `hlo`,
   `hhi`); the traversal leg inverts the `validAllFuel` match so timeout
   (`none`) and leftover bytes provably never validate; the W^X consequence
   case-splits on the writability flag with both the mapping leg and the
   executability premise shaping the close. No `intro _` / `have _ :=`
   discard; no `Prop`-typed premise.
4. Family evaluator lifted, never copied: every leg reuses an accepted
   definition or theorem (`ValidatorSkeleton`, `ValidationBudget`,
   `Bild`, `LoadedExecution`, `Byteschritt`, `HwLoadedImage`,
   `ValidatorExecution` vocabulary; `geladenByte_datei/bss`,
   `ausserhalb_rahmen`, `hwBild_fetchDekodiert_gleich`,
   `hwBild_byteschritt_gleich`, `valStark_gibt_deckung`,
   `valZeuge_mutiert_verweigert`, `valWx_verweigert`, the `innen_*` pins,
   `bildStore_*`, `schreibLese_zeuge`). The new file defines only the
   `valSound_*` packaging plus the generic traversal inversion. Green
   `lean-probe`/`lean-bau` in the evidence confirms every referenced name
   resolves; nothing is redefined.
5. Planted refusals really refuse: `valSound_mutiert_verweigert` (mutated
   witness byte) and `valSound_wx_verweigert` (writable code section) are
   proved `= false` equations over Bool admission, reusing the accepted pins;
   the joint witness pairs admission (`= true`) with refusal (`= false`) on
   near-twin images, so the checks are not vacuous. Refusals are admission
   Bools, never hardware-fault claims.
6. Witness non-degenerate: `valSound_zeuge` joins admission, mutation
   refusal, a biased store image whose loaded step writes 42 into the data
   section, a `schreibLese_zeuge` write/read with `v ≠ 0` and differing
   memory bytes (real memory-changing step), and the refused interior entry.
   Single-core loaded-image scope is correct here: this lane claims no
   multi-core/TSO behaviour (see 8), so no two-core obligation attaches.
7. Silicon facts: the candidate adds no silicon model — no encodings, flag
   effects, fault classes, or timing facts are stated. The nothing-to-check
   status is correct, and CUTS explicitly disclaims silicon correspondence.
   No green proof of a wrong definition is present because no definition is
   introduced.
8. CUTS honest, claim not larger than proof: the file ends with a CUTS block
   plus `#print axioms` per main theorem. It states NOT source refinement,
   lists `valX86_sound_full`, hardware, multi-step control flow, relocation
   re-decode, TSO/GX bridge, contracts, cost/time, termination as OPEN, and
   names coverage-from-section-bases as the boundary. No W/GX or
   hardware-correspondence claim is made. The `HwLoadedImage` fetch/step
   identities keep coincidence an explicit premise, never derived from the
   validator Bool.
9. Task-text deviations, both declared by the author and accepted by this
   review: (a) the generic MECHANISM paragraph (family event type,
   `HwAdapter`, multi-core TSO witness) does not describe this lane; the
   specific task (validator soundness) was followed instead, and inventing
   an adapter would have duplicated an accepted model against rule 16;
   (b) "every reachable executable byte decodes" as literally written is
   false in-tree, and the author proved the true base-coverage statement
   while pinning the interior-entry gap as a theorem
   (`valSound_kein_innen_eintritt`, reusing the accepted `innenBild`
   counterexample joint) — a precise obstruction, plainly stated, not a
   silent weakening. (c) The author notes the last two commit messages share
   stale wording; content is complete and green, cosmetic only.

## Build evidence relied on

Author's `./lean-probe` final state: `== 0 error(s) ... exit 0` with all
theorems on standard axioms; author's `./lean-bau`: `== exit 0; 0 error
line(s) in the COMPLETE output`, `Build completed successfully (640 jobs).`
Whole `grammatik/` stays green. Intermediate red probes in the log are the
normal small-pieces working trace, all resolved in the pinned state.

## Remaining open work (not this candidate's scope)

`valX86_sound_full`, source correspondence/refinement, silicon/hardware
correspondence, multi-step control flow, relocation re-decode, TSO/GX bridge,
contracts, cost/time, termination — all listed OPEN in the candidate CUTS and
unchanged by this review. Nothing further is required of lane 1223.
