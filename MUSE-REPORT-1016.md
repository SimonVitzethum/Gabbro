# MUSE-REPORT-1016: exact review of author 866 (dead-store optimiser rule)

Lane 1016, clone `/home/simon/Dokumente/gabbro-muse/a1016`, branch `muse/1016`.
Review-only lane: this commit owns ONLY this report. No source file was touched
(`git status` before commit showed only this untracked file).

CANDIDATE: 866 cd2610ef2f513dec875d58a5226b83f75752d7c8
VERDICT: ACCEPT

## CANDIDATE

- Author: **866**
- Pinned HEAD: **cd2610ef2f513dec875d58a5226b83f75752d7c8**
  (base `b040b155159f47629542b0083e2f0a8a607f2b4c`, identical to this clone's
  HEAD; snapshot declares `clean: true`)
- Files (exactly 3, confirmed via `PATCH.diff` hunk headers): `MUSE-REPORT-866.md`,
  `grammatik/Grammatik.lean` (one added line `import Grammatik.X86.OptDceStore`),
  `grammatik/Grammatik/X86/OptDceStore.lean` (new, 515 lines).

## Substantive verdict: accept, bounded

The candidate is a sound, honestly bounded source-level rule lemma. All
mechanical gates reproduce; the architecture matches the DESIGN section 7
dead-store row as a validator-admission lemma; the CUTS block states exactly
what is not proved. Bounded acceptance: the proved connection covers
rest-entry worlds/traces only; downstream rest-induction, the float window,
the level-(c) machine-work bound and any silicon/TSO/GX claim remain OPEN
(all listed in CUTS, none claimed).

## What was independently verified

1. **Exact probe reproduction (queued wrapper, unmodified snapshot content):**
   `./lean-probe .tmp/review/author-866/grammatik/Grammatik/X86/OptDceStore.lean`
   run in this clone against the base tree:
   `== 0 error(s) in the COMPLETE output; exit 0`, no warnings. Axiom report
   matches the author's claim exactly; worst case
   `[propext, Classical.choice, Quot.sound]` (standard), most theorems
   `[propext]` or `[propext, Quot.sound]`, cert/admission axiom-free.
2. **Banned tokens:** `rg` over the candidate file finds no `sorry`, `admit`
   (only prose "admitted"/"admission"), `axiom` (only `#print axioms`),
   `native_decide`, `unsafe`. No premise has type `Prop` itself; no
   `intro _` / `have _ :=` discard; every premise of `OptDceStore_verbindung`
   is used (`hz` via `hStabil hz`; `hStabil` via `obtain` with all three
   components rewritten; `hσ₁/hσa/hσb` via `rw`; `hw/hL` in the `assignSlot`
   conclusion terms, house style of `OptFoldConst`).
3. **Semantics cross-check against base (not just Lean green):**
   - `execStmt` `.assignSlot` arm (`Semantik.lean:700-702`) returns `.ok`
     unconditionally, so the three fault/env equations close definitionally;
     no fault is added or removed, no `ensures` derived, no fault speculated.
   - `World.lese` / `schreibSlot` defs confirm the three trace equations
     characterise exactly one private write event plus pure reads (read events
     carry pre-`lese` `haelt`, the write event post-`lese` `haelt`, as stated).
   - `offen` ignores `zugriff`/`gzugriff` (`Semantik.lean:70-76`), so
     `schreibSlot_haelt` by `rfl` is genuine, not a skipped case.
   - `World.storeSlot` frame shape confirms `storeSlot_absorbiert` is proved
     over arbitrary values `v1 v2` (dead value never matters).
   - `seqPassesAux` / `seqPassesAux_cons` (`Budget.lean:560-579`) confirm the
     budget lemma: exactly one pass dropped, surviving op lists kept.
   - All witness vocabulary exists in base with compatible shapes:
     `vertragVon` (`Syntax.lean:641`), `refD/refEin/refO/refSp0/initB/MB/refP`,
     `refIdxEin/refHundert/refDarfEin/refWriteStAt` (literal index/value, so
     the witness's stability `rfl`s are computational, not assumed),
     `refEin_schreibt/refB_erreicht/refB_schreibt`, `keinRuf`, `darf`,
     `SeqElem.ofStmt`, `storeSlot_hit`, `lese_haelt`.
4. **Inhabitation:** `OptDceStore_verbindung_zeuge` instantiates ALL premises
   jointly on non-degenerate `refD` (`einzahlen` writes its table;
   `refB_erreicht` + `refB_schreibt`: reached F-run with slot `0 -> 100`
   memory change) and uses all ten conclusion conjuncts. The `fun _ =>`
   discharging the admission antecedent ignores only a proof-irrelevant `Prop`
   argument while the equalities hold computationally; disclosed in the
   author's report item 3. `dceBudget_passAbzug_zeuge` likewise joint on `refD`.
5. **Refusals/negative side:** five refusal theorems (shared/volatile/atomic,
   live cell, trap-capable FP, impure removed store, cell mismatch), each
   closing by `simp` on the named `Bool` field, plus `decide` probes (one
   admitted, two refused shapes). Refused = fallback, never a warning.
6. **Scope hygiene:** no new diagnostic/gift/example/CLI numbers, no MARKE
   changes, no source/checker/`Spec`/goal/emitter edits, friend-reserved
   optimiser files untouched (no mention of `OptimizationRules`/
   `OptimizationWitnesses` anywhere in the patch). Single accepted-IR
   fallback used per task permission; no competing IR created. English only.
   CUTS block + `#print axioms` per main theorem present.

## Precise boundaries (accepted as stated, not as defects)

- Byte forms / REX / width / flags / TSO / atomicity: not applicable at this
  layer and correctly not claimed; correspondence stops at source worlds and
  `Zahl` values per CUTS. No invented hardware determinism found.
- IEEE: `assignSlot` performs no float computation in this semantics, so no
  `logik bereich` can hide in the removed store; `keinFalleFP` refusal is
  defence-in-depth at certificate level. Sound as stated.
- The proved rest-entry agreement (slots/globs/haelt/traces) holds
  unconditionally on liveness by overwrite absorption; the `totBestaetigt`
  bit therefore bites only in the OPEN downstream rest-induction. This is
  disclosed (CUTS: no full rest-induction over arbitrary `rest` with calls
  into `R`), so the certificate does not over-claim.
- Full-project `lean-bau` (511 jobs green) and `gabbro_ziel` axioms were taken
  from the author's BUILD-EVIDENCE.json (complete probe history ending green);
  not re-run here because integrating the candidate would dirty owned files.
  The integration surface is one import line plus an additive module, and the
  exact file content was re-probed green in this clone.

## Minimal repairs

None required. Follow-ups belong to other lanes per CUTS (rest-induction
lowering, gleit-bind window, machine-work transfer, TSO/GX bridge).

## Last check results

- `./lean-probe .tmp/review/author-866/grammatik/Grammatik/X86/OptDceStore.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`
- `git status` before commit: only untracked `MUSE-REPORT-1016.md`.
