# MUSE-REPORT-1388: Exact review of candidate 1387 (GabbroV StartPflicht bridge)

Lane 1388, clone `/home/simon/Dokumente/gabbro-muse/a1388`.
Role: report-only independent exact review. CANDIDATE: author lane 1387,
pinned HEAD `7369fb68f86facf5126fae27bbc01feb37a0553c`
(base `c943db2aff49c64e2b606310eb9aecc4bd94dddf` per `.tmp/review/SNAPSHOT.json`).
Owned deliverable of this lane: this file only.

## VERDICT: REPAIR

The candidate is an honest blocked report plus an unchecked 48-line skeleton.
Nothing in it is false, but there is nothing verified to accept, and the
committed Lean file violates the commit-green rule. Repair is small and concrete
(see section 4). This is NOT a rejection of the author's reading or plan.

## 1. What the candidate contains (verified by full read of PATCH.diff)

- `MUSE-REPORT-1387.md` (125 lines): declares BLOCKED status plainly, pins all
  reading findings with file:line references, gives a fixed 9-item implementation
  plan, and carries an honest CUTS section ("PROVED: nothing").
- `grammatik/Grammatik/X86/GvStartPflicht.lean` (48 lines): module docstring,
  11 imports, namespace, `open`, and exactly one definition `Sp0Ok`.
  No theorem, no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` anywhere in the
  added lines (checked by reading every added line of the diff).
- No existing file is modified: the diff adds exactly the two new files above.
  `grammatik/Grammatik.lean` is untouched (no import line), so the committed
  skeleton is inert for the build.

## 2. Checks I performed

- Clone/branch verified via shell: `/home/simon/Dokumente/gabbro-muse/a1388`,
  branch `muse/1388`, working tree clean except this staged report.
- `./lean-bau` RUN GREEN on my tree (which contains no Lean changes — report
  only): last line `Build completed successfully (717 jobs).` This confirms the
  base builds; it says nothing about the candidate's skeleton, which is absent
  from my tree.
- Author's pins confirmed in-tree:
  - `declOf` sets `Glob := Empty`: `grammatik/Grammatik/Parser/UebersetzeAllg.lean:156`.
  - `structure UProg`: `grammatik/Grammatik/Parser/Uebersetze.lean:201`.
  - `fieldCount` (`UebersetzeAllg.lean:40`), `fieldRangeO` (`:72-74`, returns
    `Option (Int x Int)`), `boolFeldAt` (`:77-80`, returns `Bool`), `typAt`
    (`:84-89`). The skeleton's uses (`fieldCount u t`, `boolFeldAt u t f = true`,
    `fieldRangeO u t f = some w` with `w.1 <= 0 /\ 0 <= w.2`) are name- and
    shape-plausible against these signatures. Elaboration is still unverified.
  - All 11 imports of the skeleton resolve to existing modules (checked
    `UebersetzeAllg2.lean` and `Sperren/SperreSem.lean` by glob; the rest appear
    as existing files in grep hits).
  - `structure StartPflicht`: `grammatik/Grammatik/Zielsatz/Kern/Spec.lean:1665`.
- BUILD-EVIDENCE.json is consistent with the author's story: four `./lean-probe`
  attempts, every one ending in a timeout with zero output bytes, plus honest
  `git status` transcripts. No `== N error(s)` line and no `./lean-bau` line were
  ever produced for the skeleton.
- My own tree does NOT contain `grammatik/Grammatik/X86/GvStartPflicht.lean`
  (glob: no files found), so this review introduced no contamination.
- Forbidden-token scan of the candidate Lean file: clean. Axiom status: vacuous
  (no theorems, no `#print axioms` run). Witness rule: not triggered (a lone
  `def` with no for-all-over-syntax premise needs no `_zeuge`).

## 3. Reasons for REPAIR (concrete)

1. **Unchecked Lean committed (HARD RULE 8).** Rule 8: "Never commit a red build:
   if you cannot get `./lean-bau` green, revert your Lean changes
   (`git checkout -- grammatik`) and commit only your report." The skeleton never
   produced a single `./lean-probe` error-count line, yet it is committed at the
   pinned HEAD. That it is inert (no import line) limits the damage but does not
   satisfy the rule.
2. **Missing mandatory file footer (HARD RULE 6).** The Lean file has no `CUTS:`
   comment block and no `#print axioms`. Every Lean file must end with one.
3. **Nothing to accept semantically.** No bridge statement, no obstruction
   theorem, no witness exists yet. ACCEPT would certify an unverified definition
   plus a plan; the plan's key steps (e.g. `sp0OkB_klingt` via the cited list
   lemmas, `sp0Of` via `typAt` unfolding, `gv_lowerAllg_requires` mirroring the
   S4 lemma, `gvInitWert` mirroring `GInit`) are all unexecuted by the author's
   own honest account.
4. **Task-shape finding is plausible but unverified.** The author notes the
   fragment cannot spell a `static` (`Glob := Empty`) so no single fragment unit
   pairs a non-zero static initialiser with an array. The `Glob := Empty` premise
   checks out (see section 2); the conclusion (no fragment unit carries both)
   and the proposed split witness (`uExp104` + exporter-side `gvInitWert`) are
   design, not proof. Worth keeping, not yet established.

Explicitly NOT held against the candidate: no fake closure (claims nothing
proved), no desired-correctness premise (no theorem at all), no weakened
guarantee, no existing-file edits, no touched optimiser files, report CUTS
honest, BUILD-EVIDENCE complete.

## 4. Repair prescription (minimal)

- Merge `MUSE-REPORT-1387.md` as the honest record of reading + plan.
- Drop `grammatik/Grammatik/X86/GvStartPflicht.lean` from the merge (or hold the
  whole candidate) until: one successful `./lean-probe` first line on the
  skeleton, a `CUTS:` block plus `#print axioms` appended per rule 6, and only
  then the import line and `./lean-bau`.
- Resume order per the author's plan section 3, one definition per check; first
  re-verify the four helper signatures by reading (done in section 2 above) and
  confirm `Int` decidable-LE elaboration of the `w.1 <= 0` conjuncts.

## 5. Blocker and limits of THIS lane (precise status)

- Shell file operations are restricted: `cp`/`rm`/`lake`/`lean`-direct are
  denied, and writes outside `MUSE-REPORT-1388.md` / `arbeitsprotokoll/` are
  denied. Consequences: (a) `./lean-probe` on the candidate's Lean file could
  NOT be run — the lane task suggests copying the candidate file into my own
  clone first, but creating
  `grammatik/Grammatik/X86/GvStartPflicht.lean` in my tree is outside my owned
  files (`OWN ONLY MUSE-REPORT-1388.md`) and deletion afterwards (`rm`) is
  denied, so the copy was not made; elaboration of `Sp0Ok` remains unverified
  by both lanes; (b) clone/branch verification, `git add`, `./lean-bau` and
  `./commit.sh` were allowed and used.
- `./lean-bau` last result line for this lane:
  `Build completed successfully (717 jobs).` (report-only tree, no Lean diff).

## 6. CUTS (of this review)

- PROVED: nothing about the candidate machine-checked (no candidate probe
  possible, see section 5). Base `./lean-bau` green (717 jobs) on my
  report-only tree.
- ESTABLISHED BY INSPECTION: file lists of section 1, signature/name pins of
  section 2, absence of forbidden tokens in the candidate diff, inertness of the
  committed skeleton (no import line, no existing-file edits).
- OPEN: elaboration of `Sp0Ok`; every plan item of the author's section 3; the
  `Initially`-follows-from-declarations theorem and the obstruction classes.
- `#print axioms`: never run (no build possible from this lane).
