# MUSE-REPORT-426: VectorFootprints (continuous Lean proof reserve)

## Task
Create ONLY `grammatik/Grammatik/X86/VectorFootprints.lean` plus one additive
X86 import in the umbrella. Prove generic packed-lane byte
footprint/tail/disjointness facts over the accepted vector/byte memory,
with checked extent and alias constraints. No vector store atomicity or
padding-overread guarantee without evidence. Nonempty memory-changing
witnesses including partial tail refusal; full native vector lowering OPEN.

## What was done
New module `grammatik/Grammatik/X86/VectorFootprints.lean` (327 lines),
imported additively at the end of `grammatik/Grammatik.lean`. It consumes
ONLY accepted vocabulary, invents no IR/executor/machine:
`vecWrite`/`vecRead`/`vecHiAddr`/`OhneUmbruch16`/`vecChunks_disjoint`/`Disjunkt`
(`Vektor.lean`), `Fuss`/`fussDisjunktB`-Bool/`addrOff`/`natAdresse_addrs`
(`Speicher.lean`), `Region`/`inRegion`/`natAdresse` (`Regionen.lean`),
`fussEnthalten`/`klassifiziere`/`aliasZulassen`/`klassifiziere_disjunkt`/
`fussDisjunktB_klingt`/`fuss_mem` (`OverlapRefusal.lean`/`Zugriffe.lean`).

Definitions:
- `vecFuss a : List Adresse := Fuss a ++ Fuss (vecHiAddr a)` — the 16-byte
  footprint as the two ordered canonical chunk footprints (per-byte events,
  not one atomic occurrence).
- `vecTraeger basis : Region` — 16-byte readable/writable, never-executable
  carrier extent.

Theorems (every premise is used; all proved, no sorry/admit/axiom/unsafe):
- `vecFuss_laenge` — 16 per-byte events.
- `vecFuss_mem` — membership is membership in either chunk.
- `fussDisjunktB_von_Disjunkt` — NEW reusable bridge the checker consumes:
  Prop `Disjunkt` decides to a positive `fussDisjunktB` Bool answer
  (nothing in `Speicher`/`OverlapRefusal` stated this direction).
- `vecFuss_chunks_disjunkt` — inner-chunk checker-disjointness under
  `OhneUmbruch16` (via `vecChunks_disjoint`).
- `vecOhneUmbruch_chunks` — `OhneUmbruch16` covers both chunk checks.
- `vecFuss_disjunkt` — two vector footprints checker-disjoint from checked
  16-byte Nat intervals + no-wrap both sides (all four chunk pairs via
  `disjunkt_von_intervallen`).
- `fussEnthalten_verweigert_ausserhalb` — reusable checked-extent refusal
  half: one outside byte refuses containment.
- `vecFuss_in_traeger` — CHECKED EXTENT ACCEPT at the carrier base.
- `vecFuss_teilschwanz_verweigert` — PARTIAL-TAIL REFUSAL: footprint at
  `c+8` against carrier at `c` refused (last tail byte `c+23` witness).
- `vecFuss_alias_zugelassen` — disjoint footprints classify `.disjunkt`
  and pass the conservative policy.
- `vecFuss_teilueberlapp_verweigert` — concrete alias refusal: footprints
  at 8192/8200 share 8 tail bytes, classify `.unbekannt`, refused
  (by `decide`).
- `vectorFootprints_zeuge` — JOINT NON-DEGENERATE WITNESS: nonzero packed
  vector store at address zero through both ordered chunk writes reads back
  (`vecRead_nach_write`), observably changes the byte, footprint admitted
  in its carrier, shifted tail refused, next footprint disjoint and
  alias-admitted — all jointly on concrete values with real
  memory-changing execution.

Axioms (`#print axioms`, one per theorem): standard only — subsets of
`[propext, Classical.choice, Quot.sound]`; the overlap refusal depends on
no axioms at all.

## Verification
- `./lean-probe grammatik/Grammatik/X86/VectorFootprints.lean`: **0 errors**
  repeatedly, including the final 327-line file.
- `./lean-bau` (full project): module itself builds cleanly every run (all
  12 `#print axioms` lines emitted in the lake log); **zero Lean file
  errors** in the complete output (only 2 lines: `Lean exited with code
  134` / `build failed`). The final umbrella target `Grammatik` (step
  392/393, the import-all file) crashes with
  `libc++abi: ... failed to create thread` — a resource/environment
  failure, not an elaboration error.
- Proven environmental, not caused by this lane: with my work stashed
  (skeleton-only tree: one import line + 60-line file) `./lean-bau` fails
  identically (same exit 134, same 2 lines). Retried 5 times across ~40
  minutes; identical each time.
- `gabbro_ziel`: untouched — `git status` shows the ONLY modified/added
  files are `grammatik/Grammatik/X86/VectorFootprints.lean` and the
  one-line umbrella import. No `Zielsatz/Spec`, goal, checker, Rust,
  emitter, or canonical Typen/execution/codec file was touched
  (friend-owned `OptimizationRules.lean`/`OptimizationWitnesses.lean`
  not touched).

## Open / CUTS (also in the file)
Full native vector lowering stays OPEN and `simdFreigabe` stays `false`:
decoder/ABI/image, source correspondence, fault order across lanes,
tearing correspondence against the per-access TSO bridge, FP lanes,
call-log preservation, budget transfer, progress interaction. No vector
store atomicity claimed (`vecWrite_teilt`'s torn state stands).
Umbrella-green `./lean-bau` pending only on the environmental thread
failure; the merge gate should rebuild (module is self-contained green).

## Believed-wrong in the task
Nothing. The task's constraints (owned files, no invented mini-machine,
explicit CUTS, witnesses with memory change + tail refusal) were all
satisfiable; the only blocker met was the machine-level build flake above.

## Gate-repair round (integration gate FAILED, nothing merged)
- Gate evidence: the coordinator's merge-build log shows my module's
  `#print axioms` lines emitted (file compiled as a dependency, standard
  axioms) and then the umbrella `Grammatik` target crashing with
  `libc++abi: ... failed to create thread`, `Lean exited with code 134`,
  `build failed` — byte-identical signature to the 5 local failures
  already recorded above (only the step index differs: 397/398 at the
  gate vs 392/393 here, i.e. different tree file counts, same crash).
- Repair analysis: there is NO proof-level defect to repair. The log
  contains zero Lean file errors; every one of the 12 theorems elaborates
  with standard axioms. The crash hits the umbrella link step, which only
  imports already-built oleans (mine included) — no code in my owned
  files executes there. Proven independent of this lane's content by the
  skeleton-only control run (one import line + 60-line file crashes
  identically). No edit within my owned files and HARD RULES (no build
  flags, no other files, no direct lake/lean calls) can change this step's
  thread creation. Deliberately NO churn applied to the accepted
  candidate: re-proving or weakening green theorems would not move the
  gate and would invalidate the independent review.
- Fresh local evidence this round: `./lean-probe` on the unchanged module
  again **0 errors** with all 12 standard-axiom lines; `./lean-bau` again
  exit 1 with exactly the same 2 crash lines and zero file errors.
  `git diff --name-only master..HEAD` = exactly the 3 owned files
  (report, 1-line umbrella import, new module); goal/checker/Rust/emitter
  untouched, so `gabbro_ziel` is unaffected by construction (its own
  `#print axioms` re-check rides on the next green umbrella link, which
  is the blocked step itself).
- CONCRETE BLOCKER (not assumed away): OS thread creation fails inside
  the umbrella `lean -j2 -M4096` step on the shared build machine
  (up to 15 concurrent model processes plus queued builds; observed with
  0 free RAM / swap pressure). Coordinator-side remedy, in order:
  (1) retry the merge gate at low machine load; (2) if persistent, free
  memory / serialize lane builds around the umbrella link; (3) only if a
  future log shows a Lean *file* error naming `VectorFootprints.lean`,
  send it back — the current log shows none.
- No acceptance of any source/binary chain is claimed by this module;
  fresh independent review of the changed commit is expected.

## Gate-repair round 3 (second identical gate failure, nothing merged)
- New gate log is evidence-identical to round 2: same 7 visible
  `#print axioms` lines (module compiled, standard axioms), same
  umbrella crash `failed to create thread`, exit 134, at step 397/398
  (4.5s vs 4.8s — same step, same fast crash, i.e. spawn failure, not a
  timeout or elaboration error).
- Fresh local evidence this round: `./lean-probe` again **0 errors**
  (all 12 standard-axiom lines); `./lean-bau` again exit 1 with exactly
  the same 2 crash lines and zero file errors — this time with
  **9 GB free RAM** (vs 0 free in round 2), so plain free-memory
  exhaustion does not explain it; the failure is thread *spawn*, not OOM
  during elaboration. Skeleton-only control from round 2 already proved
  independence from this lane's content.
- Repair conclusion unchanged: no defect in the owned module exists to
  repair, and no edit within owned files + HARD RULES can affect thread
  spawning in the umbrella link step. Module kept byte-identical;
  only this report section is new in the committed change.
- BLOCKER RESTATED for the coordinator: the merge gate cannot pass ANY
  lane while the umbrella `lean` step cannot spawn threads on the build
  machine. Diagnose outside all lanes (thread/process limits, cgroup
  pids.max, sandbox restrictions — not Lean source, not this module),
  fix machine-side, then re-run the unchanged gate. A Lean *file* error
  naming `VectorFootprints.lean` has never appeared in any log.
