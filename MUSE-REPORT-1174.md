# MUSE-REPORT-1174: exact review of candidate 1173 (hosted/freestanding profiles)

CANDIDATE: 1173 c6677edd11818267cb85b19caa3eb38ce5a0043f
VERDICT: ACCEPT

## Verdict

Substantive verdict ACCEPT, unchanged from the prior commit `5db9dc24`; this
update only adds the machine-readable lines above. Reviewed author lane 1173
at pinned HEAD `c6677edd11818267cb85b19caa3eb38ce5a0043f`
(base `062b979a6271b7b3044ab06be3f3cde411a0d4f1`), reviewed from the exact
snapshot `.tmp/review/author-1173/` (`SNAPSHOT.json`, `PATCH.diff`, full new
file, `MUSE-REPORT-1173.md`, `BUILD-EVIDENCE.json`). No other source was read
for the verdict.

## What was checked

New file `grammatik/Grammatik/X86/PipelineProfiles.lean` (456 lines, 5 new
defs, 22 named theorems) plus exactly one appended import line in
`grammatik/Grammatik.lean`. Snapshot file list confirms 3 changed paths only
(report, import line, new file); `OptimizationRules.lean` /
`OptimizationWitnesses.lean` untouched.

- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`: exact regex over the new
  file finds zero code occurrences (single `admit` substring is the English
  word inside a doc comment, "admit no profile"). No `split_ifs`,
  `norm_num`, `ring_nf`. No `^axiom` declaration.
- `#print axioms` standard: author build evidence lists every main theorem at
  `[propext]` or `[propext, Quot.sound]` (via reused producer lemmas), a
  subset of the goal axioms; `profilEintritt`/`profilAbi` axiom-free. No new
  axiom. `CUTS` block present plus `#print axioms` for all 27 names.
- Existing files untouched except one import line: `PATCH.diff` shows only the
  import append; all semantics come from reuse, not edits.
- Every premise used: each projection/refusal/closing theorem threads all its
  hypotheses (`hadm` via `profilOk_teile`, `hf`/`hs` into the producer step,
  `hanf`/`hende`/`hmis`/`hrip`/`href`/`hbild`/`hmx` into the producer refusal
  rewrite, `h` into `zuege_lauf`). No `intro _`, no `have _ :=`, no
  `Prop`-typed premise, no quantified-away contract, no conclusion restating a
  premise.
- Lifted, not copied: the file defines only `ZielProfil`, `profilEintritt`,
  `profilAbi`, `profilOk`, `profilProlog`. No duplicate loader, decoder,
  executor, IR or source interpreter (regex for `^def (fetch|schritt|geladen|
  valX86|stuetzOk|stuetzSchritt|...)` empty). Every lemma applies the accepted
  producer by name (`hakenZulassung_*`, `ComposeEntryHooks_verbindung`,
  `stuetzOk_teile`, `stuetzSchritt_weiter/_verweigert_ohne_fetch`,
  `stuetz_verweigert_*`, `prolog_gerade`, `zuege_lauf`); producer names were
  spot-verified to exist in this checkout (`ComposeEntryHooks.lean`,
  `ComposeSupportBytes.lean`, `PipelineEntry.lean`, `EntryExecution.lean`,
  `GateStub.lean`, `TableLayout.lean`, `Bild.lean`, `ValidatorSkeleton.lean`).
- Refusals really refuse: 7 refusal theorems (anfang, ende, status, unlisted
  RIP, gate, image, MXCSR), each `unfold profilOk` + producer refusal rewrite
  + `simp`. The joint witness decides 4 of them (missing anfang via `rfl`,
  changed status via `decide`, W^X image via `valWx_verweigert`, clobbered
  gate via `decide` on `torAusClobber`); the other 3 legs exist as proved
  refusal theorems.
- Witness non-degenerate: `pipeline_profil_verbindung_zeuge` admits BOTH
  profiles on the minimal image (`profil_gehostet_ok`, `profil_frei_ok` by
  `decide` on `valZeuge`/both hooks/zero status), carries the fetched `ret`
  (`zulassung_fetch_ret`) with its executed step (`zulassung_schritt_ret`, a
  reached run from checked bytes), a real memory-changing write/read
  (`schreibLese_zeuge`: `v != 0`, `write64`/`read64` round-trip,
  `m.bytes != m'.bytes`), a table some function writes
  (`zeugenU_schreibt`: `setze` writes `konto`), and 4 planted refusals. Two
  cores N/A: single-core profile scope, no concurrency claim made.
- Silicon facts against the supplied Intel SDM snapshot (edition 093,
  `.tmp/HARDWARE-REFERENCES/REFERENCES.json`): no new encodings. Reused
  `sysvParameter = [.rdi, .rsi, .rdx, .rcx, .r8, .r9]` (correct System V
  integer order); `profilAbi` states it per profile as data so a future target
  varies it without forking the validator. `ret` single byte, `trapBytes =
  [0x0F, 0x05]` reused literally as the documented syscall trap (never decoded
  through the pilot decoder), `mxcsrGueltig` reused, `hostedMain`/`nolibcMain`
  mapping matches IMAGE-ABI section 5. Leaving CPU feature selection
  (`ComposeProfileSelect.waehleNull/fallback`) with lane 844 is correct: it is
  CPU tuning, not an OS profile. No AMD/silicon proof claimed.
- CUTS honest, no overclaim: the file and report state NO source
  correspondence (lowering closure waits on lane 287 IR, no substitute
  invented), NO hardware/silicon correspondence, NO TSO/W/GX bridge, NO
  budget/cost transfer, no multi-step control flow, no relocation re-decoding,
  no kernel behaviour beyond the named assumption, and `verweigert` as absence
  of a transition, never termination. The generic closing
  (`pipeline_profil_verbindung` over arbitrary admitted inputs) plus
  first-step (`profilOk_erster_schritt`), support-coverage
  (`profilOk_stuetz_schritt/_verweigert`) and entry-run (`profilProlog_lauf`
  via `zuege_lauf`) theorems satisfy the task's "in the style of
  `pipeline_correct_entry`" at the byte level without inventing the missing
  source leg, as architecture decision 594 requires. No W/GX or
  hardware-correspondence claim anywhere.

## Build evidence

- Author evidence: `./lean-probe` on the new file `0 error(s)`; full
  `./lean-bau` `Build completed successfully (608 jobs).` (intermediate red
  probes during construction are recorded in `BUILD-EVIDENCE.json` and all
  resolved in the pinned HEAD).
- Independent reviewer run in this clone (`muse/1174`, clean, candidate not
  applied): `./lean-bau 2>&1 | tail -15` ends with
  `Build completed successfully (608 jobs).` (last info lines are the
  pre-existing `TsoReadBridge.lean` axiom prints; this clone's master has
  `TsoReadBridge` where the candidate base has `PipelineProfiles`, hence the
  same job count with a different tail file — expected base drift, not a
  candidate defect; merge must take the import union).

## Follow-ups (not blockers)

- The joint witness decides 4 of 7 refusal legs; `ohne_ende`, `unlisted`,
  `ohne_mxcsr` are proved as theorems but not instantiated with `decide` in
  the witness. A future lane may extend the conjunction to all 7.
- `profilOk_folgen` drops one `stuetzOk_teile` component with `_`; harmless
  (a derived conjunct, not a premise) but naming it would document which
  support half is intentionally not surfaced.
- Source correspondence remains OPEN behind lane 287 IR, exactly as the CUTS
  declares.

## Ownership

Owns only this file `MUSE-REPORT-1174.md`. No Lean, Rust, or guardian changes
made or needed for this review.
