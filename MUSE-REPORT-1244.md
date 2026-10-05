# MUSE-REPORT-1244: exact review of candidate 1243 (AVX2 32-byte memory accesses)

Clone: `/home/simon/Dokumente/gabbro-muse/a1244`, lane 1244 (review only).
CANDIDATE: author 1243, pinned HEAD `215c680fe354a2c1234341d6a73ceafd91b417fd`,
base `ca33ef1b3eaa30c178343517c9fd20f32a914b58`,
snapshot `.tmp/review/SNAPSHOT.json`, diff `.tmp/review/author-1243/PATCH.diff`.
Owned file only: this report. No source file was created or edited.

## Scope read

Author task `lanes/1243.md` (also `author-1243/OWNER-TASK.md`): NEW FILE
`grammatik/Grammatik/X86/Avx2Mem.lean` + one import line in
`grammatik/Grammatik.lean`. VMOVDQU / VMOVDQA loads/stores as
footprint-checked accesses on `HwMaschine`/`HwSchritt` via accepted TSO byte
equations; 32-byte store = 32 byte issues; no whole-vector atomicity; named CPU
profile + CPUID/XCR0/OS-state gates; two-core witness with owner-only
forwarding and drain.

Snapshot files: `MUSE-REPORT-1243.md`,
`grammatik/Grammatik.lean`, `grammatik/Grammatik/X86/Avx2Mem.lean`
(2387 lines). Snapshot reports `clean: true`.

## Checks performed (read-only static checks + fresh own-tree build)

Fresh `./lean-bau` in this clone (review-only lane, no Lean changes):
`Build completed successfully (662 jobs)`, exit 0, on `muse/1244` at
`2f139347`. This confirms the own-tree build is green; the candidate-tree
build result below comes from the author's pinned evidence.

1. Forbidden tactics: grep over `author-1243/grammatik/Grammatik/X86` for
`sorry`, `admit`, `axiom`, `native_decide`, `unsafe` (strict patterns incl.
`^\s*sorry`, `^axiom `, `native_decide`, `unsafe`): NO matches. The only
hits for the loose pattern are English words (`admitted`, `admits`) in
comments/report, not tactics.
2. Existing files untouched except one import: `PATCH.diff` shows exactly
`diff --git a/grammatik/Grammatik.lean` with one added line
`+import Grammatik.X86.Avx2Mem`, plus the new file and the author report.
No other existing file appears in the diff headers.
3. Accepted evaluator lifted, not copied: grep for
`def vecWrite|def vecRead|def issueByte|def loadByte|def flushKern|def HwSchritt|structure HwMaschine|def HwAdapter`
in the candidate file: NO matches. Usage grep confirms the file calls the
accepted `issueByte`/`loadByte`/`flushKern`/`vecRead`, uses `vecFuss` halves,
defines `adapterAvx2Mem : HwAdapter Avx2MemEreignis` and the extended step
`HwAvx2Schritt` with embedding/projection theorems
`hwAvx2Schritt_einbettet`/`hwAvx2Schritt_projiziert` and `hwAvx2Schritt_wf`
(`HwWf` preserved). Imports are only accepted modules
(`Typen`, `Speicher`, `TSO`, `HardwareExecution`, `WordAccessGrouping`,
`Vektor`, `FeatureProfile`, `VectorHardwareProfile`, `VectorFootprints`,
`Ausfuehrung`); no sibling AVX2 lane is imported.
4. Premise use: grep for `intro _`, `have _ :=`, `forall rho`, `forall v`:
NO matches. Spot-read theorems take address/vector/machine/proof arguments
used in bodies; no `Prop`-typed premise observed.
5. Planted refusals: present by name and proved:
`avx2Gp_ausgerichtet_fehler`/`_ok`, `avx2Gp_nie_unausgerichtet`,
`avx2Mem_ohne_profil`/`_ohne_cpu` (+ braucht/neg lemmas),
`avx2Speichern_verweigert_bei`, `avx2SpeicherSchritt_schreibrecht`,
`avx2LadeSchritt_leserecht`, `adapterAvx2Mem_verweigert_alt/_fehler`,
`HwAvx2Schritt` `.fehler`/`.verweigert` arms, `avx2Wit_neg_cpu`,
`avx2Wit_fehler_schritt`, `avx2Gruppe_verweigert_bei_fremdeintrag`.
6. Witness non-degenerate: `avx2WitS0`/`avx2WitS1` (core 0 issues 32 entries:
`avx2Wit_s1_buflen : ... = some 32`), `avx2Wit_weiterleitung` (core 0 forwards
whole value), `avx2Wit_fremd_alt` (core 1 reads zero), `avx2Wit_anfang_null`
plus `avx2Wit_spuelung_aendert_speicher`/`_letzt` (drain changes memory
`0x01`/`0x04`), `avx2Wit_fremd_neu`, torn halves `avx2Wit_teil_neu/_alt`,
machine-level `avx2Wit_store_schritt` (successor carries 32-entry buffer and
is a `HwAvx2Schritt`), `avx2Wit_fehler_schritt`, `avx2WitStart_wf`, joint
`avx2Wit_zeuge` (15 conjuncts: two cores, buffered store, owner-only
forwarding, memory-changing drain from both cores, torn halves,
alignment/gate/profile refusals, well-formedness). Memory-changing step and
two cores both present.
7. Silicon: `avx2GpFehler` = aligned faults exactly on `a.toNat % 32 != 0`,
unaligned never faults; gate `avx2MemZugelassen` = named profile
(`avx2ProfilName = 7`) AND `stufenCpuBereit ... .avx256` AND
`kontrollSseFrei` + `cr4Osxsave` AND `merkmalZugelassen ... .paketInt128`.
Hardware reference present clone-local:
`.tmp/HARDWARE-REFERENCES/` (Intel SDM 325462-093US Sept 2026, sha256
`a4a62e...`, verified 2026-10-02; scope notes Intel-only, no AMD). Author
honestly states VMOVDQA-specific extract lines were not pulled, facts are
stated-not-proved, and no correspondence is claimed. CUTS repeats this and
lists open: no hardware correspondence, no vector atomicity (tearing proved
via `avx2Drain_teilt16`), no YMM file (State lane), no VEX decode (Vex lane),
no lane arithmetic (Ops lane), no fetch pinning, no trap classes beyond
#GP/permission, no W/GX bridge, no source/IR/loader/entry/budget link.
No claim larger than the proof observed.
8. Axioms: file ends with CUTS block + 39 `#print axioms` lines
(`avx2GpFehler` ... `avx2Wit_store_schritt`). Build evidence final probe
lists each main theorem within `propext`/`Classical.choice`/`Quot.sound`
(e.g. `avx2Wit_zeuge` depends on `[propext, Quot.sound]`); many depend on no
axioms at all. Standard goal-allowed set, no new axiom.

## Build evidence (author-tree evidence + fresh own-tree run)

`author-1243/BUILD-EVIDENCE.json` last entry (candidate tree):
`./lean-bau` -> `== exit 0; 0 error line(s) in the COMPLETE output`,
`Built Grammatik (642 jobs)`, with per-theorem axiom lines all inside the
standard set. Final `./lean-probe` entries: `== 0 error(s) ... exit 0`.
Intermediate entries show red iterations during development, all resolved in
the final state.

Own-tree check by lane 1244: `./lean-bau` run in
`/home/simon/Dokumente/gabbro-muse/a1244` on `muse/1244` finished with
`Build completed successfully (662 jobs)`, exit 0 (tail shows only
axiom-dependency info lines plus the success line; job count differs from
the author's 642 because this clone's base is newer). The candidate tree
itself was reviewed from the pinned snapshot (`PATCH.diff` + file copy),
not rebuilt here, since rebuilding the candidate requires the author clone
which is outside lane scope.

## Notes on the task text

- `.tmp/LANE.md` line 25 says `CANDIDATE: 1243 <full pinned HEAD>` with the
hash blank; resolved via `.tmp/review/SNAPSHOT.json`
(`215c680f...`). Review used that pinned snapshot (`PATCH.diff` + file copy),
not a live author clone (direct clone access is also outside lane scope and
was not attempted beyond one blocked probe).
- Author base `ca33ef1b` is older than this clone's `Grammatik.lean` tail
(which already contains `Avx2Ops`/`Avx2State` etc.); candidate adds its import
at its own base tail. Exact-review scope only; merge rebase is the
coordinator's business.
- Two benign unused-variable linter warnings noted by the author at
`Avx2Mem.lean:1306/1310` match the evidence output; not a gate failure.

## VERDICT: ACCEPT

Candidate 1243 at pinned HEAD `215c680fe354a2c1234341d6a73ceafd91b417fd`
meets the exact-review bar: owned files only with a one-line import,
no forbidden tactics, standard axioms with `#print axioms` per main theorem,
accepted evaluator lifted (no canonical redefinition), refusals proved by
name, non-degenerate two-core memory-changing witness with joint `_zeuge`,
silicon facts in documented shape with honest stated-not-proved CUTS and no
hardware-correspondence or W/GX claim. No unsupported desired-correctness
premise, no weakened guarantee, no fake closure found in the pinned diff.
