# MUSE-REPORT-475: Independent exact-candidate review of 427

Clone `/home/simon/Dokumente/gabbro-muse/a475`, branch `muse/475` — verified.
Reviewed snapshot head `f3e57c14f1dad608d47ceb49936a4a006d848668`
(base `0b3132b7bb8bf108b3fd1613c70bc0955051f130`), files
`MUSE-REPORT-427.md`, `grammatik/Grammatik.lean`,
`grammatik/Grammatik/X86/RegisterInterference.lean` (PATCH 522 lines).

## Method

Read `.tmp/review/SNAPSHOT.json`, `author-427/OWNER-TASK.md`,
`MUSE-REPORT-427.md`, `BUILD-EVIDENCE.json`, and the full `PATCH.diff`.
Checked every `regLiest`/`regSchreibt` row against the canonical
`schritt` in my clone's `grammatik/Grammatik/X86/Ausfuehrung.lean`
(lines 69-132) and `Befehl` in `Typen.lean` (14 constructors);
checked `regSet`, `schrittRegister`, `schritt_movImm64_reg`
(Ausfuehrung.lean 408-413), `zeugeZustand`/`zeugeReg` (765-773),
and the `Stapel.Belegung` collision (Stapel.lean 213).
Grepped the candidate file for `sorry`/`admit`/`axiom`/`native_decide`/
`unsafe`/`intro _` (only hit: the English word "admitted" in CUTS
prose and `#print axioms` lines — no tactic/keyword use).
Staged the supplied candidate files temporarily in my clone,
ran `./lean-probe` and `./lean-bau`, then restored the tree
(`rm` + `git checkout -- grammatik/Grammatik.lean`;
`git status --short` clean before writing this report).
Did not read another clone; did not touch the pool.

## Findings

1. Section 1 (reads/writes) is semantically correct against canonical
   `schritt`: all 14 pilot constructors covered exhaustively
   (Lean exhaustiveness enforces this; build green confirms);
   `movImm64` reads none; `cmp`/jumps write none; stack/control
   forms read/write `rsp`; `load` reads base / writes dst;
   `store` reads base+src / writes none. `jumpIf32` reads flags,
   not registers, so `[]` is correctly scoped; flags stay owned by
   `Ausfuehrung`/`FlagBeweis` per CUTS.
2. Section 2 check is genuinely fail-closed: `kanteOk`/`bindungOk`/
   `lebtOk` return `false` on any missing assignment; `belegungOk`
   conjoins all three lists. Liveness/edges/bindings are DECLARED
   inputs — no invented liveness, no second IR, no new executor.
   Only canonical `regSet`/`schrittRegister`/`schritt` are used.
3. Check-implies facts use every premise (verified by reading each
   proof: `h` supplies the conjunct, membership selects the element;
   `belegungOk_ohne_reserviert` uses `hr` by rewrite;
   `belegung_schreibt_ohne_clobber` threads `h`/`hm` through the
   edge witnesses and closes with `regSet_fremd` in the correct
   direction `Ne.symm hne`). No conclusion restates a premise;
   no `Prop`-typed premises; no syntax quantification, so no
   `_zeuge` obligation — and non-vacuity holds anyway via the
   `decide`d positive (`belegungOk_positiv = true`) jointly
   inhabited with `belegung_zeuge_null/eins`, plus four `decide`d
   refusals and the real two-`schritt` run
   `probe_belegung_unabhaengig` (`rax=7`, `rcx=9` through actual
   `schritt` on `zeugeZustand`, which needs no memory since both
   steps are register-only with `laengeOk 3 = true`).
4. Axiom evidence authentic: my independent `./lean-probe` prints
   exactly the claimed dependencies (`regLiest`/`regSchreibt`/
   `schrittRegister_erhaelt_fremd` axiom-free; the rest
   `[propext]` or `[propext, Quot.sound]`), all subsets of the
   `gabbro_ziel` standard set. Umbrella `./lean-bau` green in my
   (newer, 410-job) tree too, so no base-drift fragility.
   The report's account of transient `failed to create thread`
   crashes matches the queued-build evidence trail and my own
   observation of queued contention; the final green line is real.
5. Trust boundaries respected: liveness validation, source lowering,
   ABI pinning beyond `rsp`, simulation, cost, contracts, timing,
   W/GX concurrency, TSO bridge and whole-image claims are all
   explicitly OPEN in CUTS, matching the task's "state how future
   accepted IR supplies validated liveness" instruction.
   `Stapel.Belegung` collision genuinely exists; the `RegBelegung`
   rename was required. Friend files, checker, Spec, goal, Rust,
   emitter untouched; `Grammatik.lean` diff is one additive import.
6. Minor notes, NOT repair-grade: `import Grammatik.X86.Zugriffe`
   is unused (no `Zugriffe` identifier occurs in the file);
   `regSchreibt (.pop64 .rsp) = [.rsp, .rsp]` is list-redundant
   but set-correct and conservative; a self-edge `(u,u)` always
   refuses (fail-closed conservative). None weakens safety or the
   stated claim.

## Reproduction results (my clone, candidate files staged)

- `./lean-probe grammatik/Grammatik/X86/RegisterInterference.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`, axioms as above.
- `./lean-bau`: `Build completed successfully (410 jobs)` including
  `Built Grammatik`. (410 vs author's 393: my base is newer with
  more X86 modules; the candidate builds on both.)
- Tree restored before this report; this commit contains ONLY
  `MUSE-REPORT-475.md`.

## Open

Nothing open on the candidate's bounded claim. The OPEN items are
the author's own CUTS (future IR-supplied validated liveness,
ABI pinning extension, source allocation refinement) — correctly
declared, not defects.

CANDIDATE: 427 f3e57c14f1dad608d47ceb49936a4a006d848668
VERDICT: ACCEPT
