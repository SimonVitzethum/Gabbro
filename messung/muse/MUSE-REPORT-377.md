# MUSE-REPORT-377: Independent exact-candidate A5 review of 339 LockedOps

## Scope and method

Reviewed snapshot for author 339 (`SNAPSHOT.json`: head
`aec553840d6efcc5b2c2aa863287cb31165b85c3`, base `f737a6f0`,
files `MUSE-REPORT-339.md`, `grammatik/Grammatik.lean`,
`grammatik/Grammatik/X86/LockedOps.lean`, clean true) against
`OWNER-TASK.md` (plan row A5), the PATCH, BUILD-EVIDENCE, and the
actual canonical sources in this clone (`TSO.lean`, `Speicher.lean`,
`Zugriffe.lean`, `Typen.lean`). Staged the candidate module plus the one
additive import privately, reproduced `./lean-probe` (0 errors, axioms as
claimed) and full `./lean-bau` (green, 387 jobs on this newer base, which
additionally contains `SpillPrivate`), reproduced the `gabbro_ziel` axiom
probe (unchanged), then restored the tree: this commit is report-only.

## What the candidate delivers (verified, not just reported)

- New `SperrBefehl` (`.xadd64 addr delta`, `.mfence` only), `LockEreignis`
  per-event records (`kern/lesen/schreiben/gelesen/geschrieben/istRmw/istZaun`,
  footprints reuse canonical `Fuss`), `ausgerichtet8` guard that gates ONLY
  the LOCK forms, `lockSchritt`/`casSchritt` over canonical `TSOZustand`
  via `read64`/`write64`, `lockKosten`/`casKosten`/`RmwForm`. No second
  evaluator for the 14 pilot `Befehl` forms (count confirmed in
  `Typen.lean`); no existing form redefined.
- Theorems all use every premise (checked by reading each proof; `simp`/`rw`
  consume `hbuf/hrd/hali/hwr/hgleich/hfehl/hles/hne/hstep` where present);
  no `Prop`-typed premise; no `intro _` / `have _ :=` discards (grep clean);
  no `sorry/admit/axiom/native_decide/unsafe` (grep clean); conclusion never
  restates a premise.
- Witnesses are joint and memory-changing: two-core locked add 0 -> 5 -> 12
  at aligned `lockAddr` with `rfl` steps and `decide` read-backs; fence on
  core 0 while core 1 keeps a pending store (local-only, no foreign drain
  claimed); CAS install and CAS stutter; split load/store refusal built from
  REAL `zugriff` footprints of genuine `load64`/`store64` for every
  pre-state. Rule-13 table clause correctly identified as N/A (no source
  premises); the memory-changing-run non-degeneracy is met.
- Safety corrections honoured: `none` refusals are validator/profile
  admission (never a hardware fault); ordinary unaligned accesses untouched;
  shape cost is syntactic (`lockKosten = 1`), CAS retry proved unbounded
  (`cas_schleife_unbeschraenkt`), cycle-bound and W/GX refinement types kept
  EMPTY (`keine_lock_zyklus_schranke`, `kein_lock_nach_w`); CUTS disclaims
  flags/registers/RIP, fetch/decode/ABI, silicon atomicity, source/goal.
  `mfence_ordnung` proves own-buffer forwarding absence only. All physical
  facts used (`Fuss`, `write64` frame/permissions, `neuestens`, empty-buffer
  gate same as `zaunBereit`) resolve against actual canonical definitions.
- Bounded claim is truthful. Two scoping observations, neither a defect:
  (a) `lock_xadd_atomar` names model-internal single-step indivisibility;
  the CUTS block explicitly leaves the silicon correspondence OPEN, which
  bounds the name correctly. (b) `RmwForm`/`rmw_nur_mit_lock` is a syntactic
  shape predicate over the author's own event type, so its force on a real
  lowering depends on the consumer constructing events honestly; CUTS places
  that obligation on the consumer. Both match the task's "helper, not
  validator" direction.
- Ownership exact: only the new module, one additive `Grammatik.lean`
  import line, and the author report. No checker/Spec/goal/Rust/emitter/
  docs/friend paths. (Note: snapshot base predates `SpillPrivate`; the
  `Grammatik.lean` merge is a clean union — reproduced here with both
  imports, 387 jobs green.)

## Reproduction (this clone, muse/377)

- `./lean-probe grammatik/Grammatik/X86/LockedOps.lean`: 0 errors; all 19
  `#print axioms` lines at most `[propext, Quot.sound]`, two axiom-free —
  exactly as the author reported.
- `./lean-bau`: `Build completed successfully (387 jobs)`.
- `gabbro_ziel` probe: `[propext, Classical.choice, Quot.sound]` — unchanged.
- Tree restored before this report commit (`git status` clean except this file).

## Verdict rationale

Task actually done, generic real TSO-memory semantics, no assumed
conclusions, no unused or Prop-typed premises, contracts N/A correctly
handled, bounded claim with explicit CUTS, standard axioms, non-degenerate
joint witnesses, proved (not merely exemplified) refusal, no guarantee
weakened anywhere. No material finding; the two observations above are
already bounded inside the candidate's own CUTS and need no change.

CANDIDATE: 339 aec553840d6efcc5b2c2aa863287cb31165b85c3
VERDICT: ACCEPT
