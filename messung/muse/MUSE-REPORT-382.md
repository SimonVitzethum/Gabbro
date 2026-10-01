# MUSE-REPORT-382: Independent exact-candidate B4 review of 344 FenceDrain

## Scope and method

Reviewed the exact author snapshot in `.tmp/review/author-344/` (PATCH.diff,
OWNER-TASK.md, MUSE-REPORT-344.md, BUILD-EVIDENCE.json, snapshot file
`grammatik/Grammatik/X86/FenceDrain.lean`) against the accepted source in this
clone (base `f737a6f0`, same base as the author). Staged ONLY the candidate
module plus the one additive import line privately, ran `./lean-probe` and full
`./lean-bau`, then restored the tree (`git status` clean apart from this
report). No network, no other clones, no agent calls.

## Verification results (all reproduced locally)

- `./lean-probe grammatik/Grammatik/X86/FenceDrain.lean`:
  `== 0 error(s) in the COMPLETE output`; per-theorem axioms are none or
  subsets of `[propext, Quot.sound]` — standard, nothing beyond the goal axioms.
- `./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`,
  `Build completed successfully (386 jobs).`
- Staged file is byte-identical to the snapshot (`diff` clean).
- Forbidden-token scan with word boundaries (`sorry|admit|axiom|native_decide|
  unsafe`): zero hits in the candidate file.
- Ownership: PATCH touches exactly `grammatik/Grammatik/X86/FenceDrain.lean`
  (new, 369 lines), one import line in `grammatik/Grammatik.lean`, and
  `MUSE-REPORT-344.md`. No checker, Spec, goal, Typen, Rust, emitter, docs, or
  friend-reserved (`OptimizationRules`/`OptimizationWitnesses`) paths touched.
- Canonical reuse confirmed against this clone's `TSO.lean`: every depended-on
  name exists with the used shape — `TSOZustand`, `issueByte`, `loadByte`,
  `flushKern`, `zaunBereit`, `zaunBereit_iff_leer`, `flush_anderer_kern`,
  `flush_entfernt_kopf`, `flush_schreibt_kopf`, `flush_rahmen`,
  `issue_haengt_an`, `flush_leer`, `TSOSchritt`, `TSOErreichbar`,
  `pufferSetze` (`TSO.lean`), `zeugenSpeicher` (`Speicher.lean`). No second IR,
  no second evaluator, no source change.
- Premise use: every theorem's premises are used in its proof (checked by
  reading: `hne` feeds `flush_rahmen` via `Ne.symm`, `hempty`/`e1`/`e2` build
  the buffer shape, `hd` feeds the frame lemma, `hp` survives the rewrite).
  No `Prop`-typed premise; quantification is over data (`Nat`, `TSOZustand`,
  `Adresse`, `Byte`), never over contracts.
- Witnesses are non-degenerate and joint: `fdS2` carries a written table on
  each core (core 0 `[fdX := 1]`, core 1 `[fdY := 7]`), is reached from
  `fdStart` via two `TSOSchritt.issue` steps inside `TSOErreichbar`, and the
  drain observably changes canonical memory (`fd_speicher_aendert`, decided).
  The three `_zeuge` companions instantiate all premises jointly on this run.
  (`drain_fifo_ordnung` has no `_zeuge`, but rule 13 does not require one:
  no syntax-universal premise, no `ZEUGE:` line in the owner task.)
- Refusal is proved, not prose: `mfence_loest_fremd_nicht` exhibits by
  `decide` a state where core 0 is fence-ready while core 1 forwards its own
  buffered byte past canonical memory.
- NON-theorem honesty: `drain_laesst_fremd` proves the OBS-5 boundary (foreign
  entries survive byte-identical), and `mfenceZulaessig` is declared as
  validator/profile admission (`zaunBereit` alias), never as a hardware fault.
  The author's note correcting the task's witness sentence (a drain DOES change
  canonical memory observably; what is local-only is fence readiness and the
  foreign buffers) is accurate and matches `fd_lokal_nur`.
- English only (no umlaut hits); CUTS block and `#print axioms` for every main
  theorem present at file end.

## Findings

No material findings. Minor observations, neither blocking:

- `mfenceZulaessig` is a thin alias over `zaunBereit`; its content comes from
  the refusal theorem, which is proved — acceptable for the B4 local-half
  scope and honestly labelled.
- Full author HEAD `75274830e649fed40d400aa7fa99b6c3936efef0` taken from
  `.tmp/review/SNAPSHOT.json` (base `f737a6f0` matches this clone).

## Bounded claim

ACCEPT covers exactly: bounded local drain iteration over canonical
`flushKern`, per-core FIFO/frame facts, the proved NON-theorem that a local
drain never discharges a foreign buffer, the decided refusal that local fence
admission discharges no foreign/device read, and the two-core reached
memory-changing local-only witness. Not covered: any source/target simulation
(`W`/`GX`), lowering map, spawn/join/handler publication lemma (OPEN),
timing/cost, devices, multi-byte atomicity, LOCK RMW — all correctly left OPEN
in CUTS.

CANDIDATE: 344 75274830e649fed40d400aa7fa99b6c3936efef0
VERDICT: ACCEPT
