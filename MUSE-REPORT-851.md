# MUSE-REPORT-851: Binding-surface closing

## What was done

New file `grammatik/Grammatik/X86/ComposeBindingSurface.lean` (244 lines)
plus one import line in `grammatik/Grammatik.lean`. It closes the
program-supplied binding surface by composition only:

- Closing interface `bindungsFlaecheOkB`: caller gate (`torOkB`),
  no-refusal legs (`c186VerweigertB`, `c187VerweigertB`, `m140VerweigertB`),
  stub shape (`bindungErstelltB`, `stubEndsTrapB`) and entry predicate
  (`eintrittOk`), reusing the accepted `GateStub` / `EntryState`
  definitions by name. No interpreter, decoder or executor is duplicated.
- `ComposeBindingSurface_verbindung`: generic over arbitrary admitted
  inputs (arbitrary gate, stub bytes, entry state, source call). From the
  seven decided admission legs plus one successful source call at actual
  values it concludes the composed admission AND the discharged
  implementation obligation (`Nonempty (InlinePflicht …)`, `RufEnsCheck`
  at the actual result), via the accepted `inlinePflicht_aus_rufAt` and
  `rufAt_ok_gibt_ens`. Every premise is used; the obligation/return
  conjuncts are derived, not restated.
- `ComposeBindingSurface_verbindung_zeuge`: joint companion instantiating
  all premises on the non-degenerate table-writing fixture (`setze`
  writes, `0 -> 5` memory change), with a reached `RufMaschineG` run, a
  real X86 byte write/read change (from `torStub_zeuge`) and the EBADF
  errno decode.
- Planted refusals, one per leg: `osName_beweist_nichts` (same gate
  number `1`, composed surface still refuses — OS names prove nothing),
  `bindung_verweigert_c186`, `bindung_verweigert_c187`,
  `bindung_verweigert_m140`, `bindung_verweigert_eintritt`, plus
  `zulassungOhneVertrag` (admitted stub+entry coexists with a refused
  entry contract — admission smuggles no user-logic obligation).
- CUTS block names the open legs with owners: source-to-byte lowering
  (lane 287), TSO/W/GX bridge and budget/cost transfer (see
  `CostSummary` CUTS), wider decoder coverage (`ValidatorSkeleton` /
  `ExtendedExecution` owners). `#print axioms` for all nine declarations.

No diagnostic/gift/example/CLI numbers, no MARKE_EMIT changes, no
source/checker/Spec/goal/emitter edits, no friend-reserved optimiser
files touched. Owned files only.

## Verification status — GREEN

- `./lean-probe grammatik/Grammatik/X86/ComposeBindingSurface.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau`: `Build completed successfully (511 jobs)`,
  including `Built Grammatik.X86.ComposeBindingSurface` and `Built
  Grammatik`.
- Axioms (`#print axioms`, probe output): every new theorem depends
  only on `[propext, Classical.choice, Quot.sound]` (the
  `Classical.choice` comes from the reused source-contract lemmas);
  no `sorryAx`, no extra axioms.
- Two probe iterations were needed: (1) `simp` with the `m140`
  refusal lemmas never fired (the rewrite holds — `rw` matches it —
  but `simp`'s matching left the goal mangled), fixed by
  `unfold` + `rw` + `simp`; (2) the witness application needed the
  `σ' = sinv` equation (second conjunct of `rufAt_ok_gibt_ens`, same
  shape as `inlinePflicht_aus_rufAt`'s use) transported into `hok'`
  before applying the closing theorem.
- Early in the session the `bash` tool was twice rejected by the
  permission classifier; a later retry succeeded and all checks above
  ran through the queued wrappers. Clone verified on `muse/851`.

## What remains open / handoff

Nothing from this lane: module proved, whole-project build green,
report written — ready for exact independent review and merge.
Missing producer legs stay explicit CUTS with owners (IR lowering
lane 287; TSO/W/GX bridge and budget transfer per `CostSummary`
CUTS; wider decoder coverage per `ValidatorSkeleton` /
`ExtendedExecution` CUTS).

Nothing in the lane task itself is believed wrong.
