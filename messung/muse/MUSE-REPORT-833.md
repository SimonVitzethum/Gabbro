# MUSE-REPORT-833: Composition closing — call-log ghost closing

## Task
Close inlining/selection with GHOST call/return events (actual values, reason
channel, order); FolgeG order loss refuses. Owned files only:
`grammatik/Grammatik/X86/ComposeCallLogGhost.lean`, `grammatik/Grammatik.lean`,
`MUSE-REPORT-833.md`.

## What was done
New module `Grammatik.X86.ComposeCallLogGhost` (wired into `Grammatik.lean`),
composing two accepted producer legs by name without re-proving them:

- Producer 1 — `AufrufOpt` (lane 310): `GeistAntwort` (value channel `.ok`
  and reason channel `.grund`, actual `rho`/`v`/`s0`/`s1`), `geistPaar`,
  `geistRekon_folge`, `geistRekon_folge_grund`.
- Producer 2 — `InstructionSelection` (`Anweisungswahl`, lane 600): the
  selector verdict `wahlOk` (clobbering `xor` under live flags refused).

Interface closed: an eliminated/inlined call site emits no physical log event,
so the site is legal only with the ghost pair re-emitted AND `FolgeLog`
preserved. New definitions/theorems:

- `senkeOk` — checked `Bool` encoding exactly the two armed side conditions
  of `geistRekon_folge`/`_grund`, both channels.
- `schlussOk` — `senkeOk && wahlOk`; either leg refuses the site.
- `senkeOk_ordnung_wert`, `senkeOk_ordnung_grund` — the `Bool` discharges the
  exact side conditions (actual values throughout).
- `ComposeCallLogGhost_verbindung` (ZEUGE target) — generic over arbitrary
  `Φ g rho s0 a rest`: `FolgeLog Φ rest` + `senkeOk = true` give
  `FolgeLog Φ (geistPaar … ++ rest)`, both channels via case split.
- `ComposeCallLogGhost_verbindung_zeuge` — joint inhabitation on the
  non-degenerate fixture program (`setze` writes table `konto`): reached
  five-step run, slots `0 -> 5` (memory-changing step), the log holds exactly
  the ghost pair of `pruefe` over the return of `setze`, `senkeOk = true` and
  `FolgeLog` there by the composition theorem.
- Refusals: `ComposeCallLogGhost_verweigert_wahl` (generic: xor under live
  flags refuses every site), `ComposeCallLogGhost_verweigert_senke`
  (generic: failed ghost leg refuses every selector choice), decided
  `ComposeCallLogGhost_ordnung_verloren` (ghost entry behind a non-return),
  decided `ComposeCallLogGhost_splice_gut` / `schluss_gut` /
  `schluss_verweigert` (good splice + preserving choice pass; xor refuses).

## Verification
- `./lean-probe …/ComposeCallLogGhost.lean`: `== 0 error(s)`; axioms
  `[propext]` throughout, `[propext, Classical.choice, Quot.sound]` for the
  `_zeuge` (inherited from the accepted run builders) — within the standard
  `gabbro_ziel` set.
- `./lean-bau`: `Build completed successfully (509 jobs).` Whole project green.
- No `sorry`/`admit`/`axiom`/`native_decide`; every premise used; no
  conclusion restates a premise (the composed check implies the order
  property, it is not projected back).
- No diagnostic/gift/example/CLI numbers, no MARKE changes, no source/
  checker/Spec/goal/emitter edits, no friend-reserved optimiser files.

## Open / believed-wrong
- Nothing in the task believed wrong. Genuinely open (file CUTS): no
  executable body-splice simulation (as in `AufrufOpt`); ghost is source
  log-data, its lowering to the shared representation is the bridge wave's
  dependency, not lane 833's; no closed `grund`-channel fixture inhabitant
  (`eD.gruende = 0` everywhere — reason channel covered generically only);
  `ensures`-extraction stays where `AufrufOpt` left it.

## Commits (branch muse/833)
- `3ce213be` skeleton + import; `928c88e0` legs/composition/refusals/decided
  instances; `b9d7b56e` joint witness + CUTS + axiom prints.
