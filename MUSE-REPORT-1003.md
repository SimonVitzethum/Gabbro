# MUSE-REPORT-1003: Exact review of author 853 (Composition closing: entry-hook closing)

## CANDIDATE

- CANDIDATE: 853 d420540f07c15ff66cbd4d57d1fe3d706d587ceb
- Base matches this clone: b040b155159f47629542b0083e2f0a8a607f2b4c (clone
  `/home/simon/Dokumente/gabbro-muse/a1003`, branch `muse/1003` verified).
- Files (from `.tmp/review/SNAPSHOT.json` and `PATCH.diff`): `MUSE-REPORT-853.md`,
  `grammatik/Grammatik.lean` (one import line), new
  `grammatik/Grammatik/X86/ComposeEntryHooks.lean` (355 lines).

## VERDICT: ACCEPT

Bounded acceptance: the candidate closes nolibc entry-hook admission
(`os_anfang`/`os_ende` presence plus unchanged main-status handoff) onto the
accepted joint entry admission at the admission (`Bool`) level, reuses the
accepted executed first-step lemma by name, and jointly witnesses admission,
fetch, executed step, a real memory-changing write/read, and five planted
single-leg refusals. No hardware, source, TSO/GX, cost/budget, or multi-step
control-flow claim is made; hook behaviour stays validator `Bool` findings
(user logic, never an assumption). Missing producer legs are explicit CUTS
with owners named (source-to-entry lowering / shared IR lane 287, async
interrupt leg owner), never assumed.

## What was inspected

- Exact sources: `.tmp/review/author-853/OWNER-TASK.md` (target
  `ComposeEntryHooks_verbindung` + `ComposeEntryHooks_verbindung_zeuge`),
  `MUSE-REPORT-853.md`, `PATCH.diff` (full 355-line new file), `BUILD-EVIDENCE.json`,
  and the snapshot copy `author-853/grammatik/.../ComposeEntryHooks.lean`.
- Producer existence in this clone (base): `EntryExecution.eintrittZulassung`,
  `zulassung_eintritt`, `zulassung_rip_ausfuehrbar`, `zulassung_stapel_rw`,
  `zulassung_erster_schritt`, `zulassung_verweigert_unlisted`,
  `zulassung_verweigert_tor`, `zeugenEintrittAusf`, `zulassung_fetch_ret`,
  `zulassung_schritt_ret` (all `EntryExecution.lean`); `valZeuge`
  (`ValidatorSkeleton.lean`); `schreibTor`, `torAusClobber` (`GateStub.lean`);
  `schreibLese_zeuge` (`Bild.lean`); art-independence of the nolibc/hosted
  admission (`EntryState.lean`: `ifErwartet` true and `guardErforderlich`
  false for both `.hostedMain` and `.nolibcMain`, so `eintrittOk` coincides
  on the shared witness state).
- Recorded queued-wrapper evidence in `BUILD-EVIDENCE.json`: `./lean-probe`
  `== 0 error(s) in the COMPLETE output; exit 0` (repeated runs), `./lean-bau`
  `Build completed successfully (511 jobs)`, per-theorem `#print axioms`
  within the `gabbro_ziel` standard (`propext`, some also `Quot.sound`
  inherited from reused accepted lemmas).

## Architecture checks (all pass)

- Byte forms / canonical execution: no new loader, decoder, executor, or ISA
  model. The only import is `Grammatik.X86.EntryExecution`; every executed
  consequence (`hakenZulassung_erster_schritt`) reuses
  `zulassung_erster_schritt`, hence `Byteschritt.byteschritt` over fetched
  bytes. No second fetch, no conjunction-of-checks passed off as execution.
- Checked mapping (not state permission): `hakenZulassung_rip_ausfuehrbar`
  routes through `zulassung_rip_ausfuehrbar`, i.e. `(geladen bild bias)`
  executability, as the report claims.
- Hooks/status: `NolibcHaken`/`hakenOk`/`statusHalt`/`eintrittHakenZulassung`
  are pure `Bool`/data combinators over the producer admission; refusal
  lemmas each consume their named mismatch (`h.anfang = false`,
  `h.ende = false`, `rueck ≠ code` via `decide_eq_false`, unlisted RIP,
  refused gate member). No invented determinism, no zeroed/ignored defined
  effect: the file touches no register/flag/memory semantics at all.
- Premise use: every theorem with premises consumes all of them (projections
  via `Bool.and_eq_true_iff` components, status via `of_decide_eq_true`,
  execution via all three of admission/fetch/step, refusals via their
  mismatch/member). No `intro _`, no `have _ :=`, no `Prop`-typed premise, no
  `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` (the only `admit` substring
  hits are the English words "admitted/admits").
- Witnesses: `ComposeEntryHooks_verbindung_zeuge` jointly instantiates
  admission (`haken_zeuge_nolibc_ok`, `.nolibcMain` on the minimal image with
  both hooks and status 0 handed as 0), fetched `ret`
  (`zulassung_fetch_ret`), executed step to RIP zero
  (`zulassung_schritt_ret`, a reached run from checked bytes), a real
  memory-changing write/read (`schreibLese_zeuge`: nonzero value, reads back,
  byte observably changes), plus five planted `decide` refusals mutating
  exactly one leg each (no `anfang`, no `ende`, changed status, unlisted RIP
  0x5000 matching the producer's refusal shape, clobbered-out gate).
  Non-degenerate by the lane standard.
- Cross-kind reuse is sound: `.nolibcMain` vs the producer's `.hostedMain`
  witness differ in no `eintrittOk` conjunct on this state (verified against
  `EntryState.lean`), and fetch/step/memory lemmas are kind-independent.
- CUTS/claim boundary: the file-top CUTS block plus `#print axioms` per main
  theorem satisfy hard rule 6; the report's open list (Bool findings only, no
  source/hardware/TSO/cost/multi-step claim, named owners for lowering and
  interrupts) matches the file.

## Two stated boundaries (not repairs)

1. The closing theorem itself is admission-level (admission, hooks, status
   equality, executable RIP, stack window); the executed step is a separate
   theorem plus the joint witness. This matches the producer module's pattern
   and the task's "composition, never re-prove internals".
2. The memory-changing conjunct lives over loaded image memory
   (`schreibLese_zeuge`), not through the entry `ret` step itself (a `ret`
   pops the stack without changing memory bytes). Same pattern as the
   producer's `eintrittAusf_zeuge`; recorded as a boundary, not a defect.

## Reproduction note (honest partial status)

No independent rebuild of the candidate was run in this clone: owning only
`MUSE-REPORT-1003.md` (no source or live-control changes per the lane task),
applying the candidate patch here would violate ownership, and `lean-probe`
resolves module imports only inside `grammatik/`. Verification is therefore
the recorded queued-wrapper outputs in `BUILD-EVIDENCE.json` (lean-probe 0
errors, lean-bau 511 jobs green, standard axioms) plus the line-by-line
inspection above, including producer-name resolution and the
nolibc/hosted art-equivalence check against `EntryState.lean`. Working tree
is otherwise untouched (`git status --short` clean before writing this
report); no source, control-plane, or registry file was modified.

## Task text

Nothing in the owner task was found to be wrong. "Missing hooks refuse" is
closed as validator admission (`= false`), never as a hardware fault claim,
consistent with the producer modules.
