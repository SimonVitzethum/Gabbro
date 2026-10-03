# MUSE-REPORT-853: Composition closing — entry-hook closing

## Task

Close nolibc entry hooks (`os_anfang`/`os_ende` handshake, main status) to
the proved entry predicates; missing hooks refuse. Compose already-accepted
modules into one checked closing step; never re-prove internals, never
duplicate an interpreter or executor. Target: `ComposeEntryHooks_verbindung`
with companion `ComposeEntryHooks_verbindung_zeuge` (jointly inhabited,
non-degenerate, memory-changing reached run).

## What was done

New file `grammatik/Grammatik/X86/ComposeEntryHooks.lean` (owned) plus the
one import line in `grammatik/Grammatik.lean` (owned). It composes the
accepted producers by name only:

- Producer: `EntryExecution.eintrittZulassung` (checked `Bild` mapping AND
  `EntryState.eintrittOk` AND admitted caller gates) with its executed
  consequences `zulassung_rip_ausfuehrbar`, `zulassung_stapel_rw`,
  `zulassung_erster_schritt` (through `Byteschritt.byteschritt`),
  `zulassung_verweigert_unlisted`, `zulassung_verweigert_tor`.
- Consumer: the nolibc hook handshake as validator `Bool` findings.

New definitions (all `Bool`/data, no new executor, no new semantics):

- `NolibcHaken` (`anfang`, `ende : Bool`): `os_anfang` handoff done,
  `os_ende` hook present. Behaviour stays user logic, never an assumption.
- `hakenOk`: both hooks present.
- `statusHalt code rueck`: handed value equals the returned main status.
- `eintrittHakenZulassung`: joint admission AND hooks AND unchanged status.

New theorems (every `Prop` premise used by its proof):

- Projections: `hakenZulassung_eintrittZulassung`, `hakenZulassung_haken`,
  `hakenZulassung_status` (`rueck = code` via `of_decide_eq_true`),
  `hakenZulassung_eintritt`, `hakenZulassung_rip_ausfuehrbar` (RIP
  executable through the CHECKED loaded mapping, not the state's own
  permission function), `hakenZulassung_stapel_rw`.
- Execution (not a conjunction of checks): `hakenZulassung_erster_schritt`
  reuses `zulassung_erster_schritt`: the fetched instruction runs as a real
  byte step.
- Refusals: `hakenZulassung_verweigert_ohne_anfang`,
  `hakenZulassung_verweigert_ohne_ende`,
  `hakenZulassung_verweigert_status` (uses the mismatch),
  `hakenZulassung_verweigert_unlisted`, `hakenZulassung_verweigert_tor`.
- Closing: `ComposeEntryHooks_verbindung`, generic over arbitrary admitted
  inputs (arbitrary `Profil`/`Bild`/bias/entry kind/state/gates/hooks/
  status pair).
- Joint witness `ComposeEntryHooks_verbindung_zeuge`: admitted nolibc
  entry on the minimal image (`valZeuge`, `zeugenEintrittAusf`,
  `[schreibTor]`, both hooks, status 0 handed as 0), the fetched `ret`
  (`zulassung_fetch_ret` reused) and its executed step to RIP zero
  (`zulassung_schritt_ret` reused — a reached run from checked bytes), a
  real memory-changing write/read (`schreibLese_zeuge` reused: nonzero
  value, reads back, byte observably changes), plus five planted `decide`
  refusals (no `anfang`, no `ende`, changed status, unlisted RIP,
  clobbered-out gate).

## Verification

- `./lean-probe grammatik/Grammatik/X86/ComposeEntryHooks.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau`: `Build completed successfully (511 jobs)`.
- Axioms: every new theorem depends only on `propext` (some also
  `Quot.sound`, inherited from the reused accepted lemmas) — within the
  `gabbro_ziel` standard (`propext`, `Classical.choice`, `Quot.sound`).
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; no `Prop`-typed
  premise; no weakened or deleted existing theorem.

## What remains open (CUTS in the file)

- Hook findings are `Bool`s, not proved call sequences; OS/binding
  behaviour stays user logic.
- Source-to-entry lowering and the shared IR (lane 287) are the named open
  dependency; no substitute IR or executor invented.
- Asynchronous interrupt behaviour after handoff stays with the
  interrupt-leg owner.
- No hardware, source, TSO/GX, cost/budget, or multi-step control-flow
  claim.

## Note on the task text

Nothing in the task was found to be wrong. One scoping remark: the task's
"missing hooks refuse" is closed here as validator admission (`= false`),
never as a hardware fault claim — consistent with the producer modules.
