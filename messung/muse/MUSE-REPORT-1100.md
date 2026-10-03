# MUSE-REPORT-1100: Defined auxiliary-carry rows for admitted integer execution

## What was done

New module `grammatik/Grammatik/X86/AuxiliaryCarryRows.lean` (only new
Lean file; no existing file touched). It covers the exact admitted 720
row set -- `ConcIntOp` (load/store at b8/b16/b32/b64) as connected to
shared TSO execution by `concLoadMaschine`/`concStoreMaschine` -- with
one dispatcher and per-row AF verdicts. All eight rows take the
non-observability leg (leg (ii) of the task): MOV affects no flags, so
flags and the `af` Option Bool abstraction are preserved, never
invented; `bedingung_af_frei` (692 family, imported via
`ArchitecturalFlags` -> `FlagDependencies`, never forked) shows no
flag consumer can observe AF behind these rows. No defined hardware AF
value is claimed for any row; no flag consumer was weakened.

## Exact names of new definitions/theorems

- `auxRowStep` (dispatcher: each `ConcIntOp` row onto the accepted 720
  machine adapter), `AuxDefined` (deliberately empty defined-AF claim
  relation: any future defined value must arrive as a new constructor
  with its canonical-helper equation)
- `auxRowStep_load`, `auxRowStep_store` (definitional routing, `rfl`)
- `auxFlags_erhalten` (every admitted row keeps the flags; reuses
  `concLoadMaschine_flags` / `concStoreMaschine_flags`)
- `auxAf_verbrauch` (AF non-observability for every `Bedingung` and any
  two AF choices; reuses imported `bedingung_af_frei`)
- `auxKeinDefiniert` (planted probe: any AF-definedness claim over any
  admitted row is refused), `auxProbe_afUndefiniert_b8load` (planted
  concrete probe: the 8-bit load, which has no accepted byte producer,
  carries no defined AF), `auxProbe_keinAfbypass` (planted probe: a
  direct-AF read bypassing `bedingung` cannot move any consumer)
- TARGET `auxCarry_definiert_alle` (per-row defined-or-unobservable
  disjunction over the exact admitted 720 row set)
- TARGET `auxCarry_byteschritt` (fetched execution agreement: the
  accepted 720 witness store's fetched bytes decode via
  `concWit_fetch_decode`, the shared dispatcher runs it on `HwMaschine`
  through the reused 720 connection, flags preserved, TSO projection
  reached)
- `auxCarry_zeuge` (joint witness for both targets on the
  non-degenerate witness run: drain changes shared memory 0 to `0x04`,
  both cores observe, beside both planted refusals)

## Verification

- `./lean-probe grammatik/Grammatik/X86/AuxiliaryCarryRows.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`. `#print axioms` for
  every main theorem is within `[propext, Quot.sound]` (subset of the
  standard `gabbro_ziel` axioms; no `sorry`/`admit`/`axiom`/
  `native_decide`/`unsafe` anywhere).
- `./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`,
  `Build completed successfully (512 jobs)`.

## What remains open (see also the CUTS block in the module)

1. No admitted row carries a DEFINED hardware AF value; all eight stay
   on the unobservable leg with the manual reason (MOV: "Flags
   Affected: None"). ADD/SUB/NEG families need their own
   `AuxDefined` constructors with canonical-helper equations
   (`afAdd`/`afSub`, `negWf`, 692 per-width identities).
2. No silicon correspondence, no per-access W/GX simulation, no
   source/IR/ABI/loader/entry/budget claim.
3. MERGE ACTION REQUIRED: the additive line
   `import Grammatik.X86.AuxiliaryCarryRows` at the end of
   `grammatik/Grammatik.lean` is still missing. This lane has no write
   permission outside its two owned files (the edit was denied by the
   lane permission gate), so the merger must append that one line;
   until then the module is verified via `./lean-probe` only. The
   non-degeneracy mapping ("a table some function writes" has no
   Gabbro-source meaning at this hardware layer; used the written
   footprint cell `concWitA` instead) is documented in the witness
   docstring for the reviewer to accept or reject.

## Task feedback

Nothing in the task is wrong, but two frictions are recorded: (a) the
task demands the `Grammatik.lean` import while the lane permission
gate denies exactly that edit -- resolved as merge action (3) above;
(b) HARD RULES 13's non-degeneracy vocabulary ("a table some function
writes") is Gabbro-source-specific and has no literal meaning for
hardware-row theorems -- mapped explicitly to the written footprint
cell rather than weakened.
