# MUSE-REPORT-1101: Exact author-HEAD review of candidate 1100

## Scope

Report-only independent exact review of CANDIDATE 1100, pinned HEAD
`ed9b6a6c2f3ea8685da1a84de2dd75fcbf649de6` (base `f31f93197c59c64371b654a960ccbdf6f166f40d`),
evidence snapshot `.tmp/review/author-1100/` (SNAPSHOT.json, PATCH.diff,
OWNER-TASK.md, BUILD-EVIDENCE.json). Own file only: MUSE-REPORT-1101.md.
No source, private, root, or network changes. Reviewer clone
`/home/simon/Dokumente/gabbro-muse/a1101`, branch `muse/1101`, verified
before starting.

## What was done

Checked every reviewer gate against the accepted tree (not against the
candidate's own claims):

1. Admitted-row inventory: `ConcIntOp` (`ConcurrentIntegerExecution.lean:30`)
   has exactly two constructors (`load`/`store`) over `Breite`
   (`Typen.lean:18`: `b8/b16/b32/b64`), i.e. eight syntactic rows.
   `auxRowStep` matches both constructors with parametric `b` and routes
   definitionally (`rfl`) to `concLoadMaschine`/`concStoreMaschine`.
   TARGET `auxCarry_definiert_alle` quantifies over all `op : ConcIntOp`,
   so every one of the eight rows gets a verdict, always leg (ii):
   flags preserved plus AF-unobservable to every consumer. No third case
   exists (exhaustive disjunction, proof always `Or.inr` with both
   conjuncts). Decode coverage (`concDecode_nur_b64_b32`: only b64/b32
   rows decode) does not shrink the verdict set: verdicts are at the
   machine-adapter level, which exists for all widths; fetched execution
   uses the b32 store representative that has an accepted byte producer.
   Reproduced, complete.
2. Flag-helper reuse, no local AF redefinition: exact token scan of the
   candidate file finds zero `sorry`/`admit`/`native_decide`/`axiom`/`unsafe`
   (the only `admit` substring hits are the English word "admitted").
   `afAdd`/`afSub` appear only in comments/CUTS, never as definitions.
   `AuxDefined` is a deliberately empty inductive (no constructor, no
   equation): no fiat hardware AF value anywhere. All flag facts are
   reused: `concLoadMaschine_flags`, `concStoreMaschine_flags`,
   `bedingung_af_frei` (692 family, in scope via `ArchitecturalFlags`
   line 42 `import FlagDependencies`, never forked). No second flag
   semantics.
3. No flag consumer weakened: PATCH.diff modifies zero existing files
   (two new files only). `bedingung` and every consumer call site are
   untouched; the candidate only calls the imported identity.
4. Fetched execution through the accepted 720 connection, no second
   executor: `auxRowStep_store`/`auxRowStep_load` are `rfl`; TARGET
   `auxCarry_byteschritt` chains `concWit_fetch_decode` (fetched bytes
   decode to the b32 store, length 7) with `concStoreMaschine` (reused),
   `concStoreMaschine_flags`, and `concStoreMaschine_erreichbar`
   (TSO projection reached). No new decoder or executor, no
   desired-equality premise (only the accepted step hypotheses). Note on
   the `HwSchritt` phrase in the review task: the owner task requires the
   accepted 720 connection, which for the multi-byte b32 store IS the
   `TSOErreichbar` leg (720 provides single-event `HwSchritt` legs only
   for b8 load/store and drain: `concLoadMaschine_b8_lade`,
   `concStoreMaschine_b8_gibAus`, `concDrain_spuele`). Demanding a single
   `HwSchritt` event for a 4-byte buffered issue would contradict the
   accepted 720 shape; the candidate's use of 720's own connection theorem
   is the correct form. Not a defect.
5. Joint `_zeuge` non-degeneracy and both refusal probes: `auxCarry_zeuge`
   conjoins the byteschritt step with `concWit_anfang_null` (cell 0),
   `concWit_spuelung` (drain writes `0x04`: a real shared-memory change),
   `concWit_fremd_neu` (second core observes the new value),
   `∀ op v, ¬ AuxDefined op v`, and the bypass equality. Non-degenerate:
   reached run with a memory-changing step plus the written footprint
   cell `concWitA` as the hardware-layer analogue of "a table some
   function writes". The mapping is explicitly documented in the witness
   docstring and report; at this hardware layer no Gabbro source table
   exists, and none is claimed. Accepted. Probes: `auxKeinDefiniert` plus
   concrete `auxProbe_afUndefiniert_b8load` (the b8 load has no accepted
   byte producer per `concDecode_nur_b64_b32`, and no defined AF) refuse
   any AF-definedness claim structurally (a positive would fail: the
   inductive has no constructor); `auxProbe_keinAfbypass` refuses a
   direct-AF consumer bypass via the imported identity (a claim that AF
   matters would fail since `bedingung` never reads it). Both pass as
   theorems; fail direction holds by construction.
6. CUTS honesty: the CUTS block lists exactly what is proved, states
   plainly that all eight rows stay on the unobservable leg with the
   manual MOV reason, names the future `AuxDefined` constructors with
   their canonical-helper equations (`afAdd`/`afSub`, `negWf`, 692
   per-width identities), and disclaims silicon correspondence, W/GX
   simulation, and source/IR/ABI/loader/entry/budget claims. Honest; no
   fake closure.
7. `Grammatik.lean` diff: the candidate adds zero lines there (PATCH.diff
   confirms). The one additive line
   `import Grammatik.X86.AuxiliaryCarryRows` is still missing, as the
   author discloses with reason (OWN ONLY gate denied the edit; merger
   must append it). Mechanically mergeable, zero semantic effect. See
   merge action below. Not proof-content grounds for REPAIR.
8. Axioms and builds (candidate evidence, cross-checked): `./lean-probe`
   `== 0 error(s)`, exit 0; every `#print axioms` within
   `[propext, Quot.sound]`, a subset of the standard `gabbro_ziel` axioms.
   `./lean-bau` `== exit 0`, 0 error lines (512 jobs in candidate tree;
   module verified via probe until the import lands, honestly disclosed).

## Exact new names (candidate)

`auxRowStep`, `AuxDefined`, `auxRowStep_load`, `auxRowStep_store`,
`auxFlags_erhalten`, `auxAf_verbrauch`, `auxKeinDefiniert`,
`auxProbe_afUndefiniert_b8load`, TARGET `auxCarry_definiert_alle`,
TARGET `auxCarry_byteschritt`, `auxProbe_keinAfbypass`,
`auxCarry_zeuge`.

## Verification (reviewer)

- `./lean-bau` on reviewer clone (unchanged tree): `== exit 0; 0 error
  line(s) in the COMPLETE output`, `Build completed successfully
  (537 jobs)`.
- Static exact scans on the pinned snapshot: forbidden-token scan clean,
  import list exactly the three accepted modules
  (`ConcurrentIntegerExecution`, `ArchitecturalFlags`,
  `HardwareExecution`), no local AF definition, PATCH.diff touches no
  existing file.
- `./lean-probe` on the candidate module was not re-run locally because
  this lane owns report-only output and must not materialise source
  files; candidate BUILD-EVIDENCE records `== 0 error(s)`, exit 0, with
  per-theorem axiom prints. Merge gate re-verifies after adding the
  import line.

## What remains open

- No admitted row carries a DEFINED hardware AF value (all eight on leg
  (ii)); ADD/SUB/NEG families still need their `AuxDefined` constructors
  with canonical-helper equations. Named in CUTS, not claimed.
- No silicon correspondence, no per-access W/GX simulation, no
  source/IR/ABI/loader/entry/budget claim. Named in CUTS.
- MERGE ACTION (mechanical, no semantic review needed): append the single
  line `import Grammatik.X86.AuxiliaryCarryRows` at the end of
  `grammatik/Grammatik.lean`, then rebuild.

## Task feedback

Nothing in the owner task or the review task is wrong. Two notes: (a) the
review task's `HwSchritt` phrase over-specifies relative to the owner task
for multi-byte buffered issues; the accepted 720 connection form
(`TSOErreichbar`) is what the candidate correctly reuses (see point 4);
(b) HARD RULES 13's "table some function writes" has no literal meaning
at the hardware layer; the candidate's explicit mapping to the written
footprint cell `concWitA` plus the memory-changing drain is the right
non-degeneracy analogue and is accepted.

## VERDICT: ACCEPT

Candidate 1100 at `ed9b6a6c2f3ea8685da1a84de2dd75fcbf649de6` is ACCEPTED
for merge with the single mechanical merge action above (append the
`Grammatik.lean` import line, then rebuild). Every admitted 720 row is
covered with no third case, flag helpers are reused with no local AF
redefinition and no weakened consumer, fetched execution steps through
the accepted 720 connection with no second executor and no
desired-correctness premise, the joint witness is non-degenerate with
both refusal probes genuine, axioms are standard, and CUTS is honest.
