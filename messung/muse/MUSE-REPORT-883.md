# MUSE-REPORT-883: Optimiser rule -- loop alignment rule

## Task
Lane 883: state the loop-alignment optimisation as a generic rule lemma over
arbitrary values with validator-decided side conditions (DESIGN section 7
row), prove value/fault/observation preservation incl. IEEE, contracts, call
logs, concurrency and budget; name the exact certificate shape and the
precise refusal case. ZEUGE: `OptLayoutAlign_verbindung` + companion
`OptLayoutAlign_verbindung_zeuge` (jointly inhabited, non-degenerate,
memory-changing reached run).

## What was done
Created `grammatik/Grammatik/X86/OptLayoutAlign.lean` (new file, ~330 lines)
and registered `import Grammatik.X86.OptLayoutAlign` at the end of
`grammatik/Grammatik.lean`. No other files touched.

Design basis (read in-clone): DIRECT-COMPILER-DESIGN sections 7 and 7A --
the `Layout / allocation` optimiser row (phase L) and the `Alignment / code
size` tuning row ("alignment effects on loop heads and vector loads ... used
for layout, relaxation rounds, padding ... no fixed timing promise"), plus
the sibling rule-lemma precedent `X86/OptFoldConst.lean` (lane 860) and the
layout-certificate precedent `X86/BranchLayout.lean` (lane 423).

Definitions:
- `AlignCert` (kopfOk, lastOk, gemessen : Bool; ausr, pad : Nat) --
  validator-decided side conditions; `alignZulassen` admission Bool.
- `AlignBeleg` (start, len, ausr, pad, ziel : Nat) -- local rewrite record;
  `alignOk` recomputing Bool (pad bound, measured class, head equation,
  head alignment, nonempty body).
- `layoutPad` -- layout-only rewrite, identity on executed syntax.

Theorems:
- Refusals: `alignVerweigert_unvermesssen`, `alignVerweigert_pad`,
  `alignVerweigert_ausr`; probes `probe_alignZulassen_ok`,
  `probe_alignZulassen_unvermesssen`, `probe_alignZulassen_pad`,
  `probe_alignZulassen_klasse`.
- Recomputed facts: `alignZulassen_pad`, `alignOk_akzeptiert`,
  `alignBeleg_adresse`, `alignBeleg_ausgerichtet`, `alignBeleg_pad`,
  `align_zeuge_akzeptiert`, `align_zeuge_verweigert`.
- `OptLayoutAlign_verbindung`: admitted + certified alignment preserves the
  `execBlock` outcome (same constructor/worlds/envs: values incl. IEEE,
  faults, contracts at their place, call logs, shared accesses, step budget)
  and pins head equation, head alignment and pad bound. Every premise used.
- `OptLayoutAlign_verbindung_zeuge`: joint witness on non-degenerate `refD`
  (`einzahlen` writes; reached F-run `MB` with slot 0 -> 100).

Refusal case: unmeasured traits, pad >= class, class outside {16,32} -- plus
never a timing promise (traits select among valid layouts only).

## Verification
- `./lean-probe grammatik/Grammatik/X86/OptLayoutAlign.lean`: 0 errors.
- `./lean-bau`: Build completed successfully (511 jobs).
- Axioms: main theorems `[propext, Classical.choice, Quot.sound]`
  (standard); helpers `[propext]` or none.

## Open / not claimed
Per CUTS: no relaxation-round convergence across sites (DESIGN 2B future);
no formal level-(c) machine-work bound (same reading as lane 860); no timing
claim (deferred per FLOAT-ZEIT 8.2, as the 7A row requires); no silicon/TSO/
ABI correspondence; no checker change.

## Task assessment
Nothing in the task appears wrong. One note: DESIGN section 7 has no
dedicated "loop alignment" optimiser row with explicit premise/certificate/
failure columns -- the row was composed from the section 7 `Layout /
allocation` row and the section 7A `Alignment / code size` tuning row, as the
task line itself describes. If a narrower row is intended, it should be added
to the DESIGN table.
