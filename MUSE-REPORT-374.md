# MUSE-REPORT-374: Independent exact-candidate A2 review of 336 MulDiv

## Scope and method

Reviewed the exact candidate snapshot for lane 336 (HEAD
`ebd8455ce3231ed21df2c159e6f44fa2fb25d6af`, base `f737a6f0`) from
`.tmp/review/author-336` (SNAPSHOT / OWNER-TASK / PATCH / BUILD-EVIDENCE /
staged `MulDiv.lean` + umbrella). Clone verified: `/home/simon/Dokumente/
gabbro-muse/a374`, branch `muse/374`.

Staged the candidate module plus the one additive umbrella import privately
in this clone, ran `./lean-probe` on the module (0 errors), full
`./lean-bau` (exit 0, 0 error lines, 387 jobs), and `./lean-probe` on
`Zielsatz/Beweis.lean` (0 errors, goal axioms unchanged), then restored both
staged paths. This clone is now clean of candidate code; report-only
ownership (this file).

## What the candidate delivers

New module `grammatik/Grammatik/X86/MulDiv.lean` (583 lines) plus one
additive import in `grammatik/Grammatik.lean`. 64-bit MUL/IMUL/DIV/IDIV as
an extension of the one pilot semantics: `MulDivBefehl` (4 forms),
`u128`/`s128` dividends, `divWeitU`/`divWeitS` with divisor-zero AND
quotient-overflow traps, `mulFlagsU`/`mulFlagsS` snapshots proved against
the canonical `MulGueltigU`/`MulGueltigS` relations, `mulDivSchritt` for the
4 new forms only, decided `zugelassen` guard, never-pure `rein` policy,
`decide` probes and the joint memory theorem `muldiv_speicher_sonde`.

## Checks performed, all passing

- Task actually done: all four forms, both trap causes, truncation toward
  zero (`tdiv`/`tmod`), MUL flag carry rules, guard/step agreement,
  non-trivial witness (17/5 = 3 rem 2 through the step and through memory),
  divisor-zero refusal proved and probed, INT_MIN/-1 and 2^64/1 overflow
  refusals probed. Matches the A2 target direction in OWNER-TASK.
- Generic real semantics, no toy: reuses canonical `Wort`/`Zustand`/
  `Register`/`Flags` (Typen), `mulLow`/`mulHighU`/`mulTragU`/`mulTragS`/
  `MulGueltigU`/`MulGueltigS`/`sVal`/`divS`-style wrapping (Ganzzahl),
  `regSet`/`ripNach`/`laengeOk` (Ausfuehrung), `read64`/`write64`/
  `writeBytes`/`read64_nach_write64`/`writeBytesN_hit`/`addrOff_null`/
  `zeugenSpeicher` (Speicher). No duplicated evaluator of the 14 pilot
  forms, no competing word-level redefinition, no source/checker/Spec/goal
  change.
- Physical ISA facts verified against the model: unsigned dividend
  `hoch*2^64+tief` and signed `hoch.toInt*2^64+tief.toNat` are the correct
  RDX:RAX decompositions; DIV traps on zero divisor or 65-bit quotient;
  IDIV traps on zero divisor or quotient outside signed range with
  truncation toward zero (probe pins -7/2 = -3 rem -1, not SAR floor);
  MUL writes RDX:RAX full product, 2-operand IMUL truncates into dst;
  CF/OF from the matching carry evidence, AF `none`, DIV/IDIV preserve all
  flags. The undefined-bit preservation is stated as an explicit modelling
  choice, not hardware truth. `hardwareHalt` only NAMES the existing
  `hardware` stop class; the guard/fault/channel/order correspondence is
  left OPEN in CUTS. No invented alignment, width, latency, TSO, FP or cost
  claims.
- No conclusion-as-premise, no `forall`-away contracts, no Prop-typed
  premise, no `intro _`/`have _ :=`; every theorem premise is used
  (checked by reading each proof). No `sorry`/`admit`/`axiom`/
  `native_decide`/`unsafe`.
- Axioms: every `#print axioms` line is within `[propext, Quot.sound]`,
  a subset of the standard goal axioms. Goal side intact.
- Witnesses: no theorem quantifies over source syntax, so HARD RULE 13
  needs no `_zeuge`; the `decide` step probes plus `muldiv_speicher_sonde`
  (real permission-checked `write64`/`read64` with an observed byte change
  at address 0) are non-degenerate. Refusal is proved generally
  (`divWeitU_verweigert_bei_null/ueberlauf`, `divWeitS_verweigert_bei_null/
  unten/oben`, `zugelassen_verweigert_nullteiler`,
  `verweigert_heisst_halt`), not merely exemplified.
- Bounded claim: report and CUTS state exactly what is OPEN (wiring into
  `Befehl`/`schritt`/decoder/image, bridge-277 correspondence, source
  range, cost, TSO/GX, silicon). No claim of a closed lowering or full
  validator. English throughout.

## Non-blocking nits (no repair required)

- The module imports `Grammatik.X86.FlagBeweis` and the report lists
  `sint` as reused, but no `FlagBeweis` definition is referenced: `s128`
  uses `hoch.toInt` directly (`sint w` is definitionally `w.toInt`, so
  semantics are identical). Suggest dropping the import or routing `s128`
  through `sint`. Harmless: build is green either way.
- `verweigert_heisst_halt` covers DIV only; the IDIV guard/trap agreement
  follows the same two-line case split but is not stated. The IDIV refusal
  side is still proved (`divWeitS_verweigert_*`) and probed
  (`probe_idiv_min`, `probe_div_halt_schritt` for DIV).
- `idivRax` success arm inlines `ripNach s.rip d.laenge` where the sibling
  arms use the `nach` let; semantically identical.

## Build evidence (this clone, candidate staged privately, then restored)

- `./lean-probe grammatik/Grammatik/X86/MulDiv.lean`: 0 errors; axioms
  within `[propext, Quot.sound]`.
- `./lean-bau`: exit 0, 0 error lines, 387 jobs, completed successfully.
- `./lean-probe grammatik/Grammatik/Zielsatz/Beweis.lean`: 0 errors;
  `gabbro_ziel_*` on `[propext, Classical.choice, Quot.sound]`.
- Staged paths restored; `git status` clean except this report.

CANDIDATE: 336 ebd8455ce3231ed21df2c159e6f44fa2fb25d6af
VERDICT: ACCEPT
