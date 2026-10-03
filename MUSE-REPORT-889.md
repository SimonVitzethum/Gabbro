# MUSE-REPORT-889: Optimiser rule — division guard rule

## What was done

New file `grammatik/Grammatik/X86/OptDivGuard.lean` (import added at the end
of `grammatik/Grammatik.lean`), proving the DESIGN section 7 LICM row for
division sites plus the section 3 / 3A obligations: IDIV/DIV are never
speculated, never hoisted above their divisor check, and divide-error
(#DE on zero/overflow) is a `hardware` stop preserved exactly.

- **Certificate** `DivGuardCert` (local rewrite record: `nichtNullOk`,
  `keinUeberlaufOk`, `unveraendertOk`, `keinGleitErsatz`) with admission
  `divGuardZulassen` (conjunction; refused optional motion falls back to
  another certified translation, never a warning). `unveraendertOk`
  stands for the recomputed B+C citations (block-map dominance/invariance
  plus duty/effect binding; cf. DESIGN section 7 register design and
  IR-VALIDIERUNG section 3 as aligned by lane 638 — read, not imported).
  TableLayout/CostSummary roles are cited in comments only; no new
  numbers, no MARKE_EMIT changes, no source/checker/Spec/goal/emitter
  edits, friend-reserved optimiser files untouched.
- **Four refusal legs** (each proved of the decided Bool):
  `divGuardVerweigert_ohneNachweis` (CE-2: hoist above `n!=0` without
  recomputed nonzero evidence), `divGuardVerweigert_ueberlauf` (65-bit
  quotient keeps the stop), `divGuardVerweigert_veraendert` (no
  invariance / shared-token local evidence), `divGuardVerweigert_gleit`
  (no RCPSS-for-DIV, no reassociation, float division never pure),
  plus five `decide` probes and the never-pure applications
  `divGuard_nieRein_div` / `divGuard_nieRein_idiv` (REUSED
  `falle_nie_rein`, so DCE can never take a division).
- **Source leg** over arbitrary values with forwarded `M102` premises:
  `divGuard_quotient_wert` (`tdiv`, truncation toward zero), 
  `divGuard_rest_wert` (`tmod`), two `decide` probes (`7/2=3`, `7%2=1`).
- **Target leg** reusing `MulDiv.lean` (no duplicated evaluator):
  `divGuard_null_halt` (zero divisor traps),
  `divGuard_ueberlauf_halt` (quotient overflow traps),
  `divGuard_idiv_null_halt` (signed zero divisor traps),
  `divGuard_div_flags_bleiben` (admitted DIV keeps flags: no FP-visible
  effect), two `decide` probes on the planted witness states.
- **Connection** `OptDivGuard_verbindung`: admitted guarded-division
  `Endblock.bind` window preserves, jointly, the evaluated value, the
  `execEnd` outcome (same constructor: no fault added/removed, contracts
  at their place / call logs / budget unchanged by same block shape),
  the footprints (`orte = []` both sides: no shared access moved),
  the width-exact word image (`divGuardWort`), and an unrelated admitted
  float-division `gleitPasst` outcome (single rounding scope).
- **Joint witness** `OptDivGuard_verbindung_zeuge`: all premises
  instantiated jointly (`7/2 → 3`, float site `(3/4)/1 = 3/4` by
  `decide`, `leave` continuation) on non-degenerate `refD`
  (`refEin_schreibt`) beside the reached memory-changing F-machine run
  (`refB_erreicht`, `refB_schreibt`: slot `0 -> 100`).

## Verification

- `./lean-probe grammatik/Grammatik/X86/OptDivGuard.lean`: 0 errors,
  no warnings. All `#print axioms` within
  `propext, Classical.choice, Quot.sound` (same footprint as the
  neighbouring `OptFoldConst` value lemmas; no new axioms).
- `./lean-bau`: `Build completed successfully (511 jobs)` — whole
  project green.
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; no premise has
  type `Prop` itself; every premise is used by its proof (two
  context-only uses — `omega` reading `hW`, `decide` closing
  witness obligations — are genuine: removing the premise breaks the
  proof).

## What remains open (see CUTS)

No signed-division window (`sdiv`/`srem`); no branch-hoist equation
with `Stmt`/branch semantics (stays with the lowering lane); no
formal level-(c) machine-work bound (OPEN per IR-VALIDIERUNG lane 278);
no silicon correspondence, no TSO/GX bridge, no ABI/loader claim.

## Remarks on the task

Nothing in the task was found to be wrong. One scoping note: the DESIGN
section 7 LICM row is a motion rule, but the only motion this lane
certifies is the value-preserving guarded window with the check kept at
its site; branch-hoisting with branch semantics is honestly recorded as
CUT rather than claimed. The `weiter`-narrowing of the admitted quotient
into the site range (`.int 0 x`) carries the DESIGN "source extent proof
AT the site" as the validator-decided conditional obligation `hEq`.
