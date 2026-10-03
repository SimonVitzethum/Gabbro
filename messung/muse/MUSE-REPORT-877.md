# MUSE-REPORT-877: displacement peephole rule

## What was done

Implemented the DESIGN section 7 "Flags-aware peepholes" row for the
displacement case in the new file
`grammatik/Grammatik/X86/OptPeepholeDisp.lean` (registered in
`grammatik/Grammatik.lean`), over the reused canonical vocabulary only
(`Typen`, `Syntax`, `Semantik`, `Gleitkomma`, `ReferenzB`,
`X86.Typen`, `X86.Wort`, and the accepted `X86.ScalarFloat` NaN row).
No new semantics, register, memory, decoder or source model; no
`ensures` derived; no refusal turned into a warning; no faulting form
speculated above its guard.

Certificate shape (exact): the local rewrite record `DispCert`
(recorded displacement `disp` plus the four validator-decided side
conditions `passt`, `keinToken`, `flagOk`, `keinNaNTausch`) decided by
`dispPeepholeZulassen` (conjunction of the four), cited together with
the recomputed analyses the validator re-decides per site
(flag liveness at the site, `layoutOk` revalidation after any byte
shortening per DESIGN 2B, `targetWork`/`expandBound` cost booking per
the cost lane, and the `Erhaltung` duty/effect binding) -- the latter
as named consumer obligations in CUTS, not re-proved here.

Precise refusal case: the rule must NOT fire when any one side
condition is false -- a displacement missing i32, a token op inside
the pure window (memory, call, check, atomic or faulting-FP op, which
is token-threaded hence excluded), a live flag across the window, or
any UCOMI-to-ordered-compare NaN swap. The fallback is the valid wider
displacement spelling, never a warning.

New definitions (2): `DispCert`, `dispPeepholeZulassen`,
`dispPasstI32` (3 total: DispCert, dispPeepholeZulassen, dispPasstI32).

New theorems (16): `dispVerweigert_passt`, `dispVerweigert_token`,
`dispVerweigert_flag`, `dispVerweigert_nan`, `probe_dispZulassen_ok`,
`probe_dispZulassen_nan`, `dispPasst_maxPos`, `dispPasst_minNeg`,
`dispPasst_drueber`, `disp8_passt_i32`, `dispZulassen_passt`,
`dispAdresse_durchRecord`, `disp0_addiert_null`,
`ucomiTausch_kollabiert`, `dispWort_ganz`,
`OptPeepholeDisp_verbindung`, `OptPeepholeDisp_verbindung_zeuge`
(17 total).

The connection `OptPeepholeDisp_verbindung` is stated over arbitrary
values at an `Endblock.bind` window with arbitrary continuation, and
concludes jointly: evaluated bound value preserved, `execEnd` outcome
equal (same constructor and successor worlds, so contracts at their
place, call logs, concurrency footprints and step-budget accounting
agree), the recomputed i32 bound carried, and the width-exact word
image. The companion `OptPeepholeDisp_verbindung_zeuge` instantiates
ALL premises jointly (`3 + 4` to `7` under the admitted record) on the
non-degenerate writer program `refD` beside the reached
memory-changing run (`refEin_schreibt`, `refB_erreicht`,
`refB_schreibt`).

## Last build result

`./lean-probe grammatik/Grammatik/X86/OptPeepholeDisp.lean`:
`== 0 error(s) in the COMPLETE output; exit 0`.
`./lean-bau`: `Build completed successfully (511 jobs).`
Axioms of both main theorems: `[propext, Classical.choice,
Quot.sound]` (within the standard `gabbro_ziel` set; no new axiom).

## What remains open

Per CUTS: encoder rows and length function for the disp8/disp0 byte
spellings, layout `layoutOk` revalidation after shortening, cost
(`targetWork`/`expandBound`) booking, silicon correspondence, the
TSO/GX bridge, and source-to-byte validation -- all with their owning
lanes, none claimed here.

## Task remarks

Nothing in the task appears wrong. Two readings were decided and are
recorded: (a) the "single accepted IR" is not available, so the rule
is stated over the real `Syntax`/`Semantik` `execEnd` fragment (as the
task permits) with the `TableLayout`/`CostSummary`/`Erhaltung`
consumers cited as obligations; (b) the `x - x` and FMA-fusion failure
cases of the same DESIGN row belong to their own rule rows and are
refused here by construction (address addition only), with the
UCOMI-NaN case proved and refused in this file.
